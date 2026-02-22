(* bats-poc -- proof of concept bats reimplementation *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use env as E
#use file as F
#use path as PA
#use process as P
#use result as R
#use sha256 as SHA
#use str as S
#use toml as T

(* ============================================================
   Global state using ATS2 refs (replaces C statics)
   ============================================================ *)

val g_verbose: ref(bool) = ref(false)
val g_quiet: ref(bool) = ref(false)
val g_test_mode: ref(bool) = ref(false)
val g_lock_dev: ref(bool) = ref(false)
val g_repo: ref(string) = ref("")
val g_bin: ref(string) = ref("")

fn is_verbose(): bool = !g_verbose
fn is_quiet(): bool = !g_quiet
fn is_test_mode(): bool = !g_test_mode

(* ============================================================
   String builder helper (safe, no $UNSAFE)
   ============================================================ *)

(* Copy a string into a builder using proof-tracked string length *)
fun bput_loop {sn:nat}{fuel:nat} .<fuel>.
  (b: !$B.builder, s: string sn, slen: int sn, i: int, fuel: int fuel): void =
  if fuel <= 0 then ()
  else let
    val ii = g1ofg0(i)
  in
    if ii >= 0 then
      if $AR.lt1_int_int(ii, slen) then let
        val c = char2int0(string_get_at(s, ii))
        val () = $B.put_byte(b, c)
      in bput_loop(b, s, slen, i + 1, fuel - 1) end
      else ()
    else ()
  end

fn bput {sn:nat} (b: !$B.builder, s: string sn): void = let
  val slen_sz = string1_length(s)
  val slen = g1u2i(slen_sz)
in bput_loop(b, s, slen, 0, $AR.checked_nat(g0ofg1(slen) + 1)) end


fun print_arr {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (buf: !$A.arr(byte, l, n), i: int, len: int, max: int n,
   fuel: int fuel): void =
  if fuel <= 0 then ()
  else if i >= len then ()
  else let val ii = g1ofg0(i) in
    if ii >= 0 then
      if ii < max then let
        val b = byte2int0($A.get<byte>(buf, ii))
        val () = print_char(int2char0(b))
      in print_arr(buf, i + 1, len, max, fuel - 1) end
      else ()
    else ()
  end

(* Find end of null-terminated token *)
fun find_null {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (buf: !$A.arr(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else let val p = g1ofg0(pos) in
    if p >= 0 then
      if p < max then
        if $AR.eq_int_int(byte2int0($A.get<byte>(buf, p)), 0) then pos
        else find_null(buf, pos + 1, max, fuel - 1)
      else pos
    else pos
  end

(* Check if dir entry is "." or ".." *)
fn is_dot_or_dotdot {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool =
  if len = 1 then
    $AR.eq_int_int(byte2int0($A.get<byte>(ent, 0)), 46)
  else if len = 2 then let val i1 = g1ofg0(1) in
    if i1 >= 0 then
      if i1 < max then
        $AR.eq_int_int(byte2int0($A.get<byte>(ent, 0)), 46) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(ent, i1)), 46)
      else false
    else false
  end
  else false

(* Check if name ends with ".bats" (46,98,97,116,115) *)
fn has_bats_ext {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool =
  if len < 5 then false
  else let val p = g1ofg0(len - 5) in
    if p >= 0 then
      if p + 4 < max then let
        val b0 = byte2int0($A.get<byte>(ent, p))
        val b1 = byte2int0($A.get<byte>(ent, p + 1))
        val b2 = byte2int0($A.get<byte>(ent, p + 2))
        val b3 = byte2int0($A.get<byte>(ent, p + 3))
        val b4 = byte2int0($A.get<byte>(ent, p + 4))
      in
        $AR.eq_int_int(b0, 46) && $AR.eq_int_int(b1, 98) &&
        $AR.eq_int_int(b2, 97) && $AR.eq_int_int(b3, 116) &&
        $AR.eq_int_int(b4, 115)
      end else false
    else false
  end

(* Check if a byte is an identifier character *)
fn is_ident_byte(b: int): bool =
  (b >= 97 && b <= 122) ||
  (b >= 65 && b <= 90) ||
  (b >= 48 && b <= 57) ||
  $AR.eq_int_int(b, 95)

fn is_ident_start(b: int): bool =
  (b >= 97 && b <= 122) ||
  (b >= 65 && b <= 90) ||
  $AR.eq_int_int(b, 95)

(* ============================================================
   Lexer: span storage
   Each span = 28 bytes in a builder:
     [0] kind  [1] dest
     [2..5] start  [6..9] end
     [10..13] aux1  [14..17] aux2
     [18..21] aux3  [22..25] aux4
     [26..27] padding
   Kinds: 0=passthrough 1=hash_use 2=pub_decl 3=qualified
          4=unsafe_block 5=unsafe_construct 6=extcode
          7=target 8=unittest 9=restricted 10=unittest_run
   Dests: 0=dats 1=sats 2=both
   ============================================================ *)

fn put_i32(b: !$B.builder, v: int): void = let
  val () = $B.put_byte(b, v mod 256)
  val v1 = v / 256
  val () = $B.put_byte(b, v1 mod 256)
  val v2 = v1 / 256
  val () = $B.put_byte(b, v2 mod 256)
  val () = $B.put_byte(b, v2 / 256)
in end

fn put_span(b: !$B.builder, kind: int, dest: int,
            sp_start: int, sp_end: int,
            a1: int, a2: int, a3: int, a4: int): void = let
  val () = $B.put_byte(b, kind)
  val () = $B.put_byte(b, dest)
  val () = put_i32(b, sp_start)
  val () = put_i32(b, sp_end)
  val () = put_i32(b, a1)
  val () = put_i32(b, a2)
  val () = put_i32(b, a3)
  val () = put_i32(b, a4)
  val () = $B.put_byte(b, 0)
  val () = $B.put_byte(b, 0)
in end

(* Read byte from borrow, returning 0 for out-of-bounds *)
fn src_byte {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): int =
  let val p = g1ofg0(pos) in
    if p >= 0 then
      if p < max then byte2int0($A.read<byte>(src, p))
      else 0
    else 0
  end

fun print_borrow {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (buf: !$A.borrow(byte, l, n), i: int, len: int, max: int n,
   fuel: int fuel): void =
  if fuel <= 0 then ()
  else if i >= len then ()
  else let
    val b = src_byte(buf, i, max)
    val () = print_char(int2char0(b))
  in print_borrow(buf, i + 1, len, max, fuel - 1) end

(* ============================================================
   Lexer: keyword detection helpers
   ============================================================ *)

fn looking_at_2 {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n,
   c0: int, c1: int): bool =
  $AR.eq_int_int(src_byte(src, pos, max), c0) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), c1)

fn is_kw_boundary {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  if pos >= max then true
  else ~(is_ident_byte(src_byte(src, pos, max)))

fn is_kw_boundary_before {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  if pos <= 0 then true
  else ~(is_ident_byte(src_byte(src, pos - 1, max)))

(* #pub = 35,112,117,98 *)
fn looking_at_pub {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int(src_byte(src, pos, max), 35) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), 112) &&
  $AR.eq_int_int(src_byte(src, pos + 2, max), 117) &&
  $AR.eq_int_int(src_byte(src, pos + 3, max), 98) &&
  is_kw_boundary(src, pos + 4, max)

(* #use = 35,117,115,101 *)
fn looking_at_use {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int(src_byte(src, pos, max), 35) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), 117) &&
  $AR.eq_int_int(src_byte(src, pos + 2, max), 115) &&
  $AR.eq_int_int(src_byte(src, pos + 3, max), 101) &&
  is_kw_boundary(src, pos + 4, max)

(* #target = 35,116,97,114,103,101,116 *)
fn looking_at_target {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int(src_byte(src, pos, max), 35) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), 116) &&
  $AR.eq_int_int(src_byte(src, pos + 2, max), 97) &&
  $AR.eq_int_int(src_byte(src, pos + 3, max), 114) &&
  $AR.eq_int_int(src_byte(src, pos + 4, max), 103) &&
  $AR.eq_int_int(src_byte(src, pos + 5, max), 101) &&
  $AR.eq_int_int(src_byte(src, pos + 6, max), 116) &&
  is_kw_boundary(src, pos + 7, max)

(* $UNSAFE = 36,85,78,83,65,70,69 *)
fn looking_at_unsafe {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int(src_byte(src, pos, max), 36) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), 85) &&
  $AR.eq_int_int(src_byte(src, pos + 2, max), 78) &&
  $AR.eq_int_int(src_byte(src, pos + 3, max), 83) &&
  $AR.eq_int_int(src_byte(src, pos + 4, max), 65) &&
  $AR.eq_int_int(src_byte(src, pos + 5, max), 70) &&
  $AR.eq_int_int(src_byte(src, pos + 6, max), 69)

(* $UNITTEST = 36,85,78,73,84,84,69,83,84 *)
fn looking_at_unittest {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int(src_byte(src, pos, max), 36) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), 85) &&
  $AR.eq_int_int(src_byte(src, pos + 2, max), 78) &&
  $AR.eq_int_int(src_byte(src, pos + 3, max), 73) &&
  $AR.eq_int_int(src_byte(src, pos + 4, max), 84) &&
  $AR.eq_int_int(src_byte(src, pos + 5, max), 84) &&
  $AR.eq_int_int(src_byte(src, pos + 6, max), 69) &&
  $AR.eq_int_int(src_byte(src, pos + 7, max), 83) &&
  $AR.eq_int_int(src_byte(src, pos + 8, max), 84)

(* "begin" = 98,101,103,105,110 *)
fn looking_at_begin {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int(src_byte(src, pos, max), 98) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), 101) &&
  $AR.eq_int_int(src_byte(src, pos + 2, max), 103) &&
  $AR.eq_int_int(src_byte(src, pos + 3, max), 105) &&
  $AR.eq_int_int(src_byte(src, pos + 4, max), 110) &&
  is_kw_boundary(src, pos + 5, max)

(* "end" = 101,110,100 *)
fn looking_at_end {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int(src_byte(src, pos, max), 101) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), 110) &&
  $AR.eq_int_int(src_byte(src, pos + 2, max), 100) &&
  is_kw_boundary(src, pos + 3, max) &&
  is_kw_boundary_before(src, pos, max)

(* "as" = 97,115 *)
fn looking_at_as {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int(src_byte(src, pos, max), 97) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), 115) &&
  is_kw_boundary(src, pos + 2, max)

(* "no_mangle" = 110,111,95,109,97,110,103,108,101 *)
fn looking_at_no_mangle {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int(src_byte(src, pos, max), 110) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), 111) &&
  $AR.eq_int_int(src_byte(src, pos + 2, max), 95) &&
  $AR.eq_int_int(src_byte(src, pos + 3, max), 109) &&
  $AR.eq_int_int(src_byte(src, pos + 4, max), 97) &&
  $AR.eq_int_int(src_byte(src, pos + 5, max), 110) &&
  $AR.eq_int_int(src_byte(src, pos + 6, max), 103) &&
  $AR.eq_int_int(src_byte(src, pos + 7, max), 108) &&
  $AR.eq_int_int(src_byte(src, pos + 8, max), 101) &&
  is_kw_boundary(src, pos + 9, max)

(* ============================================================
   Lexer: sub-lexers
   ============================================================ *)

(* Skip whitespace (space/tab only, not newlines) *)
fun skip_ws {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else let val b = src_byte(src, pos, max) in
    if $AR.eq_int_int(b, 32) || $AR.eq_int_int(b, 9) then
      skip_ws(src, pos + 1, max, fuel - 1)
    else pos
  end

(* Skip to end of line, including the newline *)
fun skip_to_eol {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else if pos >= src_len then pos
  else let val b = src_byte(src, pos, max) in
    if $AR.eq_int_int(b, 10) then pos + 1
    else skip_to_eol(src, pos + 1, src_len, max, fuel - 1)
  end

(* Skip ident chars *)
fun skip_ident {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else let val b = src_byte(src, pos, max) in
    if is_ident_byte(b) then skip_ident(src, pos + 1, max, fuel - 1)
    else pos
  end

(* Skip non-whitespace *)
fun skip_nonws {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else let val b = src_byte(src, pos, max) in
    if $AR.eq_int_int(b, 32) || $AR.eq_int_int(b, 9) ||
       $AR.eq_int_int(b, 10) || $AR.eq_int_int(b, 0)
    then pos
    else skip_nonws(src, pos + 1, max, fuel - 1)
  end

(* Lex // line comment. //// = rest-of-file *)
fn lex_line_comment {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) =
  if $AR.eq_int_int(src_byte(src, start + 2, max), 47) &&
     $AR.eq_int_int(src_byte(src, start + 3, max), 47) then let
    (* //// rest-of-file comment *)
    val () = put_span(spans, 0, 0, start, src_len, 0, 0, 0, 0)
  in @(src_len, count + 1) end
  else let
    val ep = skip_to_eol(src, start + 2, src_len, max, $AR.checked_nat(src_len))
    val () = put_span(spans, 0, 0, start, ep, 0, 0, 0, 0)
  in @(ep, count + 1) end

(* Lex /* ... */ block comment *)
fun lex_c_comment_inner {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else if pos + 1 >= src_len then src_len
  else if $AR.eq_int_int(src_byte(src, pos, max), 42) &&
          $AR.eq_int_int(src_byte(src, pos + 1, max), 47) then
    pos + 2  (* found */ *)
  else lex_c_comment_inner(src, pos + 1, src_len, max, fuel - 1)

fn lex_c_comment {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val ep = lex_c_comment_inner(src, start + 2, src_len, max, $AR.checked_nat(src_len))
  val () = put_span(spans, 0, 0, start, ep, 0, 0, 0, 0)
in @(ep, count + 1) end

(* Lex (* ... *) ML comment with nesting *)
fun lex_ml_comment_inner {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   depth: int, fuel: int fuel): int =
  if fuel <= 0 then pos
  else if depth <= 0 then pos
  else if pos + 1 >= src_len then src_len
  else let
    val b0 = src_byte(src, pos, max)
    val b1 = src_byte(src, pos + 1, max)
  in
    if $AR.eq_int_int(b0, 40) && $AR.eq_int_int(b1, 42) then
      lex_ml_comment_inner(src, pos + 2, src_len, max, depth + 1, fuel - 1)
    else if $AR.eq_int_int(b0, 42) && $AR.eq_int_int(b1, 41) then
      lex_ml_comment_inner(src, pos + 2, src_len, max, depth - 1, fuel - 1)
    else
      lex_ml_comment_inner(src, pos + 1, src_len, max, depth, fuel - 1)
  end

fn lex_ml_comment {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val ep = lex_ml_comment_inner(src, start + 2, src_len, max, 1, $AR.checked_nat(src_len))
  val () = put_span(spans, 0, 0, start, ep, 0, 0, 0, 0)
in @(ep, count + 1) end

(* Lex string literal "..." with \" escapes *)
fun lex_string_inner {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else if pos >= src_len then pos
  else let val b = src_byte(src, pos, max) in
    if $AR.eq_int_int(b, 92) then (* backslash *)
      lex_string_inner(src, pos + 2, src_len, max, fuel - 1)
    else if $AR.eq_int_int(b, 34) then pos + 1  (* closing " *)
    else lex_string_inner(src, pos + 1, src_len, max, fuel - 1)
  end

fn lex_string {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val ep = lex_string_inner(src, start + 1, src_len, max, $AR.checked_nat(src_len))
  val () = put_span(spans, 0, 0, start, ep, 0, 0, 0, 0)
in @(ep, count + 1) end

(* Lex char literal '...' *)
fn lex_char_lit {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val p1 = start + 1
  val b1 = src_byte(src, p1, max)
  val p2 = (if $AR.eq_int_int(b1, 92) then p1 + 2 else p1 + 1): int
  val p3 = (if $AR.eq_int_int(src_byte(src, p2, max), 39) then p2 + 1 else p2): int
  val () = put_span(spans, 0, 0, start, p3, 0, 0, 0, 0)
in @(p3, count + 1) end

(* Lex extcode %{ ... %} *)
fun lex_extcode_inner {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else if pos + 1 >= src_len then src_len
  else if $AR.eq_int_int(src_byte(src, pos, max), 37) &&
          $AR.eq_int_int(src_byte(src, pos + 1, max), 125) then
    pos + 2  (* found %} *)
  else lex_extcode_inner(src, pos + 1, src_len, max, fuel - 1)

fn lex_extcode {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val after_open = start + 2
  val bk = src_byte(src, after_open, max)
  (* Check for ^, $, # after %{ *)
  val @(kind, cstart) =
    (if $AR.eq_int_int(bk, 94) then @(1, after_open + 1)   (* ^ = top *)
     else if $AR.eq_int_int(bk, 36) then @(2, after_open + 1)  (* $ = static *)
     else if $AR.eq_int_int(bk, 35) then @(3, after_open + 1)  (* # = header *)
     else @(0, after_open)): @(int, int)                        (* plain *)
  val ep = lex_extcode_inner(src, cstart, src_len, max, $AR.checked_nat(src_len))
  val cend = (if ep >= 2 then ep - 2 else ep): int
  (* kind=6 extcode_block, aux1=contents_start, aux2=contents_end, aux3=extcode_kind *)
  val () = put_span(spans, 6, 0, start, ep, cstart, cend, kind, 0)
in @(ep, count + 1) end

(* Lex #use pkg as Alias [no_mangle] *)
fn lex_hash_use {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val p0 = skip_ws(src, start + 4, max, 256)
  (* package name: read until whitespace *)
  val pkg_start = p0
  val pkg_end = skip_nonws(src, p0, max, 4096)
  val p1 = skip_ws(src, pkg_end, max, 256)
  (* expect "as" *)
  val p2 = (if looking_at_as(src, p1, max) then p1 + 2 else p1): int
  val p3 = skip_ws(src, p2, max, 256)
  (* alias: ident chars *)
  val alias_start = p3
  val alias_end = skip_ident(src, p3, max, 4096)
  val p4 = skip_ws(src, alias_end, max, 256)
  (* check for no_mangle *)
  val mangle = (if looking_at_no_mangle(src, p4, max) then 0 else 1): int
  val ep = skip_to_eol(src, p4, src_len, max, $AR.checked_nat(src_len))
  (* kind=1 hash_use, aux1=pkg_start, aux2=pkg_end, aux3=alias_start, aux4=alias_end
     mangle stored in dest: 2=both+mangle, 0=both+no_mangle *)
  val () = put_span(spans, 1, mangle + 1, start, ep,
                    pkg_start, pkg_end, alias_start, alias_end)
in @(ep, count + 1) end

(* Lex $Alias.member qualified access. Returns (pos, count, matched) *)
fn lex_qualified {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int, bool) = let
  val alias_start = start + 1  (* skip $ *)
  val alias_end = skip_ident(src, alias_start, max, 4096)
  val dot_byte = src_byte(src, alias_end, max)
in
  if $AR.eq_int_int(dot_byte, 46) then let  (* '.' *)
    val member_start = alias_end + 1
    val member_end = skip_ident(src, member_start, max, 4096)
  in
    if member_end > member_start then let
      (* kind=3 qualified_access, aux1..4 = alias_start/end, member_start/end *)
      val () = put_span(spans, 3, 0, start, member_end,
                        alias_start, alias_end, member_start, member_end)
    in @(member_end, count + 1, true) end
    else @(start, count, false)
  end
  else @(start, count, false)
end

(* Check if line at pos is blank (whitespace-only or empty) *)
fun is_blank_line {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): bool =
  if fuel <= 0 then true
  else if pos >= src_len then true
  else let val b = src_byte(src, pos, max) in
    if $AR.eq_int_int(b, 10) then true
    else if $AR.eq_int_int(b, 32) || $AR.eq_int_int(b, 9) then
      is_blank_line(src, pos + 1, src_len, max, fuel - 1)
    else false
  end

(* Lex #pub declaration - reads until blank line or top-level keyword *)
fun lex_pub_lines {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else if pos >= src_len then pos
  else let
    (* consume current line *)
    val eol = skip_to_eol(src, pos, src_len, max, $AR.checked_nat(src_len))
  in
    if eol >= src_len then eol
    else if is_blank_line(src, eol, src_len, max, 256) then eol
    (* Check for top-level keywords at column 0 *)
    else if looking_at_pub(src, eol, max) then eol
    else if looking_at_use(src, eol, max) then eol
    else if looking_at_target(src, eol, max) then eol
    else if looking_at_unsafe(src, eol, max) then eol
    else if looking_at_unittest(src, eol, max) then eol
    else let val b = src_byte(src, eol, max) in
      (* Check common ATS2 keywords: fun, fn, val, var, implement, extern, typedef *)
      if $AR.eq_int_int(b, 102) && (* f *)
         ($AR.eq_int_int(src_byte(src, eol + 1, max), 117) && (* fun *)
          $AR.eq_int_int(src_byte(src, eol + 2, max), 110) &&
          is_kw_boundary(src, eol + 3, max)) then eol
      else if $AR.eq_int_int(b, 102) && (* fn *)
              $AR.eq_int_int(src_byte(src, eol + 1, max), 110) &&
              is_kw_boundary(src, eol + 2, max) then eol
      else if $AR.eq_int_int(b, 118) && (* val *)
              $AR.eq_int_int(src_byte(src, eol + 1, max), 97) &&
              $AR.eq_int_int(src_byte(src, eol + 2, max), 108) &&
              is_kw_boundary(src, eol + 3, max) then eol
      else if $AR.eq_int_int(b, 105) && (* implement *)
              $AR.eq_int_int(src_byte(src, eol + 1, max), 109) &&
              $AR.eq_int_int(src_byte(src, eol + 2, max), 112) &&
              $AR.eq_int_int(src_byte(src, eol + 3, max), 108) &&
              $AR.eq_int_int(src_byte(src, eol + 4, max), 101) &&
              $AR.eq_int_int(src_byte(src, eol + 5, max), 109) &&
              $AR.eq_int_int(src_byte(src, eol + 6, max), 101) &&
              $AR.eq_int_int(src_byte(src, eol + 7, max), 110) &&
              $AR.eq_int_int(src_byte(src, eol + 8, max), 116) &&
              is_kw_boundary(src, eol + 9, max) then eol
      else if $AR.eq_int_int(b, 37) && (* %{ *)
              $AR.eq_int_int(src_byte(src, eol + 1, max), 123) then eol
      else lex_pub_lines(src, eol, src_len, max, fuel - 1)
    end
  end

fn lex_pub_decl {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val p0 = skip_ws(src, start + 4, max, 256)  (* skip #pub + whitespace *)
  val contents_start = p0
  val ep = lex_pub_lines(src, p0, src_len, max, $AR.checked_nat(src_len))
  (* kind=2 pub_decl, aux1=contents_start, aux2=contents_end *)
  val () = put_span(spans, 2, 1, start, ep, contents_start, ep, 0, 0)
in @(ep, count + 1) end

(* Lex $UNSAFE begin...end or $UNSAFE.ident *)
fun find_end_kw {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then src_len
  else if pos >= src_len then src_len
  else if looking_at_end(src, pos, max) then pos
  else find_end_kw(src, pos + 1, src_len, max, fuel - 1)

fn lex_unsafe_dispatch {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int, bool) = let
  val after = start + 7  (* after "$UNSAFE" *)
  val next = src_byte(src, after, max)
in
  if $AR.eq_int_int(next, 46) then let  (* $UNSAFE.ident *)
    val ident_end = skip_ident(src, after + 1, max, 4096)
    val () = put_span(spans, 5, 0, start, ident_end, 0, 0, 0, 0)
  in @(ident_end, count + 1, true) end
  else let
    val p0 = skip_ws(src, after, max, 256)
  in
    if looking_at_begin(src, p0, max) then let
      val contents_start = p0 + 5
      val end_pos = find_end_kw(src, contents_start, src_len, max, $AR.checked_nat(src_len))
      val ep = (if end_pos < src_len then end_pos + 3 else end_pos): int
      val () = put_span(spans, 4, 0, start, ep, contents_start, end_pos, 0, 0)
    in @(ep, count + 1, true) end
    else @(start, count, false)
  end
end

(* Lex $UNITTEST begin...end (kind=8) and $UNITTEST.run begin...end (kind=10) *)
fn lex_unittest_dispatch {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int, bool) = let
  val after = start + 9  (* after "$UNITTEST" *)
  val p0 = skip_ws(src, after, max, 256)
  (* Check if next char is '.' (46 = '.') indicating .run *)
  val is_dot = $AR.eq_int_int(src_byte(src, p0, max), 46)
  (* Check for ".run" = 46,114,117,110 *)
  val is_run = is_dot &&
    $AR.eq_int_int(src_byte(src, p0 + 1, max), 114) &&
    $AR.eq_int_int(src_byte(src, p0 + 2, max), 117) &&
    $AR.eq_int_int(src_byte(src, p0 + 3, max), 110)
in
  if is_run then let
    val p1 = skip_ws(src, p0 + 4, max, 256)
  in
    if looking_at_begin(src, p1, max) then let
      val contents_start = p1 + 5
      val end_pos = find_end_kw(src, contents_start, src_len, max, $AR.checked_nat(src_len))
      val ep = (if end_pos < src_len then end_pos + 3 else end_pos): int
      val () = put_span(spans, 10, 0, start, ep, contents_start, end_pos, 0, 0)
    in @(ep, count + 1, true) end
    else @(start, count, false)
  end
  else if looking_at_begin(src, p0, max) then let
    val contents_start = p0 + 5
    val end_pos = find_end_kw(src, contents_start, src_len, max, $AR.checked_nat(src_len))
    val ep = (if end_pos < src_len then end_pos + 3 else end_pos): int
    val () = put_span(spans, 8, 0, start, ep, contents_start, end_pos, 0, 0)
  in @(ep, count + 1, true) end
  else @(start, count, false)
end

(* Lex #target native|wasm *)
fn lex_target_decl {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val p0 = skip_ws(src, start + 7, max, 256)
  val ident_end = skip_ident(src, p0, max, 4096)
  val ep = skip_to_eol(src, ident_end, src_len, max, $AR.checked_nat(src_len))
  (* aux1: 0=native, 1=wasm. Check first byte: 'n'=110 native, 'w'=119 wasm *)
  val target = (if $AR.eq_int_int(src_byte(src, p0, max), 119) then 1 else 0): int
  val () = put_span(spans, 7, 2, start, ep, target, 0, 0, 0)
in @(ep, count + 1) end

(* ============================================================
   Lexer: passthrough (advance until next token-start)
   ============================================================ *)

fun lex_passthrough_scan {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else if pos >= src_len then pos
  else let
    val b = src_byte(src, pos, max)
    val b1 = src_byte(src, pos + 1, max)
  in
    (* // or /* *)
    if $AR.eq_int_int(b, 47) && ($AR.eq_int_int(b1, 47) || $AR.eq_int_int(b1, 42))
    then pos
    (* paren-star ML comment *)
    else if $AR.eq_int_int(b, 40) && $AR.eq_int_int(b1, 42) then pos
    (* " *)
    else if $AR.eq_int_int(b, 34) then pos
    (* ' *)
    else if $AR.eq_int_int(b, 39) then pos
    (* %{ *)
    else if $AR.eq_int_int(b, 37) && $AR.eq_int_int(b1, 123) then pos
    (* # directives *)
    else if $AR.eq_int_int(b, 35) &&
      (looking_at_pub(src, pos, max) || looking_at_use(src, pos, max) ||
       looking_at_target(src, pos, max)) then pos
    (* $ qualified or $UNSAFE or $UNITTEST *)
    else if $AR.eq_int_int(b, 36) && is_ident_start(b1) then pos
    else lex_passthrough_scan(src, pos + 1, src_len, max, fuel - 1)
  end

(* ============================================================
   Lexer: main loop
   ============================================================ *)

fun lex_main {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, pos: int, count: int,
   fuel: int fuel): @(int, int) =
  if fuel <= 0 then @(pos, count)
  else if pos >= src_len then @(pos, count)
  else let
    val b0 = src_byte(src, pos, max)
    val b1 = src_byte(src, pos + 1, max)
  in
    (* // line comment *)
    if $AR.eq_int_int(b0, 47) && $AR.eq_int_int(b1, 47) then let
      val @(np, nc) = lex_line_comment(src, src_len, max, spans, pos, count)
    in lex_main(src, src_len, max, spans, np, nc, fuel - 1) end

    (* /* C comment *)
    else if $AR.eq_int_int(b0, 47) && $AR.eq_int_int(b1, 42) then let
      val @(np, nc) = lex_c_comment(src, src_len, max, spans, pos, count)
    in lex_main(src, src_len, max, spans, np, nc, fuel - 1) end

    (* paren-star ML comment *)
    else if $AR.eq_int_int(b0, 40) && $AR.eq_int_int(b1, 42) then let
      val @(np, nc) = lex_ml_comment(src, src_len, max, spans, pos, count)
    in lex_main(src, src_len, max, spans, np, nc, fuel - 1) end

    (* " string *)
    else if $AR.eq_int_int(b0, 34) then let
      val @(np, nc) = lex_string(src, src_len, max, spans, pos, count)
    in lex_main(src, src_len, max, spans, np, nc, fuel - 1) end

    (* ' char *)
    else if $AR.eq_int_int(b0, 39) then let
      val @(np, nc) = lex_char_lit(src, src_len, max, spans, pos, count)
    in lex_main(src, src_len, max, spans, np, nc, fuel - 1) end

    (* %{ extcode *)
    else if $AR.eq_int_int(b0, 37) && $AR.eq_int_int(b1, 123) then let
      val @(np, nc) = lex_extcode(src, src_len, max, spans, pos, count)
    in lex_main(src, src_len, max, spans, np, nc, fuel - 1) end

    (* #pub *)
    else if looking_at_pub(src, pos, max) then let
      val @(np, nc) = lex_pub_decl(src, src_len, max, spans, pos, count)
    in lex_main(src, src_len, max, spans, np, nc, fuel - 1) end

    (* #target *)
    else if looking_at_target(src, pos, max) then let
      val @(np, nc) = lex_target_decl(src, src_len, max, spans, pos, count)
    in lex_main(src, src_len, max, spans, np, nc, fuel - 1) end

    (* $UNSAFE *)
    else if looking_at_unsafe(src, pos, max) then let
      val @(np, nc, matched) = lex_unsafe_dispatch(src, src_len, max, spans, pos, count)
    in
      if matched then lex_main(src, src_len, max, spans, np, nc, fuel - 1)
      else let
        (* Fall through to passthrough *)
        val ep = lex_passthrough_scan(src, pos + 1, src_len, max, $AR.checked_nat(src_len))
        val () = put_span(spans, 0, 0, pos, ep, 0, 0, 0, 0)
      in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    end

    (* $UNITTEST *)
    else if looking_at_unittest(src, pos, max) then let
      val @(np, nc, matched) = lex_unittest_dispatch(src, src_len, max, spans, pos, count)
    in
      if matched then lex_main(src, src_len, max, spans, np, nc, fuel - 1)
      else let
        val ep = lex_passthrough_scan(src, pos + 1, src_len, max, $AR.checked_nat(src_len))
        val () = put_span(spans, 0, 0, pos, ep, 0, 0, 0, 0)
      in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    end

    (* #use *)
    else if looking_at_use(src, pos, max) then let
      val @(np, nc) = lex_hash_use(src, src_len, max, spans, pos, count)
    in lex_main(src, src_len, max, spans, np, nc, fuel - 1) end

    (* $ident.ident qualified access *)
    else if $AR.eq_int_int(b0, 36) && is_ident_start(b1) then let
      val @(np, nc, matched) = lex_qualified(src, src_len, max, spans, pos, count)
    in
      if matched then lex_main(src, src_len, max, spans, np, nc, fuel - 1)
      else let
        val ep = lex_passthrough_scan(src, pos + 1, src_len, max, $AR.checked_nat(src_len))
        val () = put_span(spans, 0, 0, pos, ep, 0, 0, 0, 0)
      in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    end

    (* Default: passthrough *)
    else let
      val ep = lex_passthrough_scan(src, pos + 1, src_len, max, $AR.checked_nat(src_len))
      val () = put_span(spans, 0, 0, pos, ep, 0, 0, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
  end

(* Top-level lex function: returns (span_arr, span_arr_len, span_count) *)
fn do_lex {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n
  ): @([ls:agz] $A.arr(byte, ls, 65536), int, int) = let
  val span_builder = $B.create()
  val @(_, span_count) = lex_main(src, src_len, max, span_builder, 0, 0, $AR.checked_nat(src_len))
  val @(span_arr, span_arr_len) = $B.to_arr(span_builder)
in @(span_arr, span_arr_len, span_count) end

(* ============================================================
   Emitter: read span records
   ============================================================ *)

fn read_i32 {l:agz}{n:pos}
  (bv: !$A.borrow(byte, l, n), off: int, max: int n): int =
  let val o = g1ofg0(off) in
    if o >= 0 then
      if o + 3 < max then let
        val b0 = byte2int0($A.read<byte>(bv, o))
        val b1 = byte2int0($A.read<byte>(bv, o + 1))
        val b2 = byte2int0($A.read<byte>(bv, o + 2))
        val b3 = byte2int0($A.read<byte>(bv, o + 3))
      in b0 + b1 * 256 + b2 * 65536 + b3 * 16777216 end
      else 0
    else 0
  end

fn span_kind {l:agz}{n:pos}
  (spans: !$A.borrow(byte, l, n), idx: int, max: int n): int =
  src_byte(spans, idx * 28, max)

fn span_dest {l:agz}{n:pos}
  (spans: !$A.borrow(byte, l, n), idx: int, max: int n): int =
  src_byte(spans, idx * 28 + 1, max)

fn span_start {l:agz}{n:pos}
  (spans: !$A.borrow(byte, l, n), idx: int, max: int n): int =
  read_i32(spans, idx * 28 + 2, max)

fn span_end {l:agz}{n:pos}
  (spans: !$A.borrow(byte, l, n), idx: int, max: int n): int =
  read_i32(spans, idx * 28 + 6, max)

fn span_aux1 {l:agz}{n:pos}
  (spans: !$A.borrow(byte, l, n), idx: int, max: int n): int =
  read_i32(spans, idx * 28 + 10, max)

fn span_aux2 {l:agz}{n:pos}
  (spans: !$A.borrow(byte, l, n), idx: int, max: int n): int =
  read_i32(spans, idx * 28 + 14, max)

fn span_aux3 {l:agz}{n:pos}
  (spans: !$A.borrow(byte, l, n), idx: int, max: int n): int =
  read_i32(spans, idx * 28 + 18, max)

fn span_aux4 {l:agz}{n:pos}
  (spans: !$A.borrow(byte, l, n), idx: int, max: int n): int =
  read_i32(spans, idx * 28 + 22, max)

(* ============================================================
   Emitter: copy source range to builder, count newlines
   ============================================================ *)

(* Copy bytes from source borrow to builder *)
fun emit_range {ls:agz}{ns:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, out: !$B.builder, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if start >= end_pos then ()
  else let
    val b = src_byte(src, start, max)
    val () = $B.put_byte(out, b)
  in emit_range(src, start + 1, end_pos, max, out, fuel - 1) end

(* Count newlines in source range, emit that many newlines *)
fun emit_blanks_count {ls:agz}{ns:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, fuel: int fuel): int =
  if fuel <= 0 then 0
  else if start >= end_pos then 0
  else let
    val b = src_byte(src, start, max)
    val rest = emit_blanks_count(src, start + 1, end_pos, max, fuel - 1)
  in
    if $AR.eq_int_int(b, 10) then rest + 1
    else rest
  end

fun emit_newlines {fuel:nat} .<fuel>.
  (out: !$B.builder, count: int, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if count <= 0 then ()
  else let
    val () = $B.put_byte(out, 10)
  in emit_newlines(out, count - 1, fuel - 1) end

fn emit_blanks {ls:agz}{ns:pos}
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, out: !$B.builder): void = let
  val nl_count = emit_blanks_count(src, start, end_pos, max,
    $AR.checked_nat(end_pos - start + 1))
  val () = emit_newlines(out, nl_count, $AR.checked_nat(nl_count + 1))
in end

(* ============================================================
   Emitter: name mangling (__BATS__<mangled_pkg>_<member>)
   ============================================================ *)

(* Emit __BATS__ prefix: 95,95,66,65,84,83,95,95 *)
fn emit_bats_prefix(out: !$B.builder): void = let
  val () = $B.put_byte(out, 95)   (* _ *)
  val () = $B.put_byte(out, 95)   (* _ *)
  val () = $B.put_byte(out, 66)   (* B *)
  val () = $B.put_byte(out, 65)   (* A *)
  val () = $B.put_byte(out, 84)   (* T *)
  val () = $B.put_byte(out, 83)   (* S *)
  val () = $B.put_byte(out, 95)   (* _ *)
  val () = $B.put_byte(out, 95)   (* _ *)
in end

(* Emit hex digit for a nibble *)
fn emit_hex_nibble(out: !$B.builder, v: int): void =
  if v < 10 then $B.put_byte(out, v + 48)  (* '0' + v *)
  else $B.put_byte(out, v - 10 + 97)  (* 'a' + v-10 *)

(* Mangle a single byte: alnum passes through, / becomes __, else _XX *)
fn emit_mangled_byte(out: !$B.builder, b: int): void =
  if (b >= 97 && b <= 122) || (b >= 65 && b <= 90) ||
     (b >= 48 && b <= 57) then
    $B.put_byte(out, b)
  else if $AR.eq_int_int(b, 47) then let  (* '/' -> __ *)
    val () = $B.put_byte(out, 95)
    val () = $B.put_byte(out, 95)
  in end
  else let  (* _XX hex *)
    val () = $B.put_byte(out, 95)
    val () = emit_hex_nibble(out, b / 16)
    val () = emit_hex_nibble(out, b mod 16)
  in end

(* Emit mangled package name from source range *)
fun emit_mangled_pkg {ls:agz}{ns:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, out: !$B.builder, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if start >= end_pos then ()
  else let
    val b = src_byte(src, start, max)
    val () = emit_mangled_byte(out, b)
  in emit_mangled_pkg(src, start + 1, end_pos, max, out, fuel - 1) end

(* Emit qualified access: __BATS__<mangled_pkg>_<member> *)
fn emit_qualified {ls:agz}{ns:pos}{lp:agz}{np:pos}
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_idx: int, span_max: int np,
   out: !$B.builder): void = let
  val alias_s = span_aux1(spans, span_idx, span_max)
  val alias_e = span_aux2(spans, span_idx, span_max)
  val member_s = span_aux3(spans, span_idx, span_max)
  val member_e = span_aux4(spans, span_idx, span_max)
  (* For now, emit $alias.member as-is since we need the use-table
     to look up which package the alias maps to.
     TODO: implement use-table lookup for proper mangling *)
  val () = $B.put_byte(out, 36)  (* $ *)
  val () = emit_range(src, alias_s, alias_e, src_max, out,
    $AR.checked_nat(alias_e - alias_s + 1))
  val () = $B.put_byte(out, 46)  (* . *)
  val () = emit_range(src, member_s, member_e, src_max, out,
    $AR.checked_nat(member_e - member_s + 1))
in end

(* ============================================================
   Emitter: generate dats prelude (staload self + dependencies)
   ============================================================ *)

(* Emit: staload "./FILENAME.sats"\n *)
fn emit_self_staload(out: !$B.builder, filename_len: int): void = let
  (* "staload " = 115,116,97,108,111,97,100,32 *)
  val () = $B.put_byte(out, 115)
  val () = $B.put_byte(out, 116)
  val () = $B.put_byte(out, 97)
  val () = $B.put_byte(out, 108)
  val () = $B.put_byte(out, 111)
  val () = $B.put_byte(out, 97)
  val () = $B.put_byte(out, 100)
  val () = $B.put_byte(out, 32)
  (* "./ *)
  val () = $B.put_byte(out, 34)
  val () = $B.put_byte(out, 46)
  val () = $B.put_byte(out, 47)
in end

(* Emit one staload line for a #use dependency *)
fn emit_dep_staload {ls:agz}{ns:pos}{lp:agz}{np:pos}
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_idx: int, span_max: int np,
   out: !$B.builder): void = let
  val pkg_s = span_aux1(spans, span_idx, span_max)
  val pkg_e = span_aux2(spans, span_idx, span_max)
  (* staload " *)
  val () = $B.put_byte(out, 115)
  val () = $B.put_byte(out, 116)
  val () = $B.put_byte(out, 97)
  val () = $B.put_byte(out, 108)
  val () = $B.put_byte(out, 111)
  val () = $B.put_byte(out, 97)
  val () = $B.put_byte(out, 100)
  val () = $B.put_byte(out, 32)
  val () = $B.put_byte(out, 34)
  (* package path *)
  val () = emit_range(src, pkg_s, pkg_e, src_max, out,
    $AR.checked_nat(pkg_e - pkg_s + 1))
  (* /src/lib.dats" + newline *)
  val () = $B.put_byte(out, 47)   (* / *)
  val () = $B.put_byte(out, 115)  (* s *)
  val () = $B.put_byte(out, 114)  (* r *)
  val () = $B.put_byte(out, 99)   (* c *)
  val () = $B.put_byte(out, 47)   (* / *)
  val () = $B.put_byte(out, 108)  (* l *)
  val () = $B.put_byte(out, 105)  (* i *)
  val () = $B.put_byte(out, 98)   (* b *)
  val () = $B.put_byte(out, 46)   (* . *)
  val () = $B.put_byte(out, 100)  (* d *)
  val () = $B.put_byte(out, 97)   (* a *)
  val () = $B.put_byte(out, 116)  (* t *)
  val () = $B.put_byte(out, 115)  (* s *)
  val () = $B.put_byte(out, 34)   (* " *)
  val () = $B.put_byte(out, 10)   (* \n *)
in end

(* ============================================================
   Emitter: main emit loop
   ============================================================ *)

fun emit_spans {ls:agz}{ns:pos}{lp:agz}{np:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_max: int np,
   span_count: int, idx: int,
   sats: !$B.builder, dats: !$B.builder,
   fuel: int fuel): void =
  if fuel <= 0 then ()
  else if idx >= span_count then ()
  else let
    val kind = span_kind(spans, idx, span_max)
    val dest = span_dest(spans, idx, span_max)
    val ss = span_start(spans, idx, span_max)
    val se = span_end(spans, idx, span_max)
  in
    (* kind=0: passthrough *)
    if $AR.eq_int_int(kind, 0) then let
      val fuel2 = $AR.checked_nat(se - ss + 1)
      val () = (if $AR.eq_int_int(dest, 0) || $AR.eq_int_int(dest, 2) then
                  emit_range(src, ss, se, src_max, dats, fuel2)
                else ())
      val () = (if $AR.eq_int_int(dest, 1) || $AR.eq_int_int(dest, 2) then
                  emit_range(src, ss, se, src_max, sats, fuel2)
                else ())
      val () = (if $AR.eq_int_int(dest, 0) then
                  emit_blanks(src, ss, se, src_max, sats)
                else ())
      val () = (if $AR.eq_int_int(dest, 1) then
                  emit_blanks(src, ss, se, src_max, dats)
                else ())
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=1: hash_use - blank out in both, staloads go in prelude *)
    else if $AR.eq_int_int(kind, 1) then let
      val () = emit_blanks(src, ss, se, src_max, sats)
      val () = emit_blanks(src, ss, se, src_max, dats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=2: pub_decl - content to sats, blanks to dats *)
    else if $AR.eq_int_int(kind, 2) then let
      val cs = span_aux1(spans, idx, span_max)
      val ce = span_aux2(spans, idx, span_max)
      (* Blank the #pub prefix in sats *)
      val () = emit_blanks(src, ss, cs, src_max, sats)
      (* Emit contents to sats *)
      val () = emit_range(src, cs, ce, src_max, sats,
        $AR.checked_nat(ce - cs + 1))
      (* Blank everything in dats *)
      val () = emit_blanks(src, ss, se, src_max, dats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=3: qualified_access - emit $alias.member to both *)
    else if $AR.eq_int_int(kind, 3) then let
      val () = emit_qualified(src, src_max, spans, idx, span_max, dats)
      val () = emit_qualified(src, src_max, spans, idx, span_max, sats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=4: unsafe_block - emit contents only *)
    else if $AR.eq_int_int(kind, 4) then let
      val cs = span_aux1(spans, idx, span_max)
      val ce = span_aux2(spans, idx, span_max)
      (* Blank the $UNSAFE begin marker *)
      val () = emit_blanks(src, ss, cs, src_max, dats)
      val () = emit_blanks(src, ss, cs, src_max, sats)
      (* Emit contents *)
      val fuel2 = $AR.checked_nat(ce - cs + 1)
      val () = emit_range(src, cs, ce, src_max, dats, fuel2)
      val () = emit_range(src, cs, ce, src_max, sats, fuel2)
      (* Blank the end marker *)
      val () = emit_blanks(src, ce, se, src_max, dats)
      val () = emit_blanks(src, ce, se, src_max, sats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=5: unsafe_construct - emit as-is *)
    else if $AR.eq_int_int(kind, 5) then let
      val fuel2 = $AR.checked_nat(se - ss + 1)
      val () = emit_range(src, ss, se, src_max, dats, fuel2)
      val () = emit_range(src, ss, se, src_max, sats, fuel2)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=6: extcode_block - emit as-is to dats *)
    else if $AR.eq_int_int(kind, 6) then let
      val fuel2 = $AR.checked_nat(se - ss + 1)
      val () = emit_range(src, ss, se, src_max, dats, fuel2)
      val () = emit_blanks(src, ss, se, src_max, sats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=7: target_decl - blank everything *)
    else if $AR.eq_int_int(kind, 7) then let
      val () = emit_blanks(src, ss, se, src_max, sats)
      val () = emit_blanks(src, ss, se, src_max, dats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=8: unittest_block - emit contents in test mode, blank otherwise *)
    else if $AR.eq_int_int(kind, 8) then let
      val cs = span_aux1(spans, idx, span_max)
      val ce = span_aux2(spans, idx, span_max)
      val tm8 = if is_test_mode() then 1 else 0
      val in_test = $AR.gt_int_int(tm8, 0)
      val () = (if in_test then let
        val fuel2 = $AR.checked_nat(ce - cs + 1)
        val () = emit_blanks(src, ss, cs, src_max, dats)
        val () = emit_blanks(src, ss, cs, src_max, sats)
        val () = emit_range(src, cs, ce, src_max, dats, fuel2)
        val () = emit_blanks(src, ce, se, src_max, dats)
        val () = emit_blanks(src, ss, se, src_max, sats)
      in end
      else let
        val () = emit_blanks(src, ss, se, src_max, sats)
        val () = emit_blanks(src, ss, se, src_max, dats)
      in end)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=9: restricted_keyword - emit as-is for now *)
    else if $AR.eq_int_int(kind, 9) then let
      val fuel2 = $AR.checked_nat(se - ss + 1)
      val () = emit_range(src, ss, se, src_max, dats, fuel2)
      val () = emit_range(src, ss, se, src_max, sats, fuel2)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=10: unittest_run - emit contents in test mode, blank otherwise *)
    else let
      val cs = span_aux1(spans, idx, span_max)
      val ce = span_aux2(spans, idx, span_max)
      val tm10 = if is_test_mode() then 1 else 0
      val in_test = $AR.gt_int_int(tm10, 0)
      val () = (if in_test then let
        val fuel2 = $AR.checked_nat(ce - cs + 1)
        val () = emit_blanks(src, ss, cs, src_max, dats)
        val () = emit_blanks(src, ss, cs, src_max, sats)
        val () = emit_range(src, cs, ce, src_max, dats, fuel2)
        val () = emit_blanks(src, ce, se, src_max, dats)
        val () = emit_blanks(src, ss, se, src_max, sats)
      in end
      else let
        val () = emit_blanks(src, ss, se, src_max, sats)
        val () = emit_blanks(src, ss, se, src_max, dats)
      in end)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end
  end

(* Build dats prelude: self-staload + dependency staloads *)
fun build_prelude {ls:agz}{ns:pos}{lp:agz}{np:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_max: int np,
   span_count: int, idx: int,
   prelude: !$B.builder, fuel: int fuel): int =
  if fuel <= 0 then 0
  else if idx >= span_count then 0
  else let
    val kind = span_kind(spans, idx, span_max)
  in
    if $AR.eq_int_int(kind, 1) then let  (* hash_use *)
      val () = emit_dep_staload(src, src_max, spans, idx, span_max, prelude)
      val rest = build_prelude(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, fuel - 1)
    in rest + 1 end
    else
      build_prelude(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, fuel - 1)
  end

(* Top-level emit: takes source + spans, returns (sats_arr, sats_len, dats_arr, dats_len, prelude_lines) *)
fn do_emit {ls:agz}{ns:pos}{lp:agz}{np:pos}
  (src: !$A.borrow(byte, ls, ns), src_len: int, src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_max: int np,
   span_count: int
  ): @([la:agz] $A.arr(byte, la, 65536), int,
      [lb:agz] $A.arr(byte, lb, 65536), int, int) = let
  val sats_b = $B.create()
  val dats_b = $B.create()
  val prelude_b = $B.create()

  (* Build prelude: self-staload line is always 1 line *)
  val dep_count = build_prelude(src, src_max, spans, span_max,
    span_count, 0, prelude_b, $AR.checked_nat(span_count + 1))
  val prelude_lines = dep_count + 1  (* self-staload + dep staloads *)

  (* Emit the prelude into dats *)
  val @(pre_arr, pre_len) = $B.to_arr(prelude_b)
  val @(fz_pre, bv_pre) = $A.freeze<byte>(pre_arr)
  val () = emit_range(bv_pre, 0, pre_len, 65536, dats_b,
    $AR.checked_nat(pre_len + 1))
  val () = $A.drop<byte>(fz_pre, bv_pre)
  val () = $A.free<byte>($A.thaw<byte>(fz_pre))

  (* Emit all spans *)
  val () = emit_spans(src, src_max, spans, span_max, span_count, 0,
    sats_b, dats_b, $AR.checked_nat(span_count + 1))

  val @(sats_arr, sats_len) = $B.to_arr(sats_b)
  val @(dats_arr, dats_len) = $B.to_arr(dats_b)
in @(sats_arr, sats_len, dats_arr, dats_len, prelude_lines) end

(* ============================================================
   Build pipeline: helpers
   ============================================================ *)

(* Copy bytes from a frozen borrow into a builder *)
fun copy_to_builder {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), start: int, len: int, max: int n,
   dst: !$B.builder, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if start >= len then ()
  else let
    val b = src_byte(src, start, max)
    val () = $B.put_byte(dst, b)
  in copy_to_builder(src, start + 1, len, max, dst, fuel - 1) end

(* Find start of basename in a null-terminated path (after last '/') *)
fun find_basename_start {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (bv: !$A.borrow(byte, l, n), pos: int, max: int n,
   last: int, fuel: int fuel): int =
  if fuel <= 0 then last + 1
  else let
    val b = src_byte(bv, pos, max)
  in
    if $AR.eq_int_int(b, 0) then last + 1
    else if $AR.eq_int_int(b, 47) then
      find_basename_start(bv, pos + 1, max, pos, fuel - 1)
    else find_basename_start(bv, pos + 1, max, last, fuel - 1)
  end

(* Find null terminator in a borrow *)
fun find_null_bv {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (bv: !$A.borrow(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else let
    val b = src_byte(bv, pos, max)
  in
    if $AR.eq_int_int(b, 0) then pos
    else find_null_bv(bv, pos + 1, max, fuel - 1)
  end

(* Write first lim bytes of a frozen builder borrow to a buffered writer *)
fun wbw_loop {l:agz}{fuel:nat} .<fuel>.
  (bw: !$F.buf_writer, bv: !$A.borrow(byte, l, 65536),
   i: int, lim: int, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if i >= lim then ()
  else let
    val b = src_byte(bv, i, 65536)
    val wr = $F.buf_write_byte(bw, b)
    val () = $R.discard<int><int>(wr)
  in wbw_loop(bw, bv, i + 1, lim, fuel - 1) end

(* Compare mtimes of two paths (as 65536-byte null-term borrows). Returns true if p1 is newer. *)
fn is_newer {l1:agz}{l2:agz}
  (p1: !$A.borrow(byte, l1, 65536), p2: !$A.borrow(byte, l2, 65536)): bool = let
  val mt1 = (case+ $F.file_mtime(p1, 65536) of
    | ~$R.ok(t) => t | ~$R.err(_) => ~1): int
  val mt2 = (case+ $F.file_mtime(p2, 65536) of
    | ~$R.ok(t) => t | ~$R.err(_) => ~1): int
in $AR.gt_int_int(mt1, 0) && $AR.gt_int_int(mt1, mt2) end

(* Check if out_path is newer than in_path (both built via builders) *)
fn freshness_check_bv
  (out_b: $B.builder, in_b: $B.builder): bool = let
  val @(oa, _) = $B.to_arr(out_b)
  val @(ia, _) = $B.to_arr(in_b)
  val @(fz_o, bv_o) = $A.freeze<byte>(oa)
  val @(fz_i, bv_i) = $A.freeze<byte>(ia)
  val result = is_newer(bv_o, bv_i)
  val () = $A.drop<byte>(fz_o, bv_o)
  val () = $A.free<byte>($A.thaw<byte>(fz_o))
  val () = $A.drop<byte>(fz_i, bv_i)
  val () = $A.free<byte>($A.thaw<byte>(fz_i))
in result end

(* Check if a null-separated token in buf at [start..end) matches a string s at si..si+slen *)
(* s_arr is a 4096-byte arr containing the null-terminated string *)
fun token_eq_arr {l:agz}{ls:agz}{fuel:nat} .<fuel>.
  (buf: !$A.arr(byte, l, 4096), tstart: int, tend: int,
   sarr: !$A.arr(byte, ls, 4096), si: int, fuel: int fuel): bool =
  if fuel <= 0 then tstart >= tend
  else if tstart >= tend then
    (* Check sarr[si] = 0 (end of string) *)
    let
      val si1 = g1ofg0(si)
    in
      if si1 >= 0 then
        if si1 < 4096 then $AR.eq_int_int(byte2int0($A.get<byte>(sarr, si1)), 0)
        else true
      else true
    end
  else let
    val ti = g1ofg0(tstart)
    val si1 = g1ofg0(si)
  in
    if ti >= 0 then
      if ti < 4096 then
        if si1 >= 0 then
          if si1 < 4096 then let
            val tb = byte2int0($A.get<byte>(buf, ti))
            val sb = byte2int0($A.get<byte>(sarr, si1))
          in
            if $AR.neq_int_int(tb, sb) then false
            else if $AR.eq_int_int(sb, 0) then false  (* null in string = end of pattern *)
            else token_eq_arr(buf, tstart + 1, tend, sarr, si + 1, fuel - 1)
          end
          else false
        else false
      else false
    else false
  end

(* Copy bytes from arr[start..end) into builder: passes both linear vars explicitly *)
fun arr_range_to_builder {l:agz}{fuel:nat} .<fuel>.
  (src: !$A.arr(byte, l, 4096), i: int, lim: int,
   dst: !$B.builder, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if i >= lim then ()
  else let
    val ii = g1ofg0(i)
  in
    if ii >= 0 then
      if $AR.lt1_int_int(ii, 4096) then let
        val b = byte2int0($A.get<byte>(src, ii))
        val () = $B.put_byte(dst, b)
      in arr_range_to_builder(src, i + 1, lim, dst, fuel - 1) end
      else ()
    else ()
  end

(* Fill helper for str_to_arr4096: uses proof-tracked string length *)
fun str_fill_loop {lb:agz}{sn:nat}{fuel:nat} .<fuel>.
  (b: !$A.arr(byte, lb, 4096), s: string sn, slen: int sn, i: int, fuel: int fuel): void =
  if fuel <= 0 then ()
  else let
    val ii = g1ofg0(i)
  in
    if ii >= 0 then
      if $AR.lt1_int_int(ii, slen) then
        if $AR.lt1_int_int(ii, 4096) then let
          val c = char2int0(string_get_at(s, ii))
          val () = $A.set<byte>(b, ii, int2byte0(c))
        in str_fill_loop(b, s, slen, i + 1, fuel - 1) end
        else ()
      else ()
    else ()
  end

(* Build a 4096-byte arr from a string literal *)
fn str_to_arr4096 {sn:nat} (s: string sn): [ls:agz] $A.arr(byte, ls, 4096) = let
  val b = $A.alloc<byte>(4096)
  val slen_sz = string1_length(s)
  val slen = g1u2i(slen_sz)
  val () = str_fill_loop(b, s, slen, 0, $AR.checked_nat(g0ofg1(slen) + 2))
in
  (if slen < 4096 then $A.set<byte>(b, slen, int2byte0(0))
  else ()); b
end

(* Check if token in buf at [tstart..tend) equals null-term string in sarr *)
fn token_matches {l:agz}{ls:agz}
  (buf: !$A.arr(byte, l, 4096), tstart: int, tend: int,
   sarr: !$A.arr(byte, ls, 4096)): bool =
  token_eq_arr(buf, tstart, tend, sarr, 0, 4096)

(* Scan null-separated tokens from offset `start`, return 1 if any matches `flag` *)
fun has_flag_loop {l:agz}{ls:agz}{fuel:nat} .<fuel>.
  (buf: !$A.arr(byte, l, 4096), cl_n: int, start: int,
   sarr: !$A.arr(byte, ls, 4096), flen: int, fuel: int fuel): int =
  if fuel <= 0 then 0
  else if start >= cl_n then 0
  else let
    val tend = find_null(buf, start, 4096, 4096)
    val tlen = tend - start
  in
    if $AR.eq_int_int(tlen, flen) && token_matches(buf, start, tend, sarr) then 1
    else has_flag_loop(buf, cl_n, tend + 1, sarr, flen, fuel - 1)
  end

fn has_flag {l:agz}{sn:nat}
  (buf: !$A.arr(byte, l, 4096), cl_n: int, start: int, flag: string sn): int = let
  val sarr = str_to_arr4096(flag)
  val flen = sz2i(string1_length(flag))
  val r = has_flag_loop(buf, cl_n, start, sarr, flen, 4096)
  val () = $A.free<byte>(sarr)
in r end

(* Copy cl_buf token at [tstart..tend) into out_buf; returns length.
   i = source index in buf, j = dest index in out *)
fun copy_token_to_arr {l:agz}{lo:agz}{no:pos}{fuel:nat} .<fuel>.
  (buf: !$A.arr(byte, l, 4096), i: int, tend: int,
   out: !$A.arr(byte, lo, no), j: int, max_out: int no, fuel: int fuel): int =
  if fuel <= 0 then j
  else if i >= tend then j
  else if $AR.gte_int_int(j, max_out) then j
  else let
    val ii = g1ofg0(i)
    val ji = g1ofg0(j)
  in
    if ii >= 0 then
      if $AR.lt1_int_int(ii, 4096) then
        if ji >= 0 then
          if $AR.lt1_int_int(ji, max_out) then let
            val bv = byte2int0($A.get<byte>(buf, ii))
            val () = $A.set<byte>(out, ji, int2byte0(bv))
          in copy_token_to_arr(buf, i + 1, tend, out, j + 1, max_out, fuel - 1) end
          else j
        else j
      else j
    else j
  end

(* Scan tokens, find one matching `flag`, copy the NEXT token into out_buf. Returns length or 0. *)
fun get_flag_val_loop {l:agz}{ls:agz}{lo:agz}{no:pos}{fuel:nat} .<fuel>.
  (buf: !$A.arr(byte, l, 4096), cl_n: int, start: int,
   sarr: !$A.arr(byte, ls, 4096), flen: int,
   out: !$A.arr(byte, lo, no), max_out: int no,
   fuel: int fuel): int =
  if fuel <= 0 then 0
  else if start >= cl_n then 0
  else let
    val tend = find_null(buf, start, 4096, 4096)
    val tlen = tend - start
  in
    if $AR.eq_int_int(tlen, flen) && token_matches(buf, start, tend, sarr) then let
      (* next token *)
      val val_start = tend + 1
      val val_end = find_null(buf, val_start, 4096, 4096)
      val vlen = val_end - val_start
    in
      if $AR.lte_int_int(vlen, 0) then 0
      else copy_token_to_arr(buf, val_start, val_end, out, 0, max_out, $AR.checked_nat(vlen + 1))
    end
    else get_flag_val_loop(buf, cl_n, tend + 1, sarr, flen, out, max_out, fuel - 1)
  end

fn get_flag_val {l:agz}{lo:agz}{no:pos}{sn:nat}
  (buf: !$A.arr(byte, l, 4096), cl_n: int, start: int, flag: string sn,
   out: !$A.arr(byte, lo, no), max_out: int no): int = let
  val sarr = str_to_arr4096(flag)
  val flen = sz2i(string1_length(flag))
  val r = get_flag_val_loop(buf, cl_n, start, sarr, flen, out, max_out, 4096)
  val () = $A.free<byte>(sarr)
in r end

(* Handle --run-in: if first_start token is "--run-in", chdir to next token and return offset after it.
   Otherwise return first_start. *)
fn handle_run_in {l:agz}
  (buf: !$A.arr(byte, l, 4096), cl_n: int,
   first_start: int, first_end: int, first_len: int): int =
  let
    val ri_sarr = str_to_arr4096("--run-in")
    val ri_match = token_matches(buf, first_start, first_end, ri_sarr)
    val () = $A.free<byte>(ri_sarr)
    val is_run_in = $AR.eq_int_int(first_len, 8) && ri_match
  in
    if is_run_in then let
      val dir_start = first_end + 1
      val dir_end = find_null(buf, dir_start, 4096, 4096)
      val dir_len = dir_end - dir_start
    in
      if dir_len > 0 then let
        (* Build a null-terminated path for chdir *)
        val pb = $B.create()
        val () = arr_range_to_builder(buf, dir_start, dir_end, pb,
          $AR.checked_nat(dir_len + 1))
        val () = $B.put_byte(pb, 0)
        val @(pa, _) = $B.to_arr(pb)
        val @(fz_pa, bv_pa) = $A.freeze<byte>(pa)
        val cdr = $F.file_chdir(bv_pa, 65536)
        val () = $R.discard<int><int>(cdr)
        val () = $A.drop<byte>(fz_pa, bv_pa)
        val () = $A.free<byte>($A.thaw<byte>(fz_pa))
      in dir_end + 1 end
      else first_start
    end
    else first_start
  end

(* Run a shell command. cmd_b is CONSUMED. Returns exit code.
   When remap_offset > 0, stderr is remapped: strip build/, .dats->.bats, adjust line=N *)
fn run_sh(cmd_b: $B.builder, remap_offset: int): int = let
  val @(cmd_arr, cmd_len) = $B.to_arr(cmd_b)
  val @(fz_cmd, bv_cmd) = $A.freeze<byte>(cmd_arr)
  val _verbose = if is_verbose() then 1 else 0
  val () = (if $AR.gt_int_int(_verbose, 0) then let
    val () = print! ("  + ")
    val () = print_borrow(bv_cmd, 0, cmd_len, 65536,
      $AR.checked_nat(cmd_len + 1))
  in print_newline() end else ())
  (* /bin/sh = 7 bytes *)
  val sh_path = $A.alloc<byte>(7)
  val () = $A.write_byte(sh_path, 0, 47)
  val () = $A.write_byte(sh_path, 1, 98)
  val () = $A.write_byte(sh_path, 2, 105)
  val () = $A.write_byte(sh_path, 3, 110)
  val () = $A.write_byte(sh_path, 4, 47)
  val () = $A.write_byte(sh_path, 5, 115)
  val () = $A.write_byte(sh_path, 6, 104)
  val @(fz_sh, bv_sh) = $A.freeze<byte>(sh_path)
  (* argv: "sh\0-c\0<cmd>\0" *)
  val argv_b = $B.create()
  val () = $B.put_byte(argv_b, 115)
  val () = $B.put_byte(argv_b, 104)
  val () = $B.put_byte(argv_b, 0)
  val () = $B.put_byte(argv_b, 45)
  val () = $B.put_byte(argv_b, 99)
  val () = $B.put_byte(argv_b, 0)
  val () = copy_to_builder(bv_cmd, 0, cmd_len, 65536, argv_b,
    $AR.checked_nat(cmd_len + 1))
  val () = $B.put_byte(argv_b, 0)
  val @(argv_arr, _) = $B.to_arr(argv_b)
  val @(fz_a, bv_a) = $A.freeze<byte>(argv_arr)
  (* envp: empty *)
  val envp = $A.alloc<byte>(1)
  val () = $A.write_byte(envp, 0, 0)
  val @(fz_e, bv_e) = $A.freeze<byte>(envp)
  val sr = $P.spawn(bv_sh, 7, bv_a, 3, bv_e, 0,
    $P.dev_null(), $P.dev_null(), $P.pipe_new())
  val () = $A.drop<byte>(fz_sh, bv_sh)
  val () = $A.free<byte>($A.thaw<byte>(fz_sh))
  val () = $A.drop<byte>(fz_a, bv_a)
  val () = $A.free<byte>($A.thaw<byte>(fz_a))
  val () = $A.drop<byte>(fz_e, bv_e)
  val () = $A.free<byte>($A.thaw<byte>(fz_e))
  val () = $A.drop<byte>(fz_cmd, bv_cmd)
  val () = $A.free<byte>($A.thaw<byte>(fz_cmd))
in
  case+ sr of
  | ~$R.ok(sp) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = sp
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(sout_p)
      val+ ~$P.pipe_fd(err_fd) = serr_p
      (* Wait for child first, then read stderr.
         Avoids SIGPIPE when child writes more than one read chunk.
         Safe as long as child stderr < PIPE_BUF (64KB). *)
      val wr = $P.child_wait(child)
      val ec = (case+ wr of
        | ~$R.ok(n) => n | ~$R.err(_) => ~1): int
      val eb = $A.alloc<byte>(65536)
      val err_r = $F.file_read(err_fd, eb, 65536)
      val elen = (case+ err_r of
        | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val ecr = $F.file_close(err_fd)
      val () = $R.discard<int><int>(ecr)
    in
      if ec <> 0 then let
        val @(fz_eb2, bv_eb2) = $A.freeze<byte>(eb)
        val () = print_borrow(bv_eb2, 0, elen, 65536, $AR.checked_nat(elen + 1))
        val () = $A.drop<byte>(fz_eb2, bv_eb2)
        val () = $A.free<byte>($A.thaw<byte>(fz_eb2))
      in ec end
      else let
        val () = $A.free<byte>(eb)
      in 0 end
    end
  | ~$R.err(_) => ~1
end

(* Write builder contents to file. builder is CONSUMED.
   Path borrow must contain a null-terminated path. *)
fn write_file_from_builder {lp:agz}{np:pos | np < 1048576}
  (path_bv: !$A.borrow(byte, lp, np), path_len: int np,
   content_b: $B.builder): int = let
  val @(content_arr, content_len) = $B.to_arr(content_b)
  val fd_r = $F.file_open(path_bv, path_len, 577, 420)
in case+ fd_r of
  | ~$R.ok(fd) => let
      val bw = $F.buf_writer_create(fd)
      val @(fz_c, bv_c) = $A.freeze<byte>(content_arr)
      val () = wbw_loop(bw, bv_c, 0, content_len, $AR.checked_nat(content_len + 1))
      val () = $A.drop<byte>(fz_c, bv_c)
      val () = $A.free<byte>($A.thaw<byte>(fz_c))
      val cr = $F.buf_writer_close(bw)
      val () = $R.discard<int><int>(cr)
    in 0 end
  | ~$R.err(_) => let val () = $A.free<byte>(content_arr) in ~1 end
end

(* Preprocess one .bats file: read -> lex -> emit -> write .sats + .dats
   All three path borrows must be null-terminated builder arrays (65536) *)
fn preprocess_one
  {l1:agz}{l2:agz}{l3:agz}
  (src_bv: !$A.borrow(byte, l1, 65536),
   sats_bv: !$A.borrow(byte, l2, 65536),
   dats_bv: !$A.borrow(byte, l3, 65536)): int = let
  (* Cache check: if .sats is newer than .bats source, skip preprocessing *)
  val fresh = (if is_newer(sats_bv, src_bv) then 1 else 0): int
in
  if fresh > 0 then 0
  else let
  val or = $F.file_open(src_bv, 65536, 0, 0)
in
  case+ or of
  | ~$R.ok(fd) => let
      val buf = $A.alloc<byte>(65536)
      val rr = $F.file_read(fd, buf, 65536)
      val nbytes = (case+ rr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val cr = $F.file_close(fd)
      val () = $R.discard<int><int>(cr)
      val @(fz_src, bv_src) = $A.freeze<byte>(buf)
      val @(span_arr, _span_len, span_count) = do_lex(bv_src, nbytes, 65536)
      val @(fz_sp, bv_sp) = $A.freeze<byte>(span_arr)
      val @(sats_arr, sats_len, dats_arr, dats_len, _pre) =
        do_emit(bv_src, nbytes, 65536, bv_sp, 65536, span_count)
      val () = $A.drop<byte>(fz_sp, bv_sp)
      val () = $A.free<byte>($A.thaw<byte>(fz_sp))
      val () = $A.drop<byte>(fz_src, bv_src)
      val () = $A.free<byte>($A.thaw<byte>(fz_src))
      (* Write .sats *)
      val sb = $B.create()
      val @(fz_s, bv_s) = $A.freeze<byte>(sats_arr)
      val () = copy_to_builder(bv_s, 0, sats_len, 65536, sb,
        $AR.checked_nat(sats_len + 1))
      val () = $A.drop<byte>(fz_s, bv_s)
      val () = $A.free<byte>($A.thaw<byte>(fz_s))
      val r1 = write_file_from_builder(sats_bv, 65536, sb)
      (* Write .dats - prepend self-staload *)
      val db = $B.create()
      val bn_start = find_basename_start(sats_bv, 0, 65536, ~1, 4096)
      val bn_end = find_null_bv(sats_bv, bn_start, 65536, 4096)
      val () = bput(db, "staload \"./")
      val () = copy_to_builder(sats_bv, bn_start, bn_end, 65536, db,
        $AR.checked_nat(bn_end - bn_start + 1))
      val () = bput(db, "\"\n")
      val @(fz_d, bv_d) = $A.freeze<byte>(dats_arr)
      val () = copy_to_builder(bv_d, 0, dats_len, 65536, db,
        $AR.checked_nat(dats_len + 1))
      val () = $A.drop<byte>(fz_d, bv_d)
      val () = $A.free<byte>($A.thaw<byte>(fz_d))
      val r2 = write_file_from_builder(dats_bv, 65536, db)
    in
      if r1 = 0 then (if r2 = 0 then 0 else ~1) else ~1
    end
  | ~$R.err(_) => ~1
end end

(* ============================================================
   Build pipeline: do_build
   ============================================================ *)

(* Build a null-terminated path array from string.
   Returns arr(byte, l, 65536) for some l. Caller must free. *)
fn str_to_path_arr {sn:nat} (s: string sn): [l:agz] $A.arr(byte, l, 65536) = let
  val b = $B.create()
  val () = bput(b, s)
  val () = $B.put_byte(b, 0)
  val @(arr, _) = $B.to_arr(b)
in arr end

(* ============================================================
   clean: remove build/ and dist/ directories
   ============================================================ *)
fn do_clean(): void = let
  val cmd = $B.create()
  val () = bput(cmd, "rm -rf build dist docs")
  val rc = run_sh(cmd, 0)
in
  if rc <> 0 then println! ("error: clean failed")
  else if ~is_quiet() then println! ("cleaned build/, dist/, and docs/")
  else ()
end

(* Strip trailing newline from a 4096-byte buffer. Returns adjusted length. *)
fn strip_newline_arr {l:agz}
  (buf: !$A.arr(byte, l, 4096), len: int): int =
  if len <= 0 then 0
  else let val last = g1ofg0(len - 1) in
    if last >= 0 then
      if last < 4096 then
        (if byte2int0($A.get<byte>(buf, last)) = 10 then len - 1 else len): int
      else len
    else len
  end

(* Strip trailing newline from a 65536-byte buffer. Returns adjusted length. *)
fn strip_newline_arr65536 {l:agz}
  (buf: !$A.arr(byte, l, 65536), len: int): int =
  if len <= 0 then 0
  else let val last = g1ofg0(len - 1) in
    if last >= 0 then
      if last < 65536 then
        (if byte2int0($A.get<byte>(buf, last)) = 10 then len - 1 else len): int
      else len
    else len
  end

(* Strip trailing newline from a 256-byte buffer. Returns adjusted length. *)
fn strip_newline_arr256 {l:agz}
  (buf: !$A.arr(byte, l, 256), len: int): int =
  if len <= 0 then 0
  else let val last = g1ofg0(len - 1) in
    if last >= 0 then
      if last < 256 then
        (if byte2int0($A.get<byte>(buf, last)) = 10 then len - 1 else len): int
      else len
    else len
  end

(* ============================================================
   lock: read bats.lock and verify it exists
   ============================================================ *)
fn do_lock(): void = let
  (* Check if --repository was specified (stored in /tmp/_bpoc_repo.txt) *)
  val repo_path = str_to_path_arr("/tmp/_bpoc_repo.txt")
  val @(fz_rp2, bv_rp2) = $A.freeze<byte>(repo_path)
  val repo_or = $F.file_open(bv_rp2, 65536, 0, 0)
  val () = $A.drop<byte>(fz_rp2, bv_rp2)
  val () = $A.free<byte>($A.thaw<byte>(fz_rp2))
  val @(repo_buf, rplen) = (case+ repo_or of
    | ~$R.ok(rfd) => let
        val rb = $A.alloc<byte>(4096)
        val rr2 = $F.file_read(rfd, rb, 4096)
        val rl = (case+ rr2 of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
        val rcr = $F.file_close(rfd)
        val () = $R.discard<int><int>(rcr)
        (* strip trailing newline *)
        val rlen2 = strip_newline_arr(rb, rl)
      in @(rb, rlen2) end
    | ~$R.err(_) => let val rb = $A.alloc<byte>(4096) in @(rb, 0) end): [lrb:agz] @($A.arr(byte, lrb, 4096), int)
in
  if rplen > 0 then let
    (* Full lock resolution with repository *)
    val @(fz_rb3, bv_rb3) = $A.freeze<byte>(repo_buf)
    val cmd = $B.create()
    val () = bput(cmd, "bats lock --repository ")
    val () = copy_to_builder(bv_rb3, 0, rplen, 4096, cmd, $AR.checked_nat(rplen + 1))
    val () = $A.drop<byte>(fz_rb3, bv_rb3)
    val () = $A.free<byte>($A.thaw<byte>(fz_rb3))
    val rc = run_sh(cmd, 0)
  in
    if rc <> 0 then println! ("error: lock resolution failed")
    else ()
  end
  else let
    (* No repository - just read existing lockfile *)
    val () = $A.free<byte>(repo_buf)
    val la = str_to_path_arr("bats.lock")
    val @(fz_la, bv_la) = $A.freeze<byte>(la)
    val lock_or = $F.file_open(bv_la, 65536, 0, 0)
    val () = $A.drop<byte>(fz_la, bv_la)
    val () = $A.free<byte>($A.thaw<byte>(fz_la))
  in
    case+ lock_or of
    | ~$R.ok(lfd) => let
        val lock_buf = $A.alloc<byte>(65536)
        val lr = $F.file_read(lfd, lock_buf, 65536)
        val lock_len = (case+ lr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
        val lcr = $F.file_close(lfd)
        val () = $R.discard<int><int>(lcr)
      in
        if lock_len > 0 then let
          val @(fz_lb, bv_lb) = $A.freeze<byte>(lock_buf)
          val () = println! ("bats.lock:")
          val () = print_borrow(bv_lb, 0, lock_len, 65536,
            $AR.checked_nat(lock_len + 1))
          val () = $A.drop<byte>(fz_lb, bv_lb)
          val () = $A.free<byte>($A.thaw<byte>(fz_lb))
        in
          println! ("lock: verified")
        end
        else let
          val () = $A.free<byte>(lock_buf)
        in
          println! ("lock: empty lockfile")
        end
      end
    | ~$R.err(_) =>
        println! ("lock: no bats.lock found (use --repository to resolve)")
  end
end

fn do_build(release: int): void = let
  (* Step 1: mkdir build directories *)
  val cmd = $B.create()
  val () = bput(cmd, "mkdir -p build/src/bin build/bats_modules dist/debug dist/release")
  val r0 = run_sh(cmd, 0)
  val () = (if r0 <> 0 then println! ("error: mkdir failed") else ())
in
  if r0 <> 0 then ()
  else let
    (* Step 1b: Write and compile native runtime *)
    val nrt_b = $B.create()
    val () = bput(nrt_b, "/* bats native runtime */\n")
    val nrt_path = str_to_path_arr("build/_bats_native_runtime.c")
    val @(fz_nrtp, bv_nrtp) = $A.freeze<byte>(nrt_path)
    val _ = write_file_from_builder(bv_nrtp, 65536, nrt_b)
    val () = $A.drop<byte>(fz_nrtp, bv_nrtp)
    val () = $A.free<byte>($A.thaw<byte>(fz_nrtp))
    val nrt_cmd = $B.create()
    val () = bput(nrt_cmd, "PATH=/usr/bin:/usr/local/bin:/bin cc -c -o build/_bats_native_runtime.o build/_bats_native_runtime.c")
    val nrt_r = run_sh(nrt_cmd, 0)
    val () = (if nrt_r <> 0 then println! ("error: failed to compile native runtime") else ())
    (* Step 2: Get PATSHOME *)
    val phbuf = $A.alloc<byte>(512)
    val ph_key = $A.alloc<byte>(8)
    val () = $A.write_byte(ph_key, 0, 80)   (* P *)
    val () = $A.write_byte(ph_key, 1, 65)   (* A *)
    val () = $A.write_byte(ph_key, 2, 84)   (* T *)
    val () = $A.write_byte(ph_key, 3, 83)   (* S *)
    val () = $A.write_byte(ph_key, 4, 72)   (* H *)
    val () = $A.write_byte(ph_key, 5, 79)   (* O *)
    val () = $A.write_byte(ph_key, 6, 77)   (* M *)
    val () = $A.write_byte(ph_key, 7, 69)   (* E *)
    val @(fz_ph, bv_ph) = $A.freeze<byte>(ph_key)
    val ph_r = $E.get(bv_ph, 8, phbuf, 512)
    val () = $A.drop<byte>(fz_ph, bv_ph)
    val () = $A.free<byte>($A.thaw<byte>(fz_ph))
    val phlen = (case+ ph_r of
      | ~$R.some(n) => n | ~$R.none() => 0): int
  in
    if phlen <= 0 then let
      val () = $A.free<byte>(phbuf)
    in println! ("error: PATSHOME not set") end
    else let
      val @(fz_patshome, bv_patshome) = $A.freeze<byte>(phbuf)

      (* Step 3: Scan bats_modules/ for deps and preprocess *)
      val bm_arr = str_to_path_arr("bats_modules")
      val @(fz_bm, bv_bm) = $A.freeze<byte>(bm_arr)
      val bmdir_r = $F.dir_open(bv_bm, 65536)
      val () = $A.drop<byte>(fz_bm, bv_bm)
      val () = $A.free<byte>($A.thaw<byte>(fz_bm))
      val () = (case+ bmdir_r of
        | ~$R.ok(d) => let
            fun scan_deps {lph:agz}{fuel:nat} .<fuel>.
              (d: !$F.dir, ph: !$A.borrow(byte, lph, 512),
               fuel: int fuel): void =
              if fuel <= 0 then ()
              else let
                val ent = $A.alloc<byte>(256)
                val nr = $F.dir_next(d, ent, 256)
                val elen = $R.option_unwrap_or<int>(nr, ~1)
              in
                if elen < 0 then $A.free<byte>(ent)
                else let
                  val dd = is_dot_or_dotdot(ent, elen, 256)
                in
                  if dd then let
                    val () = $A.free<byte>(ent)
                  in scan_deps(d, ph, fuel - 1) end
                  else let
                    val @(fz_e, bv_e) = $A.freeze<byte>(ent)
                    (* mkdir -p build/bats_modules/<name>/src *)
                    val mc = $B.create()
                    val () = bput(mc, "mkdir -p build/bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, mc,
                      $AR.checked_nat(elen + 1))
                    val () = bput(mc, "/src")
                    val _ = run_sh(mc, 0)
                    (* source: bats_modules/<name>/src/lib.bats *)
                    val sp = $B.create()
                    val () = bput(sp, "bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, sp,
                      $AR.checked_nat(elen + 1))
                    val () = bput(sp, "/src/lib.bats")
                    val () = $B.put_byte(sp, 0)
                    val @(sa, _) = $B.to_arr(sp)
                    val @(fz_sp, bv_sp) = $A.freeze<byte>(sa)
                    (* sats: build/bats_modules/<name>/src/lib.sats *)
                    val ss = $B.create()
                    val () = bput(ss, "build/bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, ss,
                      $AR.checked_nat(elen + 1))
                    val () = bput(ss, "/src/lib.sats")
                    val () = $B.put_byte(ss, 0)
                    val @(ssa, _) = $B.to_arr(ss)
                    val @(fz_ss, bv_ss) = $A.freeze<byte>(ssa)
                    (* dats: build/bats_modules/<name>/src/lib.dats *)
                    val sd = $B.create()
                    val () = bput(sd, "build/bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, sd,
                      $AR.checked_nat(elen + 1))
                    val () = bput(sd, "/src/lib.dats")
                    val () = $B.put_byte(sd, 0)
                    val @(sda, _) = $B.to_arr(sd)
                    val @(fz_sd, bv_sd) = $A.freeze<byte>(sda)
                    val pr = preprocess_one(bv_sp, bv_ss, bv_sd)
                    val () = (if pr <> 0 then let
                      val () = print! ("warning: preprocess failed for dep ")
                      val () = print_borrow(bv_e, 0, elen, 256, $AR.checked_nat(elen + 1))
                    in print_newline() end
                    else if ~is_quiet() then let
                      val () = print! ("  preprocessed dep: ")
                      val () = print_borrow(bv_e, 0, elen, 256, $AR.checked_nat(elen + 1))
                    in print_newline() end
                    else ())
                    val () = $A.drop<byte>(fz_sp, bv_sp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                    val () = $A.drop<byte>(fz_ss, bv_ss)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ss))
                    val () = $A.drop<byte>(fz_sd, bv_sd)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sd))
                    val () = $A.drop<byte>(fz_e, bv_e)
                    val () = $A.free<byte>($A.thaw<byte>(fz_e))
                  in scan_deps(d, ph, fuel - 1) end
                end
              end
            val () = scan_deps(d, bv_patshome, 200)
            val dcr = $F.dir_close(d)
            val () = $R.discard<int><int>(dcr)
          in end
        | ~$R.err(_) =>
            println! ("warning: no bats_modules/ directory"))

      (* Step 4: Preprocess src/bin/*.bats *)
      val sb_arr = str_to_path_arr("src/bin")
      val @(fz_sb, bv_sb) = $A.freeze<byte>(sb_arr)
      val sbdir_r = $F.dir_open(bv_sb, 65536)
      val () = $A.drop<byte>(fz_sb, bv_sb)
      val () = $A.free<byte>($A.thaw<byte>(fz_sb))
      val () = (case+ sbdir_r of
        | ~$R.ok(d2) => let
            fun scan_bins {lph:agz}{fuel:nat} .<fuel>.
              (d: !$F.dir, ph: !$A.borrow(byte, lph, 512),
               phlen: int, rel: int, fuel: int fuel): void =
              if fuel <= 0 then ()
              else let
                val ent = $A.alloc<byte>(256)
                val nr = $F.dir_next(d, ent, 256)
                val elen = $R.option_unwrap_or<int>(nr, ~1)
              in
                if elen < 0 then $A.free<byte>(ent)
                else let
                  val dd = is_dot_or_dotdot(ent, elen, 256)
                  val bb = has_bats_ext(ent, elen, 256)
                in
                  if dd then let
                    val () = $A.free<byte>(ent)
                  in scan_bins(d, ph, phlen, rel, fuel - 1) end
                  else if bb then let
                    val @(fz_e, bv_e) = $A.freeze<byte>(ent)
                    (* stem = name without .bats extension *)
                    val stem_len = elen - 5
                    (* source: src/bin/<name>.bats *)
                    val sp = $B.create()
                    val () = bput(sp, "src/bin/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, sp,
                      $AR.checked_nat(elen + 1))
                    val () = $B.put_byte(sp, 0)
                    val @(sa, _) = $B.to_arr(sp)
                    val @(fz_sp, bv_sp) = $A.freeze<byte>(sa)
                    (* sats: build/src/bin/<name>.sats *)
                    val ss = $B.create()
                    val () = bput(ss, "build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, ss,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(ss, ".sats")
                    val () = $B.put_byte(ss, 0)
                    val @(ssa, _) = $B.to_arr(ss)
                    val @(fz_ss, bv_ss) = $A.freeze<byte>(ssa)
                    (* dats: build/src/bin/<name>.dats *)
                    val sd = $B.create()
                    val () = bput(sd, "build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, sd,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(sd, ".dats")
                    val () = $B.put_byte(sd, 0)
                    val @(sda, _) = $B.to_arr(sd)
                    val @(fz_sd, bv_sd) = $A.freeze<byte>(sda)
                    val pr = preprocess_one(bv_sp, bv_ss, bv_sd)
                    val () = (if pr <> 0 then let
                      val () = print! ("error: preprocess failed for ")
                      val () = print_borrow(bv_e, 0, elen, 256, $AR.checked_nat(elen + 1))
                    in print_newline() end
                    else if ~is_quiet() then let
                      val () = print! ("  preprocessed: src/bin/")
                      val () = print_borrow(bv_e, 0, elen, 256, $AR.checked_nat(elen + 1))
                    in print_newline() end
                    else ())
                    (* Step 5: Generate synthetic entry *)
                    val entry = $B.create()
                    val () = bput(entry, "staload \"./src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, entry,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(entry, ".sats\"\n")
                    (* dynload all dep modules *)
                    val bm2_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm2, bv_bm2) = $A.freeze<byte>(bm2_arr)
                    val bdir2 = $F.dir_open(bv_bm2, 65536)
                    val () = $A.drop<byte>(fz_bm2, bv_bm2)
                    val () = $A.free<byte>($A.thaw<byte>(fz_bm2))
                    val () = (case+ bdir2 of
                      | ~$R.ok(dd) => let
                          fun add_dynloads {fuel2:nat} .<fuel2>.
                            (dd: !$F.dir, eb: !$B.builder,
                             fuel2: int fuel2): void =
                            if fuel2 <= 0 then ()
                            else let
                              val de = $A.alloc<byte>(256)
                              val dnr = $F.dir_next(dd, de, 256)
                              val dlen = $R.option_unwrap_or<int>(dnr, ~1)
                            in
                              if dlen < 0 then $A.free<byte>(de)
                              else let
                                val ddd = is_dot_or_dotdot(de, dlen, 256)
                              in
                                if ddd then let
                                  val () = $A.free<byte>(de)
                                in add_dynloads(dd, eb, fuel2 - 1) end
                                else let
                                  val @(fz_de, bv_de) = $A.freeze<byte>(de)
                                  val () = bput(eb, "dynload \"./bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256,
                                    eb, $AR.checked_nat(dlen + 1))
                                  val () = bput(eb, "/src/lib.dats\"\n")
                                  val () = $A.drop<byte>(fz_de, bv_de)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                in add_dynloads(dd, eb, fuel2 - 1) end
                              end
                            end
                          val () = add_dynloads(dd, entry, 200)
                          val dcr2 = $F.dir_close(dd)
                          val () = $R.discard<int><int>(dcr2)
                        in end
                      | ~$R.err(_) => ())
                    val () = bput(entry, "dynload \"./src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, entry,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(entry, ".dats\"\n")
                    val () = bput(entry, "implement ")
                    val () = bput(entry, "main0 () = __BATS_main0 ()\n")
                    (* Write synthetic entry *)
                    val ep = $B.create()
                    val () = bput(ep, "build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, ep,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(ep, ".dats")
                    val () = $B.put_byte(ep, 0)
                    val @(epa, _) = $B.to_arr(ep)
                    val @(fz_ep, bv_ep) = $A.freeze<byte>(epa)
                    val ew = write_file_from_builder(bv_ep, 65536, entry)
                    val () = $A.drop<byte>(fz_ep, bv_ep)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ep))
                    val () = (if ew <> 0 then
                      println! ("error: failed to write synthetic entry")
                      else if ~is_quiet() then println! ("  generated synthetic entry")
                      else ())

                    (* Step 6: Run patsopt on all .dats files *)
                    (* patsopt for dep modules *)
                    val bm3_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm3, bv_bm3) = $A.freeze<byte>(bm3_arr)
                    val bdir3 = $F.dir_open(bv_bm3, 65536)
                    val () = $A.drop<byte>(fz_bm3, bv_bm3)
                    val () = $A.free<byte>($A.thaw<byte>(fz_bm3))
                    val () = (case+ bdir3 of
                      | ~$R.ok(dd3) => let
                          fun patsopt_deps {lph:agz}{fuel3:nat} .<fuel3>.
                            (dd3: !$F.dir,
                             ph: !$A.borrow(byte, lph, 512), phlen: int,
                             fuel3: int fuel3): void =
                            if fuel3 <= 0 then ()
                            else let
                              val de = $A.alloc<byte>(256)
                              val dnr = $F.dir_next(dd3, de, 256)
                              val dlen = $R.option_unwrap_or<int>(dnr, ~1)
                            in
                              if dlen < 0 then $A.free<byte>(de)
                              else let
                                val ddd = is_dot_or_dotdot(de, dlen, 256)
                              in
                                if ddd then let
                                  val () = $A.free<byte>(de)
                                in patsopt_deps(dd3, ph, phlen, fuel3 - 1) end
                                else let
                                  val @(fz_de, bv_de) = $A.freeze<byte>(de)
                                  val pats_fresh = let
                                    val ob = $B.create()
                                    val () = bput(ob, "build/bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ob, $AR.checked_nat(dlen+1))
                                    val () = bput(ob, "/src/lib_dats.c")
                                    val () = $B.put_byte(ob, 0)
                                    val ib = $B.create()
                                    val () = bput(ib, "build/bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ib, $AR.checked_nat(dlen+1))
                                    val () = bput(ib, "/src/lib.dats")
                                    val () = $B.put_byte(ib, 0)
                                  in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                                  val () = (if pats_fresh > 0 then ()
                                  else let
                                  val pc = $B.create()
                                  val () = bput(pc, "PATSHOME=")
                                  val () = copy_to_builder(ph, 0, phlen, 512, pc,
                                    $AR.checked_nat(phlen + 1))
                                  val () = $B.put_byte(pc, 32)
                                  val () = copy_to_builder(ph, 0, phlen, 512, pc,
                                    $AR.checked_nat(phlen + 1))
                                  val () = bput(pc, "/bin/patsopt -IATS build -IATS build/src -IATS build/bats_modules -o build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pc,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(pc, "/src/lib_dats.c -d build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pc,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(pc, "/src/lib.dats")
                                  val rc = run_sh(pc, 1)
                                  in (if rc <> 0 then let
                                    val () = print! ("error: patsopt failed for dep ")
                                    val () = print_borrow(bv_de, 0, dlen, 256,
                                      $AR.checked_nat(dlen + 1))
                                  in print_newline() end
                                  else if ~is_quiet() then let
                                    val () = print! ("  patsopt: ")
                                    val () = print_borrow(bv_de, 0, dlen, 256,
                                      $AR.checked_nat(dlen + 1))
                                  in print_newline() end
                                  else ()) end)
                                  val () = $A.drop<byte>(fz_de, bv_de)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                in patsopt_deps(dd3, ph, phlen, fuel3 - 1) end
                              end
                            end
                          val () = patsopt_deps(dd3, ph, phlen, 200)
                          val dcr3 = $F.dir_close(dd3)
                          val () = $R.discard<int><int>(dcr3)
                        in end
                      | ~$R.err(_) => ())

                    (* patsopt for the binary *)
                    val bin_pats_fresh = let
                      val ob = $B.create()
                      val () = bput(ob, "build/src/bin/")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ob, $AR.checked_nat(stem_len+1))
                      val () = bput(ob, "_dats.c")
                      val () = $B.put_byte(ob, 0)
                      val ib = $B.create()
                      val () = bput(ib, "build/src/bin/")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ib, $AR.checked_nat(stem_len+1))
                      val () = bput(ib, ".dats")
                      val () = $B.put_byte(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if bin_pats_fresh > 0 then ()
                    else let
                    val pbin = $B.create()
                    val () = bput(pbin, "PATSHOME=")
                    val () = copy_to_builder(ph, 0, phlen, 512, pbin,
                      $AR.checked_nat(phlen + 1))
                    val () = $B.put_byte(pbin, 32)
                    val () = copy_to_builder(ph, 0, phlen, 512, pbin,
                      $AR.checked_nat(phlen + 1))
                    val () = bput(pbin, "/bin/patsopt -IATS build -IATS build/src -IATS build/bats_modules -o build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, pbin,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(pbin, "_dats.c -d build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, pbin,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(pbin, ".dats")
                    val rbp = run_sh(pbin, 1)
                    in (if rbp <> 0 then
                      println! ("error: patsopt failed for binary")
                      else if ~is_quiet() then println! ("  patsopt: binary")
                      else ()) end)

                    (* patsopt for synthetic entry *)
                    val ent_pats_fresh = let
                      val ob = $B.create()
                      val () = bput(ob, "build/_bats_entry_")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ob, $AR.checked_nat(stem_len+1))
                      val () = bput(ob, "_dats.c")
                      val () = $B.put_byte(ob, 0)
                      val ib = $B.create()
                      val () = bput(ib, "build/_bats_entry_")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ib, $AR.checked_nat(stem_len+1))
                      val () = bput(ib, ".dats")
                      val () = $B.put_byte(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if ent_pats_fresh > 0 then ()
                    else let
                    val pent = $B.create()
                    val () = bput(pent, "PATSHOME=")
                    val () = copy_to_builder(ph, 0, phlen, 512, pent,
                      $AR.checked_nat(phlen + 1))
                    val () = $B.put_byte(pent, 32)
                    val () = copy_to_builder(ph, 0, phlen, 512, pent,
                      $AR.checked_nat(phlen + 1))
                    val () = bput(pent, "/bin/patsopt -IATS build -IATS build/src -IATS build/bats_modules -o build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, pent,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(pent, "_dats.c -d build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, pent,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(pent, ".dats")
                    val rep = run_sh(pent, 0)
                    in (if rep <> 0 then
                      println! ("error: patsopt failed for entry")
                      else if ~is_quiet() then println! ("  patsopt: entry")
                      else ()) end)

                    (* Step 7: clang compile all _dats.c *)
                    (* Compile deps *)
                    val bm4_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm4, bv_bm4) = $A.freeze<byte>(bm4_arr)
                    val bdir4 = $F.dir_open(bv_bm4, 65536)
                    val () = $A.drop<byte>(fz_bm4, bv_bm4)
                    val () = $A.free<byte>($A.thaw<byte>(fz_bm4))
                    val () = (case+ bdir4 of
                      | ~$R.ok(dd4) => let
                          fun clang_deps {lph:agz}{fuel4:nat} .<fuel4>.
                            (dd4: !$F.dir,
                             ph: !$A.borrow(byte, lph, 512), phlen: int,
                             rr: int, fuel4: int fuel4): void =
                            if fuel4 <= 0 then ()
                            else let
                              val de = $A.alloc<byte>(256)
                              val dnr = $F.dir_next(dd4, de, 256)
                              val dlen = $R.option_unwrap_or<int>(dnr, ~1)
                            in
                              if dlen < 0 then $A.free<byte>(de)
                              else let
                                val ddd = is_dot_or_dotdot(de, dlen, 256)
                              in
                                if ddd then let
                                  val () = $A.free<byte>(de)
                                in clang_deps(dd4, ph, phlen, rr, fuel4 - 1) end
                                else let
                                  val @(fz_de, bv_de) = $A.freeze<byte>(de)
                                  val cc_fresh = let
                                    val ob = $B.create()
                                    val () = bput(ob, "build/bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ob, $AR.checked_nat(dlen+1))
                                    val () = bput(ob, "/src/lib_dats.o")
                                    val () = $B.put_byte(ob, 0)
                                    val ib = $B.create()
                                    val () = bput(ib, "build/bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ib, $AR.checked_nat(dlen+1))
                                    val () = bput(ib, "/src/lib_dats.c")
                                    val () = $B.put_byte(ib, 0)
                                  in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                                  val () = (if cc_fresh > 0 then ()
                                  else let
                                  val cc = $B.create()
                                  val () = bput(cc, "PATH=/usr/bin:/usr/local/bin:/bin cc -c -o build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, cc,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(cc, "/src/lib_dats.o build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, cc,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(cc, "/src/lib_dats.c ")
                                  val () = (if rr > 0 then bput(cc, "-O2 -I")
                                    else bput(cc, "-g -O0 -I"))
                                  val () = copy_to_builder(ph, 0, phlen, 512, cc,
                                    $AR.checked_nat(phlen + 1))
                                  val () = bput(cc, " -I")
                                  val () = copy_to_builder(ph, 0, phlen, 512, cc,
                                    $AR.checked_nat(phlen + 1))
                                  val () = bput(cc, "/ccomp/runtime")
                                  val rc = run_sh(cc, 0)
                                  in (if rc <> 0 then let
                                    val () = print! ("error: cc failed for dep ")
                                    val () = print_borrow(bv_de, 0, dlen, 256,
                                      $AR.checked_nat(dlen + 1))
                                  in print_newline() end else ()) end)
                                  val () = $A.drop<byte>(fz_de, bv_de)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                in clang_deps(dd4, ph, phlen, rr, fuel4 - 1) end
                              end
                            end
                          val () = clang_deps(dd4, ph, phlen, rel, 200)
                          val dcr4 = $F.dir_close(dd4)
                          val () = $R.discard<int><int>(dcr4)
                        in end
                      | ~$R.err(_) => ())

                    (* Compile binary *)
                    val bin_cc_fresh = let
                      val ob = $B.create()
                      val () = bput(ob, "build/src/bin/")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ob, $AR.checked_nat(stem_len+1))
                      val () = bput(ob, "_dats.o")
                      val () = $B.put_byte(ob, 0)
                      val ib = $B.create()
                      val () = bput(ib, "build/src/bin/")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ib, $AR.checked_nat(stem_len+1))
                      val () = bput(ib, "_dats.c")
                      val () = $B.put_byte(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if bin_cc_fresh > 0 then ()
                    else let
                    val cbin = $B.create()
                    val () = bput(cbin, "PATH=/usr/bin:/usr/local/bin:/bin cc -c -o build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, cbin,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(cbin, "_dats.o build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, cbin,
                      $AR.checked_nat(stem_len + 1))
                    val () = (if rel > 0 then bput(cbin, "_dats.c -O2 -I")
                      else bput(cbin, "_dats.c -g -O0 -I"))
                    val () = copy_to_builder(ph, 0, phlen, 512, cbin,
                      $AR.checked_nat(phlen + 1))
                    val () = bput(cbin, " -I")
                    val () = copy_to_builder(ph, 0, phlen, 512, cbin,
                      $AR.checked_nat(phlen + 1))
                    val () = bput(cbin, "/ccomp/runtime")
                    val _ = run_sh(cbin, 0)
                    in end)

                    (* Compile entry *)
                    val ent_cc_fresh = let
                      val ob = $B.create()
                      val () = bput(ob, "build/_bats_entry_")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ob, $AR.checked_nat(stem_len+1))
                      val () = bput(ob, "_dats.o")
                      val () = $B.put_byte(ob, 0)
                      val ib = $B.create()
                      val () = bput(ib, "build/_bats_entry_")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ib, $AR.checked_nat(stem_len+1))
                      val () = bput(ib, "_dats.c")
                      val () = $B.put_byte(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if ent_cc_fresh > 0 then ()
                    else let
                    val cent = $B.create()
                    val () = bput(cent, "PATH=/usr/bin:/usr/local/bin:/bin cc -c -o build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, cent,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(cent, "_dats.o build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, cent,
                      $AR.checked_nat(stem_len + 1))
                    val () = (if rel > 0 then bput(cent, "_dats.c -O2 -I")
                      else bput(cent, "_dats.c -g -O0 -I"))
                    val () = copy_to_builder(ph, 0, phlen, 512, cent,
                      $AR.checked_nat(phlen + 1))
                    val () = bput(cent, " -I")
                    val () = copy_to_builder(ph, 0, phlen, 512, cent,
                      $AR.checked_nat(phlen + 1))
                    val () = bput(cent, "/ccomp/runtime")
                    val _ = run_sh(cent, 0)
                    in end)

                    (* Step 8: Link *)
                    val link = $B.create()
                    val () = (if rel > 0 then
                      bput(link, "PATH=/usr/bin:/usr/local/bin:/bin cc -o dist/release/")
                      else bput(link, "PATH=/usr/bin:/usr/local/bin:/bin cc -o dist/debug/"))
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, link,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(link, " build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, link,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(link, "_dats.o build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, link,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(link, "_dats.o build/_bats_native_runtime.o")
                    (* Add all dep .o files *)
                    val bm5_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm5, bv_bm5) = $A.freeze<byte>(bm5_arr)
                    val bdir5 = $F.dir_open(bv_bm5, 65536)
                    val () = $A.drop<byte>(fz_bm5, bv_bm5)
                    val () = $A.free<byte>($A.thaw<byte>(fz_bm5))
                    val () = (case+ bdir5 of
                      | ~$R.ok(dd5) => let
                          fun link_deps {fuel5:nat} .<fuel5>.
                            (dd5: !$F.dir, lb: !$B.builder,
                             fuel5: int fuel5): void =
                            if fuel5 <= 0 then ()
                            else let
                              val de = $A.alloc<byte>(256)
                              val dnr = $F.dir_next(dd5, de, 256)
                              val dlen = $R.option_unwrap_or<int>(dnr, ~1)
                            in
                              if dlen < 0 then $A.free<byte>(de)
                              else let
                                val ddd = is_dot_or_dotdot(de, dlen, 256)
                              in
                                if ddd then let
                                  val () = $A.free<byte>(de)
                                in link_deps(dd5, lb, fuel5 - 1) end
                                else let
                                  val @(fz_de, bv_de) = $A.freeze<byte>(de)
                                  val () = bput(lb, " build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256,
                                    lb, $AR.checked_nat(dlen + 1))
                                  val () = bput(lb, "/src/lib_dats.o")
                                  val () = $A.drop<byte>(fz_de, bv_de)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                in link_deps(dd5, lb, fuel5 - 1) end
                              end
                            end
                          val () = link_deps(dd5, link, 200)
                          val dcr5 = $F.dir_close(dd5)
                          val () = $R.discard<int><int>(dcr5)
                        in end
                      | ~$R.err(_) => ())
                    val () = (if rel > 0 then bput(link, " -O2")
                      else bput(link, " -g -O0"))
                    val rl = run_sh(link, 0)

                    val () = $A.drop<byte>(fz_sp, bv_sp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                    val () = $A.drop<byte>(fz_ss, bv_ss)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ss))
                    val () = $A.drop<byte>(fz_sd, bv_sd)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sd))
                    val () = (if rl = 0 then
                      if ~is_quiet() then let
                        val () = (if rel > 0 then print! ("  built: dist/release/")
                          else print! ("  built: dist/debug/"))
                        val () = print_borrow(bv_e, 0, stem_len, 256,
                          $AR.checked_nat(stem_len + 1))
                      in print_newline() end
                      else ()
                    else println! ("error: link failed"))
                    val () = $A.drop<byte>(fz_e, bv_e)
                    val () = $A.free<byte>($A.thaw<byte>(fz_e))
                  in scan_bins(d, ph, phlen, rel, fuel - 1) end
                  else let
                    val () = $A.free<byte>(ent)
                  in scan_bins(d, ph, phlen, rel, fuel - 1) end
                end
              end
            val () = scan_bins(d2, bv_patshome, phlen, release, 100)
            val dcr2 = $F.dir_close(d2)
            val () = $R.discard<int><int>(dcr2)
          in end
        | ~$R.err(_) =>
            println! ("error: cannot open src/bin/"))

      val () = $A.drop<byte>(fz_patshome, bv_patshome)
      val () = $A.free<byte>($A.thaw<byte>(fz_patshome))
    in end
  end
end

(* ============================================================
   String constant builders
   ============================================================ *)

(* Write "bats.toml" into buf -- 9 bytes *)
fn make_bats_toml {l:agz}{n:pos | n >= 9}
  (buf: !$A.arr(byte, l, n)): void =
  let
    val () = $A.write_byte(buf, 0, 98)   (* b *)
    val () = $A.write_byte(buf, 1, 97)   (* a *)
    val () = $A.write_byte(buf, 2, 116)  (* t *)
    val () = $A.write_byte(buf, 3, 115)  (* s *)
    val () = $A.write_byte(buf, 4, 46)   (* . *)
    val () = $A.write_byte(buf, 5, 116)  (* t *)
    val () = $A.write_byte(buf, 6, 111)  (* o *)
    val () = $A.write_byte(buf, 7, 109)  (* m *)
    val () = $A.write_byte(buf, 8, 108)  (* l *)
  in end

(* Write "src/bin" into buf -- 7 bytes *)
fn make_src_bin {l:agz}{n:pos | n >= 7}
  (buf: !$A.arr(byte, l, n)): void =
  let
    val () = $A.write_byte(buf, 0, 115)  (* s *)
    val () = $A.write_byte(buf, 1, 114)  (* r *)
    val () = $A.write_byte(buf, 2, 99)   (* c *)
    val () = $A.write_byte(buf, 3, 47)   (* / *)
    val () = $A.write_byte(buf, 4, 98)   (* b *)
    val () = $A.write_byte(buf, 5, 105)  (* i *)
    val () = $A.write_byte(buf, 6, 110)  (* n *)
  in end

(* Write "package" into buf -- 7 bytes *)
fn make_package {l:agz}{n:pos | n >= 7}
  (buf: !$A.arr(byte, l, n)): void =
  let
    val () = $A.write_byte(buf, 0, 112)
    val () = $A.write_byte(buf, 1, 97)
    val () = $A.write_byte(buf, 2, 99)
    val () = $A.write_byte(buf, 3, 107)
    val () = $A.write_byte(buf, 4, 97)
    val () = $A.write_byte(buf, 5, 103)
    val () = $A.write_byte(buf, 6, 101)
  in end

(* Write "name" into buf -- 4 bytes *)
fn make_name {l:agz}{n:pos | n >= 4}
  (buf: !$A.arr(byte, l, n)): void =
  let
    val () = $A.write_byte(buf, 0, 110)
    val () = $A.write_byte(buf, 1, 97)
    val () = $A.write_byte(buf, 2, 109)
    val () = $A.write_byte(buf, 3, 101)
  in end

(* Write "kind" into buf -- 4 bytes *)
fn make_kind {l:agz}{n:pos | n >= 4}
  (buf: !$A.arr(byte, l, n)): void =
  let
    val () = $A.write_byte(buf, 0, 107)
    val () = $A.write_byte(buf, 1, 105)
    val () = $A.write_byte(buf, 2, 110)
    val () = $A.write_byte(buf, 3, 100)
  in end

(* Write "/proc/self/cmdline" into buf -- 18 bytes *)
fn make_proc_cmdline {l:agz}{n:pos | n >= 18}
  (buf: !$A.arr(byte, l, n)): void =
  let
    val () = $A.write_byte(buf, 0, 47)   (* / *)
    val () = $A.write_byte(buf, 1, 112)  (* p *)
    val () = $A.write_byte(buf, 2, 114)  (* r *)
    val () = $A.write_byte(buf, 3, 111)  (* o *)
    val () = $A.write_byte(buf, 4, 99)   (* c *)
    val () = $A.write_byte(buf, 5, 47)   (* / *)
    val () = $A.write_byte(buf, 6, 115)  (* s *)
    val () = $A.write_byte(buf, 7, 101)  (* e *)
    val () = $A.write_byte(buf, 8, 108)  (* l *)
    val () = $A.write_byte(buf, 9, 102)  (* f *)
    val () = $A.write_byte(buf, 10, 47)  (* / *)
    val () = $A.write_byte(buf, 11, 99)  (* c *)
    val () = $A.write_byte(buf, 12, 109) (* m *)
    val () = $A.write_byte(buf, 13, 100) (* d *)
    val () = $A.write_byte(buf, 14, 108) (* l *)
    val () = $A.write_byte(buf, 15, 105) (* i *)
    val () = $A.write_byte(buf, 16, 110) (* n *)
    val () = $A.write_byte(buf, 17, 101) (* e *)
  in end

(* ============================================================
   Command matching
   ============================================================ *)

fn cmd_is_check {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 5 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 4 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
        val c4 = byte2int0($A.get<byte>(buf, o0 + 4))
      in (* "check" = 99,104,101,99,107 *)
        $AR.eq_int_int(c0, 99) && $AR.eq_int_int(c1, 104) &&
        $AR.eq_int_int(c2, 101) && $AR.eq_int_int(c3, 99) &&
        $AR.eq_int_int(c4, 107)
      end else false
    else false
  end

fn cmd_is_build {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 5 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 4 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
        val c4 = byte2int0($A.get<byte>(buf, o0 + 4))
      in (* "build" = 98,117,105,108,100 *)
        $AR.eq_int_int(c0, 98) && $AR.eq_int_int(c1, 117) &&
        $AR.eq_int_int(c2, 105) && $AR.eq_int_int(c3, 108) &&
        $AR.eq_int_int(c4, 100)
      end else false
    else false
  end

fn cmd_is_clean {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 5 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 4 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
        val c4 = byte2int0($A.get<byte>(buf, o0 + 4))
      in (* "clean" = 99,108,101,97,110 *)
        $AR.eq_int_int(c0, 99) && $AR.eq_int_int(c1, 108) &&
        $AR.eq_int_int(c2, 101) && $AR.eq_int_int(c3, 97) &&
        $AR.eq_int_int(c4, 110)
      end else false
    else false
  end

fn cmd_is_lock {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 4 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 3 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
      in (* "lock" = 108,111,99,107 *)
        $AR.eq_int_int(c0, 108) && $AR.eq_int_int(c1, 111) &&
        $AR.eq_int_int(c2, 99) && $AR.eq_int_int(c3, 107)
      end else false
    else false
  end

fn cmd_is_run {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 3 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 2 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
      in (* "run" = 114,117,110 *)
        $AR.eq_int_int(c0, 114) && $AR.eq_int_int(c1, 117) &&
        $AR.eq_int_int(c2, 110)
      end else false
    else false
  end

fn cmd_is_init {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 4 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 3 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
      in (* "init" = 105,110,105,116 *)
        $AR.eq_int_int(c0, 105) && $AR.eq_int_int(c1, 110) &&
        $AR.eq_int_int(c2, 105) && $AR.eq_int_int(c3, 116)
      end else false
    else false
  end

fn cmd_is_tree {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 4 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 3 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
      in (* "tree" = 116,114,101,101 *)
        $AR.eq_int_int(c0, 116) && $AR.eq_int_int(c1, 114) &&
        $AR.eq_int_int(c2, 101) && $AR.eq_int_int(c3, 101)
      end else false
    else false
  end

fn cmd_is_add {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 3 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 2 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
      in (* "add" = 97,100,100 *)
        $AR.eq_int_int(c0, 97) && $AR.eq_int_int(c1, 100) &&
        $AR.eq_int_int(c2, 100)
      end else false
    else false
  end

fn cmd_is_remove {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 6 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 5 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
        val c4 = byte2int0($A.get<byte>(buf, o0 + 4))
        val c5 = byte2int0($A.get<byte>(buf, o0 + 5))
      in (* "remove" = 114,101,109,111,118,101 *)
        $AR.eq_int_int(c0, 114) && $AR.eq_int_int(c1, 101) &&
        $AR.eq_int_int(c2, 109) && $AR.eq_int_int(c3, 111) &&
        $AR.eq_int_int(c4, 118) && $AR.eq_int_int(c5, 101)
      end else false
    else false
  end

fn cmd_is_version {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 9 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 8 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
      in (* "--version" = 45,45,118,101,114,115,105,111,110 *)
        $AR.eq_int_int(c0, 45) && $AR.eq_int_int(c1, 45) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 2)), 118) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 3)), 101) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 4)), 114) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 5)), 115) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 6)), 105) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 7)), 111) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 8)), 110)
      end else false
    else false
  end

fn cmd_is_completions {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 11 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 10 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
      in (* "completions" = 99,111,109,112,108,101,116,105,111,110,115 *)
        $AR.eq_int_int(c0, 99) && $AR.eq_int_int(c1, 111) &&
        $AR.eq_int_int(c2, 109) && $AR.eq_int_int(c3, 112) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 4)), 108) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 5)), 101) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 6)), 116) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 7)), 105) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 8)), 111) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 9)), 110) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 10)), 115)
      end else false
    else false
  end

fn cmd_is_test {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 4 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 3 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
      in (* "test" = 116,101,115,116 *)
        $AR.eq_int_int(c0, 116) && $AR.eq_int_int(c1, 101) &&
        $AR.eq_int_int(c2, 115) && $AR.eq_int_int(c3, 116)
      end else false
    else false
  end

fn cmd_is_upload {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 6 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 5 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
        val c4 = byte2int0($A.get<byte>(buf, o0 + 4))
        val c5 = byte2int0($A.get<byte>(buf, o0 + 5))
      in (* "upload" = 117,112,108,111,97,100 *)
        $AR.eq_int_int(c0, 117) && $AR.eq_int_int(c1, 112) &&
        $AR.eq_int_int(c2, 108) && $AR.eq_int_int(c3, 111) &&
        $AR.eq_int_int(c4, 97) && $AR.eq_int_int(c5, 100)
      end else false
    else false
  end

(* ============================================================
   test: build and run tests
   ============================================================ *)
fn do_test(): void = let
  (* Enable test mode so emit includes unittest blocks *)
  val () = (!g_test_mode := true)
  val () = do_build(0)
  val () = (!g_test_mode := false)
  (* Scan source for test function names in $UNITTEST.run blocks *)
  (* Use C helper to scan the source file *)
  val src_arr = str_to_path_arr("src/bin")
  val @(fz_sa, bv_sa) = $A.freeze<byte>(src_arr)
  val dir_r = $F.dir_open(bv_sa, 65536)
  val () = $A.drop<byte>(fz_sa, bv_sa)
  val () = $A.free<byte>($A.thaw<byte>(fz_sa))
  val found_tests = $A.alloc<byte>(1)
  val () = $A.write_byte(found_tests, 0, 0)
in
  case+ dir_r of
  | ~$R.ok(sd) => let
      fun scan_test_dir {lft:agz}{fuel:nat} .<fuel>.
        (sd: !$F.dir, ft: !$A.arr(byte, lft, 1), fuel: int fuel): void =
        if fuel <= 0 then ()
        else let
          val ent = $A.alloc<byte>(256)
          val nr = $F.dir_next(sd, ent, 256)
          val elen = $R.option_unwrap_or<int>(nr, ~1)
        in
          if elen < 0 then $A.free<byte>(ent)
          else let
            val ddd = is_dot_or_dotdot(ent, elen, 256)
            val bb = has_bats_ext(ent, elen, 256)
          in
            if ddd then let val () = $A.free<byte>(ent) in scan_test_dir(sd, ft, fuel - 1) end
            else if bb then let
              (* Read source file *)
              val spath = $B.create()
              val @(fz_e, bv_e) = $A.freeze<byte>(ent)
              val () = bput(spath, "src/bin/")
              val () = copy_to_builder(bv_e, 0, elen, 256, spath,
                $AR.checked_nat(elen + 1))
              val () = $B.put_byte(spath, 0)
              val () = $A.drop<byte>(fz_e, bv_e)
              val () = $A.free<byte>($A.thaw<byte>(fz_e))
              val @(spa, _) = $B.to_arr(spath)
              val @(fz_sp, bv_sp) = $A.freeze<byte>(spa)
              val sfd = $F.file_open(bv_sp, 65536, 0, 0)
              val () = $A.drop<byte>(fz_sp, bv_sp)
              val () = $A.free<byte>($A.thaw<byte>(fz_sp))
              val () = (case+ sfd of
                | ~$R.ok(fd) => let
                    val sbuf = $A.alloc<byte>(65536)
                    val rr = $F.file_read(fd, sbuf, 65536)
                    val slen = (case+ rr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                    val cr = $F.file_close(fd)
                    val () = $R.discard<int><int>(cr)
                    (* Scan for test functions *)
                    val names_buf = $A.alloc<byte>(12800) (* 100 * 128 bytes *)
                    val nfns = 0
                    val () = $A.free<byte>(sbuf)
                  in
                    if nfns > 0 then let
                      val () = $A.write_byte(ft, 0, 1)
                      val () = println! ("running ", nfns, " test(s)")
                      val () = $A.free<byte>(names_buf)
                    in () end
                    else let
                      val () = $A.free<byte>(names_buf)
                    in () end
                  end
                | ~$R.err(_) => ())
            in scan_test_dir(sd, ft, fuel - 1) end
            else let val () = $A.free<byte>(ent) in scan_test_dir(sd, ft, fuel - 1) end
          end
        end
      val () = scan_test_dir(sd, found_tests, 200)
      val dcr = $F.dir_close(sd)
      val () = $R.discard<int><int>(dcr)
      val ft0 = byte2int0($A.get<byte>(found_tests, 0))
      val () = $A.free<byte>(found_tests)
    in
      if ft0 = 0 then println! ("no tests found") else ()
    end
  | ~$R.err(_) => let
      val () = $A.free<byte>(found_tests)
    in
      println! ("no tests found")
    end
end

(* ============================================================
   upload: package library for repository
   ============================================================ *)
fn do_upload(): void = let
  (* Read bats.toml for package name and verify kind = "lib" *)
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 65536, 0, 0)
  val () = $A.drop<byte>(fz_tp, bv_tp)
  val () = $A.free<byte>($A.thaw<byte>(fz_tp))
in
  case+ tor of
  | ~$R.ok(tfd) => let
      val tbuf = $A.alloc<byte>(8192)
      val trr = $F.file_read(tfd, tbuf, 8192)
      val tlen = (case+ trr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val tcr = $F.file_close(tfd)
      val () = $R.discard<int><int>(tcr)
      val @(fz_tb, bv_tb) = $A.freeze<byte>(tbuf)
      val pr = $T.parse(bv_tb, 8192)
      val () = $A.drop<byte>(fz_tb, bv_tb)
      val () = $A.free<byte>($A.thaw<byte>(fz_tb))
    in
      case+ pr of
      | ~$R.ok(doc) => let
          val sec = $A.alloc<byte>(7)
          val () = make_package(sec)
          val @(fz_s, bv_s) = $A.freeze<byte>(sec)
          (* Get package name *)
          val kn = $A.alloc<byte>(4)
          val () = make_name(kn)
          val @(fz_kn, bv_kn) = $A.freeze<byte>(kn)
          val nbuf = $A.alloc<byte>(256)
          val nr = $T.get(doc, bv_s, 7, bv_kn, 4, nbuf, 256)
          val () = $A.drop<byte>(fz_kn, bv_kn)
          val () = $A.free<byte>($A.thaw<byte>(fz_kn))
          (* Get package kind *)
          val kk = $A.alloc<byte>(4)
          val () = $A.set<byte>(kk, 0, int2byte0(107)) (* k *)
          val () = $A.set<byte>(kk, 1, int2byte0(105)) (* i *)
          val () = $A.set<byte>(kk, 2, int2byte0(110)) (* n *)
          val () = $A.set<byte>(kk, 3, int2byte0(100)) (* d *)
          val @(fz_kk, bv_kk) = $A.freeze<byte>(kk)
          val kbuf = $A.alloc<byte>(32)
          val kr = $T.get(doc, bv_s, 7, bv_kk, 4, kbuf, 32)
          val () = $A.drop<byte>(fz_kk, bv_kk)
          val () = $A.free<byte>($A.thaw<byte>(fz_kk))
          val () = $A.drop<byte>(fz_s, bv_s)
          val () = $A.free<byte>($A.thaw<byte>(fz_s))
          val () = $T.toml_free(doc)
          (* Check kind is "lib" (3 chars, l=108, i=105, b=98) *)
          val is_lib = (case+ kr of
            | ~$R.some(klen) => (if klen = 3 then let
                val @(fz_kb, bv_kb) = $A.freeze<byte>(kbuf)
                val k0 = byte2int0($A.read<byte>(bv_kb, 0))
                val () = $A.drop<byte>(fz_kb, bv_kb)
                val () = $A.free<byte>($A.thaw<byte>(fz_kb))
              in $AR.eq_int_int(k0, 108) end
              else let val () = $A.free<byte>(kbuf) in false end): bool
            | ~$R.none() => let val () = $A.free<byte>(kbuf) in false end): bool
          (* Get repository path (stored in /tmp/_bpoc_repo.txt by main0) *)
          val upl_rp = str_to_path_arr("/tmp/_bpoc_repo.txt")
          val @(fz_urp, bv_urp) = $A.freeze<byte>(upl_rp)
          val upl_ror = $F.file_open(bv_urp, 65536, 0, 0)
          val () = $A.drop<byte>(fz_urp, bv_urp)
          val () = $A.free<byte>($A.thaw<byte>(fz_urp))
          val @(repo, rplen) = (case+ upl_ror of
            | ~$R.ok(urfd) => let
                val repo_b2 = $A.alloc<byte>(65536)
                val urr = $F.file_read(urfd, repo_b2, 65536)
                val url = (case+ urr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                val urcr = $F.file_close(urfd)
                val () = $R.discard<int><int>(urcr)
                val url2 = strip_newline_arr65536(repo_b2, url)
              in @(repo_b2, url2) end
            | ~$R.err(_) => let val repo_b2 = $A.alloc<byte>(65536) in @(repo_b2, 0) end): [lurb:agz] @($A.arr(byte, lurb, 65536), int)
        in
          case+ nr of
          | ~$R.some(nlen) =>
            if is_lib then
              if rplen > 0 then let
                (* Get version: from git log or date *)
                val @(verbuf, verlen) = (let
                  val vcmd = $B.create()
                  val () = bput(vcmd, "git log -1 --format=%cd --date=format:%Y.%-m.%-d 2>/dev/null | tr -d '\\n' > /tmp/_bpoc_ver.txt || date +%Y.%-m.%-d > /tmp/_bpoc_ver.txt")
                  val _ = run_sh(vcmd, 0)
                  val vp = str_to_path_arr("/tmp/_bpoc_ver.txt")
                  val @(fz_vp, bv_vp) = $A.freeze<byte>(vp)
                  val vf = $F.file_open(bv_vp, 65536, 0, 0)
                  val () = $A.drop<byte>(fz_vp, bv_vp)
                  val () = $A.free<byte>($A.thaw<byte>(fz_vp))
                in case+ vf of
                  | ~$R.ok(vfd) => let
                      val vb = $A.alloc<byte>(64)
                      val vr = $F.file_read(vfd, vb, 64)
                      val vl = (case+ vr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                      val vcr = $F.file_close(vfd)
                      val () = $R.discard<int><int>(vcr)
                    in @(vb, vl) end
                  | ~$R.err(_) => let val vb = $A.alloc<byte>(64) in @(vb, 0) end
                end): [lvb:agz] @($A.arr(byte, lvb, 64), int)
                val @(fz_vb, bv_vb) = $A.freeze<byte>(verbuf)
                (* Build output zip path: repo/pkg/prefix_ver.bats *)
                val zip_path = $B.create()
                val @(fz_rp, bv_rp) = $A.freeze<byte>(repo)
                val () = copy_to_builder(bv_rp, 0, rplen, 65536, zip_path,
                  $AR.checked_nat(rplen + 1))
                val () = bput(zip_path, "/")
                val @(fz_nb, bv_nb) = $A.freeze<byte>(nbuf)
                val () = copy_to_builder(bv_nb, 0, nlen, 256, zip_path,
                  $AR.checked_nat(nlen + 1))
                val () = bput(zip_path, "/")
                (* Build prefix: replace '/' with '_' in name *)
                val pfx = $B.create()
                val () = copy_to_builder(bv_nb, 0, nlen, 256, pfx,
                  $AR.checked_nat(nlen + 1))
                (* TODO: replace '/' with '_' in prefix -- skip for now *)
                val @(pfx_arr, pfx_len) = $B.to_arr(pfx)
                val @(fz_px, bv_px) = $A.freeze<byte>(pfx_arr)
                val () = copy_to_builder(bv_px, 0, pfx_len, 65536, zip_path,
                  $AR.checked_nat(pfx_len + 1))
                val () = bput(zip_path, "_")
                val () = copy_to_builder(bv_vb, 0, verlen, 64, zip_path,
                  $AR.checked_nat(verlen + 1))
                val () = bput(zip_path, ".bats")
                val () = $B.put_byte(zip_path, 0)
                val @(zpa, zpa_len) = $B.to_arr(zip_path)
                val @(fz_zp, bv_zp) = $A.freeze<byte>(zpa)
                (* Build mkdir+zip command *)
                val cmd = $B.create()
                val () = bput(cmd, "mkdir -p ")
                val () = copy_to_builder(bv_rp, 0, rplen, 65536, cmd,
                  $AR.checked_nat(rplen + 1))
                val () = bput(cmd, "/")
                val () = copy_to_builder(bv_nb, 0, nlen, 256, cmd,
                  $AR.checked_nat(nlen + 1))
                val () = bput(cmd, " && zip -r ")
                val () = copy_to_builder(bv_zp, 0, zpa_len - 1, 65536, cmd,
                  $AR.checked_nat(zpa_len + 1))
                val () = bput(cmd, " bats.toml src/")
                val () = $A.drop<byte>(fz_nb, bv_nb)
                val () = $A.free<byte>($A.thaw<byte>(fz_nb))
                val () = $A.drop<byte>(fz_rp, bv_rp)
                val () = $A.free<byte>($A.thaw<byte>(fz_rp))
                val () = $A.drop<byte>(fz_px, bv_px)
                val () = $A.free<byte>($A.thaw<byte>(fz_px))
                val rc = run_sh(cmd, 0)
              in
                if rc <> 0 then let
                  val () = $A.drop<byte>(fz_zp, bv_zp)
                  val () = $A.free<byte>($A.thaw<byte>(fz_zp))
                  val () = $A.drop<byte>(fz_vb, bv_vb)
                  val () = $A.free<byte>($A.thaw<byte>(fz_vb))
                in println! ("error: upload failed") end
                else let
                  (* Write SHA-256 sidecar file: zip_path + ".sha256" *)
                  val @(sha_buf, sha_rc) = (let
                    val sha_cmd = $B.create()
                    val () = bput(sha_cmd, "sha256sum ")
                    val () = copy_to_builder(bv_zp, 0, zpa_len - 1, 65536, sha_cmd, $AR.checked_nat(zpa_len + 1))
                    val () = bput(sha_cmd, " | head -c 64 > /tmp/_bpoc_sha.txt")
                    val sha_r = run_sh(sha_cmd, 0)
                  in
                    if sha_r <> 0 then let val sb = $A.alloc<byte>(65) in @(sb, ~1) end
                    else let
                      val sp3 = str_to_path_arr("/tmp/_bpoc_sha.txt")
                      val @(fz_sp3, bv_sp3) = $A.freeze<byte>(sp3)
                      val sf = $F.file_open(bv_sp3, 65536, 0, 0)
                      val () = $A.drop<byte>(fz_sp3, bv_sp3)
                      val () = $A.free<byte>($A.thaw<byte>(fz_sp3))
                    in case+ sf of
                      | ~$R.ok(sfd) => let
                          val sb = $A.alloc<byte>(65)
                          val sr2 = $F.file_read(sfd, sb, 65)
                          val slen2 = (case+ sr2 of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                          val scr = $F.file_close(sfd)
                          val () = $R.discard<int><int>(scr)
                        in @(sb, (if slen2 >= 64 then 0 else ~1): int) end
                      | ~$R.err(_) => let val sb = $A.alloc<byte>(65) in @(sb, ~1) end
                    end
                  end): [lsb:agz] @($A.arr(byte, lsb, 65), int)
                  val () = (if sha_rc = 0 then let
                    val sidecar = $B.create()
                    val @(fz_sh, bv_sh) = $A.freeze<byte>(sha_buf)
                    val () = copy_to_builder(bv_sh, 0, 64, 65, sidecar,
                      $AR.checked_nat(65))
                    val () = bput(sidecar, "  ")
                    (* just the filename part of zip_path *)
                    val () = copy_to_builder(bv_zp, 0, zpa_len - 1, 65536,
                      sidecar, $AR.checked_nat(zpa_len + 1))
                    val () = bput(sidecar, "\n")
                    val () = $A.drop<byte>(fz_sh, bv_sh)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sh))
                    (* write to zip_path + ".sha256" *)
                    val sp2 = $B.create()
                    val () = copy_to_builder(bv_zp, 0, zpa_len - 1, 65536,
                      sp2, $AR.checked_nat(zpa_len + 1))
                    val () = bput(sp2, ".sha256")
                    val () = $B.put_byte(sp2, 0)
                    val @(sp2a, _) = $B.to_arr(sp2)
                    val @(fz_sp2, bv_sp2) = $A.freeze<byte>(sp2a)
                    val _ = write_file_from_builder(bv_sp2, 65536, sidecar)
                    val () = $A.drop<byte>(fz_sp2, bv_sp2)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sp2))
                  in end
                  else $A.free<byte>(sha_buf))
                  val () = $A.drop<byte>(fz_zp, bv_zp)
                  val () = $A.free<byte>($A.thaw<byte>(fz_zp))
                  val () = $A.drop<byte>(fz_vb, bv_vb)
                  val () = $A.free<byte>($A.thaw<byte>(fz_vb))
                in println! ("uploaded successfully") end
              end
              else let
                val () = $A.free<byte>(repo)
                val () = $A.free<byte>(nbuf)
              in println! ("error: --repository is required for upload") end
            else let
              val () = $A.free<byte>(nbuf)
              val () = $A.free<byte>(repo)
            in println! ("error: 'upload' is only for library packages (kind = \"lib\")") end
          | ~$R.none() => let
              val () = $A.free<byte>(nbuf)
              val () = $A.free<byte>(repo)
            in println! ("error: package.name not found in bats.toml") end
        end
      | ~$R.err(_) => println! ("error: could not parse bats.toml")
    end
  | ~$R.err(_) => println! ("error: could not open bats.toml")
end

(* ============================================================
   completions: generate shell completion scripts
   ============================================================ *)
fn do_completions(shell: int): void =
  if shell = 0 then
    print_string "# bash completions\ncomplete -W 'build check clean lock run test tree add remove upload init completions' bats-poc\n"
  else if shell = 1 then
    print_string "#compdef bats-poc\n_bats_poc_cmds=(build check clean lock run test tree add remove upload init completions)\ncompadd $_bats_poc_cmds\n"
  else if shell = 2 then
    print_string "# fish completions\nfor c in build check clean lock run test tree add remove upload init completions; complete -c bats-poc -n __fish_use_subcommand -a $c; end\n"
  else println! ("error: specify a shell (bash, zsh, fish)")

(* ============================================================
   init: create a new bats project
   ============================================================ *)
fn do_init(kind: int): void = let
  (* kind: 0=binary, 1=library *)
  (* Get current directory name via readlink /proc/self/cwd *)
  val @(cwd_buf, cwd_len) = (let
    val cc = $B.create()
    val () = bput(cc, "readlink /proc/self/cwd > /tmp/_bpoc_cwd.txt 2>/dev/null || pwd > /tmp/_bpoc_cwd.txt 2>/dev/null")
    val _ = run_sh(cc, 0)
    val cp = str_to_path_arr("/tmp/_bpoc_cwd.txt")
    val @(fz_cp, bv_cp) = $A.freeze<byte>(cp)
    val cf = $F.file_open(bv_cp, 65536, 0, 0)
    val () = $A.drop<byte>(fz_cp, bv_cp)
    val () = $A.free<byte>($A.thaw<byte>(fz_cp))
  in case+ cf of
    | ~$R.ok(cfd) => let
        val cb = $A.alloc<byte>(4096)
        val cr2 = $F.file_read(cfd, cb, 4096)
        val clen = (case+ cr2 of | ~$R.ok(nn) => nn | ~$R.err(_) => 0): int
        val ccr = $F.file_close(cfd)
        val () = $R.discard<int><int>(ccr)
        (* strip trailing newline *)
        val clen2 = strip_newline_arr(cb, clen)
      in @(cb, clen2) end
    | ~$R.err(_) => let val cb = $A.alloc<byte>(4096) in @(cb, 0) end
  end): [lcwd:agz] @($A.arr(byte, lcwd, 4096), int)
  val @(fz_cwd, bv_cwd) = $A.freeze<byte>(cwd_buf)
  (* Find last '/' in cwd path to extract basename *)
  fun find_last_slash {l2:agz}{fuel2:nat} .<fuel2>.
    (bv: !$A.borrow(byte, l2, 4096), pos: int, len: int,
     last: int, fuel2: int fuel2): int =
    if fuel2 <= 0 then last
    else if pos >= len then last
    else let
      val b = src_byte(bv, pos, 4096)
    in
      if b = 47 then find_last_slash(bv, pos + 1, len, pos, fuel2 - 1)
      else find_last_slash(bv, pos + 1, len, last, fuel2 - 1)
    end
  val last_slash = find_last_slash(bv_cwd, 0, cwd_len, ~1,
    $AR.checked_nat(cwd_len + 1))
  val name_start = last_slash + 1
  val name_len = cwd_len - name_start
  (* mkdir *)
  val cmd1 = $B.create()
  val () = (if kind = 0 then bput(cmd1, "mkdir -p src/bin")
    else bput(cmd1, "mkdir -p src"))
  val _ = run_sh(cmd1, 0)
  (* Write bats.toml *)
  val toml = $B.create()
  val () = bput(toml, "[package]\nname = \"")
  val () = copy_to_builder(bv_cwd, name_start, cwd_len, 4096, toml,
    $AR.checked_nat(name_len + 1))
  val () = (if kind = 0 then bput(toml, "\"\nkind = \"bin\"\n\n[dependencies]\n")
    else bput(toml, "\"\nkind = \"lib\"\n\n[dependencies]\n"))
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val rc = write_file_from_builder(bv_tp, 65536, toml)
  val () = $A.drop<byte>(fz_tp, bv_tp)
  val () = $A.free<byte>($A.thaw<byte>(fz_tp))
  (* Write source file *)
  val src = $B.create()
  val src_path = $B.create()
  val () = (if kind = 0 then let
    val () = bput(src, "implement ")
    val () = bput(src, "main0 () = println! (\"hello, world!\")\n")
    val () = bput(src_path, "src/bin/")
    val () = copy_to_builder(bv_cwd, name_start, cwd_len, 4096, src_path,
      $AR.checked_nat(name_len + 1))
  in bput(src_path, ".bats") end
  else let
    val () = bput(src, "#pub fun hello(): void\n\n")
    val () = bput(src, "implement hello () = println! (\"hello from library\")\n")
  in bput(src_path, "src/lib.bats") end)
  val () = $B.put_byte(src_path, 0)
  val @(src_pa, _) = $B.to_arr(src_path)
  val @(fz_sp, bv_sp) = $A.freeze<byte>(src_pa)
  val rc2 = write_file_from_builder(bv_sp, 65536, src)
  val () = $A.drop<byte>(fz_sp, bv_sp)
  val () = $A.free<byte>($A.thaw<byte>(fz_sp))
  val () = $A.drop<byte>(fz_cwd, bv_cwd)
  val () = $A.free<byte>($A.thaw<byte>(fz_cwd))
  (* Write .gitignore *)
  val gi = $B.create()
  val () = bput(gi, "build/\ndist/\nbats_modules/\ndocs/\n")
  val gp = str_to_path_arr(".gitignore")
  val @(fz_gp, bv_gp) = $A.freeze<byte>(gp)
  val rc3 = write_file_from_builder(bv_gp, 65536, gi)
  val () = $A.drop<byte>(fz_gp, bv_gp)
  val () = $A.free<byte>($A.thaw<byte>(fz_gp))
in
  if rc = 0 then
    if rc2 = 0 then
      if rc3 = 0 then println! ("initialized bats project in current directory")
      else println! ("error: failed to write .gitignore")
    else println! ("error: failed to write source file")
  else println! ("error: failed to write bats.toml")
end

(* ============================================================
   tree: display dependency tree from bats.lock
   ============================================================ *)
fn do_tree(): void = let
  val la = str_to_path_arr("bats.lock")
  val @(fz_la, bv_la) = $A.freeze<byte>(la)
  val lock_or = $F.file_open(bv_la, 65536, 0, 0)
  val () = $A.drop<byte>(fz_la, bv_la)
  val () = $A.free<byte>($A.thaw<byte>(fz_la))
in
  case+ lock_or of
  | ~$R.ok(lfd) => let
      val lock_buf = $A.alloc<byte>(65536)
      val lr = $F.file_read(lfd, lock_buf, 65536)
      val lock_len = (case+ lr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val lcr = $F.file_close(lfd)
      val () = $R.discard<int><int>(lcr)
    in
      if lock_len > 0 then let
        (* Use C helper to print Unicode tree (├──, └──) *)
        val @(fz_lb, bv_lb) = $A.freeze<byte>(lock_buf)
        val () = print_borrow(bv_lb, 0, lock_len, 65536, $AR.checked_nat(lock_len + 1))
        val () = $A.drop<byte>(fz_lb, bv_lb)
        val () = $A.free<byte>($A.thaw<byte>(fz_lb))
      in end
      else let
        val () = $A.free<byte>(lock_buf)
      in println! ("no dependencies") end
    end
  | ~$R.err(_) => println! ("error: no bats.lock found (run lock first)")
end

(* ============================================================
   add: add a dependency to bats.toml
   ============================================================ *)
fn do_add {l:agz}{n:pos}
  (bv: !$A.borrow(byte, l, n), pkg_start: int, pkg_len: int,
   max: int n): void = let
  (* Read bats.toml *)
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 65536, 0, 0)
  val () = $A.drop<byte>(fz_tp, bv_tp)
  val () = $A.free<byte>($A.thaw<byte>(fz_tp))
in
  case+ tor of
  | ~$R.ok(tfd) => let
      val tbuf = $A.alloc<byte>(4096)
      val trr = $F.file_read(tfd, tbuf, 4096)
      val tlen = (case+ trr of | ~$R.ok(nn) => nn | ~$R.err(_) => 0): int
      val tcr = $F.file_close(tfd)
      val () = $R.discard<int><int>(tcr)
      val @(fz_tb2, bv_tb2) = $A.freeze<byte>(tbuf)
      val out_b = $B.create()
      val () = copy_to_builder(bv_tb2, 0, tlen, 4096, out_b, $AR.checked_nat(tlen + 1))
      val () = $A.drop<byte>(fz_tb2, bv_tb2)
      val () = $A.free<byte>($A.thaw<byte>(fz_tb2))
      val () = bput(out_b, "\"")
      val () = copy_to_builder(bv, pkg_start, pkg_start + pkg_len, max, out_b, $AR.checked_nat(pkg_len + 1))
      val () = bput(out_b, "\" = \"\"\n")
      val tp3 = str_to_path_arr("bats.toml")
      val @(fz_tp3, bv_tp3) = $A.freeze<byte>(tp3)
      val rc = write_file_from_builder(bv_tp3, 65536, out_b)
      val () = $A.drop<byte>(fz_tp3, bv_tp3)
      val () = $A.free<byte>($A.thaw<byte>(fz_tp3))
    in
      if rc = 0 then let
          val () = print! ("added '")
          val () = print_borrow(bv, pkg_start, pkg_start + pkg_len, max,
            $AR.checked_nat(pkg_len + 1))
        in println! ("' to [dependencies]") end
      else println! ("error: cannot write bats.toml")
    end
  | ~$R.err(_) => println! ("error: cannot open bats.toml")
end

(* ============================================================
   remove: remove a dependency from bats.toml
   ============================================================ *)
fn do_remove {l:agz}{n:pos}
  (bv: !$A.borrow(byte, l, n), pkg_start: int, pkg_len: int,
   max: int n): void = let
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 65536, 0, 0)
  val () = $A.drop<byte>(fz_tp, bv_tp)
  val () = $A.free<byte>($A.thaw<byte>(fz_tp))
in
  case+ tor of
  | ~$R.ok(tfd) => let
      val tbuf = $A.alloc<byte>(4096)
      val trr = $F.file_read(tfd, tbuf, 4096)
      val tlen = (case+ trr of | ~$R.ok(nn) => nn | ~$R.err(_) => 0): int
      val tcr = $F.file_close(tfd)
      val () = $R.discard<int><int>(tcr)
      val () = $A.free<byte>(tbuf)
      val sed_cmd = $B.create()
      val () = bput(sed_cmd, "sed -i '/^\"")
      val () = copy_to_builder(bv, pkg_start, pkg_start + pkg_len, max, sed_cmd, $AR.checked_nat(pkg_len + 1))
      val () = bput(sed_cmd, "\"/d' bats.toml")
      val rc = run_sh(sed_cmd, 0)
    in
      if rc = 0 then let
          val () = print! ("removed '")
          val () = print_borrow(bv, pkg_start, pkg_start + pkg_len, max,
            $AR.checked_nat(pkg_len + 1))
        in println! ("' from [dependencies]") end
      else let
        val () = print! ("error: package '")
        val () = print_borrow(bv, pkg_start, pkg_start + pkg_len, max,
          $AR.checked_nat(pkg_len + 1))
      in println! ("' not found in [dependencies]") end
    end
  | ~$R.err(_) => println! ("error: cannot open bats.toml")
end

(* ============================================================
   Process spawning
   ============================================================ *)

fn run_process_demo(): void = let
  (* "/bin/echo" -- 9 bytes, exact alloc for spawn path *)
  val path_arr = $A.alloc<byte>(9)
  val () = $A.write_byte(path_arr, 0, 47)   (* / *)
  val () = $A.write_byte(path_arr, 1, 98)   (* b *)
  val () = $A.write_byte(path_arr, 2, 105)  (* i *)
  val () = $A.write_byte(path_arr, 3, 110)  (* n *)
  val () = $A.write_byte(path_arr, 4, 47)   (* / *)
  val () = $A.write_byte(path_arr, 5, 101)  (* e *)
  val () = $A.write_byte(path_arr, 6, 99)   (* c *)
  val () = $A.write_byte(path_arr, 7, 104)  (* h *)
  val () = $A.write_byte(path_arr, 8, 111)  (* o *)
  val @(fz_p, bv_p) = $A.freeze<byte>(path_arr)

  (* argv: "echo\0check passed\0" *)
  val b_argv = $B.create()
  val () = $B.put_byte(b_argv, 101)
  val () = $B.put_byte(b_argv, 99)
  val () = $B.put_byte(b_argv, 104)
  val () = $B.put_byte(b_argv, 111)
  val () = $B.put_byte(b_argv, 0)
  val () = $B.put_byte(b_argv, 99)
  val () = $B.put_byte(b_argv, 104)
  val () = $B.put_byte(b_argv, 101)
  val () = $B.put_byte(b_argv, 99)
  val () = $B.put_byte(b_argv, 107)
  val () = $B.put_byte(b_argv, 32)
  val () = $B.put_byte(b_argv, 112)
  val () = $B.put_byte(b_argv, 97)
  val () = $B.put_byte(b_argv, 115)
  val () = $B.put_byte(b_argv, 115)
  val () = $B.put_byte(b_argv, 101)
  val () = $B.put_byte(b_argv, 100)
  val () = $B.put_byte(b_argv, 0)
  val @(argv_arr, _) = $B.to_arr(b_argv)
  val @(fz_a, bv_a) = $A.freeze<byte>(argv_arr)

  (* envp: single null byte *)
  val envp_arr = $A.alloc<byte>(1)
  val () = $A.write_byte(envp_arr, 0, 0)
  val @(fz_e, bv_e) = $A.freeze<byte>(envp_arr)

  val spawn_r = $P.spawn(bv_p, 9, bv_a, 2, bv_e, 0,
    $P.dev_null(), $P.pipe_new(), $P.dev_null())

  val () = $A.drop<byte>(fz_p, bv_p)
  val () = $A.free<byte>($A.thaw<byte>(fz_p))
  val () = $A.drop<byte>(fz_a, bv_a)
  val () = $A.free<byte>($A.thaw<byte>(fz_a))
  val () = $A.drop<byte>(fz_e, bv_e)
  val () = $A.free<byte>($A.thaw<byte>(fz_e))
in
  case+ spawn_r of
  | ~$R.ok(sp) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = sp
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(serr_p)
      val+ ~$P.pipe_fd(stdout_fd) = sout_p
      val out_buf = $A.alloc<byte>(256)
      val read_r = $F.file_read(stdout_fd, out_buf, 256)
      val out_len = (case+ read_r of
        | ~$R.ok(n) => n
        | ~$R.err(_) => 0): int
      val fcr = $F.file_close(stdout_fd)
      val () = $R.discard<int><int>(fcr)
      val wait_r = $P.child_wait(child)
      val exit_code = (case+ wait_r of
        | ~$R.ok(n) => n
        | ~$R.err(_) => ~1): int
      val () = print! ("  process: ")
      val () = print_arr(out_buf, 0, out_len, 256, $AR.checked_nat(out_len))
      val () = println! ("  exit code: ", exit_code)
      val () = $A.free<byte>(out_buf)
    in end
  | ~$R.err(e) =>
      println! ("  spawn failed: ", e)
end

(* ============================================================
   run: build then execute the binary
   ============================================================ *)
fn do_run(): void = let
  val () = do_build(0)
  (* Read bats.toml to find the package name *)
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 65536, 0, 0)
  val () = $A.drop<byte>(fz_tp, bv_tp)
  val () = $A.free<byte>($A.thaw<byte>(fz_tp))
in
  case+ tor of
  | ~$R.ok(tfd) => let
      val tbuf = $A.alloc<byte>(4096)
      val trr = $F.file_read(tfd, tbuf, 4096)
      val tlen = (case+ trr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val tcr = $F.file_close(tfd)
      val () = $R.discard<int><int>(tcr)
      val @(fz_tb, bv_tb) = $A.freeze<byte>(tbuf)
      val pr = $T.parse(bv_tb, 4096)
      val () = $A.drop<byte>(fz_tb, bv_tb)
      val () = $A.free<byte>($A.thaw<byte>(fz_tb))
    in
      case+ pr of
      | ~$R.ok(doc) => let
          (* Query package.name *)
          val sec = $A.alloc<byte>(7)
          val () = make_package(sec)
          val @(fz_s, bv_s) = $A.freeze<byte>(sec)
          val kn = $A.alloc<byte>(4)
          val () = make_name(kn)
          val @(fz_kn, bv_kn) = $A.freeze<byte>(kn)
          val nbuf = $A.alloc<byte>(256)
          val nr = $T.get(doc, bv_s, 7, bv_kn, 4, nbuf, 256)
          val () = $A.drop<byte>(fz_kn, bv_kn)
          val () = $A.free<byte>($A.thaw<byte>(fz_kn))
          val () = $A.drop<byte>(fz_s, bv_s)
          val () = $A.free<byte>($A.thaw<byte>(fz_s))
          val () = $T.toml_free(doc)
        in
          case+ nr of
          | ~$R.some(nlen) => let
              (* Check if --bin was specified (stored in /tmp/_bpoc_bin.txt) *)
              val bin_path2 = str_to_path_arr("/tmp/_bpoc_bin.txt")
              val @(fz_bp2, bv_bp2) = $A.freeze<byte>(bin_path2)
              val bin_or = $F.file_open(bv_bp2, 65536, 0, 0)
              val () = $A.drop<byte>(fz_bp2, bv_bp2)
              val () = $A.free<byte>($A.thaw<byte>(fz_bp2))
              val @(bin_name, bn_len) = (case+ bin_or of
                | ~$R.ok(bfd2) => let
                    val bbn = $A.alloc<byte>(256)
                    val brr = $F.file_read(bfd2, bbn, 256)
                    val brl = (case+ brr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                    val bcr = $F.file_close(bfd2)
                    val () = $R.discard<int><int>(bcr)
                    val brl2 = strip_newline_arr256(bbn, brl)
                  in @(bbn, brl2) end
                | ~$R.err(_) => let val bbn = $A.alloc<byte>(256) in @(bbn, 0) end): [lbbn:agz] @($A.arr(byte, lbbn, 256), int)
              val cmd = $B.create()
              val () = bput(cmd, "./dist/debug/")
            in
              if bn_len > 0 then let
                val @(fz_bn, bv_bn) = $A.freeze<byte>(bin_name)
                val () = copy_to_builder(bv_bn, 0, bn_len, 256, cmd,
                  $AR.checked_nat(bn_len + 1))
                val () = $A.drop<byte>(fz_bn, bv_bn)
                val () = $A.free<byte>($A.thaw<byte>(fz_bn))
                val () = $A.free<byte>(nbuf)
                val rc = run_sh(cmd, 0)
              in
                if rc <> 0 then println! ("error: run failed")
                else ()
              end
              else let
                val () = $A.free<byte>(bin_name)
                val @(fz_nb, bv_nb) = $A.freeze<byte>(nbuf)
                val () = copy_to_builder(bv_nb, 0, nlen, 256, cmd,
                  $AR.checked_nat(nlen + 1))
                val () = $A.drop<byte>(fz_nb, bv_nb)
                val () = $A.free<byte>($A.thaw<byte>(fz_nb))
                val rc = run_sh(cmd, 0)
              in
                if rc <> 0 then println! ("error: run failed")
                else ()
              end
            end
          | ~$R.none() => let
              val () = $A.free<byte>(nbuf)
            in println! ("error: package.name not found in bats.toml") end
        end
      | ~$R.err(_) => println! ("error: could not parse bats.toml")
    end
  | ~$R.err(_) => println! ("error: could not open bats.toml")
end

(* ============================================================
   do_check: read bats.toml, find .bats files
   ============================================================ *)

fn do_check(): void = let
  val path = $A.alloc<byte>(9)
  val () = make_bats_toml(path)
  val @(fz, bv) = $A.freeze<byte>(path)
  val open_r = $F.file_open(bv, 9, 0, 0)
  val () = $A.drop<byte>(fz, bv)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in
  case+ open_r of
  | ~$R.ok(fd) => let
      val buf = $A.alloc<byte>(4096)
      val read_r = $F.file_read(fd, buf, 4096)
    in
      case+ read_r of
      | ~$R.ok(_) => let
          val cr = $F.file_close(fd)
          val () = $R.discard<int><int>(cr)
          val @(fz2, bv2) = $A.freeze<byte>(buf)
          val pr = $T.parse(bv2, 4096)
          val () = $A.drop<byte>(fz2, bv2)
          val () = $A.free<byte>($A.thaw<byte>(fz2))
        in
          case+ pr of
          | ~$R.ok(doc) => let
              val sec = $A.alloc<byte>(7)
              val () = make_package(sec)
              val @(fz_s, bv_s) = $A.freeze<byte>(sec)

              val kn = $A.alloc<byte>(4)
              val () = make_name(kn)
              val @(fz_kn, bv_kn) = $A.freeze<byte>(kn)
              val nbuf = $A.alloc<byte>(256)
              val nr = $T.get(doc, bv_s, 7, bv_kn, 4, nbuf, 256)
              val () = $A.drop<byte>(fz_kn, bv_kn)
              val () = $A.free<byte>($A.thaw<byte>(fz_kn))
              val () = (case+ nr of
                | ~$R.some(len) => let
                    val () = print! ("package.name = ")
                    val () = print_arr(nbuf, 0, len, 256, $AR.checked_nat(len))
                    val () = print_newline()
                    val () = $A.free<byte>(nbuf)
                  in end
                | ~$R.none() => let
                    val () = println! ("package.name not found")
                    val () = $A.free<byte>(nbuf)
                  in end)

              val kk = $A.alloc<byte>(4)
              val () = make_kind(kk)
              val @(fz_kk, bv_kk) = $A.freeze<byte>(kk)
              val kbuf = $A.alloc<byte>(256)
              val kr = $T.get(doc, bv_s, 7, bv_kk, 4, kbuf, 256)
              val () = $A.drop<byte>(fz_kk, bv_kk)
              val () = $A.free<byte>($A.thaw<byte>(fz_kk))
              val () = (case+ kr of
                | ~$R.some(len) => let
                    val () = print! ("package.kind = ")
                    val () = print_arr(kbuf, 0, len, 256, $AR.checked_nat(len))
                    val () = print_newline()
                    val () = $A.free<byte>(kbuf)
                  in end
                | ~$R.none() => let
                    val () = println! ("package.kind not found")
                    val () = $A.free<byte>(kbuf)
                  in end)

              val () = $A.drop<byte>(fz_s, bv_s)
              val () = $A.free<byte>($A.thaw<byte>(fz_s))

              val () = println! ("Scanning src/bin/ for .bats files...")
              val sp = $A.alloc<byte>(7)
              val () = make_src_bin(sp)
              val @(fz_sp, bv_sp) = $A.freeze<byte>(sp)
              val dir_r = $F.dir_open(bv_sp, 7)
              val () = $A.drop<byte>(fz_sp, bv_sp)
              val () = $A.free<byte>($A.thaw<byte>(fz_sp))
              val () = (case+ dir_r of
                | ~$R.ok(d) => let
                    fun scan_dir {fuel:nat} .<fuel>.
                      (d: !$F.dir, fuel: int fuel): void =
                      if fuel <= 0 then ()
                      else let
                        val ent = $A.alloc<byte>(256)
                        val nr = $F.dir_next(d, ent, 256)
                        val len = $R.option_unwrap_or<int>(nr, ~1)
                      in
                        if len >= 0 then let
                          val dd = is_dot_or_dotdot(ent, len, 256)
                          val bb = has_bats_ext(ent, len, 256)
                        in
                          if dd then let
                            val () = $A.free<byte>(ent)
                          in scan_dir(d, fuel - 1) end
                          else if bb then let
                            val () = print! ("  src/bin/")
                            val () = print_arr(ent, 0, len, 256, $AR.checked_nat(len))
                            val () = print_newline()
                            val () = $A.free<byte>(ent)
                          in scan_dir(d, fuel - 1) end
                          else let
                            val () = $A.free<byte>(ent)
                          in scan_dir(d, fuel - 1) end
                        end
                        else
                          $A.free<byte>(ent)
                      end
                    val () = scan_dir(d, 1000)
                    val dcr = $F.dir_close(d)
                    val () = $R.discard<int><int>(dcr)
                  in end
                | ~$R.err(_) =>
                    println! ("Cannot open src/bin/ directory"))

              (* Lex a test: read our own source and lex it *)
              val () = println! ("Lexing src/bin/bats-poc.bats...")
              val lex_path = $A.alloc<byte>(22)
              (* "src/bin/bats-poc.bats" *)
              val () = $A.write_byte(lex_path, 0, 115)   (* s *)
              val () = $A.write_byte(lex_path, 1, 114)   (* r *)
              val () = $A.write_byte(lex_path, 2, 99)    (* c *)
              val () = $A.write_byte(lex_path, 3, 47)    (* / *)
              val () = $A.write_byte(lex_path, 4, 98)    (* b *)
              val () = $A.write_byte(lex_path, 5, 105)   (* i *)
              val () = $A.write_byte(lex_path, 6, 110)   (* n *)
              val () = $A.write_byte(lex_path, 7, 47)    (* / *)
              val () = $A.write_byte(lex_path, 8, 98)    (* b *)
              val () = $A.write_byte(lex_path, 9, 97)    (* a *)
              val () = $A.write_byte(lex_path, 10, 116)  (* t *)
              val () = $A.write_byte(lex_path, 11, 115)  (* s *)
              val () = $A.write_byte(lex_path, 12, 45)   (* - *)
              val () = $A.write_byte(lex_path, 13, 112)  (* p *)
              val () = $A.write_byte(lex_path, 14, 111)  (* o *)
              val () = $A.write_byte(lex_path, 15, 99)   (* c *)
              val () = $A.write_byte(lex_path, 16, 46)   (* . *)
              val () = $A.write_byte(lex_path, 17, 98)   (* b *)
              val () = $A.write_byte(lex_path, 18, 97)   (* a *)
              val () = $A.write_byte(lex_path, 19, 116)  (* t *)
              val () = $A.write_byte(lex_path, 20, 115)  (* s *)
              val () = $A.write_byte(lex_path, 21, 0)
              val @(fz_lp, bv_lp) = $A.freeze<byte>(lex_path)
              val lex_or = $F.file_open(bv_lp, 22, 0, 0)
              val () = $A.drop<byte>(fz_lp, bv_lp)
              val () = $A.free<byte>($A.thaw<byte>(fz_lp))
              val () = (case+ lex_or of
                | ~$R.ok(lfd) => let
                    val lbuf = $A.alloc<byte>(65536)
                    val lr = $F.file_read(lfd, lbuf, 65536)
                    val lbytes = (case+ lr of
                      | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                    val lcr = $F.file_close(lfd)
                    val () = $R.discard<int><int>(lcr)
                    val @(fz_lb, bv_lb) = $A.freeze<byte>(lbuf)
                    val @(span_arr, span_len, span_count) =
                      do_lex(bv_lb, lbytes, 65536)
                    val () = println! ("  lexed ", lbytes, " bytes -> ",
                                       span_count, " spans")
                    (* Now emit .sats/.dats *)
                    val @(fz_sp, bv_sp) = $A.freeze<byte>(span_arr)
                    val @(sats_arr, sats_len, dats_arr, dats_len, pre_lines) =
                      do_emit(bv_lb, lbytes, 65536, bv_sp, 65536, span_count)
                    val () = $A.drop<byte>(fz_sp, bv_sp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                    val () = $A.drop<byte>(fz_lb, bv_lb)
                    val () = $A.free<byte>($A.thaw<byte>(fz_lb))
                    val () = println! ("  emitted sats: ", sats_len,
                                       " bytes, dats: ", dats_len,
                                       " bytes (", pre_lines, " prelude lines)")
                    val () = $A.free<byte>(sats_arr)
                    val () = $A.free<byte>(dats_arr)
                  in end
                | ~$R.err(_) =>
                    println! ("  could not open source for lexing"))
              val () = run_process_demo()
              val () = println! ("check passed")
              val () = $T.toml_free(doc)
            in end
          | ~$R.err(e) =>
              println! ("TOML parse error: ", e)
        end
      | ~$R.err(e) => let
          val cr = $F.file_close(fd)
          val () = $R.discard<int><int>(cr)
          val () = $A.free<byte>(buf)
        in println! ("Read error: ", e) end
    end
  | ~$R.err(e) =>
      println! ("Cannot open bats.toml: ", e)
end

(* ============================================================
   Main: read argv from /proc/self/cmdline, dispatch
   ============================================================ *)

implement main0 () = let
  val clp = $A.alloc<byte>(18)
  val () = make_proc_cmdline(clp)
  val @(fz_cl, bv_cl) = $A.freeze<byte>(clp)
  val cl_open = $F.file_open(bv_cl, 18, 0, 0)
  val () = $A.drop<byte>(fz_cl, bv_cl)
  val () = $A.free<byte>($A.thaw<byte>(fz_cl))
in
  case+ cl_open of
  | ~$R.ok(cl_fd) => let
      val cl_buf = $A.alloc<byte>(4096)
      val cl_read = $F.file_read(cl_fd, cl_buf, 4096)
    in
      case+ cl_read of
      | ~$R.ok(cl_n) => let
          val cr = $F.file_close(cl_fd)
          val () = $R.discard<int><int>(cr)
          val tok0_end = find_null(cl_buf, 0, 4096, 4096)
          (* Check for --run-in <dir> global flag before subcommand *)
          val first_start = tok0_end + 1
          val first_end = find_null(cl_buf, first_start, 4096, 4096)
          val first_len = first_end - first_start
          (* Handle --run-in; returns offset to actual command *)
          val cmd_start = handle_run_in(cl_buf, cl_n, first_start, first_end, first_len)
          val cmd_end = find_null(cl_buf, cmd_start, 4096, 4096)
          val cmd_len = cmd_end - cmd_start
          (* Parse global flags --verbose/-v and --quiet/-q *)
          val has_verbose = has_flag(cl_buf, cl_n, cmd_end + 1, "--verbose")
          val has_v = has_flag(cl_buf, cl_n, cmd_end + 1, "-v")
          val has_quiet = has_flag(cl_buf, cl_n, cmd_end + 1, "--quiet")
          val has_q = has_flag(cl_buf, cl_n, cmd_end + 1, "-q")
          val () = (if has_verbose > 0 orelse has_v > 0 then
            (!g_verbose := true)
            else ())
          val () = (if has_quiet > 0 orelse has_q > 0 then
            (!g_quiet := true)
            else ())
          (* Parse --repository flag: store in /tmp/_bpoc_repo.txt for later use *)
          val repo_buf = $A.alloc<byte>(4096)
          val rlen = get_flag_val(cl_buf, cl_n, cmd_end + 1, "--repository", repo_buf, 4096)
          val () = (if rlen > 0 then let
              val @(fz_rb2, bv_rb2) = $A.freeze<byte>(repo_buf)
              val rb2 = $B.create()
              val () = copy_to_builder(bv_rb2, 0, rlen, 4096, rb2, $AR.checked_nat(rlen + 1))
              val () = $B.put_byte(rb2, 10)
              val () = $A.drop<byte>(fz_rb2, bv_rb2)
              val () = $A.free<byte>($A.thaw<byte>(fz_rb2))
              val rtp = str_to_path_arr("/tmp/_bpoc_repo.txt")
              val @(fz_rtp, bv_rtp) = $A.freeze<byte>(rtp)
              val _ = write_file_from_builder(bv_rtp, 65536, rb2)
              val () = $A.drop<byte>(fz_rtp, bv_rtp)
              val () = $A.free<byte>($A.thaw<byte>(fz_rtp))
            in end
            else $A.free<byte>(repo_buf))
        in
          if cmd_is_check(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_check() end
          else if cmd_is_build(cl_buf, cmd_start, cmd_len, 4096) then let
            val only_val = $A.alloc<byte>(32)
            val olen = get_flag_val(cl_buf, cl_n, cmd_end + 1, "--only", only_val, 32)
            val () = $A.free<byte>(cl_buf)
            (* Check if --only debug|release|native|wasm *)
            val @(fz_ov, bv_ov) = $A.freeze<byte>(only_val)
            val only_debug = (if olen = 5 then let
              val b0 = byte2int0($A.read<byte>(bv_ov, 0))
              val b1 = byte2int0($A.read<byte>(bv_ov, 1))
            in $AR.eq_int_int(b0, 100) && $AR.eq_int_int(b1, 101) end
              else false): bool
            val only_release = (if olen = 7 then let
              val b0 = byte2int0($A.read<byte>(bv_ov, 0))
              val b1 = byte2int0($A.read<byte>(bv_ov, 1))
            in $AR.eq_int_int(b0, 114) && $AR.eq_int_int(b1, 101) end
              else false): bool
            (* "wasm" = 4 chars, w=119 *)
            val only_wasm = (if olen = 4 then let
              val b0 = byte2int0($A.read<byte>(bv_ov, 0))
            in $AR.eq_int_int(b0, 119) end
              else false): bool
            val () = $A.drop<byte>(fz_ov, bv_ov)
            val () = $A.free<byte>($A.thaw<byte>(fz_ov))
          in
            if only_wasm then println! ("error: wasm target is not yet supported")
            else if only_debug then do_build(0)
            else if only_release then do_build(1)
            else let
              val () = do_build(0)
            in do_build(1) end
          end
          else if cmd_is_clean(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_clean() end
          else if cmd_is_lock(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_lock() end
          else if cmd_is_run(cl_buf, cmd_start, cmd_len, 4096) then let
            val bin_buf = $A.alloc<byte>(256)
            val blen = get_flag_val(cl_buf, cl_n, cmd_end + 1, "--bin", bin_buf, 256)
            val () = (if blen > 0 then let
                val @(fz_bb2, bv_bb2) = $A.freeze<byte>(bin_buf)
                val bb2 = $B.create()
                val () = copy_to_builder(bv_bb2, 0, blen, 256, bb2, $AR.checked_nat(blen + 1))
                val () = $B.put_byte(bb2, 10)
                val () = $A.drop<byte>(fz_bb2, bv_bb2)
                val () = $A.free<byte>($A.thaw<byte>(fz_bb2))
                val btp = str_to_path_arr("/tmp/_bpoc_bin.txt")
                val @(fz_btp, bv_btp) = $A.freeze<byte>(btp)
                val _ = write_file_from_builder(bv_btp, 65536, bb2)
                val () = $A.drop<byte>(fz_btp, bv_btp)
                val () = $A.free<byte>($A.thaw<byte>(fz_btp))
              in end
              else $A.free<byte>(bin_buf))
            val () = $A.free<byte>(cl_buf)
          in do_run() end
          else if cmd_is_init(cl_buf, cmd_start, cmd_len, 4096) then let
            (* Parse init argument: "binary"|"bin" or "library"|"lib" *)
            val arg_start = cmd_end + 1
            val arg_end = find_null(cl_buf, arg_start, 4096, 4096)
            val arg_len = arg_end - arg_start
            (* Check for "binary"(6) or "bin"(3) → 0, "library"(7) or "lib"(3) → 1 *)
            fn get_init_kind {l2:agz}
              (buf: !$A.arr(byte, l2, 4096), astart: int, alen: int): int =
              if alen = 3 orelse alen = 6 orelse alen = 7 then
                let val a0 = g1ofg0(astart) in
                  if a0 >= 0 then
                    if a0 < 4096 then let
                      val c0 = byte2int0($A.get<byte>(buf, a0))
                    in
                      if $AR.eq_int_int(c0, 98) then 0    (* 'b' = binary/bin *)
                      else if $AR.eq_int_int(c0, 108) then 1  (* 'l' = library/lib *)
                      else ~1
                    end else ~1
                  else ~1
                end
              else ~1
            val kind = get_init_kind(cl_buf, arg_start, arg_len)
            val () = $A.free<byte>(cl_buf)
          in
            if kind >= 0 then do_init(kind)
            else println! ("error: specify 'binary' or 'library'\nusage: bats-poc init binary|library")
          end
          else if cmd_is_test(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_test() end
          else if cmd_is_upload(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_upload() end
          else if cmd_is_tree(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_tree() end
          else if cmd_is_add(cl_buf, cmd_start, cmd_len, 4096) then let
            val pkg_start = cmd_end + 1
            val pkg_end = find_null(cl_buf, pkg_start, 4096, 4096)
            val pkg_len = pkg_end - pkg_start
            val @(fz_ab, bv_ab) = $A.freeze<byte>(cl_buf)
          in
            if pkg_len > 0 then let
              val () = do_add(bv_ab, pkg_start, pkg_len, 4096)
              val () = $A.drop<byte>(fz_ab, bv_ab)
              val () = $A.free<byte>($A.thaw<byte>(fz_ab))
            in end
            else let
              val () = $A.drop<byte>(fz_ab, bv_ab)
              val () = $A.free<byte>($A.thaw<byte>(fz_ab))
            in println! ("error: specify a package name\nusage: bats-poc add <package>") end
          end
          else if cmd_is_remove(cl_buf, cmd_start, cmd_len, 4096) then let
            val pkg_start = cmd_end + 1
            val pkg_end = find_null(cl_buf, pkg_start, 4096, 4096)
            val pkg_len = pkg_end - pkg_start
            val @(fz_rb, bv_rb) = $A.freeze<byte>(cl_buf)
          in
            if pkg_len > 0 then let
              val () = do_remove(bv_rb, pkg_start, pkg_len, 4096)
              val () = $A.drop<byte>(fz_rb, bv_rb)
              val () = $A.free<byte>($A.thaw<byte>(fz_rb))
            in end
            else let
              val () = $A.drop<byte>(fz_rb, bv_rb)
              val () = $A.free<byte>($A.thaw<byte>(fz_rb))
            in println! ("error: specify a package name\nusage: bats-poc remove <package>") end
          end
          else if cmd_is_completions(cl_buf, cmd_start, cmd_len, 4096) then let
            val arg_start = cmd_end + 1
            val arg_end = find_null(cl_buf, arg_start, 4096, 4096)
            val arg_len = arg_end - arg_start
            (* "bash"=4: b=98, "zsh"=3: z=122, "fish"=4: f=102 *)
            fn get_shell_kind {l2:agz}
              (buf: !$A.arr(byte, l2, 4096), astart: int, alen: int): int =
              let val a0 = g1ofg0(astart) in
                if a0 >= 0 then
                  if a0 < 4096 then let
                    val c0 = byte2int0($A.get<byte>(buf, a0))
                  in
                    if alen = 4 then
                      (if $AR.eq_int_int(c0, 98) then 0    (* 'b' = bash *)
                       else if $AR.eq_int_int(c0, 102) then 2  (* 'f' = fish *)
                       else ~1)
                    else if alen = 3 then
                      (if $AR.eq_int_int(c0, 122) then 1 else ~1)  (* 'z' = zsh *)
                    else ~1
                  end else ~1
                else ~1
              end
            val shell = get_shell_kind(cl_buf, arg_start, arg_len)
            val () = $A.free<byte>(cl_buf)
          in
            if shell >= 0 then do_completions(shell)
            else println! ("error: specify a shell (bash, zsh, fish)\nusage: bats-poc completions bash|zsh|fish")
          end
          else if cmd_is_version(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in println! ("bats-poc 0.1.0") end
          else let
            val () = $A.free<byte>(cl_buf)
          in println! ("usage: bats-poc <init|lock|add|remove|build|run|test|check|tree|upload|clean|completions> [--only debug|release]") end
        end
      | ~$R.err(e) => let
          val cr = $F.file_close(cl_fd)
          val () = $R.discard<int><int>(cr)
          val () = $A.free<byte>(cl_buf)
        in println! ("Cannot read /proc/self/cmdline: ", e) end
    end
  | ~$R.err(e) =>
      println! ("Cannot open /proc/self/cmdline: ", e)
end
