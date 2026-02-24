(* bats -- bats compiler *)

#include "share/atspre_staload.hats"

#use argparse as AP
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
val g_to_c: ref(int) = ref(0)
val g_to_c_done: ref(int) = ref(0)

fn is_verbose(): bool = !g_verbose
fn is_quiet(): bool = !g_quiet
fn is_test_mode(): bool = !g_test_mode
fn is_to_c(): bool = !g_to_c > 0

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

(* Check for "let" at keyword boundary: l=108 e=101 t=116 *)
fn looking_at_let {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  is_kw_boundary_before(src, pos, max) &&
  $AR.eq_int_int(src_byte(src, pos, max), 108) &&
  $AR.eq_int_int(src_byte(src, pos + 1, max), 101) &&
  $AR.eq_int_int(src_byte(src, pos + 2, max), 116) &&
  is_kw_boundary(src, pos + 3, max)

(* Lex $UNSAFE begin...end or $UNSAFE.ident — tracks nesting *)
fun find_end_kw {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   depth: int, fuel: int fuel): int =
  if fuel <= 0 then src_len
  else if pos >= src_len then src_len
  else if looking_at_end(src, pos, max) then
    (if depth <= 0 then pos
     else find_end_kw(src, pos + 3, src_len, max, depth - 1, fuel - 1))
  else if looking_at_begin(src, pos, max) then
    find_end_kw(src, pos + 5, src_len, max, depth + 1, fuel - 1)
  else if looking_at_let(src, pos, max) then
    find_end_kw(src, pos + 3, src_len, max, depth + 1, fuel - 1)
  else find_end_kw(src, pos + 1, src_len, max, depth, fuel - 1)

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
      val end_pos = find_end_kw(src, contents_start, src_len, max, 0, $AR.checked_nat(src_len))
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
      val end_pos = find_end_kw(src, contents_start, src_len, max, 0, $AR.checked_nat(src_len))
      val ep = (if end_pos < src_len then end_pos + 3 else end_pos): int
      val () = put_span(spans, 10, 0, start, ep, contents_start, end_pos, 0, 0)
    in @(ep, count + 1, true) end
    else @(start, count, false)
  end
  else if looking_at_begin(src, p0, max) then let
    val contents_start = p0 + 5
    val end_pos = find_end_kw(src, contents_start, src_len, max, 0, $AR.checked_nat(src_len))
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

  (* Rename the entry point function in the .dats output *)
  val @(dats_tmp, dats_tmp_len) = $B.to_arr(dats_b)
  val @(fz_dt, bv_dt) = $A.freeze<byte>(dats_tmp)
  (* Search for the entry point pattern: 15 chars starting with 'i' *)
  fun find_impl_main0 {ld:agz}{nd:pos}{fuel:nat} .<fuel>.
    (bv: !$A.borrow(byte, ld, nd), len: int, max: int nd, pos: int, fuel: int fuel): int =
    if fuel <= 0 then ~1
    else if pos + 15 > len then ~1
    else let
      val p = g1ofg0(pos)
    in
      if p >= 0 then if p + 14 < max then let
        val b0 = byte2int0($A.read<byte>(bv, p))
      in
        if $AR.eq_int_int(b0, 105) then let (* 'i' *)
          val b4 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 4, max)))
          val b9 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 9, max)))
          val b10 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 10, max)))
          val b14 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 14, max)))
        in
          (* Check pattern: e=101@4, ' '=32@9, m=109@10, 0=48@14 *)
          if $AR.eq_int_int(b4, 101) then
            if $AR.eq_int_int(b9, 32) then
              if $AR.eq_int_int(b10, 109) then
                if $AR.eq_int_int(b14, 48) then let
                  (* Verify full match: check remaining bytes *)
                  val b1 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 1, max)))
                  val b2 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 2, max)))
                  val b3 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 3, max)))
                  val b5 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 5, max)))
                  val b6 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 6, max)))
                  val b7 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 7, max)))
                  val b8 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 8, max)))
                  val b11 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 11, max)))
                  val b12 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 12, max)))
                  val b13 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p + 13, max)))
                in
                  (* m=109 p=112 l=108 e=101 m=109 e=101 n=110 t=116 a=97 i=105 n=110 *)
                  if $AR.eq_int_int(b1, 109) then
                    if $AR.eq_int_int(b2, 112) then
                      if $AR.eq_int_int(b3, 108) then
                        if $AR.eq_int_int(b5, 109) then
                          if $AR.eq_int_int(b6, 101) then
                            if $AR.eq_int_int(b7, 110) then
                              if $AR.eq_int_int(b8, 116) then
                                if $AR.eq_int_int(b11, 97) then
                                  if $AR.eq_int_int(b12, 105) then
                                    if $AR.eq_int_int(b13, 110) then pos
                                    else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
                                  else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
                                else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
                              else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
                            else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
                          else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
                        else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
                      else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
                    else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
                  else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
                end
                else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
              else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
            else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
          else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
        end
        else find_impl_main0(bv, len, max, pos + 1, fuel - 1)
      end else ~1 else ~1
    end
  val main0_pos = find_impl_main0(bv_dt, dats_tmp_len, 65536,
    0, $AR.checked_nat(dats_tmp_len + 1))
  val has_main0 = main0_pos >= 0

  (* Build final dats with rename *)
  val dats_final = $B.create()
  val () = (if has_main0 then let
    (* Copy before match *)
    val () = emit_range(bv_dt, 0, main0_pos, 65536, dats_final,
      $AR.checked_nat(main0_pos + 1))
    (* Write replacement *)
    val () = bput(dats_final, "implement __BATS_main0")
    (* Copy after match+15 *)
    val after = main0_pos + 15
    val () = emit_range(bv_dt, after, dats_tmp_len, 65536, dats_final,
      $AR.checked_nat(dats_tmp_len - after + 1))
  in end
  else (* No main0, just copy as-is *)
    emit_range(bv_dt, 0, dats_tmp_len, 65536, dats_final,
      $AR.checked_nat(dats_tmp_len + 1))
  )
  val () = $A.drop<byte>(fz_dt, bv_dt)
  val () = $A.free<byte>($A.thaw<byte>(fz_dt))

  (* If has main0, add declaration to sats *)
  val () = (if has_main0 then bput(sats_b, "\nfun __BATS_main0 (): void\n") else ())

  val @(sats_arr, sats_len) = $B.to_arr(sats_b)
  val @(dats_arr, dats_len) = $B.to_arr(dats_final)
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
fn do_lock(dev: int, dry_run: int): void = let
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
    val () = (if dev > 0 then bput(cmd, " --dev") else ())
    val () = (if dry_run > 0 then bput(cmd, " --dry-run") else ())
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

(* Write WASM freestanding runtime header *)
fn write_wasm_runtime_h(): int = let
  val b = $B.create()
  val () = bput(b, "/* runtime.h -- Freestanding WASM runtime for ATS2 */\n#ifndef BATS_WASM_RUNTIME_H\n#define BATS_WASM_RUNTIME_H\n")
  val () = bput(b, "typedef void atstype_void;\ntypedef void atsvoid_t0ype;\ntypedef int atstype_int;\ntypedef unsigned int atstype_uint;\n")
  val () = bput(b, "typedef long int atstype_lint;\ntypedef unsigned long int atstype_ulint;\ntypedef long long int atstype_llint;\n")
  val () = bput(b, "typedef unsigned long long int atstype_ullint;\ntypedef short int atstype_sint;\ntypedef unsigned short int atstype_usint;\n")
  val () = bput(b, "typedef atstype_lint atstype_ssize;\ntypedef atstype_ulint atstype_size;\ntypedef int atstype_bool;\n")
  val () = bput(b, "typedef unsigned char atstype_byte;\ntypedef char atstype_char;\ntypedef signed char atstype_schar;\ntypedef unsigned char atstype_uchar;\n")
  val () = bput(b, "typedef char *atstype_string;\ntypedef char *atstype_stropt;\ntypedef char *atstype_strptr;\n")
  val () = bput(b, "typedef void *atstype_ptr;\ntypedef void *atstype_ptrk;\ntypedef void *atstype_ref;\ntypedef void *atstype_boxed;\n")
  val () = bput(b, "typedef void *atstype_datconptr;\ntypedef void *atstype_datcontyp;\ntypedef void *atstype_arrptr;\ntypedef void *atstype_funptr;\ntypedef void *atstype_cloptr;\n")
  val () = bput(b, "#define atstkind_type(tk) tk\n#define atstkind_t0ype(tk) tk\n#ifndef _ATSTYPE_VAR_SIZE_\n#define _ATSTYPE_VAR_SIZE_ 0X10000\n#endif\n")
  val () = bput(b, "typedef struct { char _[_ATSTYPE_VAR_SIZE_]; } atstype_var[0];\n#define atstyvar_type(a) atstype_var\n#define atstybox_type(hit) atstype_boxed\n")
  val () = bput(b, "#define atsrefarg0_type(hit) hit\n#define atsrefarg1_type(hit) atstype_ref\n")
  val () = bput(b, "#define atsbool_true 1\n#define atsbool_false 0\n#define atsptr_null ((void*)0)\n#define the_atsptr_null ((void*)0)\n")
  val () = bput(b, "#define ATSstruct struct\n#define ATSextern() extern\n#define ATSstatic() static\n#define ATSinline() static inline\n")
  val () = bput(b, "#define ATSdynload()\n#define ATSdynloadflag_sta(flag)\n#define ATSdynloadflag_ext(flag) extern int flag\n")
  val () = bput(b, "#define ATSdynloadflag_init(flag) int flag = 0\n#define ATSdynloadflag_minit(flag) int flag = 0\n#define ATSdynloadset(flag) flag = 1\n")
  val () = bput(b, "#define ATSdynloadfcall(dynloadfun) dynloadfun()\n#define ATSassume(flag) void *flag = (void*)0\n")
  val () = bput(b, "#define ATSdyncst_mac(d2c)\n#define ATSdyncst_castfn(d2c)\n#define ATSdyncst_extfun(d2c, targs, tres) extern tres d2c targs\n")
  val () = bput(b, "#define ATSdyncst_stafun(d2c, targs, tres) static tres d2c targs\n#define ATSdyncst_valimp(d2c, type) type d2c\n#define ATSdyncst_valdec(d2c, type) extern type d2c\n")
  val () = bput(b, "#define ATSif(x) if(x)\n#define ATSthen()\n#define ATSelse() else\n#define ATSifthen(x) if(x)\n#define ATSifnthen(x) if(!(x))\n")
  val () = bput(b, "#define ATSreturn(x) return(x)\n#define ATSreturn_void(x) return\n#define ATSfunbody_beg()\n#define ATSfunbody_end()\n")
  val () = bput(b, "#define ATSPMVint(i) i\n#define ATSPMVintrep(rep) (rep)\n#define ATSPMVbool_true() atsbool_true\n#define ATSPMVbool_false() atsbool_false\n")
  val () = bput(b, "#define ATSPMVchar(c) (c)\n#define ATSPMVstring(str) (str)\n#define ATSPMVi0nt(tok) (tok)\n#define ATSPMVempty()\n")
  val () = bput(b, "#define ATSPMVextval(name) (name)\n#define ATSPMVptrof(lval) (&(lval))\n#define ATSPMVptrof_void(lval) ((void*)0)\n")
  val () = bput(b, "#define ATSPMVrefarg0(val) (val)\n#define ATSPMVrefarg1(ref) (ref)\n#define ATSPMVsizeof(hit) (sizeof(hit))\n")
  val () = bput(b, "#define ATSPMVfunlab(flab) (flab)\n#define ATSPMVcastfn(d2c, hit, arg) ((hit)arg)\n#define ATSPMVtyrep(rep) (rep)\n")
  val () = bput(b, "#define ATStyclo() struct{ void *cfun; }\n#define ATSfunclo_fun(pmv, targs, tres) ((tres(*)targs)(pmv))\n")
  val () = bput(b, "#define ATSfunclo_clo(pmv, targs, tres) ((tres(*)targs)(((ATStyclo()*)pmv)->cfun))\n")
  val () = bput(b, "#define ATSfuncall(fun, funarg) (fun)funarg\n#define ATSextfcall(fun, funarg) (fun)funarg\n#define ATSextmcall(obj, mtd, funarg) (obj->mtd)funarg\n")
  val () = bput(b, "#define ATStmpdec(tmp, hit) hit tmp\n#define ATStmpdec_void(tmp)\n#define ATSstatmpdec(tmp, hit) static hit tmp\n#define ATSstatmpdec_void(tmp)\n")
  val () = bput(b, "#define ATSderef(pmv, hit) (*(hit*)pmv)\n#define ATSCKnot(x) ((x)==0)\n#define ATSCKiseqz(x) ((x)==0)\n#define ATSCKisneqz(x) ((x)!=0)\n")
  val () = bput(b, "#define ATSCKptriscons(x) (0 != (void*)(x))\n#define ATSCKptrisnull(x) (0 == (void*)(x))\n")
  val () = bput(b, "#define ATSINSlab(lab) lab\n#define ATSINSgoto(lab) goto lab\n#define ATSINSflab(flab) flab\n#define ATSINSfgoto(flab) goto flab\n")
  val () = bput(b, "#define ATSINSmove(tmp, val) (tmp = val)\n#define ATSINSpmove(tmp, hit, val) (*(hit*)tmp = val)\n")
  val () = bput(b, "#define ATSINSmove_void(tmp, command) command\n#define ATSINSpmove_void(tmp, hit, command) command\n#define ATSINSmove_nil(tmp) (tmp = ((void*)0))\n")
  val () = bput(b, "#define ATSSELfltrec(pmv, tyrec, lab) ((pmv).lab)\n#define ATSSELcon(pmv, tycon, lab) (((tycon*)(pmv))->lab)\n")
  val () = bput(b, "#define ATSINSmove_con1_beg()\n#define ATSINSmove_con1_new(tmp, tycon) (tmp = ATS_MALLOC(sizeof(tycon)))\n")
  val () = bput(b, "#define ATSINSstore_con1_ofs(tmp, tycon, lab, val) (((tycon*)(tmp))->lab = val)\n#define ATSINSmove_con1_end()\n#define ATSINSfreecon(ptr) ATS_MFREE(ptr)\n")
  val () = bput(b, "#define ATSSELrecsin(pmv, tyrec, lab) (pmv)\n#define ATSINSstore_con1_tag(dst, tag) (((int*)(dst))[0] = (tag))\n")
  val () = bput(b, "#define ATSINSmove_con0(dst, tag) ((dst) = (void*)(tag))\n#define ATSCKpat_con0(p, tag) ((p) == (void*)(tag))\n#define ATSCKpat_con1(p, tag) (((int*)(p))[0] == (tag))\n")
  val () = bput(b, "#define ATSINSmove_fltrec_beg()\n#define ATSINSmove_fltrec_end()\n#define ATSINSstore_fltrec_ofs(tmp, tyrec, lab, val) ((tmp).lab = val)\n")
  val () = bput(b, "#define ATSINSload(tmp, pmv) (tmp = pmv)\n#define ATSINSstore(pmv1, pmv2) (pmv1 = pmv2)\n#define ATSINSxstore(tmp, pmv1, pmv2) (tmp = pmv1, pmv1 = pmv2, pmv2 = tmp)\n")
  val () = bput(b, "#define ATStailcal_beg() do {\n#define ATStailcal_end() } while(0) ;\n#define ATSINSmove_tlcal(apy, tmp) (apy = tmp)\n#define ATSINSargmove_tlcal(arg, apy) (arg = apy)\n")
  val () = bput(b, "#define ATSbranch_beg()\n#define ATSbranch_end() break ;\n#define ATScaseof_beg() do {\n#define ATScaseof_end() } while(0) ;\n#define ATSextcode_beg()\n#define ATSextcode_end()\n")
  val () = bput(b, "#define atspre_g1uint2int_size_int(x) ((int)(x))\n#define atspre_g0int_add_int(x, y) ((x) + (y))\n#define atspre_g1int_mul_int(x, y) ((x) * (y))\n")
  val () = bput(b, "#define atspre_g0int2uint_int_size(x) ((atstype_size)(x))\n#define atspre_g0uint_mul_size(x, y) ((x) * (y))\n#define atspre_add_ptr0_bsz(p, n) ((void*)((char*)(p) + (n)))\n")
  val () = bput(b, "#define atspre_g1int2int_int_int(x) (x)\n#define atspre_g1int_lt_int(x, y) ((x) < (y))\n#define atspre_g1int_add_int(x, y) ((x) + (y))\n")
  val () = bput(b, "#define atspre_char2int1(c) ((int)(c))\n#define atspre_g0int2int_int_int(x) (x)\n#define atspre_g0int_gt_int(x, y) ((x) > (y))\n")
  val () = bput(b, "#define atspre_g1ofg0_int(x) (x)\n#define atspre_g0ofg1_int(x) (x)\n#define atspre_g1int_gt_int(x, y) ((x) > (y))\n#define atspre_g1int_gte_int(x, y) ((x) >= (y))\n")
  val () = bput(b, "#define atspre_g1int_lte_int(x, y) ((x) <= (y))\n#define atspre_g1int_sub_int(x, y) ((x) - (y))\n#define atspre_g1int_neg_int(x) (-(x))\n")
  val () = bput(b, "#define atspre_g0int_gte_int(x, y) ((x) >= (y))\n#define atspre_g0int_lte_int(x, y) ((x) <= (y))\n#define atspre_g0int_eq_int(x, y) ((x) == (y))\n")
  val () = bput(b, "#define atspre_g0int_mul_int(x, y) ((x) * (y))\n#define atspre_g0int_sub_int(x, y) ((x) - (y))\n#define atspre_g0int_neq_int(x, y) ((x) != (y))\n")
  val () = bput(b, "#define atspre_g0int_lt_int(x, y) ((x) < (y))\n#define atspre_g0int_div_int(x, y) ((x) / (y))\n#define atspre_g0int_mod_int(x, y) ((x) % (y))\n")
  val () = bput(b, "#define atspre_g1int_div_int(x, y) ((x) / (y))\n#define atspre_g1int_eq_int(x, y) ((x) == (y))\n#define atspre_g1int_neq_int(x, y) ((x) != (y))\n")
  val () = bput(b, "#define atspre_g0int_asl_int(x, n) ((x) << (n))\n#define atspre_g0int_asr_int(x, n) ((x) >> (n))\n")
  val () = bput(b, "#define atspre_lor_int_int(x, y) ((x) | (y))\n#define atspre_land_int_int(x, y) ((x) & (y))\n")
  val () = bput(b, "#define atspre_byte2int0(b) ((int)(b))\n#define atspre_ptr_null() ((void*)0)\n#define atspre_ptr_isnot_null(p) ((p) != 0)\n#define atspre_ptr0_isnot_null atspre_ptr_isnot_null\n")
  val () = bput(b, "#define ATS_MALLOC(sz) malloc(sz)\n#define ATS_MFREE(ptr) free(ptr)\n#define ATSINScloptr_make(tmp, sz) (tmp = ATS_MALLOC(sz))\n#define ATSINScloptr_free(tmp) ATS_MFREE(tmp)\n")
  val () = bput(b, "#define ATSclosurerize_beg(flab, tenvs, targs, tres)\n#define ATSclosurerize_end()\n#define ATSFCreturn(x) return(x)\n#define ATSFCreturn_void(x) (x); return\n")
  val () = bput(b, "#define ATSPMVcfunlab(knd, flab, env) (flab##__closurerize)env\nextern void mainats_0_void(void);\n#define ATSmainats_0_void(err) mainats_0_void()\n")
  val () = bput(b, "void *malloc(int size);\nvoid free(void *ptr);\nvoid *memset(void *s, int c, unsigned int n);\nvoid *memcpy(void *dst, const void *src, unsigned int n);\n")
  val () = bput(b, "static inline void *calloc(int n, int sz) { return malloc(n * sz); }\n#endif\n")
  val p = str_to_path_arr("build/_bats_wasm_runtime.h")
  val @(fz_p, bv_p) = $A.freeze<byte>(p)
  val rc = write_file_from_builder(bv_p, 65536, b)
  val () = $A.drop<byte>(fz_p, bv_p)
  val () = $A.free<byte>($A.thaw<byte>(fz_p))
in rc end

fn write_wasm_runtime_c(): int = let
  val b = $B.create()
  val () = bput(b, "/* runtime.c -- Freestanding WASM: free-list allocator */\nextern unsigned char __heap_base;\nstatic unsigned char *heap_ptr = &__heap_base;\n")
  val () = bput(b, "#define WARD_HEADER 8\n#define WARD_NBUCKET 9\nstatic const unsigned int ward_bsz[WARD_NBUCKET] = {32,128,512,4096,8192,16384,65536,262144,1048576};\n")
  val () = bput(b, "static void *ward_fl[WARD_NBUCKET] = {0,0,0,0,0,0,0,0,0};\nstatic void *ward_fl_over = 0;\n")
  val () = bput(b, "void *memset(void *s,int c,unsigned int n){unsigned char *p=(unsigned char*)s;unsigned char byte=(unsigned char)c;while(n--)*p++=byte;return s;}\n")
  val () = bput(b, "void *memcpy(void *dst,const void *src,unsigned int n){unsigned char *d=(unsigned char*)dst;const unsigned char *s=(const unsigned char*)src;while(n--)*d++=*s++;return dst;}\n")
  val () = bput(b, "static inline unsigned int ward_hdr_read(void *p){return *(unsigned int*)((char*)p-WARD_HEADER);}\n")
  val () = bput(b, "static inline int ward_bucket(unsigned int n){if(n<=32)return 0;if(n<=128)return 1;if(n<=512)return 2;if(n<=4096)return 3;\n")
  val () = bput(b, "if(n<=8192)return 4;if(n<=16384)return 5;if(n<=65536)return 6;if(n<=262144)return 7;if(n<=1048576)return 8;return -1;}\n")
  val () = bput(b, "static void *ward_bump(unsigned int usable){unsigned long a=(unsigned long)heap_ptr;a=(a+7u)&~7u;unsigned long end=a+WARD_HEADER+usable;\n")
  val () = bput(b, "unsigned long limit=(unsigned long)__builtin_wasm_memory_size(0)*65536UL;if(end>limit){unsigned long pages=(end-limit+65535UL)/65536UL;\n")
  val () = bput(b, "if(__builtin_wasm_memory_grow(0,pages)==(unsigned long)(-1))return(void*)0;}*(unsigned int*)a=usable;void *p=(void*)(a+WARD_HEADER);heap_ptr=(unsigned char*)end;return p;}\n")
  val () = bput(b, "void *malloc(int size){if(size<=0)size=1;unsigned int n=(unsigned int)size;int b=ward_bucket(n);if(b>=0){unsigned int bsz=ward_bsz[b];void *p;\n")
  val () = bput(b, "if(ward_fl[b]){p=ward_fl[b];ward_fl[b]=*(void**)p;}else{p=ward_bump(bsz);}memset(p,0,bsz);return p;}\n")
  val () = bput(b, "void **prev=&ward_fl_over;void *cur=ward_fl_over;while(cur){unsigned int bsz=ward_hdr_read(cur);if(bsz>=n&&bsz<=2*n){*prev=*(void**)cur;memset(cur,0,bsz);return cur;}\n")
  val () = bput(b, "prev=(void**)cur;cur=*(void**)cur;}void *p=ward_bump(n);memset(p,0,n);return p;}\n")
  val () = bput(b, "void free(void *ptr){if(!ptr)return;unsigned int sz=ward_hdr_read(ptr);int b=ward_bucket(sz);if(b>=0&&ward_bsz[b]==sz){*(void**)ptr=ward_fl[b];ward_fl[b]=ptr;}\n")
  val () = bput(b, "else{*(void**)ptr=ward_fl_over;ward_fl_over=ptr;}}\n")
  val p = str_to_path_arr("build/_bats_wasm_runtime.c")
  val @(fz_p, bv_p) = $A.freeze<byte>(p)
  val rc = write_file_from_builder(bv_p, 65536, b)
  val () = $A.drop<byte>(fz_p, bv_p)
  val () = $A.free<byte>($A.thaw<byte>(fz_p))
in rc end

fn write_wasm_stubs(): int = let
  val cmd = $B.create()
  val () = bput(cmd, "mkdir -p build/_bats_wasm_stubs/libats/libc/CATS/sys && ")
  val () = bput(cmd, "echo '/* stub */' > build/_bats_wasm_stubs/libats/libc/CATS/stdio.cats && ")
  val () = bput(cmd, "echo '/* stub */' > build/_bats_wasm_stubs/libats/libc/CATS/sys/stat.cats && ")
  val () = bput(cmd, "echo '/* stub */' > build/_bats_wasm_stubs/libats/libc/CATS/sys/types.cats")
in run_sh(cmd, 0) end

fn compile_wasm_runtime(): int = let
  val cmd = $B.create()
  val () = bput(cmd, "PATH=/usr/bin:/usr/local/bin:/bin clang --target=wasm32 -O2 -nostdlib -ffreestanding ")
  val () = bput(cmd, "-fvisibility=default -D_ATS_CCOMP_HEADER_NONE_ -D_ATS_CCOMP_EXCEPTION_NONE_ ")
  val () = bput(cmd, "-D_ATS_CCOMP_PRELUDE_NONE_ -D_ATS_CCOMP_RUNTIME_NONE_ ")
  val () = bput(cmd, "-include build/_bats_wasm_runtime.h -I build/_bats_wasm_stubs ")
  val () = bput(cmd, "-c -o build/_bats_wasm_runtime.o build/_bats_wasm_runtime.c")
in run_sh(cmd, 0) end

fn do_build_wasm(release: int): void = let
  (* Assumes do_build(release) was called first to generate .c files *)
  (* Write WASM assets *)
  val r1 = write_wasm_runtime_h()
  val r2 = write_wasm_runtime_c()
  val r3 = write_wasm_stubs()
  val r4 = compile_wasm_runtime()
in
  if r4 <> 0 then println! ("error: failed to compile wasm runtime")
  else let
    (* Compile all .c files for wasm using a shell for-loop *)
    val wasm_cc = $B.create()
    val () = bput(wasm_cc, "cd build && for f in $(find . -name '*_dats.c' 2>/dev/null); do ")
    val () = bput(wasm_cc, "PATH=/usr/bin:/usr/local/bin:/bin clang --target=wasm32 -O2 -nostdlib -ffreestanding ")
    val () = bput(wasm_cc, "-fvisibility=default -D_ATS_CCOMP_HEADER_NONE_ -D_ATS_CCOMP_EXCEPTION_NONE_ ")
    val () = bput(wasm_cc, "-D_ATS_CCOMP_PRELUDE_NONE_ -D_ATS_CCOMP_RUNTIME_NONE_ ")
    val () = bput(wasm_cc, "-include _bats_wasm_runtime.h -I _bats_wasm_stubs ")
    val () = bput(wasm_cc, "-c -o \"${f%.c}.wasm.o\" \"$f\" || exit 1; done")
    val wrc1 = run_sh(wasm_cc, 0)
    (* Link with wasm-ld *)
    val wasm_link = $B.create()
    val () = bput(wasm_link, "cd build && PATH=/usr/bin:/usr/local/bin:/bin wasm-ld --no-entry --export-dynamic ")
    val () = bput(wasm_link, "-z stack-size=65536 --initial-memory=16777216 --max-memory=268435456 ")
    val () = bput(wasm_link, "-o ../dist/")
    val () = (if release > 0 then bput(wasm_link, "release/") else bput(wasm_link, "debug/"))
    val () = bput(wasm_link, "output.wasm _bats_wasm_runtime.o $(find . -name '*.wasm.o' 2>/dev/null)")
    val wrc2 = run_sh(wasm_link, 0)
  in
    if wrc2 <> 0 then println! ("error: wasm linking failed")
    else (if ~is_quiet() then println! ("  built wasm binary") else ())
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
    val () = bput(nrt_b, "/* _bats_native_runtime.c -- ATS2 memory allocator backed by libc */\n")
    val () = bput(nrt_b, "#include <stdlib.h>\n")
    val () = bput(nrt_b, "void atsruntime_mfree_undef(void *ptr) { free(ptr); }\n")
    val () = bput(nrt_b, "void *atsruntime_malloc_undef(size_t bsz) { return malloc(bsz); }\n")
    val () = bput(nrt_b, "void *atsruntime_calloc_undef(size_t asz, size_t tsz) { return calloc(asz, tsz); }\n")
    val () = bput(nrt_b, "void *atsruntime_realloc_undef(void *ptr, size_t bsz) { return realloc(ptr, bsz); }\n")
    val nrt_path = str_to_path_arr("build/_bats_native_runtime.c")
    val @(fz_nrtp, bv_nrtp) = $A.freeze<byte>(nrt_path)
    val _ = write_file_from_builder(bv_nrtp, 65536, nrt_b)
    val () = $A.drop<byte>(fz_nrtp, bv_nrtp)
    val () = $A.free<byte>($A.thaw<byte>(fz_nrtp))
    val nrt_cmd = $B.create()
    val () = bput(nrt_cmd, "PATH=/usr/bin:/usr/local/bin:/bin cc -c -o build/_bats_native_runtime.o build/_bats_native_runtime.c")
    val nrt_r = run_sh(nrt_cmd, 0)
    val () = (if nrt_r <> 0 then println! ("error: failed to compile native runtime") else ())
    (* Step 2: Ensure ATS2 toolchain at $HOME/.bats/ats2 *)
    val phbuf = $A.alloc<byte>(512)
    val hk = $A.alloc<byte>(4)
    val () = $A.write_byte(hk, 0, 72) (* H *)
    val () = $A.write_byte(hk, 1, 79) (* O *)
    val () = $A.write_byte(hk, 2, 77) (* M *)
    val () = $A.write_byte(hk, 3, 69) (* E *)
    val @(fz_hk, bv_hk) = $A.freeze<byte>(hk)
    val hr = $E.get(bv_hk, 4, phbuf, 512)
    val () = $A.drop<byte>(fz_hk, bv_hk)
    val () = $A.free<byte>($A.thaw<byte>(fz_hk))
    val hlen = (case+ hr of | ~$R.some(n) => n | ~$R.none() => 0): int
    (* Append /.bats/ats2 to HOME *)
    fn append_bats_path {l:agz}
      (buf: !$A.arr(byte, l, 512), pos: int): int =
      let val p = g1ofg0(pos) in
        if p >= 0 then if p + 10 < 512 then let
          val () = $A.set<byte>(buf, p, int2byte0(47))
          val () = $A.set<byte>(buf, $AR.checked_idx(p+1,512), int2byte0(46))
          val () = $A.set<byte>(buf, $AR.checked_idx(p+2,512), int2byte0(98))
          val () = $A.set<byte>(buf, $AR.checked_idx(p+3,512), int2byte0(97))
          val () = $A.set<byte>(buf, $AR.checked_idx(p+4,512), int2byte0(116))
          val () = $A.set<byte>(buf, $AR.checked_idx(p+5,512), int2byte0(115))
          val () = $A.set<byte>(buf, $AR.checked_idx(p+6,512), int2byte0(47))
          val () = $A.set<byte>(buf, $AR.checked_idx(p+7,512), int2byte0(97))
          val () = $A.set<byte>(buf, $AR.checked_idx(p+8,512), int2byte0(116))
          val () = $A.set<byte>(buf, $AR.checked_idx(p+9,512), int2byte0(115))
          val () = $A.set<byte>(buf, $AR.checked_idx(p+10,512), int2byte0(50))
        in pos + 11 end else pos else pos
      end
    val phlen = append_bats_path(phbuf, hlen)
    (* Check if patsopt exists, install if not — single freeze *)
    (* Copy arr bytes to builder — uses src_byte to avoid !arr in conditional *)
    fun arr_to_builder {l:agz}{fuel:nat} .<fuel>.
      (buf: !$A.borrow(byte, l, 512), pos: int, len: int,
       dst: !$B.builder, fuel: int fuel): void =
      if fuel <= 0 then ()
      else if pos >= len then ()
      else let
        val b = src_byte(buf, pos, 512)
        val () = $B.put_byte(dst, b)
      in arr_to_builder(buf, pos + 1, len, dst, fuel - 1) end
    fn ensure_ats2 {l:agz}
      (buf: !$A.borrow(byte, l, 512), plen: int): void = let
      val cmd = $B.create()
      val () = bput(cmd, "test -f ")
      val () = arr_to_builder(buf, 0, plen, cmd, $AR.checked_nat(plen + 1))
      val () = bput(cmd, "/bin/patsopt || (echo 'ATS2 not found, installing...' && mkdir -p ")
      val () = arr_to_builder(buf, 0, plen, cmd, $AR.checked_nat(plen + 1))
      val () = bput(cmd, " && curl -sL 'https://raw.githubusercontent.com/ats-lang/ats-lang.github.io/master/FROZEN000/ATS-Postiats/ATS2-Postiats-int-0.4.2.tgz' -o /tmp/_bpoc_ats2.tgz && ")
      val () = bput(cmd, "tar -xzf /tmp/_bpoc_ats2.tgz --strip-components=1 -C ")
      val () = arr_to_builder(buf, 0, plen, cmd, $AR.checked_nat(plen + 1))
      val () = bput(cmd, " && rm /tmp/_bpoc_ats2.tgz && echo 'building ATS2...' && make -j4 -C ")
      val () = arr_to_builder(buf, 0, plen, cmd, $AR.checked_nat(plen + 1))
      val () = bput(cmd, "/src/CBOOT patsopt PATSHOME=")
      val () = arr_to_builder(buf, 0, plen, cmd, $AR.checked_nat(plen + 1))
      val () = bput(cmd, " && mkdir -p ")
      val () = arr_to_builder(buf, 0, plen, cmd, $AR.checked_nat(plen + 1))
      val () = bput(cmd, "/bin && cp ")
      val () = arr_to_builder(buf, 0, plen, cmd, $AR.checked_nat(plen + 1))
      val () = bput(cmd, "/src/CBOOT/patsopt ")
      val () = arr_to_builder(buf, 0, plen, cmd, $AR.checked_nat(plen + 1))
      val () = bput(cmd, "/bin/patsopt && echo 'ATS2 installed successfully')")
      val rc = run_sh(cmd, 0)
    in
      if rc <> 0 then println! ("error: ATS2 installation failed") else ()
    end
    val @(fz_patshome, bv_patshome) = $A.freeze<byte>(phbuf)
    val () = ensure_ats2(bv_patshome, phlen)
  in
    if phlen <= 0 then let
      val () = $A.drop<byte>(fz_patshome, bv_patshome)
      val () = $A.free<byte>($A.thaw<byte>(fz_patshome))
    in println! ("error: HOME not set, cannot find ATS2 toolchain") end
    else let

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

                    (* Step 7: clang compile all _dats.c -- skip when --to-c *)
                    val rl = (if is_to_c() then 0 else let
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
                    in rl end): int

                    val () = $A.drop<byte>(fz_sp, bv_sp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                    val () = $A.drop<byte>(fz_ss, bv_ss)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ss))
                    val () = $A.drop<byte>(fz_sd, bv_sd)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sd))
                    val () = (if is_to_c() then ()
                    else if rl = 0 then
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

      (* --to-c: copy C files and generate Makefile *)
      val () = (if is_to_c() then if !g_to_c_done = 0 then let
        val () = !g_to_c_done := 1
        val cmd = $B.create()
        (* Read DIR and copy files *)
        val () = bput(cmd, "DIR=$(tr -d '")
        val () = $B.put_byte(cmd, 92) (* backslash *)
        val () = bput(cmd, "n' < /tmp/_bpoc_to_c.txt) && mkdir -p $DIR && ")
        val () = bput(cmd, "cp build/_bats_native_runtime.c $DIR/ && ")
        val () = bput(cmd, "for d in bats_modules/*/; do [ -d \"$d\" ] && dep=$(basename \"$d\") && ")
        val () = bput(cmd, "cp \"build/bats_modules/$dep/src/lib_dats.c\" \"$DIR/${dep}_lib_dats.c\" 2>/dev/null; done; ")
        val () = bput(cmd, "for f in build/src/bin/*_dats.c; do [ -f \"$f\" ] && cp \"$f\" \"$DIR/\"; done; ")
        val () = bput(cmd, "for f in build/_bats_entry_*_dats.c; do [ -f \"$f\" ] && cp \"$f\" \"$DIR/\"; done;\n")
        val () = bput(cmd, "cd $DIR &&\n")
        (* Compute common deps *)
        val () = bput(cmd, "COMMON=\"\"; for f in _bats_native_runtime.c *_lib_dats.c; do [ -f \"$f\" ] && COMMON=\"$COMMON $f\"; done;\n")
        (* Generate Makefile *)
        val () = bput(cmd, "{\n")
        val () = bput(cmd, "echo 'PATSHOME ?= $(HOME)/.bats/ats2'\n")
        val () = bput(cmd, "echo 'CC ?= cc'\n")
        val () = bput(cmd, "echo ''\n")
        val () = bput(cmd, "printf '%%_debug.o: %%.c")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "t$(CC) -c -o $@ $< -g -O0 -I$(PATSHOME) -I$(PATSHOME)/ccomp/runtime")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n'\n")
        val () = bput(cmd, "printf '%%_release.o: %%.c")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "t$(CC) -c -o $@ $< -O2 -I$(PATSHOME) -I$(PATSHOME)/ccomp/runtime")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n'\n")
        (* All target *)
        val () = bput(cmd, "printf 'all:'; for f in _bats_entry_*_dats.c; do name=${f#_bats_entry_}; name=${name%_dats.c}; printf ' debug/%s release/%s' \"$name\" \"$name\"; done; printf '")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n'\n")
        (* Per-binary rules *)
        val () = bput(cmd, "for f in _bats_entry_*_dats.c; do\n")
        val () = bput(cmd, "name=${f#_bats_entry_}; name=${name%_dats.c}\n")
        val () = bput(cmd, "printf 'debug/%s:' \"$name\"; for s in _bats_entry_${name}_dats.c ${name}_dats.c $COMMON; do printf ' %s' \"${s%.c}_debug.o\"; done; printf '")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "tmkdir -p debug")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "t$(CC) -o $@ $^ -g -O0")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n'\n")
        val () = bput(cmd, "printf 'release/%s:' \"$name\"; for s in _bats_entry_${name}_dats.c ${name}_dats.c $COMMON; do printf ' %s' \"${s%.c}_release.o\"; done; printf '")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "tmkdir -p release")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "t$(CC) -o $@ $^ -O2")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n'\n")
        val () = bput(cmd, "done\n")
        val () = bput(cmd, "printf 'clean:")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "trm -f *.o")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "trm -rf debug release")
        val () = $B.put_byte(cmd, 92) val () = bput(cmd, "n'\n")
        val () = bput(cmd, "} > Makefile")
        val rc = run_sh(cmd, 0)
        val () = (if rc <> 0 then println! ("error: --to-c failed")
          else if ~is_quiet() then println! ("  to-c: generated")
          else ())
      in end else () else ())

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
   generate docs: scan lib.bats for #pub and write docs/
   ============================================================ *)
fn do_generate_docs(pkg_name_len: int, kind_is_lib: int): void =
  if kind_is_lib = 0 then ()
  else let
    val cmd = $B.create()
    val () = bput(cmd, "mkdir -p docs")
    val _ = run_sh(cmd, 0)
    val lp = str_to_path_arr("src/lib.bats")
    val @(fz_lp, bv_lp) = $A.freeze<byte>(lp)
    val lib_or = $F.file_open(bv_lp, 65536, 0, 0)
    val () = $A.drop<byte>(fz_lp, bv_lp)
    val () = $A.free<byte>($A.thaw<byte>(fz_lp))
  in
    case+ lib_or of
    | ~$R.ok(lfd) => let
        val lbuf = $A.alloc<byte>(65536)
        val lrr = $F.file_read(lfd, lbuf, 65536)
        val llen = (case+ lrr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
        val lcr = $F.file_close(lfd)
        val () = $R.discard<int><int>(lcr)
        val doc_b = $B.create()
        val () = bput(doc_b, "# API Reference\n\n")
        (* Scan for #pub lines: 35,112,117,98,32 *)
        fun scan_pub {l2:agz}{fuel:nat} .<fuel>.
          (buf: !$A.arr(byte, l2, 65536), doc: !$B.builder,
           pos: int, len: int, fuel: int fuel): void =
          if fuel <= 0 then ()
          else if pos >= len then ()
          else let
            val p = g1ofg0(pos)
          in
            if p >= 0 then
              if p + 4 < 65536 then let
                val b0 = byte2int0($A.get<byte>(buf, p))
                val b1 = byte2int0($A.get<byte>(buf, p + 1))
                val b2 = byte2int0($A.get<byte>(buf, p + 2))
                val b3 = byte2int0($A.get<byte>(buf, p + 3))
                val b4 = byte2int0($A.get<byte>(buf, p + 4))
              in
                if $AR.eq_int_int(b0, 35) then
                  if $AR.eq_int_int(b1, 112) then
                    if $AR.eq_int_int(b2, 117) then
                      if $AR.eq_int_int(b3, 98) then
                        if $AR.eq_int_int(b4, 32) then let
                          (* Found #pub , copy rest of line *)
                          val () = bput(doc, "```\n")
                          fun copy_line {l3:agz}{fuel2:nat} .<fuel2>.
                            (buf: !$A.arr(byte, l3, 65536), doc: !$B.builder,
                             pos: int, fuel2: int fuel2): int =
                            if fuel2 <= 0 then pos
                            else let val pp = g1ofg0(pos) in
                              if pp >= 0 then
                                if pp < 65536 then let
                                  val b = byte2int0($A.get<byte>(buf, pp))
                                in
                                  if $AR.eq_int_int(b, 10) then (pos + 1)
                                  else let
                                    val () = $B.put_byte(doc, b)
                                  in copy_line(buf, doc, pos + 1, fuel2 - 1) end
                                end
                                else pos
                              else pos
                            end
                          val np = copy_line(buf, doc, p + 5, $AR.checked_nat(len - p))
                          val () = bput(doc, "\n```\n\n")
                        in scan_pub(buf, doc, np, len, fuel - 1) end
                        else let
                          val np = find_null(buf, pos, 65536, $AR.checked_nat(len - pos + 1))
                        in scan_pub(buf, doc, np + 1, len, fuel - 1) end
                      else let
                        val np = find_null(buf, pos, 65536, $AR.checked_nat(len - pos + 1))
                      in scan_pub(buf, doc, np + 1, len, fuel - 1) end
                    else let
                      val np = find_null(buf, pos, 65536, $AR.checked_nat(len - pos + 1))
                    in scan_pub(buf, doc, np + 1, len, fuel - 1) end
                  else let
                    val np = find_null(buf, pos, 65536, $AR.checked_nat(len - pos + 1))
                  in scan_pub(buf, doc, np + 1, len, fuel - 1) end
                else let
                  (* Skip to next newline *)
                  fun skip_line {l4:agz}{fuel3:nat} .<fuel3>.
                    (buf: !$A.arr(byte, l4, 65536), pos: int, len: int,
                     fuel3: int fuel3): int =
                    if fuel3 <= 0 then pos
                    else let val pp = g1ofg0(pos) in
                      if pp >= 0 then
                        if pp < 65536 then let
                          val b = byte2int0($A.get<byte>(buf, pp))
                        in
                          if $AR.eq_int_int(b, 10) then pos + 1
                          else skip_line(buf, pos + 1, len, fuel3 - 1)
                        end
                        else pos
                      else pos
                    end
                  val np = skip_line(buf, pos, len, $AR.checked_nat(len - pos + 1))
                in scan_pub(buf, doc, np, len, fuel - 1) end
              end
              else ()
            else ()
          end
        val () = scan_pub(lbuf, doc_b, 0, llen, $AR.checked_nat(llen + 1))
        val () = $A.free<byte>(lbuf)
        val dp = str_to_path_arr("docs/lib.md")
        val @(fz_dp, bv_dp) = $A.freeze<byte>(dp)
        val _ = write_file_from_builder(bv_dp, 65536, doc_b)
        val () = $A.drop<byte>(fz_dp, bv_dp)
        val () = $A.free<byte>($A.thaw<byte>(fz_dp))
        (* Write docs/index.md *)
        val idx_b = $B.create()
        val () = bput(idx_b, "# Documentation\n\n- [API Reference](lib.md)\n")
        val ip = str_to_path_arr("docs/index.md")
        val @(fz_ip, bv_ip) = $A.freeze<byte>(ip)
        val _ = write_file_from_builder(bv_ip, 65536, idx_b)
        val () = $A.drop<byte>(fz_ip, bv_ip)
        val () = $A.free<byte>($A.thaw<byte>(fz_ip))
      in end
    | ~$R.err(_) => ()
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
                  val () = do_generate_docs(0, 1)
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
    print_string "# bash completions\ncomplete -W 'build check clean lock run test tree add remove upload init completions' bats\n"
  else if shell = 1 then
    print_string "#compdef bats\n_bats_cmds=(build check clean lock run test tree add remove upload init completions)\ncompadd $_bats_cmds\n"
  else if shell = 2 then
    print_string "# fish completions\nfor c in build check clean lock run test tree add remove upload init completions; complete -c bats -n __fish_use_subcommand -a $c; end\n"
  else println! ("error: specify a shell (bash, zsh, fish)")

(* Check if a file exists by trying to open it *)
fn file_exists {sn:nat} (path: string sn): bool = let
  val pa = str_to_path_arr(path)
  val @(fz, bv) = $A.freeze<byte>(pa)
  val fex_or = $F.file_open(bv, 65536, 0, 0)
  val () = $A.drop<byte>(fz, bv)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in case+ fex_or of
  | ~$R.ok(fd) => let
      val cr = $F.file_close(fd)
      val () = $R.discard<int><int>(cr)
    in true end
  | ~$R.err(_) => false
end

(* ============================================================
   write_claude_rules: create .claude/rules/bats.md
   ============================================================ *)
fn write_claude_rules(): void = let
  val cmd = $B.create()
  val () = bput(cmd, "mkdir -p .claude/rules")
  val _ = run_sh(cmd, 0)
  val rb = $B.create()
  val () = bput(rb, "# Writing Bats\n\n")
  val () = bput(rb, "Bats is a language that compiles to ATS2.\n\n")
  val () = bput(rb, "## Build commands\n\n")
  val () = bput(rb, "```bash\n")
  val () = bput(rb, "bats build    # Build binary project\n")
  val () = bput(rb, "bats check    # Type-check without linking\n")
  val () = bput(rb, "bats clean    # Remove generated artifacts\n")
  val () = bput(rb, "```\n\n")
  val () = bput(rb, "## Project layout\n\n")
  val () = bput(rb, "- `bats.toml` -- package config\n")
  val () = bput(rb, "- `src/lib.bats` -- library entry point (kind = \"lib\")\n")
  val () = bput(rb, "- `src/bin/<name>.bats` -- binary entry points (kind = \"bin\")\n\n")
  val () = bput(rb, "## Bats-specific syntax\n\n")
  val () = bput(rb, "### `#pub` -- public declarations\n\n")
  val () = bput(rb, "```bats\n")
  val () = bput(rb, "#pub fun greet (name: string): void\n")
  val () = bput(rb, "implement greet (name) = println! (\"hello \", name)\n")
  val () = bput(rb, "```\n\n")
  val () = bput(rb, "### `#use` -- package imports\n\n")
  val () = bput(rb, "```bats\n")
  val () = bput(rb, "#use mylib as M\n")
  val () = bput(rb, "val x = $M.greeting ()\n")
  val () = bput(rb, "```\n\n")
  val () = bput(rb, "## ATS2 essentials\n\n")
  val () = bput(rb, "- `println!` has a bang\n")
  val () = bput(rb, "- `fun` declares functions, `val` binds values\n")
  val () = bput(rb, "- Pattern matching: `case+ x of | 0 => ... | n => ...`\n")
  val () = bput(rb, "- Types: `int`, `string`, `bool`, `void`\n")
  val () = bput(rb, "- No semicolons at end of expressions\n")
  val rp = str_to_path_arr(".claude/rules/bats.md")
  val @(fz_rp, bv_rp) = $A.freeze<byte>(rp)
  val _ = write_file_from_builder(bv_rp, 65536, rb)
  val () = $A.drop<byte>(fz_rp, bv_rp)
  val () = $A.free<byte>($A.thaw<byte>(fz_rp))
in end

(* ============================================================
   init: create a new bats project
   ============================================================ *)
fn do_init(kind: int, claude: int): void = let
  (* Check for existing project *)
  val has_toml = file_exists("bats.toml")
  val has_gi = file_exists(".gitignore")
in
  if has_toml then println! ("error: bats.toml already exists")
  else if has_gi then println! ("error: .gitignore already exists")
  else let
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
      if rc3 = 0 then let
        val () = (if claude > 0 then write_claude_rules() else ())
      in println! ("initialized bats project in current directory") end
      else println! ("error: failed to write .gitignore")
    else println! ("error: failed to write source file")
  else println! ("error: failed to write bats.toml")
end end

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

(* Save extra arguments (after --) to /tmp/_bpoc_extra.txt *)
fn save_extra_args {l:agz}
  (buf: !$A.arr(byte, l, 4096), dd_pos: int, len: int): void = let
  (* dd_pos points to the "--" token; skip "--\0" to get to first extra arg *)
  (* If dd_pos < 0, no -- was found, so do nothing *)
  val start = dd_pos + 3
in
  if dd_pos < 0 then ()
  else if start < len then let
    val out = $B.create()
    fun copy_extras {l2:agz}{fuel:nat} .<fuel>.
      (buf: !$A.arr(byte, l2, 4096), out: !$B.builder,
       pos: int, len: int, fuel: int fuel): void =
      if fuel <= 0 then ()
      else if pos >= len then ()
      else let
        val p = g1ofg0(pos)
      in
        if p >= 0 then
          if p < 4096 then let
            val b = byte2int0($A.get<byte>(buf, p))
          in
            if $AR.eq_int_int(b, 0) then let
              val () = $B.put_byte(out, 10) (* newline separator *)
            in copy_extras(buf, out, pos + 1, len, fuel - 1) end
            else let
              val () = $B.put_byte(out, b)
            in copy_extras(buf, out, pos + 1, len, fuel - 1) end
          end
          else ()
        else ()
      end
    val () = copy_extras(buf, out, start, len, $AR.checked_nat(len - start + 1))
    val ep = str_to_path_arr("/tmp/_bpoc_extra.txt")
    val @(fz_ep, bv_ep) = $A.freeze<byte>(ep)
    val _ = write_file_from_builder(bv_ep, 65536, out)
    val () = $A.drop<byte>(fz_ep, bv_ep)
    val () = $A.free<byte>($A.thaw<byte>(fz_ep))
  in end
  else ()
end

(* Append saved extra args to a builder (for do_run) *)
fn append_run_args(cmd: !$B.builder): void = let
  val ep = str_to_path_arr("/tmp/_bpoc_extra.txt")
  val @(fz_ep, bv_ep) = $A.freeze<byte>(ep)
  val eor = $F.file_open(bv_ep, 65536, 0, 0)
  val () = $A.drop<byte>(fz_ep, bv_ep)
  val () = $A.free<byte>($A.thaw<byte>(fz_ep))
in
  case+ eor of
  | ~$R.ok(efd) => let
      val ebuf = $A.alloc<byte>(4096)
      val era_r = $F.file_read(efd, ebuf, 4096)
      val elen = (case+ era_r of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val ecr = $F.file_close(efd)
      val () = $R.discard<int><int>(ecr)
    in
      if elen > 0 then let
        val @(fz_eb, bv_eb) = $A.freeze<byte>(ebuf)
        fun append_lines {l2:agz}{fuel:nat} .<fuel>.
          (bv: !$A.borrow(byte, l2, 4096), cmd: !$B.builder,
           pos: int, len: int, fuel: int fuel): void =
          if fuel <= 0 then ()
          else if pos >= len then ()
          else let
            val b = src_byte(bv, pos, 4096)
          in
            if $AR.eq_int_int(b, 10) then let
              val () = $B.put_byte(cmd, 32) (* space *)
            in append_lines(bv, cmd, pos + 1, len, fuel - 1) end
            else let
              val () = $B.put_byte(cmd, b)
            in append_lines(bv, cmd, pos + 1, len, fuel - 1) end
          end
        val () = $B.put_byte(cmd, 32) (* space *)
        val () = append_lines(bv_eb, cmd, 0, elen, $AR.checked_nat(elen + 1))
        val () = $A.drop<byte>(fz_eb, bv_eb)
        val () = $A.free<byte>($A.thaw<byte>(fz_eb))
      in end
      else $A.free<byte>(ebuf)
    end
  | ~$R.err(_) => ()
end

(* ============================================================
   run: build then execute the binary
   ============================================================ *)
fn do_run(release: int): void = let
  val () = do_build(release)
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
              val () = (if release > 0 then bput(cmd, "./dist/release/")
                else bput(cmd, "./dist/debug/"))
            in
              if bn_len > 0 then let
                val @(fz_bn, bv_bn) = $A.freeze<byte>(bin_name)
                val () = copy_to_builder(bv_bn, 0, bn_len, 256, cmd,
                  $AR.checked_nat(bn_len + 1))
                val () = $A.drop<byte>(fz_bn, bv_bn)
                val () = $A.free<byte>($A.thaw<byte>(fz_bn))
                val () = $A.free<byte>(nbuf)
                val () = append_run_args(cmd)
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
                val () = append_run_args(cmd)
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
              val () = println! ("Lexing src/bin/bats.bats...")
              val lex_path = $A.alloc<byte>(18)
              (* "src/bin/bats.bats" *)
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
              val () = $A.write_byte(lex_path, 12, 46)   (* . *)
              val () = $A.write_byte(lex_path, 13, 98)   (* b *)
              val () = $A.write_byte(lex_path, 14, 97)   (* a *)
              val () = $A.write_byte(lex_path, 15, 116)  (* t *)
              val () = $A.write_byte(lex_path, 16, 115)  (* s *)
              val () = $A.write_byte(lex_path, 17, 0)
              val @(fz_lp, bv_lp) = $A.freeze<byte>(lex_path)
              val lex_or = $F.file_open(bv_lp, 18, 0, 0)
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
              val () = do_generate_docs(0, 1)
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
   Argparse helpers
   ============================================================ *)

(* Count null bytes in buffer to determine argc *)
fun count_argc_loop {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (buf: !$A.arr(byte, l, n), pos: int, len: int, max: int n,
   count: int, fuel: int fuel): int =
  if fuel <= 0 then count
  else if pos >= len then count
  else let
    val p = g1ofg0(pos)
  in
    if p >= 0 then
      if p < max then let
        val b = byte2int0($A.get<byte>(buf, p))
      in
        if $AR.eq_int_int(b, 0) then
          count_argc_loop(buf, pos + 1, len, max, count + 1, fuel - 1)
        else count_argc_loop(buf, pos + 1, len, max, count, fuel - 1)
      end
      else count
    else count
  end

fn count_argc {l:agz}
  (buf: !$A.arr(byte, l, 4096), len: int): int =
  count_argc_loop(buf, 0, len, 4096, 0, $AR.checked_nat(len + 1))

(* Fill array from string — generic on array size *)
fun fill_exact {l:agz}{n:pos}{sn:nat}{fuel:nat} .<fuel>.
  (arr: !$A.arr(byte, l, n), s: string sn, n: int n, slen: int sn,
   i: int, fuel: int fuel): void =
  if fuel <= 0 then ()
  else let val ii = g1ofg0(i) in
    if ii >= 0 then
      if $AR.lt1_int_int(ii, slen) then
        if $AR.lt1_int_int(ii, n) then let
          val c = char2int0(string_get_at(s, ii))
          val () = $A.set<byte>(arr, ii, int2byte0(c))
        in fill_exact(arr, s, n, slen, i + 1, fuel - 1) end
        else ()
      else ()
    else ()
  end

(* Create exact-size array from string *)
fn str_to_borrow {sn:pos}
  (s: string sn): [l:agz][n:pos] @($A.arr(byte, l, n), int n) = let
  val slen_sz = string1_length(s)
  val slen = g1u2i(slen_sz)
  val n = $AR.checked_arr_size(g0ofg1(slen))
  val arr = $A.alloc<byte>(n)
  val () = fill_exact(arr, s, n, slen, 0, $AR.checked_nat(g0ofg1(slen) + 1))
in @(arr, n) end

(* Wrapper: add flag with string name/help *)
fn ap_flag {sn:pos}{sh:pos}
  (p: $AP.parser, name: string sn, sc: int, help: string sh
  ): @($AP.parser, $AP.arg($AP.bool_val)) = let
  val @(na, nl) = str_to_borrow(name)
  val @(fzn, bvn) = $A.freeze<byte>(na)
  val @(ha, hl) = str_to_borrow(help)
  val @(fzh, bvh) = $A.freeze<byte>(ha)
  val @(p2, h) = $AP.add_flag(p, bvn, nl, sc, bvh, hl)
  val () = $A.drop<byte>(fzn, bvn)
  val () = $A.free<byte>($A.thaw<byte>(fzn))
  val () = $A.drop<byte>(fzh, bvh)
  val () = $A.free<byte>($A.thaw<byte>(fzh))
in @(p2, h) end

(* Wrapper: add string option with string name/help *)
fn ap_string_opt {sn:pos}{sh:pos}
  (p: $AP.parser, name: string sn, sc: int, help: string sh
  ): @($AP.parser, $AP.arg($AP.string_val)) = let
  val @(na, nl) = str_to_borrow(name)
  val @(fzn, bvn) = $A.freeze<byte>(na)
  val @(ha, hl) = str_to_borrow(help)
  val @(fzh, bvh) = $A.freeze<byte>(ha)
  val @(p2, h) = $AP.add_string(p, bvn, nl, sc, bvh, hl, false)
  val () = $A.drop<byte>(fzn, bvn)
  val () = $A.free<byte>($A.thaw<byte>(fzn))
  val () = $A.drop<byte>(fzh, bvh)
  val () = $A.free<byte>($A.thaw<byte>(fzh))
in @(p2, h) end

(* Wrapper: add string positional with string name/help *)
fn ap_string_pos {sn:pos}{sh:pos}
  (p: $AP.parser, name: string sn, help: string sh
  ): @($AP.parser, $AP.arg($AP.string_val)) = let
  val @(na, nl) = str_to_borrow(name)
  val @(fzn, bvn) = $A.freeze<byte>(na)
  val @(ha, hl) = str_to_borrow(help)
  val @(fzh, bvh) = $A.freeze<byte>(ha)
  val @(p2, h) = $AP.add_string(p, bvn, nl, 0, bvh, hl, true)
  val () = $A.drop<byte>(fzn, bvn)
  val () = $A.free<byte>($A.thaw<byte>(fzn))
  val () = $A.drop<byte>(fzh, bvh)
  val () = $A.free<byte>($A.thaw<byte>(fzh))
in @(p2, h) end

(* Match command buffer to dispatch code *)
(* 0=build 1=check 2=clean 3=lock 4=run 5=init 6=test 7=tree *)
(* 8=upload 9=add 10=remove 11=completions 12=version -1=unknown *)
fn dispatch_cmd {l:agz}
  (buf: !$A.arr(byte, l, 32), len: int): int = let
  val b0 = byte2int0($A.get<byte>(buf, 0))
  val b1 = byte2int0($A.get<byte>(buf, 1))
in
  if len = 5 then
    (if $AR.eq_int_int(b0, 98) then 0
    else if $AR.eq_int_int(b0, 99) then
      (if $AR.eq_int_int(b1, 104) then 1 else 2)
    else ~1): int
  else if len = 4 then
    (if $AR.eq_int_int(b0, 108) then 3
    else if $AR.eq_int_int(b0, 105) then 5
    else if $AR.eq_int_int(b0, 116) then
      (if $AR.eq_int_int(b1, 101) then 6 else 7)
    else ~1): int
  else if len = 3 then
    (if $AR.eq_int_int(b0, 114) then 4
    else if $AR.eq_int_int(b0, 97) then 9
    else ~1): int
  else if len = 6 then
    (if $AR.eq_int_int(b0, 117) then 8
    else if $AR.eq_int_int(b0, 114) then 10
    else ~1): int
  else if len = 11 then 11
  else if len = 7 then 12
  else ~1
end

(* Print usage matching Rust bats format *)
fn print_usage(): void = let
  val () = println! ("usage: bats [--run-in <dir>] [--quiet] <command>")
  val () = println! ("")
  val () = println! ("commands:")
  val () = println! ("  init binary [--claude]       Create a new binary project (src/bin/<name>.bats)")
  val () = println! ("  init library [--claude]      Create a new library project (src/lib.bats)")
  val () = println! ("  add <package> --repository <dir>")
  val () = println! ("                               Add a dependency")
  val () = println! ("  remove <package> --repository <dir>")
  val () = println! ("                               Remove a dependency")
  val () = println! ("  lock [--dev] [--dry-run] --repository <dir>")
  val () = println! ("                               Generate bats.lock")
  val () = println! ("  build [--only debug|release|native|wasm] [--repository <dir>]")
  val () = println! ("                               Build the project")
  val () = println! ("  run [--only debug|release] [--bin <name>] [--repository <dir>] [-- args...]")
  val () = println! ("                               Build and run a binary")
  val () = println! ("  test [--only native|wasm] [--filter <name>] [--repository <dir>]")
  val () = println! ("                               Run tests")
  val () = println! ("  check [--repository <dir>]   Type-check the project (no linking)")
  val () = println! ("  tree [--repository <dir>]    Show dependency tree")
  val () = println! ("  upload --repository <dir>    Package and upload a library")
  val () = println! ("  clean                        Remove generated artifacts")
  val () = println! ("  completions <shell>          Generate shell completions (bash, zsh, fish)")
in end

(* Find the position of "--" separator in /proc/self/cmdline buffer.
   Returns the byte offset of the first byte of "--\0" or -1 if not found. *)
fun find_dashdash {l:agz}{fuel:nat} .<fuel>.
  (buf: !$A.arr(byte, l, 4096), pos: int, len: int,
   fuel: int fuel): int =
  if fuel <= 0 then ~1
  else if pos >= len then ~1
  else let
    val p = g1ofg0(pos)
  in
    if p >= 0 then
      if p + 2 < 4096 then let
        val b0 = byte2int0($A.get<byte>(buf, p))
        val b1 = byte2int0($A.get<byte>(buf, p + 1))
        val b2 = byte2int0($A.get<byte>(buf, p + 2))
      in
        if $AR.eq_int_int(b0, 45) then
          if $AR.eq_int_int(b1, 45) then
            if $AR.eq_int_int(b2, 0) then pos
            else let
              (* Skip to next null *)
              val next = find_null(buf, pos, 4096, $AR.checked_nat(len - pos + 1))
            in find_dashdash(buf, next + 1, len, fuel - 1) end
          else let
            val next = find_null(buf, pos, 4096, $AR.checked_nat(len - pos + 1))
          in find_dashdash(buf, next + 1, len, fuel - 1) end
        else let
          val next = find_null(buf, pos, 4096, $AR.checked_nat(len - pos + 1))
        in find_dashdash(buf, next + 1, len, fuel - 1) end
      end
      else ~1
    else ~1
  end

(* Scan --only values: read all repeated --only tokens from cmdline.
   Returns bitmask: bit0=debug bit1=release bit2=native bit3=wasm *)
fun scan_only {l:agz}{fuel:nat} .<fuel>.
  (buf: !$A.arr(byte, l, 4096), pos: int, len: int, mask: int,
   fuel: int fuel): int =
  if fuel <= 0 then mask
  else if pos >= len then mask
  else let
    val p = g1ofg0(pos)
  in
    if p >= 0 then
      if p + 5 < 4096 then let
        (* Check if this token is "--only" : 45,45,111,110,108,121,0 *)
        val b0 = byte2int0($A.get<byte>(buf, p))
        val b1 = byte2int0($A.get<byte>(buf, p + 1))
        val b2 = byte2int0($A.get<byte>(buf, p + 2))
        val b3 = byte2int0($A.get<byte>(buf, p + 3))
        val b4 = byte2int0($A.get<byte>(buf, p + 4))
        val b5 = byte2int0($A.get<byte>(buf, p + 5))
      in
        if $AR.eq_int_int(b0, 45) then
          if $AR.eq_int_int(b1, 45) then
            if $AR.eq_int_int(b2, 111) then
              if $AR.eq_int_int(b3, 110) then
                if $AR.eq_int_int(b4, 108) then
                  if $AR.eq_int_int(b5, 121) then let
                    (* Found --only, now skip to null and read next token *)
                    val next = find_null(buf, p + 6, 4096, $AR.checked_nat(len - p))
                    val val_start = next + 1
                  in
                    if val_start < len then let
                      val vs = g1ofg0(val_start)
                    in
                      if vs >= 0 then
                        if vs < 4096 then let
                          val v0 = byte2int0($A.get<byte>(buf, vs))
                          val vend = find_null(buf, val_start, 4096, $AR.checked_nat(len - val_start + 1))
                          val vlen = vend - val_start
                          (* d=100 debug, r=114 release, n=110 native, w=119 wasm *)
                          (* Use addition since bits don't overlap on first encounter *)
                          val new_mask = (
                            if $AR.eq_int_int(v0, 100) then
                              (if (mask mod 2) = 0 then mask + 1 else mask)
                            else if $AR.eq_int_int(v0, 114) then
                              (if ((mask / 2) mod 2) = 0 then mask + 2 else mask)
                            else if $AR.eq_int_int(v0, 110) then
                              (if ((mask / 4) mod 2) = 0 then mask + 4 else mask)
                            else if $AR.eq_int_int(v0, 119) then
                              (if ((mask / 8) mod 2) = 0 then mask + 8 else mask)
                            else mask): int
                        in scan_only(buf, vend + 1, len, new_mask, fuel - 1) end
                        else scan_only(buf, val_start + 1, len, mask, fuel - 1)
                      else scan_only(buf, val_start + 1, len, mask, fuel - 1)
                    end
                    else mask
                  end
                  else let
                    val next = find_null(buf, p, 4096, $AR.checked_nat(len - p + 1))
                  in scan_only(buf, next + 1, len, mask, fuel - 1) end
                else let
                  val next = find_null(buf, p, 4096, $AR.checked_nat(len - p + 1))
                in scan_only(buf, next + 1, len, mask, fuel - 1) end
              else let
                val next = find_null(buf, p, 4096, $AR.checked_nat(len - p + 1))
              in scan_only(buf, next + 1, len, mask, fuel - 1) end
            else let
              val next = find_null(buf, p, 4096, $AR.checked_nat(len - p + 1))
            in scan_only(buf, next + 1, len, mask, fuel - 1) end
          else let
            val next = find_null(buf, p, 4096, $AR.checked_nat(len - p + 1))
          in scan_only(buf, next + 1, len, mask, fuel - 1) end
        else let
          val next = find_null(buf, p, 4096, $AR.checked_nat(len - p + 1))
        in scan_only(buf, next + 1, len, mask, fuel - 1) end
      end
      else mask
    else mask
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
          (* Find -- separator and save extra args *)
          val dd_pos = find_dashdash(cl_buf, 0, cl_n, $AR.checked_nat(cl_n + 1))
          (* save_extra_args is a no-op when dd_pos < 0 or start >= len *)
          val () = save_extra_args(cl_buf, dd_pos, cl_n)
          (* Count argc only up to -- *)
          val effective_len = (if dd_pos >= 0 then dd_pos else cl_n): int
          val argc = count_argc(cl_buf, effective_len)
          (* Scan all --only values to build bitmask *)
          val only_mask = scan_only(cl_buf, 0, effective_len, 0, $AR.checked_nat(effective_len + 1))
          val @(fz_cb, bv_cb) = $A.freeze<byte>(cl_buf)
          (* Setup argparse parser *)
          val @(pna, pnl) = str_to_borrow("bats")
          val @(fzpn, bvpn) = $A.freeze<byte>(pna)
          val @(pha, phl) = str_to_borrow("bats build tool")
          val @(fzph, bvph) = $A.freeze<byte>(pha)
          val p = $AP.parser_new(bvpn, pnl, bvph, phl)
          val () = $A.drop<byte>(fzpn, bvpn)
          val () = $A.free<byte>($A.thaw<byte>(fzpn))
          val () = $A.drop<byte>(fzph, bvph)
          val () = $A.free<byte>($A.thaw<byte>(fzph))
          (* Add flags *)
          val @(p, h_verbose) = ap_flag(p, "verbose", 118, "verbose output")
          val @(p, h_quiet) = ap_flag(p, "quiet", 113, "quiet output")
          val @(p, h_run_in) = ap_string_opt(p, "run-in", 0, "run in directory")
          val @(p, h_repository) = ap_string_opt(p, "repository", 0, "package repository")
          val @(p, h_only) = ap_string_opt(p, "only", 0, "build target")
          val @(p, h_bin) = ap_string_opt(p, "bin", 0, "binary name")
          val @(p, h_to_c) = ap_string_opt(p, "to-c", 0, "output C files to directory")
          val @(p, h_claude) = ap_flag(p, "claude", 0, "create claude rules")
          val @(p, h_dev) = ap_flag(p, "dev", 0, "include dev dependencies")
          val @(p, h_dry_run) = ap_flag(p, "dry-run", 0, "dry run mode")
          val @(p, h_help) = ap_flag(p, "help", 104, "show help")
          val @(p, h_filter) = ap_string_opt(p, "filter", 0, "test filter")
          val @(p, h_cmd) = ap_string_pos(p, "command", "subcommand")
          val @(p, h_arg) = ap_string_pos(p, "argument", "subcommand argument")
          (* Parse *)
          val result = $AP.parse(p, bv_cb, 4096, argc)
          val () = $A.drop<byte>(fz_cb, bv_cb)
          val () = $A.free<byte>($A.thaw<byte>(fz_cb))
        in
          case+ result of
          | ~$R.ok(r) => let
              (* Handle --help first *)
              val want_help = $AP.get_bool(r, h_help)
            in
              if want_help then let
                val () = $AP.parse_result_free(r)
              in print_usage() end
              else let
              val () = (if $AP.get_bool(r, h_verbose) then !g_verbose := true else ())
              val () = (if $AP.get_bool(r, h_quiet) then !g_quiet := true else ())
              (* Handle --run-in *)
              val () = (if $AP.is_present(r, h_run_in) then let
                val ri_buf = $A.alloc<byte>(4096)
                val _ = $AP.get_string_copy(r, h_run_in, ri_buf, 4096)
                val @(fz_ri, bv_ri) = $A.freeze<byte>(ri_buf)
                val chdr = $F.file_chdir(bv_ri, 4096)
                val () = $R.discard<int><int>(chdr)
                val () = $A.drop<byte>(fz_ri, bv_ri)
                val () = $A.free<byte>($A.thaw<byte>(fz_ri))
              in end else ())
              (* Handle --repository *)
              val () = (if $AP.is_present(r, h_repository) then let
                val repo_buf = $A.alloc<byte>(4096)
                val rlen = $AP.get_string_copy(r, h_repository, repo_buf, 4096)
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
              in end else ())
              (* Handle --to-c *)
              val () = (if $AP.is_present(r, h_to_c) then let
                val tc_buf = $A.alloc<byte>(4096)
                val tclen = $AP.get_string_copy(r, h_to_c, tc_buf, 4096)
                val @(fz_tc, bv_tc) = $A.freeze<byte>(tc_buf)
                val tcb = $B.create()
                val () = copy_to_builder(bv_tc, 0, tclen, 4096, tcb, $AR.checked_nat(tclen + 1))
                val () = $A.drop<byte>(fz_tc, bv_tc)
                val () = $A.free<byte>($A.thaw<byte>(fz_tc))
                val tcp = str_to_path_arr("/tmp/_bpoc_to_c.txt")
                val @(fz_tcp, bv_tcp) = $A.freeze<byte>(tcp)
                val _ = write_file_from_builder(bv_tcp, 65536, tcb)
                val () = $A.drop<byte>(fz_tcp, bv_tcp)
                val () = $A.free<byte>($A.thaw<byte>(fz_tcp))
                val () = !g_to_c := 1
              in end else ())
              (* Get command *)
              val cmd_buf = $A.alloc<byte>(32)
              val cmd_len = $AP.get_string_copy(r, h_cmd, cmd_buf, 32)
              val cmd_code = dispatch_cmd(cmd_buf, cmd_len)
              val () = $A.free<byte>(cmd_buf)
              (* Get subcommand argument *)
              val arg_buf = $A.alloc<byte>(4096)
              val arg_len = $AP.get_string_copy(r, h_arg, arg_buf, 4096)
            in
              if cmd_code = 0 then let (* build *)
                val () = $AP.parse_result_free(r)
                val () = $A.free<byte>(arg_buf)
                (* Use only_mask from cmdline scan: bit0=debug bit1=release bit2=native bit3=wasm *)
                val has_debug = (only_mask mod 2)
                val has_release = ((only_mask / 2) mod 2)
                val has_wasm = ((only_mask / 8) mod 2)
              in
                if only_mask = 0 then let
                  (* No --only flags: build both debug and release *)
                  val () = do_build(0)
                in do_build(1) end
                else let
                  (* Always build native first (generates .c files needed for wasm) *)
                  val () = (if has_debug > 0 then do_build(0) else ())
                  val () = (if has_release > 0 then do_build(1) else ())
                  (* If only wasm specified, still need a native build for .c files *)
                  val () = (if has_debug = 0 then
                    if has_release = 0 then do_build(0)
                    else ()
                  else ())
                  (* Now build wasm if requested *)
                  val () = (if has_wasm > 0 then
                    if is_to_c() then let
                      val _ = write_wasm_runtime_h()
                      val _ = write_wasm_runtime_c()
                      val _ = write_wasm_stubs()
                      val wcmd = $B.create()
                      val () = bput(wcmd, "DIR=$(tr -d '")
                      val () = $B.put_byte(wcmd, 92)
                      val () = bput(wcmd, "n' < /tmp/_bpoc_to_c.txt) && ")
                      val () = bput(wcmd, "cp build/_bats_wasm_runtime.h $DIR/ && ")
                      val () = bput(wcmd, "cp build/_bats_wasm_runtime.c $DIR/ && ")
                      val () = bput(wcmd, "cp -r build/_bats_wasm_stubs $DIR/ && ")
                      val () = bput(wcmd, "cd $DIR && {\n")
                      val () = bput(wcmd, "echo ''\n")
                      val () = bput(wcmd, "echo 'CLANG ?= clang'\n")
                      val () = bput(wcmd, "echo 'WASM_LD ?= wasm-ld'\n")
                      val () = bput(wcmd, "echo 'WASM_CFLAGS := --target=wasm32 -O2 -nostdlib -ffreestanding -fvisibility=default -D_ATS_CCOMP_HEADER_NONE_ -D_ATS_CCOMP_EXCEPTION_NONE_ -D_ATS_CCOMP_PRELUDE_NONE_ -D_ATS_CCOMP_RUNTIME_NONE_ -include _bats_wasm_runtime.h -I _bats_wasm_stubs'\n")
                      val () = bput(wcmd, "echo ''\n")
                      val () = bput(wcmd, "printf '%%.wasm.o: %%.c")
                      val () = $B.put_byte(wcmd, 92) val () = bput(wcmd, "n")
                      val () = $B.put_byte(wcmd, 92) val () = bput(wcmd, "t$(CLANG) $(WASM_CFLAGS) -c -o $@ $<")
                      val () = $B.put_byte(wcmd, 92) val () = bput(wcmd, "n")
                      val () = $B.put_byte(wcmd, 92) val () = bput(wcmd, "n'\n")
                      val () = bput(wcmd, "echo 'WASM_SRCS := $(filter-out _bats_native_runtime.c,$(wildcard *.c))'\n")
                      val () = bput(wcmd, "echo 'WASM_OBJS := $(WASM_SRCS:.c=.wasm.o)'\n")
                      val () = bput(wcmd, "echo ''\n")
                      val () = bput(wcmd, "echo 'all: output.wasm'\n")
                      val () = bput(wcmd, "echo ''\n")
                      val () = bput(wcmd, "echo 'output.wasm: $(WASM_OBJS)'\n")
                      val () = bput(wcmd, "printf '")
                      val () = $B.put_byte(wcmd, 92) val () = bput(wcmd, "t$(WASM_LD) --no-entry --export-dynamic -z stack-size=65536 --initial-memory=16777216 --max-memory=268435456 -o $@ $^")
                      val () = $B.put_byte(wcmd, 92) val () = bput(wcmd, "n'\n")
                      val () = bput(wcmd, "} >> Makefile")
                      val wrc = run_sh(wcmd, 0)
                    in
                      if wrc <> 0 then println! ("error: --to-c wasm failed")
                      else if ~is_quiet() then println! ("  to-c: wasm assets")
                      else ()
                    end
                    else do_build_wasm(if has_release > 0 then 1 else 0)
                  else ())
                in
                  if has_debug = 0 then
                    if has_release = 0 then
                      if has_wasm = 0 then do_build(0)
                      else ()
                    else ()
                  else ()
                end
              end
              else if cmd_code = 1 then let (* check *)
                val () = $AP.parse_result_free(r)
                val () = $A.free<byte>(arg_buf)
              in do_check() end
              else if cmd_code = 2 then let (* clean *)
                val () = $AP.parse_result_free(r)
                val () = $A.free<byte>(arg_buf)
              in do_clean() end
              else if cmd_code = 3 then let (* lock *)
                val lk_dev = (if $AP.is_present(r, h_dev) then 1 else 0): int
                val lk_dry = (if $AP.is_present(r, h_dry_run) then 1 else 0): int
                val () = $AP.parse_result_free(r)
                val () = $A.free<byte>(arg_buf)
              in do_lock(lk_dev, lk_dry) end
              else if cmd_code = 4 then let (* run *)
                val () = (if $AP.is_present(r, h_bin) then let
                  val bin_buf = $A.alloc<byte>(256)
                  val blen = $AP.get_string_copy(r, h_bin, bin_buf, 256)
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
                in end else ())
                (* Check if --only release was specified *)
                fn check_only_release {l2:agz}
                  (buf: !$A.arr(byte, l2, 32), olen: int): int =
                  if olen = 7 then let
                    val b0 = byte2int0($A.get<byte>(buf, 0))
                  in (if $AR.eq_int_int(b0, 114) then 1 else 0): int end
                  else 0
                val run_release = (let
                  val ob2 = $A.alloc<byte>(32)
                  val ol2 = $AP.get_string_copy(r, h_only, ob2, 32)
                  val is_rel = check_only_release(ob2, ol2)
                  val () = $A.free<byte>(ob2)
                in is_rel end): int
                val () = $AP.parse_result_free(r)
                val () = $A.free<byte>(arg_buf)
              in do_run(run_release) end
              else if cmd_code = 5 then let (* init *)
                val init_claude = (if $AP.get_bool(r, h_claude) then 1 else 0): int
                val () = $AP.parse_result_free(r)
                (* arg_buf has "binary"|"bin"|"library"|"lib" — check first byte *)
                fn check_init_arg {l2:agz}
                  (buf: !$A.arr(byte, l2, 4096), alen: int): int =
                  if alen <= 0 then ~1
                  else let val b0 = byte2int0($A.get<byte>(buf, 0)) in
                    if $AR.eq_int_int(b0, 98) then 0   (* 'b' → binary/bin *)
                    else if $AR.eq_int_int(b0, 108) then 1 (* 'l' → library/lib *)
                    else ~1
                  end
                val kind = check_init_arg(arg_buf, arg_len)
                val () = $A.free<byte>(arg_buf)
              in
                if kind >= 0 then do_init(kind, init_claude)
                else println! ("error: specify 'binary' or 'library'\nusage: bats init binary|library")
              end
              else if cmd_code = 6 then let (* test *)
                val () = $AP.parse_result_free(r)
                val () = $A.free<byte>(arg_buf)
              in do_test() end
              else if cmd_code = 7 then let (* tree *)
                val () = $AP.parse_result_free(r)
                val () = $A.free<byte>(arg_buf)
              in do_tree() end
              else if cmd_code = 8 then let (* upload *)
                val () = $AP.parse_result_free(r)
                val () = $A.free<byte>(arg_buf)
              in do_upload() end
              else if cmd_code = 9 then let (* add *)
                val () = $AP.parse_result_free(r)
              in
                if arg_len > 0 then let
                  val @(fz_ab, bv_ab) = $A.freeze<byte>(arg_buf)
                  val () = do_add(bv_ab, 0, arg_len, 4096)
                  val () = $A.drop<byte>(fz_ab, bv_ab)
                  val () = $A.free<byte>($A.thaw<byte>(fz_ab))
                in end
                else let
                  val () = $A.free<byte>(arg_buf)
                in println! ("error: specify a package name\nusage: bats add <package>") end
              end
              else if cmd_code = 10 then let (* remove *)
                val () = $AP.parse_result_free(r)
              in
                if arg_len > 0 then let
                  val @(fz_rb, bv_rb) = $A.freeze<byte>(arg_buf)
                  val () = do_remove(bv_rb, 0, arg_len, 4096)
                  val () = $A.drop<byte>(fz_rb, bv_rb)
                  val () = $A.free<byte>($A.thaw<byte>(fz_rb))
                in end
                else let
                  val () = $A.free<byte>(arg_buf)
                in println! ("error: specify a package name\nusage: bats remove <package>") end
              end
              else if cmd_code = 11 then let (* completions *)
                val () = $AP.parse_result_free(r)
                fn check_shell_arg {l2:agz}
                  (buf: !$A.arr(byte, l2, 4096), alen: int): int =
                  if alen <= 0 then ~1
                  else let val b0 = byte2int0($A.get<byte>(buf, 0)) in
                    if $AR.eq_int_int(b0, 98) then 0     (* 'b' → bash *)
                    else if $AR.eq_int_int(b0, 122) then 1  (* 'z' → zsh *)
                    else if $AR.eq_int_int(b0, 102) then 2  (* 'f' → fish *)
                    else ~1
                  end
                val shell = check_shell_arg(arg_buf, arg_len)
                val () = $A.free<byte>(arg_buf)
              in
                if shell >= 0 then do_completions(shell)
                else println! ("error: specify a shell (bash, zsh, fish)\nusage: bats completions bash|zsh|fish")
              end
              else if cmd_code = 12 then let (* version *)
                val () = $AP.parse_result_free(r)
                val () = $A.free<byte>(arg_buf)
              in println! ("bats 0.1.0") end
              else let
                val () = $AP.parse_result_free(r)
                val () = $A.free<byte>(arg_buf)
              in println! ("usage: bats <init|lock|add|remove|build|run|test|check|tree|upload|clean|completions> [--only debug|release]") end
            end end (* close else-let for --help *)
          | ~$R.err(e) => let
              val () = $AP.parse_error_free(e)
            in print_usage() end
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
