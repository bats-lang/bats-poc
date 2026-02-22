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
#use str as S
#use toml as T

(* ============================================================
   Helpers
   ============================================================ *)

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

(* Lex $UNITTEST begin...end *)
fn lex_unittest_dispatch {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int, bool) = let
  val after = start + 9  (* after "$UNITTEST" *)
  val p0 = skip_ws(src, after, max, 256)
in
  if looking_at_begin(src, p0, max) then let
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

    (* kind=8: unittest_block - blank for now (emit in test mode later) *)
    else if $AR.eq_int_int(kind, 8) then let
      val () = emit_blanks(src, ss, se, src_max, sats)
      val () = emit_blanks(src, ss, se, src_max, dats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=9: restricted_keyword - emit as-is for now *)
    else if $AR.eq_int_int(kind, 9) then let
      val fuel2 = $AR.checked_nat(se - ss + 1)
      val () = emit_range(src, ss, se, src_max, dats, fuel2)
      val () = emit_range(src, ss, se, src_max, sats, fuel2)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, fuel - 1) end

    (* kind=10: unittest_run - blank for now *)
    else let
      val () = emit_blanks(src, ss, se, src_max, sats)
      val () = emit_blanks(src, ss, se, src_max, dats)
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
          val cmd_start = tok0_end + 1
          val cmd_end = find_null(cl_buf, cmd_start, 4096, 4096)
          val cmd_len = cmd_end - cmd_start
        in
          if cmd_is_check(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_check() end
          else if cmd_is_build(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in println! ("build: not yet implemented") end
          else if cmd_is_clean(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in println! ("clean: not yet implemented") end
          else if cmd_is_lock(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in println! ("lock: not yet implemented") end
          else if cmd_is_run(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in println! ("run: not yet implemented") end
          else let
            val () = $A.free<byte>(cl_buf)
          in println! ("usage: bats-poc <check|build|clean|lock|run>") end
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
