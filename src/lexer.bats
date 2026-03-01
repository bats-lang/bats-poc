(* lexer -- tokenizer for the bats compiler *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use str as S

staload "helpers.sats"

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

(* ============================================================
   Lexer: keyword detection helpers
   ============================================================ *)

fn looking_at_2 {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n,
   c0: int, c1: int): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), c0) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), c1)

fn is_kw_boundary {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  if pos >= max then true
  else ~(is_ident_byte($S.borrow_byte(src, pos, max)))

fn is_kw_boundary_before {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  if pos <= 0 then true
  else ~(is_ident_byte($S.borrow_byte(src, pos - 1, max)))

(* #pub = 35,112,117,98 *)
fn looking_at_pub {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 35) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 112) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 117) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 98) &&
  is_kw_boundary(src, pos + 4, max)

(* #use = 35,117,115,101 *)
fn looking_at_use {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 35) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 117) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 115) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 101) &&
  is_kw_boundary(src, pos + 4, max)

(* #target = 35,116,97,114,103,101,116 *)
fn looking_at_target {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 35) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 116) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 97) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 114) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 103) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 6, max), 116) &&
  is_kw_boundary(src, pos + 7, max)

(* $UNSAFE = 36,85,78,83,65,70,69 *)
fn looking_at_unsafe {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 36) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 85) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 78) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 83) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 65) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 70) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 6, max), 69)

(* $UNITTEST = 36,85,78,73,84,84,69,83,84 *)
fn looking_at_unittest {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 36) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 85) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 78) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 73) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 84) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 84) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 6, max), 69) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 7, max), 83) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 8, max), 84)

(* "begin" = 98,101,103,105,110 *)
fn looking_at_begin {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 98) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 103) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 105) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 110) &&
  is_kw_boundary(src, pos + 5, max)

(* "end" = 101,110,100 *)
fn looking_at_end {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 110) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 100) &&
  is_kw_boundary(src, pos + 3, max) &&
  is_kw_boundary_before(src, pos, max)

(* "as" = 97,115 *)
fn looking_at_as {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 97) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 115) &&
  is_kw_boundary(src, pos + 2, max)

(* "castfn" = 99,97,115,116,102,110 *)
fn looking_at_castfn {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 99) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 97) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 115) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 116) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 102) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 110) &&
  is_kw_boundary(src, pos + 6, max)

(* "praxi" = 112,114,97,120,105 *)
fn looking_at_praxi {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 112) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 114) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 97) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 120) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 105) &&
  is_kw_boundary(src, pos + 5, max)

(* "extern" = 101,120,116,101,114,110 *)
fn looking_at_extern {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 120) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 116) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 114) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 110) &&
  is_kw_boundary(src, pos + 6, max)

(* "assume" = 97,115,115,117,109,101 *)
fn looking_at_assume {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 97) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 115) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 115) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 117) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 109) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 101) &&
  is_kw_boundary(src, pos + 6, max)

(* $extval — $-prefixed unsafe construct *)
fn looking_at_extval {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 36) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 120) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 116) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 118) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 97) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 6, max), 108) &&
  is_kw_boundary(src, pos + 7, max)

(* $extfcall *)
fn looking_at_extfcall {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 36) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 120) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 116) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 102) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 99) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 6, max), 97) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 7, max), 108) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 8, max), 108) &&
  is_kw_boundary(src, pos + 9, max)

(* $extype *)
fn looking_at_extype {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 36) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 120) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 116) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 121) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 112) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 6, max), 101) &&
  is_kw_boundary(src, pos + 7, max)

(* $extkind *)
fn looking_at_extkind {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 36) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 120) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 116) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 107) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 105) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 6, max), 110) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 7, max), 100) &&
  is_kw_boundary(src, pos + 8, max)

(* "mac#" = 109,97,99,35 — C function binding *)
fn looking_at_mac_hash {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 109) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 97) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 99) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 35)

(* "ext#" = 101,120,116,35 — WASM export binding *)
fn looking_at_ext_hash {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 120) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 116) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 35)

(* "fun" = 102,117,110 — only unsafe WITHOUT termination metric *)
fn looking_at_fun {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 102) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 117) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 110) &&
  is_kw_boundary(src, pos + 3, max) &&
  is_kw_boundary_before(src, pos, max)

(* Scan forward from pos looking for ".< " before "=" to detect termination metric.
   Returns true if .<...>. is found, meaning the fun IS safe. *)
fun _has_metric {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, max: int n, fuel: int fuel): bool =
  if fuel <= 0 then false
  else if pos >= max then false
  else let
    val b = $S.borrow_byte(src, pos, max)
  in
    (* Found ".< " — has metric *)
    if $AR.eq_int_int(b, 46) then
      if $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 60) then true
      else _has_metric(src, pos + 1, max, fuel - 1)
    (* Found standalone "=" — end of signature, no metric *)
    (* Skip <= >= == != by checking previous byte *)
    else if $AR.eq_int_int(b, 61) then let
      val prev = (if pos > 0 then $S.borrow_byte(src, pos - 1, max) else 32): int
    in
      if $AR.eq_int_int(prev, 60) then _has_metric(src, pos + 1, max, fuel - 1)
      else if $AR.eq_int_int(prev, 62) then _has_metric(src, pos + 1, max, fuel - 1)
      else if $AR.eq_int_int(prev, 61) then _has_metric(src, pos + 1, max, fuel - 1)
      else if $AR.eq_int_int(prev, 33) then _has_metric(src, pos + 1, max, fuel - 1)
      else false
    end
    (* Found newline followed by non-whitespace — end of declaration *)
    else if $AR.eq_int_int(b, 10) then let
      val nb = $S.borrow_byte(src, pos + 1, max)
    in
      if $AR.eq_int_int(nb, 32) || $AR.eq_int_int(nb, 9) then
        _has_metric(src, pos + 1, max, fuel - 1)
      else false
    end
    else _has_metric(src, pos + 1, max, fuel - 1)
  end

(* "prfun" = 112,114,102,117,110 — only unsafe if #pub without primplement *)
fn _content_starts_prfun {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 112) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 114) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 102) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 117) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 110) &&
  is_kw_boundary(src, pos + 5, max)

(* "prfn" = 112,114,102,110 *)
fn _content_starts_prfn {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 112) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 114) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 102) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 110) &&
  is_kw_boundary(src, pos + 4, max)

(* "primplement" = 112,114,105,109,112,108,101,109,101,110,116 *)
fn _looking_at_primplement {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 112) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 114) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 105) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 109) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 112) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 108) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 6, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 7, max), 109) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 8, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 9, max), 110) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 10, max), 116)

(* "no_mangle" = 110,111,95,109,97,110,103,108,101 *)
fn looking_at_no_mangle {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 110) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 111) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 95) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 109) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 97) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 5, max), 110) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 6, max), 103) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 7, max), 108) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 8, max), 101) &&
  is_kw_boundary(src, pos + 9, max)

(* ============================================================
   Lexer: sub-lexers
   ============================================================ *)

(* Skip whitespace (space/tab only, not newlines) *)
fun skip_ws {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else let val b = $S.borrow_byte(src, pos, max) in
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
  else let val b = $S.borrow_byte(src, pos, max) in
    if $AR.eq_int_int(b, 10) then pos + 1
    else skip_to_eol(src, pos + 1, src_len, max, fuel - 1)
  end

(* Skip ident chars *)
fun skip_ident {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else let val b = $S.borrow_byte(src, pos, max) in
    if is_ident_byte(b) then skip_ident(src, pos + 1, max, fuel - 1)
    else pos
  end

(* Extract the declaration name start position after prfun/prfn keyword *)
fun _skip_to_name {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, max: int n, fuel: int fuel): int =
  if fuel <= 0 then pos
  else if pos >= max then pos
  else let val b = $S.borrow_byte(src, pos, max) in
    if $AR.eq_int_int(b, 32) || $AR.eq_int_int(b, 9) || $AR.eq_int_int(b, 10) then
      _skip_to_name(src, pos + 1, max, fuel - 1)
    else if $AR.eq_int_int(b, 123) then let (* skip {quantifiers} *)
      fun _skip_brace {l:agz}{n:pos}{f:nat} .<f>.
        (src: !$A.borrow(byte, l, n), p: int, max: int n, f: int f): int =
        if f <= 0 then p
        else if p >= max then p
        else if $AR.eq_int_int($S.borrow_byte(src, p, max), 125) then p + 1
        else _skip_brace(src, p + 1, max, f - 1)
    in _skip_to_name(src, _skip_brace(src, pos + 1, max, fuel - 1), max, fuel - 1) end
    else pos
  end

(* Check if primplement exists for a name starting at name_start with length name_len *)
fun _has_primplement {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   name_start: int, name_len: int, scan_pos: int, fuel: int fuel): bool =
  if fuel <= 0 then false
  else if scan_pos >= src_len then false
  else
    if _looking_at_primplement(src, scan_pos, max) then let
      val after = scan_pos + 11
      val p = _skip_to_name(src, after, max, 256)
      fun _names_match {l:agz}{n:pos}{f:nat} .<f>.
        (src: !$A.borrow(byte, l, n), a: int, b: int, len: int, max: int n, f: int f): bool =
        if f <= 0 then true
        else if len <= 0 then true
        else if $AR.eq_int_int($S.borrow_byte(src, a, max), $S.borrow_byte(src, b, max)) then
          _names_match(src, a + 1, b + 1, len - 1, max, f - 1)
        else false
      val nend = skip_ident(src, p, max, 4096)
      val found_len = nend - p
    in
      if $AR.eq_int_int(found_len, name_len) then
        if _names_match(src, name_start, p, name_len, max, $AR.checked_nat(name_len)) then true
        else _has_primplement(src, src_len, max, name_start, name_len, scan_pos + 1, fuel - 1)
      else _has_primplement(src, src_len, max, name_start, name_len, scan_pos + 1, fuel - 1)
    end
    else _has_primplement(src, src_len, max, name_start, name_len, scan_pos + 1, fuel - 1)

(* Skip non-whitespace *)
fun skip_nonws {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else let val b = $S.borrow_byte(src, pos, max) in
    if $AR.eq_int_int(b, 32) || $AR.eq_int_int(b, 9) ||
       $AR.eq_int_int(b, 10) || $AR.eq_int_int(b, 0)
    then pos
    else skip_nonws(src, pos + 1, max, fuel - 1)
  end

(* Lex // line comment. //// = rest-of-file *)
fn lex_line_comment {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) =
  if $AR.eq_int_int($S.borrow_byte(src, start + 2, max), 47) &&
     $AR.eq_int_int($S.borrow_byte(src, start + 3, max), 47) then let
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
  else if $AR.eq_int_int($S.borrow_byte(src, pos, max), 42) &&
          $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 47) then
    pos + 2
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
    val b0 = $S.borrow_byte(src, pos, max)
    val b1 = $S.borrow_byte(src, pos + 1, max)
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
  else let val b = $S.borrow_byte(src, pos, max) in
    if $AR.eq_int_int(b, 92) then
      lex_string_inner(src, pos + 2, src_len, max, fuel - 1)
    else if $AR.eq_int_int(b, 34) then pos + 1
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
  val b1 = $S.borrow_byte(src, p1, max)
  val p2 = (if $AR.eq_int_int(b1, 92) then p1 + 2 else p1 + 1): int
  val p3 = (if $AR.eq_int_int($S.borrow_byte(src, p2, max), 39) then p2 + 1 else p2): int
  val () = put_span(spans, 0, 0, start, p3, 0, 0, 0, 0)
in @(p3, count + 1) end

(* Lex extcode %{ ... %} *)
fun lex_extcode_inner {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else if pos + 1 >= src_len then src_len
  else if $AR.eq_int_int($S.borrow_byte(src, pos, max), 37) &&
          $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 125) then
    pos + 2
  else lex_extcode_inner(src, pos + 1, src_len, max, fuel - 1)

fn lex_extcode {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val after_open = start + 2
  val bk = $S.borrow_byte(src, after_open, max)
  val @(kind, cstart) =
    (if $AR.eq_int_int(bk, 94) then @(1, after_open + 1)
     else if $AR.eq_int_int(bk, 36) then @(2, after_open + 1)
     else if $AR.eq_int_int(bk, 35) then @(3, after_open + 1)
     else @(0, after_open)): @(int, int)
  val ep = lex_extcode_inner(src, cstart, src_len, max, $AR.checked_nat(src_len))
  val cend = (if ep >= 2 then ep - 2 else ep): int
  val () = put_span(spans, 6, 0, start, ep, cstart, cend, kind, 0)
in @(ep, count + 1) end

(* Lex #use pkg as Alias [no_mangle] *)
fn lex_hash_use {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val p0 = skip_ws(src, start + 4, max, 256)
  val pkg_start = p0
  val pkg_end = skip_nonws(src, p0, max, 4096)
  val p1 = skip_ws(src, pkg_end, max, 256)
  val p2 = (if looking_at_as(src, p1, max) then p1 + 2 else p1): int
  val p3 = skip_ws(src, p2, max, 256)
  val alias_start = p3
  val alias_end = skip_ident(src, p3, max, 4096)
  val p4 = skip_ws(src, alias_end, max, 256)
  val mangle = (if looking_at_no_mangle(src, p4, max) then 0 else 1): int
  val ep = skip_to_eol(src, p4, src_len, max, $AR.checked_nat(src_len))
  val () = put_span(spans, 1, mangle + 1, start, ep,
                    pkg_start, pkg_end, alias_start, alias_end)
in @(ep, count + 1) end

(* Lex $Alias.member qualified access *)
fn lex_qualified {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int, bool) = let
  val alias_start = start + 1
  val alias_end = skip_ident(src, alias_start, max, 4096)
  val dot_byte = $S.borrow_byte(src, alias_end, max)
in
  if $AR.eq_int_int(dot_byte, 46) then let
    val member_start = alias_end + 1
    val member_end = skip_ident(src, member_start, max, 4096)
  in
    if member_end > member_start then let
      val () = put_span(spans, 3, 0, start, member_end,
                        alias_start, alias_end, member_start, member_end)
    in @(member_end, count + 1, true) end
    else @(start, count, false)
  end
  else @(start, count, false)
end

(* Check if line at pos is blank *)
fun is_blank_line {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): bool =
  if fuel <= 0 then true
  else if pos >= src_len then true
  else let val b = $S.borrow_byte(src, pos, max) in
    if $AR.eq_int_int(b, 10) then true
    else if $AR.eq_int_int(b, 32) || $AR.eq_int_int(b, 9) then
      is_blank_line(src, pos + 1, src_len, max, fuel - 1)
    else false
  end

(* Lex #pub declaration - find end of block *)
fun lex_pub_lines {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else if pos >= src_len then pos
  else let
    val eol = skip_to_eol(src, pos, src_len, max, $AR.checked_nat(src_len))
  in
    if eol >= src_len then eol
    else if is_blank_line(src, eol, src_len, max, 256) then eol
    else if looking_at_pub(src, eol, max) then eol
    else if looking_at_use(src, eol, max) then eol
    else if looking_at_target(src, eol, max) then eol
    else if looking_at_unsafe(src, eol, max) then eol
    else if looking_at_unittest(src, eol, max) then eol
    else let val b = $S.borrow_byte(src, eol, max) in
      if $AR.eq_int_int(b, 102) &&
         ($AR.eq_int_int($S.borrow_byte(src, eol + 1, max), 117) &&
          $AR.eq_int_int($S.borrow_byte(src, eol + 2, max), 110) &&
          is_kw_boundary(src, eol + 3, max)) then eol
      else if $AR.eq_int_int(b, 102) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 1, max), 110) &&
              is_kw_boundary(src, eol + 2, max) then eol
      else if $AR.eq_int_int(b, 118) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 1, max), 97) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 2, max), 108) &&
              is_kw_boundary(src, eol + 3, max) then eol
      else if $AR.eq_int_int(b, 105) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 1, max), 109) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 2, max), 112) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 3, max), 108) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 4, max), 101) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 5, max), 109) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 6, max), 101) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 7, max), 110) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 8, max), 116) &&
              is_kw_boundary(src, eol + 9, max) then eol
      else if $AR.eq_int_int(b, 37) &&
              $AR.eq_int_int($S.borrow_byte(src, eol + 1, max), 123) then eol
      else lex_pub_lines(src, eol, src_len, max, fuel - 1)
    end
  end

(* Check for "let" *)
fn looking_at_let {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  is_kw_boundary_before(src, pos, max) &&
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 108) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 101) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 116) &&
  is_kw_boundary(src, pos + 3, max)

(* "local" = 108,111,99,97,108 *)
fn looking_at_local {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): bool =
  is_kw_boundary_before(src, pos, max) &&
  $AR.eq_int_int($S.borrow_byte(src, pos, max), 108) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 1, max), 111) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 2, max), 99) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 3, max), 97) &&
  $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 108) &&
  is_kw_boundary(src, pos + 5, max)

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
  else if looking_at_local(src, pos, max) then
    find_end_kw(src, pos + 5, src_len, max, depth + 1, fuel - 1)
  else find_end_kw(src, pos + 1, src_len, max, depth, fuel - 1)

fn lex_unsafe_dispatch {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int, bool) = let
  val after = start + 7
  val next = $S.borrow_byte(src, after, max)
in
  if $AR.eq_int_int(next, 46) then let
    val ident_end = skip_ident(src, after + 1, max, 4096)
    val () = put_span(spans, 5, 0, start, ident_end, 0, 0, 0, 0)
  in @(ident_end, count + 1, true) end
  else let
    val p0 = skip_ws(src, after, max, 256)
  in
    if looking_at_begin(src, p0, max) then let
      val contents_start = p0 + 5
      val end_pos = find_end_kw(src, contents_start, src_len, max, 1, $AR.checked_nat(src_len))
      val ep = (if end_pos < src_len then end_pos + 3 else end_pos): int
      val () = put_span(spans, 4, 0, start, ep, contents_start, end_pos, 0, 0)
    in @(ep, count + 1, true) end
    else @(start, count, false)
  end
end

fn lex_unittest_dispatch {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int, bool) = let
  val after = start + 9
  val p0 = skip_ws(src, after, max, 256)
  val is_dot = $AR.eq_int_int($S.borrow_byte(src, p0, max), 46)
  val is_run = is_dot &&
    $AR.eq_int_int($S.borrow_byte(src, p0 + 1, max), 114) &&
    $AR.eq_int_int($S.borrow_byte(src, p0 + 2, max), 117) &&
    $AR.eq_int_int($S.borrow_byte(src, p0 + 3, max), 110)
in
  if is_run then let
    val p1 = skip_ws(src, p0 + 4, max, 256)
  in
    if looking_at_begin(src, p1, max) then let
      val contents_start = p1 + 5
      val end_pos = find_end_kw(src, contents_start, src_len, max, 1, $AR.checked_nat(src_len))
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

fn lex_target_decl {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n,
   spans: !$B.builder, start: int, count: int): @(int, int) = let
  val p0 = skip_ws(src, start + 7, max, 256)
  val ident_end = skip_ident(src, p0, max, 4096)
  val target = (if $AR.eq_int_int($S.borrow_byte(src, p0, max), 119) then 1 else 0): int
  (* Check for block form: #target wasm begin...end *)
  val p1 = skip_ws(src, ident_end, max, 256)
in
  if looking_at_begin(src, p1, max) then let
    (* Block form: find matching end, store content range *)
    val contents_start = p1 + 5
    val end_pos = find_end_kw(src, contents_start, src_len, max, 1, $AR.checked_nat(src_len))
    val ep = (if end_pos < src_len then end_pos + 3 else end_pos): int
    (* kind=11: target_block. aux1=target(0=native,1=wasm), aux2/aux3=content range *)
    val () = put_span(spans, 11, 0, start, ep, target, contents_start, end_pos, 0)
  in @(ep, count + 1) end
  else let
    (* Line form: just the directive *)
    val ep = skip_to_eol(src, ident_end, src_len, max, $AR.checked_nat(src_len))
    val () = put_span(spans, 7, 2, start, ep, target, 0, 0, 0)
  in @(ep, count + 1) end
end

(* ============================================================
   Lexer: passthrough scanner
   ============================================================ *)

fun lex_passthrough_scan {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), pos: int, src_len: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else if pos >= src_len then pos
  else let
    val b = $S.borrow_byte(src, pos, max)
    val b1 = $S.borrow_byte(src, pos + 1, max)
  in
    if $AR.eq_int_int(b, 47) && ($AR.eq_int_int(b1, 47) || $AR.eq_int_int(b1, 42))
    then pos
    else if $AR.eq_int_int(b, 40) && $AR.eq_int_int(b1, 42) then pos
    else if $AR.eq_int_int(b, 34) then pos
    else if $AR.eq_int_int(b, 39) then pos
    else if $AR.eq_int_int(b, 37) && $AR.eq_int_int(b1, 123) then pos
    else if $AR.eq_int_int(b, 35) &&
      (looking_at_pub(src, pos, max) || looking_at_use(src, pos, max) ||
       looking_at_target(src, pos, max)) then pos
    else if $AR.eq_int_int(b, 36) && is_ident_start(b1) then pos
    (* Stop at unsafe keywords so lex_main can detect them *)
    else if looking_at_castfn(src, pos, max) then pos
    else if looking_at_praxi(src, pos, max) then pos
    else if looking_at_extern(src, pos, max) then pos
    else if looking_at_assume(src, pos, max) then pos
    else if looking_at_fun(src, pos, max) then pos
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
    val b0 = $S.borrow_byte(src, pos, max)
    val b1 = $S.borrow_byte(src, pos + 1, max)
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

    (* #pub declaration *)
    else if looking_at_pub(src, pos, max) then let
      val p0 = skip_ws(src, pos + 4, max, 256)
      val contents_start = p0
      val ep = lex_pub_lines(src, p0, src_len, max, $AR.checked_nat(src_len))
      val is_prfun = _content_starts_prfun(src, contents_start, max)
      val is_prfn = if is_prfun then false else _content_starts_prfn(src, contents_start, max)
      val span_kind =
        if is_prfun || is_prfn then let
          val kw_len = if is_prfun then 5 else 4
          val name_pos = _skip_to_name(src, $AR.add_int_int(contents_start, kw_len), max, 256)
          val name_end = skip_ident(src, name_pos, max, 4096)
          val name_len = name_end - name_pos
        in
          if _has_primplement(src, src_len, max, name_pos, name_len, 0, $AR.checked_nat(src_len)) then 2
          else 5
        end
        else 2
      val () = put_span(spans, span_kind, 1, pos, ep, contents_start, ep, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end

    (* #target *)
    else if looking_at_target(src, pos, max) then let
      val @(np, nc) = lex_target_decl(src, src_len, max, spans, pos, count)
    in lex_main(src, src_len, max, spans, np, nc, fuel - 1) end

    (* $extval, $extfcall, $extype, $extkind — unsafe constructs *)
    else if looking_at_extval(src, pos, max) then let
      val ep = pos + 7
      val () = put_span(spans, 5, 0, pos, ep, 0, 0, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    else if looking_at_extfcall(src, pos, max) then let
      val ep = pos + 9
      val () = put_span(spans, 5, 0, pos, ep, 0, 0, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    else if looking_at_extype(src, pos, max) then let
      val ep = pos + 7
      val () = put_span(spans, 5, 0, pos, ep, 0, 0, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    else if looking_at_extkind(src, pos, max) then let
      val ep = pos + 8
      val () = put_span(spans, 5, 0, pos, ep, 0, 0, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end

    (* $UNSAFE *)
    else if looking_at_unsafe(src, pos, max) then let
      val @(np, nc, matched) = lex_unsafe_dispatch(src, src_len, max, spans, pos, count)
    in
      if matched then lex_main(src, src_len, max, spans, np, nc, fuel - 1)
      else let
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

    (* fun without termination metric — unsafe (can diverge) *)
    else if looking_at_fun(src, pos, max) then let
      val after = pos + 3
    in
      if _has_metric(src, after, max, $AR.checked_nat(max)) then let
        val ep = lex_passthrough_scan(src, pos + 1, src_len, max, $AR.checked_nat(src_len))
        val () = put_span(spans, 0, 0, pos, ep, 0, 0, 0, 0)
      in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
      else let
        val ep = pos + 3
        val () = put_span(spans, 5, 0, pos, ep, 0, 0, 0, 0)
      in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    end

    (* castfn, praxi, extern, assume — unsafe constructs *)
    else if looking_at_castfn(src, pos, max) then let
      val ep = pos + 6
      val () = put_span(spans, 5, 0, pos, ep, 0, 0, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    else if looking_at_praxi(src, pos, max) then let
      val ep = pos + 5
      val () = put_span(spans, 5, 0, pos, ep, 0, 0, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    else if looking_at_extern(src, pos, max) then let
      val ep = pos + 6
      val () = put_span(spans, 5, 0, pos, ep, 0, 0, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    else if looking_at_assume(src, pos, max) then let
      val ep = pos + 6
      val () = put_span(spans, 5, 0, pos, ep, 0, 0, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
    (* Default: passthrough *)
    else let
      val ep = lex_passthrough_scan(src, pos + 1, src_len, max, $AR.checked_nat(src_len))
      val () = put_span(spans, 0, 0, pos, ep, 0, 0, 0, 0)
    in lex_main(src, src_len, max, spans, ep, count + 1, fuel - 1) end
  end

(* Top-level lex function *)
#pub fn do_lex {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), src_len: int, max: int n
  ): @([ls:agz] $A.arr(byte, ls, 524288), int, int)

implement do_lex (src, src_len, max) = let
  val span_builder = $B.create()
  val @(_, span_count) = lex_main(src, src_len, max, span_builder, 0, 0, $AR.checked_nat(src_len))
  val @(span_arr, span_arr_len) = $B.to_arr(span_builder)
in @(span_arr, span_arr_len, span_count) end
