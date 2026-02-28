(* emitter -- emit .sats/.dats from source + spans *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use str as S

staload "helpers.sats"

(* Compute line number from byte offset by counting newlines *)
fn _byte_to_line {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): int = let
  fun count {l2:agz}{n2:pos}{fuel:nat} .<fuel>.
    (src: !$A.borrow(byte, l2, n2), max: int n2,
     i: int, limit: int, line: int, fuel: int fuel): int =
    if fuel <= 0 then line
    else if i >= limit then line
    else if $AR.eq_int_int(byte2int0($A.read<byte>(src, $AR.checked_idx(i, max))), 10)
    then count(src, max, i + 1, limit, line + 1, fuel - 1)
    else count(src, max, i + 1, limit, line, fuel - 1)
in count(src, max, 0, pos, 1, $AR.checked_nat(pos)) end

(* Compute column from byte offset by finding last newline before pos *)
fn _byte_to_col {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): int = let
  fun scan {l2:agz}{n2:pos}{fuel:nat} .<fuel>.
    (src: !$A.borrow(byte, l2, n2), max: int n2,
     i: int, fuel: int fuel): int =
    if fuel <= 0 then pos + 1
    else if i < 0 then pos + 1
    else if $AR.eq_int_int(byte2int0($A.read<byte>(src, $AR.checked_idx(i, max))), 10)
    then pos - i
    else scan(src, max, i - 1, fuel - 1)
in scan(src, max, pos - 1, $AR.checked_nat(pos)) end

(* ============================================================
   Emitter: read span records
   ============================================================ *)

fn read_i32 {l:agz}{n:pos}
  (bv: !$A.borrow(byte, l, n), off: int, max: int n): int =
  let
    val b0 = byte2int0($A.read<byte>(bv, $AR.checked_idx(off, max)))
    val b1 = byte2int0($A.read<byte>(bv, $AR.checked_idx(off + 1, max)))
    val b2 = byte2int0($A.read<byte>(bv, $AR.checked_idx(off + 2, max)))
    val b3 = byte2int0($A.read<byte>(bv, $AR.checked_idx(off + 3, max)))
  in b0 + b1 * 256 + b2 * 65536 + b3 * 16777216 end

fn span_kind {l:agz}{n:pos}
  (spans: !$A.borrow(byte, l, n), idx: int, max: int n): int =
  $S.borrow_byte(spans, idx * 28, max)

fn span_dest {l:agz}{n:pos}
  (spans: !$A.borrow(byte, l, n), idx: int, max: int n): int =
  $S.borrow_byte(spans, idx * 28 + 1, max)

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
    val b = $S.borrow_byte(src, start, max)
    val () = $B.put_byte(out, b)
  in emit_range(src, start + 1, end_pos, max, out, fuel - 1) end

(* Count newlines in source range, emit that many newlines *)
fun emit_blanks_count {ls:agz}{ns:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, count: int, fuel: int fuel): int =
  if fuel <= 0 then count
  else if start >= end_pos then count
  else let
    val b = $S.borrow_byte(src, start, max)
    val new_count = (if $AR.eq_int_int(b, 10) then count + 1 else count): int
  in emit_blanks_count(src, start + 1, end_pos, max, new_count, fuel - 1) end

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
  val nl_count = emit_blanks_count(src, start, end_pos, max, 0,
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
    val b = $S.borrow_byte(src, start, max)
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

(* Emit one staload line for a #use dependency: staload "pkg/src/lib.dats" (no alias) *)
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
  (* /src/lib.dats"\n *)
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

(* Emit one staload line for .sats: staload ALIAS = "pkg/src/lib.sats" *)
fn emit_dep_staload_sats {ls:agz}{ns:pos}{lp:agz}{np:pos}
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_idx: int, span_max: int np,
   out: !$B.builder): void = let
  val pkg_s = span_aux1(spans, span_idx, span_max)
  val pkg_e = span_aux2(spans, span_idx, span_max)
  val alias_s = span_aux3(spans, span_idx, span_max)
  val alias_e = span_aux4(spans, span_idx, span_max)
  (* staload  *)
  val () = $B.put_byte(out, 115)
  val () = $B.put_byte(out, 116)
  val () = $B.put_byte(out, 97)
  val () = $B.put_byte(out, 108)
  val () = $B.put_byte(out, 111)
  val () = $B.put_byte(out, 97)
  val () = $B.put_byte(out, 100)
  val () = $B.put_byte(out, 32)
  (* ALIAS = " *)
  val () = emit_range(src, alias_s, alias_e, src_max, out,
    $AR.checked_nat(alias_e - alias_s + 1))
  val () = $B.put_byte(out, 32)   (* space *)
  val () = $B.put_byte(out, 61)   (* = *)
  val () = $B.put_byte(out, 32)   (* space *)
  val () = $B.put_byte(out, 34)   (* " *)
  (* package path *)
  val () = emit_range(src, pkg_s, pkg_e, src_max, out,
    $AR.checked_nat(pkg_e - pkg_s + 1))
  (* /src/lib.sats"\n *)
  val () = $B.put_byte(out, 47)   (* / *)
  val () = $B.put_byte(out, 115)  (* s *)
  val () = $B.put_byte(out, 114)  (* r *)
  val () = $B.put_byte(out, 99)   (* c *)
  val () = $B.put_byte(out, 47)   (* / *)
  val () = $B.put_byte(out, 108)  (* l *)
  val () = $B.put_byte(out, 105)  (* i *)
  val () = $B.put_byte(out, 98)   (* b *)
  val () = $B.put_byte(out, 46)   (* . *)
  val () = $B.put_byte(out, 115)  (* s *)
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
   build_target: int, is_unsafe: int, errors: int, fuel: int fuel): int =
  if fuel <= 0 then errors
  else if idx >= span_count then errors
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
                  sats, dats, build_target, is_unsafe, errors, fuel - 1) end

    (* kind=1: hash_use - emit aliased staload in dats, blank in sats *)
    else if $AR.eq_int_int(kind, 1) then let
      val () = emit_blanks(src, ss, se, src_max, sats)
      (* In dats: emit staload ALIAS = "pkg/src/lib.sats" at the #use position *)
      val () = emit_dep_staload_sats(src, src_max, spans, idx, span_max, dats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, fuel - 1) end

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
                  sats, dats, build_target, is_unsafe, errors, fuel - 1) end

    (* kind=3: qualified_access - emit $alias.member respecting dest *)
    else if $AR.eq_int_int(kind, 3) then let
      val () = (if $AR.eq_int_int(dest, 0) || $AR.eq_int_int(dest, 2) then
                  emit_qualified(src, src_max, spans, idx, span_max, dats)
                else ())
      val () = (if $AR.eq_int_int(dest, 1) || $AR.eq_int_int(dest, 2) then
                  emit_qualified(src, src_max, spans, idx, span_max, sats)
                else ())
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, fuel - 1) end

    (* kind=4: unsafe_block - emit contents if unsafe=true, error if unsafe=false *)
    else if $AR.eq_int_int(kind, 4) then
      if $AR.gt_int_int(is_unsafe, 0) then let
        val cs = span_aux1(spans, idx, span_max)
        val ce = span_aux2(spans, idx, span_max)
        val () = emit_blanks(src, ss, cs, src_max, dats)
        val () = emit_blanks(src, ss, cs, src_max, sats)
        val fuel2 = $AR.checked_nat(ce - cs + 1)
        val () = (if $AR.eq_int_int(dest, 0) || $AR.eq_int_int(dest, 2) then
                    emit_range(src, cs, ce, src_max, dats, fuel2)
                  else ())
        val () = (if $AR.eq_int_int(dest, 1) || $AR.eq_int_int(dest, 2) then
                    emit_range(src, cs, ce, src_max, sats, fuel2)
                  else ())
        val () = emit_blanks(src, ce, se, src_max, dats)
        val () = emit_blanks(src, ce, se, src_max, sats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors, fuel - 1) end
      else let
        val () = println! ("error: $UNSAFE block at line ", _byte_to_line(src, ss, src_max), " column ", _byte_to_col(src, ss, src_max), " not allowed in safe package")
        val () = emit_blanks(src, ss, se, src_max, dats)
        val () = emit_blanks(src, ss, se, src_max, sats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors + 1, fuel - 1) end

    (* kind=5: unsafe_construct outside $UNSAFE block *)
    else if $AR.eq_int_int(kind, 5) then
      if $AR.gt_int_int(is_unsafe, 0) then let
        (* unsafe package: emit as-is *)
        val fuel2 = $AR.checked_nat(se - ss + 1)
        val () = (if $AR.eq_int_int(dest, 0) || $AR.eq_int_int(dest, 2) then
                    emit_range(src, ss, se, src_max, dats, fuel2)
                  else ())
        val () = (if $AR.eq_int_int(dest, 1) || $AR.eq_int_int(dest, 2) then
                    emit_range(src, ss, se, src_max, sats, fuel2)
                  else ())
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors, fuel - 1) end
      else let
        (* safe package: error *)
        val () = println! ("error: unsafe construct at line ", _byte_to_line(src, ss, src_max), " column ", _byte_to_col(src, ss, src_max), " outside $UNSAFE block")
        val () = emit_blanks(src, ss, se, src_max, dats)
        val () = emit_blanks(src, ss, se, src_max, sats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors + 1, fuel - 1) end

    (* kind=6: extcode_block - emit as-is to dats *)
    else if $AR.eq_int_int(kind, 6) then let
      val fuel2 = $AR.checked_nat(se - ss + 1)
      val () = emit_range(src, ss, se, src_max, dats, fuel2)
      val () = emit_blanks(src, ss, se, src_max, sats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, fuel - 1) end

    (* kind=7: target_decl - blank everything *)
    else if $AR.eq_int_int(kind, 7) then let
      val () = emit_blanks(src, ss, se, src_max, sats)
      val () = emit_blanks(src, ss, se, src_max, dats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, fuel - 1) end

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
                  sats, dats, build_target, is_unsafe, errors, fuel - 1) end

    (* kind=9: restricted_keyword — same as kind 5 *)
    else if $AR.eq_int_int(kind, 9) then
      if $AR.gt_int_int(is_unsafe, 0) then let
        val fuel2 = $AR.checked_nat(se - ss + 1)
        val () = (if $AR.eq_int_int(dest, 0) || $AR.eq_int_int(dest, 2) then
                    emit_range(src, ss, se, src_max, dats, fuel2)
                  else ())
        val () = (if $AR.eq_int_int(dest, 1) || $AR.eq_int_int(dest, 2) then
                    emit_range(src, ss, se, src_max, sats, fuel2)
                  else ())
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors, fuel - 1) end
      else let
        val () = println! ("error: unsafe construct at line ", _byte_to_line(src, ss, src_max), " column ", _byte_to_col(src, ss, src_max), " outside $UNSAFE block")
        val () = emit_blanks(src, ss, se, src_max, dats)
        val () = emit_blanks(src, ss, se, src_max, sats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors + 1, fuel - 1) end

    (* kind=10: unittest_run - emit contents in test mode, blank otherwise *)
    else if $AR.eq_int_int(kind, 10) then let
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
                  sats, dats, build_target, is_unsafe, errors, fuel - 1) end

    (* kind=11: target_block - emit contents only if build_target matches *)
    else if $AR.eq_int_int(kind, 11) then let
      val block_target = span_aux1(spans, idx, span_max)
      val cs = span_aux2(spans, idx, span_max)
      val ce = span_aux3(spans, idx, span_max)
      val matches = $AR.eq_int_int(block_target, build_target)
    in
      if matches then let
        (* Target matches: emit content, blank markers *)
        val () = emit_blanks(src, ss, cs, src_max, dats)
        val () = emit_blanks(src, ss, cs, src_max, sats)
        val fuel2 = $AR.checked_nat(ce - cs + 1)
        val () = emit_range(src, cs, ce, src_max, dats, fuel2)
        val () = emit_blanks(src, cs, ce, src_max, sats)
        val () = emit_blanks(src, ce, se, src_max, dats)
        val () = emit_blanks(src, ce, se, src_max, sats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors, fuel - 1) end
      else let
        (* Target doesn't match: blank everything *)
        val () = emit_blanks(src, ss, se, src_max, sats)
        val () = emit_blanks(src, ss, se, src_max, dats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors, fuel - 1) end
    end

    (* Unknown kind: skip *)
    else
      emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, fuel - 1)
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

(* Build sats prelude: staload ALIAS = "pkg/src/lib.sats" for each #use *)
fun build_prelude_sats {ls:agz}{ns:pos}{lp:agz}{np:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_max: int np,
   span_count: int, idx: int,
   prelude: !$B.builder, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if idx >= span_count then ()
  else let
    val kind = span_kind(spans, idx, span_max)
  in
    if $AR.eq_int_int(kind, 1) then let
      val () = emit_dep_staload_sats(src, src_max, spans, idx, span_max, prelude)
    in build_prelude_sats(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, fuel - 1) end
    else
      build_prelude_sats(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, fuel - 1)
  end

(* Top-level emit *)
#pub fn do_emit {ls:agz}{ns:pos}{lp:agz}{np:pos}
  (src: !$A.borrow(byte, ls, ns), src_len: int, src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_max: int np,
   span_count: int, build_target: int, is_unsafe: int
  ): @([la:agz] $A.arr(byte, la, 524288), int,
      [lb:agz] $A.arr(byte, lb, 524288), int, int, int)

implement do_emit (src, src_len, src_max, spans, span_max, span_count, build_target, is_unsafe) = let
  val sats_b = $B.create()
  val dats_b = $B.create()
  val prelude_b = $B.create()
  val sats_prelude_b = $B.create()

  (* Build dats prelude: self-staload line is always 1 line *)
  val dep_count = build_prelude(src, src_max, spans, span_max,
    span_count, 0, prelude_b, $AR.checked_nat(span_count + 1))
  val prelude_lines = dep_count + 1

  (* Build sats prelude: staload ALIAS = "pkg/src/lib.sats" *)
  val () = build_prelude_sats(src, src_max, spans, span_max,
    span_count, 0, sats_prelude_b, $AR.checked_nat(span_count + 1))

  (* Emit dats prelude *)
  val @(pre_arr, pre_len) = $B.to_arr(prelude_b)
  val @(fz_pre, bv_pre) = $A.freeze<byte>(pre_arr)
  val () = emit_range(bv_pre, 0, pre_len, 524288, dats_b,
    $AR.checked_nat(pre_len + 1))
  val () = $A.drop<byte>(fz_pre, bv_pre)
  val () = $A.free<byte>($A.thaw<byte>(fz_pre))

  (* Emit sats prelude *)
  val @(spre_arr, spre_len) = $B.to_arr(sats_prelude_b)
  val @(fz_spre, bv_spre) = $A.freeze<byte>(spre_arr)
  val () = emit_range(bv_spre, 0, spre_len, 524288, sats_b,
    $AR.checked_nat(spre_len + 1))
  val () = $A.drop<byte>(fz_spre, bv_spre)
  val () = $A.free<byte>($A.thaw<byte>(fz_spre))

  (* Emit all spans *)
  val emit_errors = emit_spans(src, src_max, spans, span_max, span_count, 0,
    sats_b, dats_b, build_target, is_unsafe, 0, $AR.checked_nat(span_count + 1))

  (* Rename the entry point function in the .dats output *)
  val @(dats_tmp, dats_tmp_len) = $B.to_arr(dats_b)
  val @(fz_dt, bv_dt) = $A.freeze<byte>(dats_tmp)
  (* Search for the entry point pattern: 15 chars starting with 'i' *)
  fun find_impl_main0 {ld:agz}{nd:pos}{fuel:nat} .<fuel>.
    (bv: !$A.borrow(byte, ld, nd), len: int, max: int nd, pos: int, fuel: int fuel): int =
    if fuel <= 0 then ~1
    else if pos + 15 > len then ~1
    else let
      val p = pos
      val b0 = byte2int0($A.read<byte>(bv, $AR.checked_idx(p, max)))
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
      end
  val main0_pos = find_impl_main0(bv_dt, dats_tmp_len, 524288,
    0, $AR.checked_nat(dats_tmp_len + 1))
  val has_main0 = main0_pos >= 0

  (* Build final dats with rename *)
  val dats_final = $B.create()
  val () = (if has_main0 then let
    (* Copy before match *)
    val () = emit_range(bv_dt, 0, main0_pos, 524288, dats_final,
      $AR.checked_nat(main0_pos + 1))
    (* Write replacement *)
    val () = $B.bput(dats_final, "implement __BATS_main0")
    (* Copy after match+15 *)
    val after = main0_pos + 15
    val () = emit_range(bv_dt, after, dats_tmp_len, 524288, dats_final,
      $AR.checked_nat(dats_tmp_len - after + 1))
  in end
  else (* No main0, just copy as-is *)
    emit_range(bv_dt, 0, dats_tmp_len, 524288, dats_final,
      $AR.checked_nat(dats_tmp_len + 1))
  )
  val () = $A.drop<byte>(fz_dt, bv_dt)
  val () = $A.free<byte>($A.thaw<byte>(fz_dt))

  (* If has main0, add declaration to sats *)
  val () = (if has_main0 then $B.bput(sats_b, "\nfun __BATS_main0 (): void\n") else ())

  val @(sats_arr, sats_len) = $B.to_arr(sats_b)
  val @(dats_arr, dats_len) = $B.to_arr(dats_final)
in @(sats_arr, sats_len, dats_arr, dats_len, prelude_lines, emit_errors) end
