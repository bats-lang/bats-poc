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
in count(src, max, 0, pos, 1, max) end

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
in scan(src, max, pos - 1, max) end

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

(* Copy bytes from source borrow to builder. *)
fun emit_range {ls:agz}{ns:pos}{bn:nat}{fuel:nat | bn + fuel <= $B.BUILDER_CAP} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, out: !$B.builder(bn) >> [m:nat | bn <= m; m <= bn + fuel] $B.builder(m), fuel: int fuel): void =
  if fuel <= 0 then ()
  else if start >= end_pos then ()
  else let
    val b = $S.borrow_byte(src, start, max)
    val () = $B.put_char(out, b)
  in emit_range(src, start + 1, end_pos, max, out, fuel - 1) end

(* Copy bytes, transforming .bats" → .sats" for staload paths. *)
fun emit_range_stald {ls:agz}{ns:pos}{bn:nat}{fuel:nat | bn + fuel <= $B.BUILDER_CAP} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, out: !$B.builder(bn) >> [m:nat | bn <= m; m <= bn + fuel] $B.builder(m), fuel: int fuel): void =
  if fuel <= 0 then ()
  else if start >= end_pos then ()
  else let
    val b = $S.borrow_byte(src, start, max)
    (* Check for .bats" pattern: 46,98,97,116,115,34 → replace b(98) with s(115) *)
    val b_out = (if $AR.eq_int_int(b, 98) &&
      $AR.eq_int_int($S.borrow_byte(src, start - 1, max), 46) &&
      $AR.eq_int_int($S.borrow_byte(src, start + 1, max), 97) &&
      $AR.eq_int_int($S.borrow_byte(src, start + 2, max), 116) &&
      $AR.eq_int_int($S.borrow_byte(src, start + 3, max), 115) &&
      $AR.eq_int_int($S.borrow_byte(src, start + 4, max), 34)
    then 115 else b): int
    val () = $B.put_char(out, b_out)
  in emit_range_stald(src, start + 1, end_pos, max, out, fuel - 1) end

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

fun emit_newlines {bn:nat}{fuel:nat | bn + fuel <= $B.BUILDER_CAP} .<fuel>.
  (out: !$B.builder(bn) >> [m:nat | bn <= m; m <= bn + fuel] $B.builder(m), count: int, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if count <= 0 then ()
  else let
    val () = $B.put_char(out, 10)
  in emit_newlines(out, count - 1, fuel - 1) end

fun emit_blanks {ls:agz}{ns:pos}{bn:nat}{fuel:nat | bn + fuel <= $B.BUILDER_CAP} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, out: !$B.builder(bn) >> [m:nat | bn <= m; m <= bn + fuel] $B.builder(m), fuel: int fuel): void =
  if fuel <= 0 then ()
  else if start >= end_pos then ()
  else let
    val b = $S.borrow_byte(src, start, max)
  in
    if $AR.eq_int_int(b, 10) then let
      val () = $B.put_char(out, 10)
    in emit_blanks(src, start + 1, end_pos, max, out, fuel - 1) end
    else emit_blanks(src, start + 1, end_pos, max, out, fuel - 1)
  end

(* Builder_v wrappers: compute fuel from remaining capacity *)
fn emit_range_v {ls:agz}{ns:pos}
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, out: !$B.builder_v >> $B.builder_v): void =
  emit_range(src, start, end_pos, max, out, 524288 - $B.length(out))

fn emit_range_stald_v {ls:agz}{ns:pos}
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, out: !$B.builder_v >> $B.builder_v): void =
  emit_range_stald(src, start, end_pos, max, out, 524288 - $B.length(out))

fn emit_blanks_v {ls:agz}{ns:pos}
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, out: !$B.builder_v >> $B.builder_v): void =
  emit_blanks(src, start, end_pos, max, out, 524288 - $B.length(out))

(* Single-pass: blank [ss,cs), content [cs,ce), blank [ce,se) *)
fun emit_blank_content_blank {ls:agz}{ns:pos}{bn:nat}{fuel:nat | bn + fuel <= $B.BUILDER_CAP} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), pos: int, se: int,
   cs: int, ce: int, max: int ns,
   out: !$B.builder(bn) >> [m:nat | bn <= m; m <= bn + fuel] $B.builder(m), fuel: int fuel): void =
  if fuel <= 0 then ()
  else if pos >= se then ()
  else let
    val b = $S.borrow_byte(src, pos, max)
    val in_content = pos >= cs && pos < ce
  in
    if in_content then let
      val () = $B.put_char(out, b)
    in emit_blank_content_blank(src, pos + 1, se, cs, ce, max, out, fuel - 1) end
    else if $AR.eq_int_int(b, 10) then let
      val () = $B.put_char(out, 10)
    in emit_blank_content_blank(src, pos + 1, se, cs, ce, max, out, fuel - 1) end
    else emit_blank_content_blank(src, pos + 1, se, cs, ce, max, out, fuel - 1)
  end

(* Find matching end keyword for $UNSAFE begin, tracking begin/let/local/end nesting *)
fun find_matching_end {ls:agz}{ns:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), pos: int, src_len: int, max: int ns,
   depth: int, fuel: int fuel): int =
  if fuel <= 0 then src_len
  else if pos >= src_len then src_len
  else let
    val b0 = $S.borrow_byte(src, pos, max)
    val b1 = $S.borrow_byte(src, pos + 1, max)
    val b2 = $S.borrow_byte(src, pos + 2, max)
    val b3 = $S.borrow_byte(src, pos + 3, max)
    val bp = $S.borrow_byte(src, pos - 1, max)
    (* Keyword boundary: byte is NOT a-z, A-Z, 0-9, or _ *)
    val after_boundary = ~($AR.gte_int_int(b3, 97) && $AR.lte_int_int(b3, 122)) &&
                         ~($AR.gte_int_int(b3, 65) && $AR.lte_int_int(b3, 90)) &&
                         ~($AR.gte_int_int(b3, 48) && $AR.lte_int_int(b3, 57)) &&
                         ~$AR.eq_int_int(b3, 95)
    val before_boundary = ~($AR.gte_int_int(bp, 97) && $AR.lte_int_int(bp, 122)) &&
                          ~($AR.gte_int_int(bp, 65) && $AR.lte_int_int(bp, 90)) &&
                          ~($AR.gte_int_int(bp, 48) && $AR.lte_int_int(bp, 57)) &&
                          ~$AR.eq_int_int(bp, 95)
  in
    (* Check for end: e(101) n(110) d(100) with word boundaries *)
    if $AR.eq_int_int(b0, 101) && $AR.eq_int_int(b1, 110) && $AR.eq_int_int(b2, 100)
       && after_boundary && before_boundary then
      (if depth <= 1 then pos
       else find_matching_end(src, pos + 3, src_len, max, depth - 1, fuel - 1))
    (* Check for begin: b(98) e(101) g(103) i(105) n(110) with before boundary *)
    else if $AR.eq_int_int(b0, 98) && $AR.eq_int_int(b1, 101) &&
            $AR.eq_int_int(b2, 103) && $AR.eq_int_int(b3, 105) &&
            $AR.eq_int_int($S.borrow_byte(src, pos + 4, max), 110)
            && before_boundary then
      find_matching_end(src, pos + 5, src_len, max, depth + 1, fuel - 1)
    (* Check for let: l(108) e(101) t(116) with word boundaries *)
    else if $AR.eq_int_int(b0, 108) && $AR.eq_int_int(b1, 101) && $AR.eq_int_int(b2, 116)
            && after_boundary && before_boundary then
      find_matching_end(src, pos + 3, src_len, max, depth + 1, fuel - 1)
    else find_matching_end(src, pos + 1, src_len, max, depth, fuel - 1)
  end

(* Blank a range then tail-call content processing *)
fun emit_blank_then_content {ls:agz}{ns:pos}{bn:nat}{fuel:nat | bn + fuel <= $B.BUILDER_CAP} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), pos: int, blank_end: int,
   content_end: int, end_kw_end: int, scan_end: int, overall_end: int,
   max: int ns, out: !$B.builder(bn) >> [m:nat | bn <= m; m <= bn + fuel] $B.builder(m), fuel: int fuel): void =
  if fuel <= 0 then ()
  else if pos < blank_end then let
    (* Phase 1: blank "$UNSAFE begin" region *)
    val b = $S.borrow_byte(src, pos, max)
  in
    if $AR.eq_int_int(b, 10) then let
      val () = $B.put_char(out, 10)
    in emit_blank_then_content(src, pos + 1, blank_end, content_end, end_kw_end, scan_end, overall_end, max, out, fuel - 1) end
    else emit_blank_then_content(src, pos + 1, blank_end, content_end, end_kw_end, scan_end, overall_end, max, out, fuel - 1)
  end
  else if pos < content_end then let
    (* Phase 2: copy inner $UNSAFE content *)
    val () = $B.put_char(out, $S.borrow_byte(src, pos, max))
  in emit_blank_then_content(src, pos + 1, blank_end, content_end, end_kw_end, scan_end, overall_end, max, out, fuel - 1) end
  else if pos < end_kw_end then let
    (* Phase 3: blank "end" keyword *)
    val b = $S.borrow_byte(src, pos, max)
  in
    if $AR.eq_int_int(b, 10) then let
      val () = $B.put_char(out, 10)
    in emit_blank_then_content(src, pos + 1, blank_end, content_end, end_kw_end, scan_end, overall_end, max, out, fuel - 1) end
    else emit_blank_then_content(src, pos + 1, blank_end, content_end, end_kw_end, scan_end, overall_end, max, out, fuel - 1)
  end
  else
    (* Phase 4: continue scanning for more $UNSAFE blocks *)
    emit_range_process_unsafe(src, pos, scan_end, overall_end, max, out, fuel - 1)

(* Emit range processing $UNSAFE begin...end blocks inside #target content.
   Scans byte by byte. When $UNSAFE begin is found, blanks it, emits inner
   content recursively, blanks end. Other content emitted as-is. *)
and emit_range_process_unsafe {ls:agz}{ns:pos}{bn:nat}{fuel:nat | bn + fuel <= $B.BUILDER_CAP} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   overall_end: int,
   max: int ns, out: !$B.builder(bn) >> [m:nat | bn <= m; m <= bn + fuel] $B.builder(m), fuel: int fuel): void =
  if fuel <= 0 then ()
  else if start >= end_pos then
    (* After content range, blank [end_pos, overall_end) *)
    emit_blanks(src, end_pos, overall_end, max, out, fuel)
  else let
    val b = $S.borrow_byte(src, start, max)
  in
    if $AR.eq_int_int(b, 36) &&
       $AR.eq_int_int($S.borrow_byte(src, start + 1, max), 85) &&
       $AR.eq_int_int($S.borrow_byte(src, start + 2, max), 78) &&
       $AR.eq_int_int($S.borrow_byte(src, start + 3, max), 83) &&
       $AR.eq_int_int($S.borrow_byte(src, start + 4, max), 65) &&
       $AR.eq_int_int($S.borrow_byte(src, start + 5, max), 70) &&
       $AR.eq_int_int($S.borrow_byte(src, start + 6, max), 69) then let
      val after = start + 7
      val next = $S.borrow_byte(src, after, max)
    in
      if $AR.eq_int_int(next, 46) then let
        val () = $B.put_char(out, b)
      in emit_range_process_unsafe(src, start + 1, end_pos, overall_end, max, out, fuel - 1) end
      else let
        (* Skip whitespace after $UNSAFE *)
        val p0 = (let fun skip {ls2:agz}{ns2:pos}{f:nat} .<f>.
          (s: !$A.borrow(byte, ls2, ns2), m: int ns2, p: int, lim: int, f: int f): int =
          if f <= 0 then p else if p >= lim then p
          else let val c = $S.borrow_byte(s, p, m) in
            if $AR.eq_int_int(c, 32) || $AR.eq_int_int(c, 10) || $AR.eq_int_int(c, 13) || $AR.eq_int_int(c, 9)
            then skip(s, m, p + 1, lim, f - 1) else p end
        in skip(src, max, after, end_pos, 256) end): int
      in
        (* Check for begin: 98,101,103,105,110 *)
        if $AR.eq_int_int($S.borrow_byte(src, p0, max), 98) &&
           $AR.eq_int_int($S.borrow_byte(src, p0 + 1, max), 101) &&
           $AR.eq_int_int($S.borrow_byte(src, p0 + 2, max), 103) &&
           $AR.eq_int_int($S.borrow_byte(src, p0 + 3, max), 105) &&
           $AR.eq_int_int($S.borrow_byte(src, p0 + 4, max), 110) then let
          val cs2 = p0 + 5
          val end2 = find_matching_end(src, cs2, end_pos, max, 1, 524288)
          val ep2 = (if end2 < end_pos then end2 + 3 else end2): int
          (* Blank [start, cs2), then process [cs2, end2), then blank [end2, ep2),
             then continue with [ep2, end_pos). All via tail calls. *)
        in emit_blank_then_content(src, start, cs2, end2, ep2, end_pos, overall_end, max, out, fuel - 1) end
        else let
          val () = $B.put_char(out, b)
        in emit_range_process_unsafe(src, start + 1, end_pos, overall_end, max, out, fuel - 1) end
      end
    end
    else let
      val b_out = (if $AR.eq_int_int(b, 98) &&
        $AR.eq_int_int($S.borrow_byte(src, start - 1, max), 46) &&
        $AR.eq_int_int($S.borrow_byte(src, start + 1, max), 97) &&
        $AR.eq_int_int($S.borrow_byte(src, start + 2, max), 116) &&
        $AR.eq_int_int($S.borrow_byte(src, start + 3, max), 115) &&
        $AR.eq_int_int($S.borrow_byte(src, start + 4, max), 34)
      then 115 else b): int
      val () = $B.put_char(out, b_out)
    in emit_range_process_unsafe(src, start + 1, end_pos, overall_end, max, out, fuel - 1) end
  end

fn emit_range_process_unsafe_v {ls:agz}{ns:pos}
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   overall_end: int, max: int ns, out: !$B.builder_v >> $B.builder_v): void =
  emit_range_process_unsafe(src, start, end_pos, overall_end, max, out, 524288 - $B.length(out))

(* ============================================================
   Emitter: name mangling (__BATS__<mangled_pkg>_<member>)
   ============================================================ *)

(* Emit __BATS__ prefix: 95,95,66,65,84,83,95,95 *)
fn emit_bats_prefix(out: !$B.builder_v >> $B.builder_v): void = let
  val () = put_char_v(out, 95)   (* _ *)
  val () = put_char_v(out, 95)   (* _ *)
  val () = put_char_v(out, 66)   (* B *)
  val () = put_char_v(out, 65)   (* A *)
  val () = put_char_v(out, 84)   (* T *)
  val () = put_char_v(out, 83)   (* S *)
  val () = put_char_v(out, 95)   (* _ *)
  val () = put_char_v(out, 95)   (* _ *)
in end

(* Emit hex digit for a nibble *)
fn emit_hex_nibble(out: !$B.builder_v >> $B.builder_v, v: int): void =
  if v < 10 then put_char_v(out, v + 48)  (* '0' + v *)
  else put_char_v(out, v - 10 + 97)  (* 'a' + v-10 *)

(* Mangle a single byte: alnum passes through, / becomes __, else _XX *)
fn emit_mangled_byte(out: !$B.builder_v >> $B.builder_v, b: int): void =
  if (b >= 97 && b <= 122) || (b >= 65 && b <= 90) ||
     (b >= 48 && b <= 57) then
    put_char_v(out, b)
  else if $AR.eq_int_int(b, 47) then let  (* '/' -> __ *)
    val () = put_char_v(out, 95)
    val () = put_char_v(out, 95)
  in end
  else let  (* _XX hex *)
    val () = put_char_v(out, 95)
    val () = emit_hex_nibble(out, b / 16)
    val () = emit_hex_nibble(out, b mod 16)
  in end

(* Emit mangled package name from source range *)
fun emit_mangled_pkg {ls:agz}{ns:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), start: int, end_pos: int,
   max: int ns, out: !$B.builder_v >> $B.builder_v, fuel: int fuel): void =
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
   out: !$B.builder_v >> $B.builder_v): void = let
  val alias_s = span_aux1(spans, span_idx, span_max)
  val alias_e = span_aux2(spans, span_idx, span_max)
  val member_s = span_aux3(spans, span_idx, span_max)
  val member_e = span_aux4(spans, span_idx, span_max)
  (* For now, emit $alias.member as-is since we need the use-table
     to look up which package the alias maps to.
     TODO: implement use-table lookup for proper mangling *)
  val () = put_char_v(out, 36)  (* $ *)
  val () = emit_range_v(src, alias_s, alias_e, src_max, out)
  val () = put_char_v(out, 46)  (* . *)
  val () = emit_range_v(src, member_s, member_e, src_max, out)
in end

(* ============================================================
   Emitter: generate dats prelude (staload self + dependencies)
   ============================================================ *)

(* Emit: staload "./FILENAME.sats"\n *)
fn emit_self_stld(out: !$B.builder_v >> $B.builder_v, filename_len: int): void = let
  (* "staload " = 115,116,97,108,111,97,100,32 *)
  val () = put_char_v(out, 115)
  val () = put_char_v(out, 116)
  val () = put_char_v(out, 97)
  val () = put_char_v(out, 108)
  val () = put_char_v(out, 111)
  val () = put_char_v(out, 97)
  val () = put_char_v(out, 100)
  val () = put_char_v(out, 32)
  (* "./ *)
  val () = put_char_v(out, 34)
  val () = put_char_v(out, 46)
  val () = put_char_v(out, 47)
in end

(* Emit one staload line for a #use dependency: staload "pkg/src/lib.dats" (no alias) *)
fn emit_dep_stld {ls:agz}{ns:pos}{lp:agz}{np:pos}
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_idx: int, span_max: int np,
   out: !$B.builder_v >> $B.builder_v): void = let
  val pkg_s = span_aux1(spans, span_idx, span_max)
  val pkg_e = span_aux2(spans, span_idx, span_max)
  (* staload " *)
  val () = put_char_v(out, 115)
  val () = put_char_v(out, 116)
  val () = put_char_v(out, 97)
  val () = put_char_v(out, 108)
  val () = put_char_v(out, 111)
  val () = put_char_v(out, 97)
  val () = put_char_v(out, 100)
  val () = put_char_v(out, 32)
  val () = put_char_v(out, 34)
  (* package path *)
  val () = emit_range_v(src, pkg_s, pkg_e, src_max, out)
  (* /src/lib.dats"\n *)
  val () = put_char_v(out, 47)   (* / *)
  val () = put_char_v(out, 115)  (* s *)
  val () = put_char_v(out, 114)  (* r *)
  val () = put_char_v(out, 99)   (* c *)
  val () = put_char_v(out, 47)   (* / *)
  val () = put_char_v(out, 108)  (* l *)
  val () = put_char_v(out, 105)  (* i *)
  val () = put_char_v(out, 98)   (* b *)
  val () = put_char_v(out, 46)   (* . *)
  val () = put_char_v(out, 100)  (* d *)
  val () = put_char_v(out, 97)   (* a *)
  val () = put_char_v(out, 116)  (* t *)
  val () = put_char_v(out, 115)  (* s *)
  val () = put_char_v(out, 34)   (* " *)
  val () = put_char_v(out, 10)   (* \n *)
in end

(* Emit one staload line for .sats: staload ALIAS = "pkg/src/lib.sats" *)
fn emit_dep_stld_sats {ls:agz}{ns:pos}{lp:agz}{np:pos}
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_idx: int, span_max: int np,
   out: !$B.builder_v >> $B.builder_v): void = let
  val pkg_s = span_aux1(spans, span_idx, span_max)
  val pkg_e = span_aux2(spans, span_idx, span_max)
  val alias_s = span_aux3(spans, span_idx, span_max)
  val alias_e = span_aux4(spans, span_idx, span_max)
  (* staload  *)
  val () = put_char_v(out, 115)
  val () = put_char_v(out, 116)
  val () = put_char_v(out, 97)
  val () = put_char_v(out, 108)
  val () = put_char_v(out, 111)
  val () = put_char_v(out, 97)
  val () = put_char_v(out, 100)
  val () = put_char_v(out, 32)
  (* ALIAS = " *)
  val () = emit_range_v(src, alias_s, alias_e, src_max, out)
  val () = put_char_v(out, 32)   (* space *)
  val () = put_char_v(out, 61)   (* = *)
  val () = put_char_v(out, 32)   (* space *)
  val () = put_char_v(out, 34)   (* " *)
  (* package path *)
  val () = emit_range_v(src, pkg_s, pkg_e, src_max, out)
  (* /src/lib.sats"\n *)
  val () = put_char_v(out, 47)   (* / *)
  val () = put_char_v(out, 115)  (* s *)
  val () = put_char_v(out, 114)  (* r *)
  val () = put_char_v(out, 99)   (* c *)
  val () = put_char_v(out, 47)   (* / *)
  val () = put_char_v(out, 108)  (* l *)
  val () = put_char_v(out, 105)  (* i *)
  val () = put_char_v(out, 98)   (* b *)
  val () = put_char_v(out, 46)   (* . *)
  val () = put_char_v(out, 115)  (* s *)
  val () = put_char_v(out, 97)   (* a *)
  val () = put_char_v(out, 116)  (* t *)
  val () = put_char_v(out, 115)  (* s *)
  val () = put_char_v(out, 34)   (* " *)
  val () = put_char_v(out, 10)   (* \n *)
in end

(* ============================================================
   Emitter: main emit loop
   ============================================================ *)

fun emit_spans {ls:agz}{ns:pos}{lp:agz}{np:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_max: int np,
   span_count: int, idx: int,
   sats: !$B.builder_v >> $B.builder_v, dats: !$B.builder_v >> $B.builder_v,
   build_target: int, is_unsafe: int, errors: int,
   target_state: int, fuel: int fuel): int =
  if fuel <= 0 then errors
  else if idx >= span_count then errors
  else let
    val kind = span_kind(spans, idx, span_max)
    val dest = span_dest(spans, idx, span_max)
    val ss = span_start(spans, idx, span_max)
    val se = span_end(spans, idx, span_max)
  in
    (* kind=13: target_begin - update target state *)
    if $AR.eq_int_int(kind, 13) then let
      val block_target = span_aux1(spans, idx, span_max)
      val () = emit_blanks_v(src, ss, se, src_max, sats)
      val () = emit_blanks_v(src, ss, se, src_max, dats)
      val new_ts = (if target_state > 0 then target_state + 1
                    else if $AR.eq_int_int(block_target, build_target) then 0
                    else 1): int
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, new_ts, fuel - 1) end

    (* kind=14: target_end - restore target state *)
    else if $AR.eq_int_int(kind, 14) then let
      val () = emit_blanks_v(src, ss, se, src_max, sats)
      val () = emit_blanks_v(src, ss, se, src_max, dats)
      val new_ts = (if target_state > 0 then target_state - 1 else 0): int
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, new_ts, fuel - 1) end

    (* Inside non-matching target block: blank everything *)
    else if target_state > 0 then let
      val () = emit_blanks_v(src, ss, se, src_max, sats)
      val () = emit_blanks_v(src, ss, se, src_max, dats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end

    (* kind=0: passthrough *)
    else if $AR.eq_int_int(kind, 0) then let
      val () = (if $AR.eq_int_int(dest, 0) || $AR.eq_int_int(dest, 2) then
                  emit_range_v(src, ss, se, src_max, dats)
                else ())
      val () = (if $AR.eq_int_int(dest, 1) || $AR.eq_int_int(dest, 2) then
                  emit_range_v(src, ss, se, src_max, sats)
                else ())
      val () = (if $AR.eq_int_int(dest, 0) then
                  emit_blanks_v(src, ss, se, src_max, sats)
                else ())
      val () = (if $AR.eq_int_int(dest, 1) then
                  emit_blanks_v(src, ss, se, src_max, dats)
                else ())
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end

    (* kind=1: hash_use - emit aliased staload in dats, blank in sats *)
    else if $AR.eq_int_int(kind, 1) then let
      val () = emit_blanks_v(src, ss, se, src_max, sats)
      (* In dats: emit staload ALIAS = "pkg/src/lib.sats" at the #use position *)
      val () = emit_dep_stld_sats(src, src_max, spans, idx, span_max, dats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end

    (* kind=2: pub_decl - content to sats, blanks to dats *)
    else if $AR.eq_int_int(kind, 2) then let
      val cs = span_aux1(spans, idx, span_max)
      val ce = span_aux2(spans, idx, span_max)
      (* Blank the #pub prefix in sats *)
      val () = emit_blanks_v(src, ss, cs, src_max, sats)
      (* Emit contents to sats *)
      val () = emit_range_v(src, cs, ce, src_max, sats)
      (* Blank everything in dats *)
      val () = emit_blanks_v(src, ss, se, src_max, dats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end

    (* kind=3: qualified_access - emit $alias.member respecting dest *)
    else if $AR.eq_int_int(kind, 3) then let
      val () = (if $AR.eq_int_int(dest, 0) || $AR.eq_int_int(dest, 2) then
                  emit_qualified(src, src_max, spans, idx, span_max, dats)
                else ())
      val () = (if $AR.eq_int_int(dest, 1) || $AR.eq_int_int(dest, 2) then
                  emit_qualified(src, src_max, spans, idx, span_max, sats)
                else ())
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end

    (* kind=4: unsafe_block - emit contents if unsafe=true, error if unsafe=false *)
    else if $AR.eq_int_int(kind, 4) then
      if $AR.gt_int_int(is_unsafe, 0) then let
        val cs = span_aux1(spans, idx, span_max)
        val ce = span_aux2(spans, idx, span_max)
        val () = emit_blanks_v(src, ss, cs, src_max, dats)
        val () = emit_blanks_v(src, ss, cs, src_max, sats)
        val () = (if $AR.eq_int_int(dest, 0) || $AR.eq_int_int(dest, 2) then
                    emit_range_v(src, cs, ce, src_max, dats)
                  else ())
        val () = (if $AR.eq_int_int(dest, 1) || $AR.eq_int_int(dest, 2) then
                    emit_range_v(src, cs, ce, src_max, sats)
                  else ())
        val () = emit_blanks_v(src, ce, se, src_max, dats)
        val () = emit_blanks_v(src, ce, se, src_max, sats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end
      else let
        val () = println! ("error: $UNSAFE block at line ", _byte_to_line(src, ss, src_max), " column ", _byte_to_col(src, ss, src_max), " not allowed in safe package")
        val () = emit_blanks_v(src, ss, se, src_max, dats)
        val () = emit_blanks_v(src, ss, se, src_max, sats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors + 1, target_state, fuel - 1) end

    (* kind=5: unsafe_construct outside $UNSAFE block — always error *)
    else if $AR.eq_int_int(kind, 5) then let
      val () = println! ("error: unsafe construct at line ", _byte_to_line(src, ss, src_max), " column ", _byte_to_col(src, ss, src_max), " outside $UNSAFE block")
      val () = emit_blanks_v(src, ss, se, src_max, dats)
      val () = emit_blanks_v(src, ss, se, src_max, sats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors + 1, target_state, fuel - 1) end

    (* kind=6: extcode_block - emit as-is to dats *)
    else if $AR.eq_int_int(kind, 6) then let
      val () = emit_range_v(src, ss, se, src_max, dats)
      val () = emit_blanks_v(src, ss, se, src_max, sats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end

    (* kind=7: target_decl - blank everything *)
    else if $AR.eq_int_int(kind, 7) then let
      val () = emit_blanks_v(src, ss, se, src_max, sats)
      val () = emit_blanks_v(src, ss, se, src_max, dats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end

    (* kind=8: unittest_block - emit contents in test mode, blank otherwise *)
    else if $AR.eq_int_int(kind, 8) then let
      val cs = span_aux1(spans, idx, span_max)
      val ce = span_aux2(spans, idx, span_max)
      val tm8 = if is_test_mode() then 1 else 0
      val in_test = $AR.gt_int_int(tm8, 0)
    in
      if in_test then let
        val () = emit_blanks_v(src, ss, cs, src_max, dats)
        val () = emit_blanks_v(src, ss, cs, src_max, sats)
        val () = emit_range_v(src, cs, ce, src_max, dats)
        val () = emit_blanks_v(src, ce, se, src_max, dats)
        val () = emit_blanks_v(src, ss, se, src_max, sats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end
      else let
        val () = emit_blanks_v(src, ss, se, src_max, sats)
        val () = emit_blanks_v(src, ss, se, src_max, dats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end
    end

    (* kind=9: restricted_keyword — same as kind 5, always error *)
    else if $AR.eq_int_int(kind, 9) then let
      val () = println! ("error: unsafe construct at line ", _byte_to_line(src, ss, src_max), " column ", _byte_to_col(src, ss, src_max), " outside $UNSAFE block")
      val () = emit_blanks_v(src, ss, se, src_max, dats)
      val () = emit_blanks_v(src, ss, se, src_max, sats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors + 1, target_state, fuel - 1) end

    (* kind=10: unittest_run - emit contents in test mode, blank otherwise *)
    else if $AR.eq_int_int(kind, 10) then let
      val cs = span_aux1(spans, idx, span_max)
      val ce = span_aux2(spans, idx, span_max)
      val tm10 = if is_test_mode() then 1 else 0
      val in_test = $AR.gt_int_int(tm10, 0)
    in
      if in_test then let
        val () = emit_blanks_v(src, ss, cs, src_max, dats)
        val () = emit_blanks_v(src, ss, cs, src_max, sats)
        val () = emit_range_v(src, cs, ce, src_max, dats)
        val () = emit_blanks_v(src, ce, se, src_max, dats)
        val () = emit_blanks_v(src, ss, se, src_max, sats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end
      else let
        val () = emit_blanks_v(src, ss, se, src_max, sats)
        val () = emit_blanks_v(src, ss, se, src_max, dats)
      in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                    sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end
    end

    (* kind=12: staload_line - emit to both with .bats→.sats rename *)
    else if $AR.eq_int_int(kind, 12) then let
      val () = emit_range_stald_v(src, ss, se, src_max, dats)
      val () = emit_range_stald_v(src, ss, se, src_max, sats)
    in emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1) end

    (* Unknown kind: skip *)
    else
      emit_spans(src, src_max, spans, span_max, span_count, idx + 1,
                  sats, dats, build_target, is_unsafe, errors, target_state, fuel - 1)
  end

(* Build dats prelude: self-stld + dependency staloads.
   Skips #use spans inside non-matching target blocks. *)
fun build_prelude {ls:agz}{ns:pos}{lp:agz}{np:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_max: int np,
   span_count: int, idx: int,
   prelude: !$B.builder_v >> $B.builder_v,
   build_target: int, target_state: int, fuel: int fuel): int =
  if fuel <= 0 then 0
  else if idx >= span_count then 0
  else let
    val kind = span_kind(spans, idx, span_max)
  in
    if $AR.eq_int_int(kind, 13) then let
      val block_target = span_aux1(spans, idx, span_max)
      val new_ts = (if target_state > 0 then target_state + 1
                    else if $AR.eq_int_int(block_target, build_target) then 0
                    else 1): int
    in build_prelude(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, build_target, new_ts, fuel - 1) end
    else if $AR.eq_int_int(kind, 14) then let
      val new_ts = (if target_state > 0 then target_state - 1 else 0): int
    in build_prelude(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, build_target, new_ts, fuel - 1) end
    else if $AR.eq_int_int(kind, 1) && target_state <= 0 then let
      val () = emit_dep_stld(src, src_max, spans, idx, span_max, prelude)
      val rest = build_prelude(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, build_target, target_state, fuel - 1)
    in rest + 1 end
    else
      build_prelude(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, build_target, target_state, fuel - 1)
  end

(* Build sats prelude: staload ALIAS = "pkg/src/lib.sats" for each #use.
   Skips #use spans inside non-matching target blocks. *)
fun build_prelude_sats {ls:agz}{ns:pos}{lp:agz}{np:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, ls, ns), src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_max: int np,
   span_count: int, idx: int,
   prelude: !$B.builder_v >> $B.builder_v,
   build_target: int, target_state: int, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if idx >= span_count then ()
  else let
    val kind = span_kind(spans, idx, span_max)
  in
    if $AR.eq_int_int(kind, 13) then let
      val block_target = span_aux1(spans, idx, span_max)
      val new_ts = (if target_state > 0 then target_state + 1
                    else if $AR.eq_int_int(block_target, build_target) then 0
                    else 1): int
    in build_prelude_sats(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, build_target, new_ts, fuel - 1) end
    else if $AR.eq_int_int(kind, 14) then let
      val new_ts = (if target_state > 0 then target_state - 1 else 0): int
    in build_prelude_sats(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, build_target, new_ts, fuel - 1) end
    else if $AR.eq_int_int(kind, 1) && target_state <= 0 then let
      val () = emit_dep_stld_sats(src, src_max, spans, idx, span_max, prelude)
    in build_prelude_sats(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, build_target, target_state, fuel - 1) end
    else
      build_prelude_sats(src, src_max, spans, span_max, span_count,
        idx + 1, prelude, build_target, target_state, fuel - 1)
  end

(* Top-level emit *)
#pub fn do_emit {ls:agz}{ns:pos}{lp:agz}{np:pos}
  (src: !$A.borrow(byte, ls, ns), src_len: int, src_max: int ns,
   spans: !$A.borrow(byte, lp, np), span_max: int np,
   span_count: int, build_target: int, is_unsafe: int
  ): @([la:agz] $A.arr(byte, la, 524288), int,
      [lb:agz] $A.arr(byte, lb, 524288), int, int, int)

implement do_emit (src, src_len, src_max, spans, span_max, span_count, build_target, is_unsafe) = let
  var sats_b = $B.create()
  var dats_b = $B.create()
  var prelude_b = $B.create()
  var sats_prelude_b = $B.create()

  (* Build dats prelude: self-stld line is always 1 line *)
  val dep_count = build_prelude(src, src_max, spans, span_max,
    span_count, 0, prelude_b, build_target, 0, 524288)
  val prelude_lines = dep_count + 1

  (* Build sats prelude: staload ALIAS = "pkg/src/lib.sats" *)
  val () = build_prelude_sats(src, src_max, spans, span_max,
    span_count, 0, sats_prelude_b, build_target, 0, 524288)

  (* Emit dats prelude *)
  val @(pre_arr, pre_len) = $B.to_arr(prelude_b)
  val @(fz_pre, bv_pre) = $A.freeze<byte>(pre_arr)
  val () = emit_range_v(bv_pre, 0, pre_len, 524288, dats_b)
  val () = $A.drop<byte>(fz_pre, bv_pre)
  val () = $A.free<byte>($A.thaw<byte>(fz_pre))

  (* Emit sats prelude *)
  val @(spre_arr, spre_len) = $B.to_arr(sats_prelude_b)
  val @(fz_spre, bv_spre) = $A.freeze<byte>(spre_arr)
  val () = emit_range_v(bv_spre, 0, spre_len, 524288, sats_b)
  val () = $A.drop<byte>(fz_spre, bv_spre)
  val () = $A.free<byte>($A.thaw<byte>(fz_spre))

  (* Emit all spans *)
  val emit_errors = emit_spans(src, src_max, spans, span_max, span_count, 0,
    sats_b, dats_b, build_target, is_unsafe, 0, 0, 524288)

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
    0, 524288)
  val has_main0 = main0_pos >= 0

  (* Convert sats_b to array before the conditional *)
  val @(sats_tmp, sats_tmp_len) = $B.to_arr(sats_b)
  val @(fz_st, bv_st) = $A.freeze<byte>(sats_tmp)

  (* Build final dats and sats without branch merge *)
  val @(dats_final, sats_final) = (if has_main0 then let
    var df = $B.create()
    val () = emit_range_v(bv_dt, 0, main0_pos, 524288, df)
    val () = bput_v(df, "implement __BATS_main0")
    val after = main0_pos + 15
    val () = emit_range_v(bv_dt, after, dats_tmp_len, 524288, df)
    var sf = $B.create()
    val () = emit_range_v(bv_st, 0, sats_tmp_len, 524288, sf)
    val () = bput_v(sf, "\nfun __BATS_main0 (): void\n")
  in @(df, sf) end
  else let
    var df = $B.create()
    val () = emit_range_v(bv_dt, 0, dats_tmp_len, 524288, df)
    var sf = $B.create()
    val () = emit_range_v(bv_st, 0, sats_tmp_len, 524288, sf)
  in @(df, sf) end): @($B.builder_v, $B.builder_v)

  val () = $A.drop<byte>(fz_dt, bv_dt)
  val () = $A.free<byte>($A.thaw<byte>(fz_dt))
  val () = $A.drop<byte>(fz_st, bv_st)
  val () = $A.free<byte>($A.thaw<byte>(fz_st))
  val @(sats_arr, sats_len) = $B.to_arr(sats_final)
  val @(dats_arr, dats_len) = $B.to_arr(dats_final)
in @(sats_arr, sats_len, dats_arr, dats_len, prelude_lines, emit_errors) end
