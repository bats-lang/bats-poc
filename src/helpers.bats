(* helpers -- shared utilities for the bats compiler *)

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
#use str as S

(* ============================================================
   Global state using ATS2 refs (replaces C statics)
   ============================================================ *)

val g_verbose = ref<bool>(false)
val g_quiet = ref<bool>(false)
val g_test_mode = ref<bool>(false)
val g_lock_dev = ref<bool>(false)
val g_repo: ref(string) = ref("")
val g_bin: ref(string) = ref("")
val g_to_c = ref<int>(0)
val g_to_c_done = ref<int>(0)
val g_self_path: ref(string) = ref("")

#pub fn is_verbose(): bool

#pub fn is_quiet(): bool

#pub fn is_test_mode(): bool

#pub fn is_to_c(): bool

#pub fn set_verbose(v: bool): void

#pub fn set_quiet(v: bool): void

#pub fn set_test_mode(v: bool): void

#pub fn set_lock_dev(v: bool): void

#pub fn is_lock_dev(): bool

#pub fn set_repo {sn:nat} (s: string sn): void

#pub fn get_repo(): string

#pub fn set_bin {sn:nat} (s: string sn): void

#pub fn get_bin(): string

#pub fn set_to_c(v: int): void

#pub fn get_to_c(): int

#pub fn set_to_c_done(v: int): void

#pub fn get_to_c_done(): int

#pub fn set_self_path {sn:nat} (s: string sn): void

#pub fn get_self_path(): string

implement is_verbose() = !g_verbose
implement is_quiet() = !g_quiet
implement is_test_mode() = !g_test_mode
implement is_to_c() = !g_to_c > 0
implement set_verbose(v) = !g_verbose := v
implement set_quiet(v) = !g_quiet := v
implement set_test_mode(v) = !g_test_mode := v
implement set_lock_dev(v) = !g_lock_dev := v
implement is_lock_dev() = !g_lock_dev
implement set_repo(s) = !g_repo := s
implement get_repo() = !g_repo
implement set_bin(s) = !g_bin := s
implement get_bin() = !g_bin
implement set_to_c(v) = !g_to_c := v
implement get_to_c() = !g_to_c
implement set_to_c_done(v) = !g_to_c_done := v
implement get_to_c_done() = !g_to_c_done
implement set_self_path(s) = !g_self_path := s
implement get_self_path() = !g_self_path

(* ============================================================
   String builder helpers
   ============================================================ *)

#pub fun bput_loop {sn:nat}{fuel:nat}  (b: !$B.builder, s: string sn, slen: int sn, i: int, fuel: int fuel): void

implement bput_loop(b, s, slen, i, fuel) =
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

#pub fn bput {sn:nat} (b: !$B.builder, s: string sn): void

implement bput(b, s) = let
  val slen_sz = string1_length(s)
  val slen = g1u2i(slen_sz)
in bput_loop(b, s, slen, 0, $AR.checked_nat(g0ofg1(slen) + 1)) end

#pub fun print_arr {l:agz}{n:pos}{fuel:nat}  (buf: !$A.arr(byte, l, n), i: int, len: int, max: int n,
   fuel: int fuel): void

implement print_arr(buf, i, len, max, fuel) =
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

#pub fun find_null {l:agz}{n:pos}{fuel:nat}  (buf: !$A.arr(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int

implement find_null(buf, pos, max, fuel) =
  if fuel <= 0 then pos
  else let val p = g1ofg0(pos) in
    if p >= 0 then
      if p < max then
        if $AR.eq_int_int(byte2int0($A.get<byte>(buf, p)), 0) then pos
        else find_null(buf, pos + 1, max, fuel - 1)
      else pos
    else pos
  end

#pub fn is_dot_or_dotdot {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool

implement is_dot_or_dotdot(ent, len, max) =
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

(* ============================================================
   Filename matchers
   ============================================================ *)

#pub fun bytes_match {l:agz}{n:pos}{sn:nat}{fuel:nat}  (ent: !$A.arr(byte, l, n), p: int, max: int n,
   pat: string sn, pi: int, plen: int sn, fuel: int fuel): bool

implement bytes_match(ent, p, max, pat, pi, plen, fuel) =
  if fuel <= 0 then pi >= plen
  else if pi >= plen then true
  else let
    val ei = g1ofg0(p + pi)
    val pii = g1ofg0(pi)
  in
    if ei >= 0 then
      if ei < max then
        if pii >= 0 then
          if $AR.lt1_int_int(pii, plen) then
            if $AR.eq_int_int(byte2int0($A.get<byte>(ent, ei)),
                 char2int0(string_get_at(pat, pii))) then
              bytes_match(ent, p, max, pat, pi + 1, plen, fuel - 1)
            else false
          else false
        else false
      else false
    else false
  end

#pub fn has_suffix {l:agz}{n:pos}{sn:nat}
  (ent: !$A.arr(byte, l, n), len: int, max: int n,
   suf: string sn, slen: int sn): bool

implement has_suffix(ent, len, max, suf, slen) =
  if len < slen then false
  else let val p = g1ofg0(len - slen) in
    if p >= 0 then bytes_match(ent, g0ofg1(p), max, suf, 0, slen,
      $AR.checked_nat(slen + 1))
    else false
  end

#pub fn name_eq {l:agz}{n:pos}{sn:nat}
  (ent: !$A.arr(byte, l, n), len: int, max: int n,
   s: string sn, slen: int sn): bool

implement name_eq(ent, len, max, s, slen) =
  if len <> slen then false
  else bytes_match(ent, 0, max, s, 0, slen, $AR.checked_nat(slen + 1))

#pub fn has_bats_ext {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool

implement has_bats_ext(ent, len, max) =
  has_suffix(ent, len, max, ".bats", 5)

#pub fn has_dats_ext {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool

implement has_dats_ext(ent, len, max) =
  has_suffix(ent, len, max, ".dats", 5)

#pub fn has_dats_c_ext {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool

implement has_dats_c_ext(ent, len, max) =
  has_suffix(ent, len, max, "_dats.c", 7)

#pub fn has_dats_o_ext {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool

implement has_dats_o_ext(ent, len, max) =
  has_suffix(ent, len, max, "_dats.o", 7)

#pub fn is_lib_bats {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool

implement is_lib_bats(ent, len, max) =
  name_eq(ent, len, max, "lib.bats", 8)

#pub fn is_lib_dats {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool

implement is_lib_dats(ent, len, max) =
  name_eq(ent, len, max, "lib.dats", 8)

#pub fn is_lib_dats_c {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool

implement is_lib_dats_c(ent, len, max) =
  name_eq(ent, len, max, "lib_dats.c", 10)

#pub fn is_lib_dats_o {l:agz}{n:pos}
  (ent: !$A.arr(byte, l, n), len: int, max: int n): bool

implement is_lib_dats_o(ent, len, max) =
  name_eq(ent, len, max, "lib_dats.o", 10)

(* ============================================================
   Byte-level helpers
   ============================================================ *)

#pub fn src_byte {l:agz}{n:pos}
  (src: !$A.borrow(byte, l, n), pos: int, max: int n): int

implement src_byte(src, pos, max) =
  let val p = g1ofg0(pos) in
    if p >= 0 then
      if p < max then byte2int0($A.read<byte>(src, p))
      else 0
    else 0
  end

#pub fun print_borrow {l:agz}{n:pos}{fuel:nat}  (buf: !$A.borrow(byte, l, n), i: int, len: int, max: int n,
   fuel: int fuel): void

implement print_borrow(buf, i, len, max, fuel) =
  if fuel <= 0 then ()
  else if i >= len then ()
  else let
    val b = src_byte(buf, i, max)
    val () = print_char(int2char0(b))
  in print_borrow(buf, i + 1, len, max, fuel - 1) end

(* ============================================================
   Build pipeline helpers
   ============================================================ *)

#pub fun copy_to_builder {l:agz}{n:pos}{fuel:nat}  (src: !$A.borrow(byte, l, n), start: int, len: int, max: int n,
   dst: !$B.builder, fuel: int fuel): void

implement copy_to_builder(src, start, len, max, dst, fuel) =
  if fuel <= 0 then ()
  else if start >= len then ()
  else let
    val b = src_byte(src, start, max)
    val () = $B.put_byte(dst, b)
  in copy_to_builder(src, start + 1, len, max, dst, fuel - 1) end

#pub fun find_basename_start {l:agz}{n:pos}{fuel:nat}  (bv: !$A.borrow(byte, l, n), pos: int, max: int n,
   last: int, fuel: int fuel): int

implement find_basename_start(bv, pos, max, last, fuel) =
  if fuel <= 0 then last + 1
  else let
    val b = src_byte(bv, pos, max)
  in
    if $AR.eq_int_int(b, 0) then last + 1
    else if $AR.eq_int_int(b, 47) then
      find_basename_start(bv, pos + 1, max, pos, fuel - 1)
    else find_basename_start(bv, pos + 1, max, last, fuel - 1)
  end

#pub fun find_null_bv {l:agz}{n:pos}{fuel:nat}  (bv: !$A.borrow(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int

implement find_null_bv(bv, pos, max, fuel) =
  if fuel <= 0 then pos
  else let
    val b = src_byte(bv, pos, max)
  in
    if $AR.eq_int_int(b, 0) then pos
    else find_null_bv(bv, pos + 1, max, fuel - 1)
  end

#pub fun wbw_loop {l:agz}{fuel:nat}  (bw: !$F.buf_writer, bv: !$A.borrow(byte, l, 524288),
   i: int, lim: int, fuel: int fuel): void

implement wbw_loop(bw, bv, i, lim, fuel) =
  if fuel <= 0 then ()
  else if i >= lim then ()
  else let
    val b = src_byte(bv, i, 524288)
    val wr = $F.buf_write_byte(bw, b)
    val () = $R.discard<int><int>(wr)
  in wbw_loop(bw, bv, i + 1, lim, fuel - 1) end

#pub fn is_newer {l1:agz}{l2:agz}
  (p1: !$A.borrow(byte, l1, 524288), p2: !$A.borrow(byte, l2, 524288)): bool

implement is_newer(p1, p2) = let
  val mt1 = (case+ $F.file_mtime(p1, 524288) of
    | ~$R.ok(t) => t | ~$R.err(_) => ~1): int
  val mt2 = (case+ $F.file_mtime(p2, 524288) of
    | ~$R.ok(t) => t | ~$R.err(_) => ~1): int
in $AR.gt_int_int(mt1, 0) && $AR.gt_int_int(mt1, mt2) end

#pub fn freshness_check_bv
  (out_b: $B.builder, in_b: $B.builder): bool

implement freshness_check_bv(out_b, in_b) = let
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

#pub fun token_eq_arr {l:agz}{ls:agz}{fuel:nat}  (buf: !$A.arr(byte, l, 4096), tstart: int, tend: int,
   sarr: !$A.arr(byte, ls, 4096), si: int, fuel: int fuel): bool

implement token_eq_arr(buf, tstart, tend, sarr, si, fuel) =
  if fuel <= 0 then tstart >= tend
  else if tstart >= tend then
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
            else if $AR.eq_int_int(sb, 0) then false
            else token_eq_arr(buf, tstart + 1, tend, sarr, si + 1, fuel - 1)
          end
          else false
        else false
      else false
    else false
  end

#pub fun arr_range_to_builder {l:agz}{fuel:nat}  (src: !$A.arr(byte, l, 4096), i: int, lim: int,
   dst: !$B.builder, fuel: int fuel): void

implement arr_range_to_builder(src, i, lim, dst, fuel) =
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

#pub fun str_fill_loop {lb:agz}{sn:nat}{fuel:nat}  (b: !$A.arr(byte, lb, 4096), s: string sn, slen: int sn, i: int, fuel: int fuel): void

implement str_fill_loop(b, s, slen, i, fuel) =
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

#pub fn str_to_arr4096 {sn:nat} (s: string sn): [ls:agz] $A.arr(byte, ls, 4096)

implement str_to_arr4096(s) = let
  val b = $A.alloc<byte>(4096)
  val slen_sz = string1_length(s)
  val slen = g1u2i(slen_sz)
  val () = str_fill_loop(b, s, slen, 0, $AR.checked_nat(g0ofg1(slen) + 2))
in
  (if slen < 4096 then $A.set<byte>(b, slen, int2byte0(0))
  else ()); b
end

(* ============================================================
   Process execution
   ============================================================ *)


(* Run a program directly. exec_path is null-terminated path to executable.
   argv_b is a builder with null-separated arguments (consumed).
   argc is the number of arguments.
   Returns exit code or -1 on error. *)
(* Run mkdir -p <path>. path_b is consumed. Returns exit code. *)
#pub fn run_mkdir(path_b: $B.builder): int

implement run_mkdir(path_b) = let
  val () = $B.put_byte(path_b, 0)
  val exec = str_to_path_arr("/bin/mkdir")
  val @(fz_exec, bv_exec) = $A.freeze<byte>(exec)
  val argv = $B.create()
  val () = bput(argv, "mkdir")
  val () = $B.put_byte(argv, 0)
  val () = bput(argv, "-p")
  val () = $B.put_byte(argv, 0)
  val @(pa, pl) = $B.to_arr(path_b)
  val @(fz_p, bv_p) = $A.freeze<byte>(pa)
  val () = copy_to_builder(bv_p, 0, pl, 524288, argv, $AR.checked_nat(pl + 1))
  val () = $A.drop<byte>(fz_p, bv_p)
  val () = $A.free<byte>($A.thaw<byte>(fz_p))
  val rc = run_cmd(bv_exec, 524288, argv, 3)
  val () = $A.drop<byte>(fz_exec, bv_exec)
  val () = $A.free<byte>($A.thaw<byte>(fz_exec))
in rc end

#pub fn run_cmd {le:agz}
  (exec_bv: !$A.borrow(byte, le, 524288), exec_len: int,
   argv_b: $B.builder, argc: int): int

implement run_cmd (exec_bv, exec_len, argv_b, argc) = let
  val @(argv_arr, _) = $B.to_arr(argv_b)
  val @(fz_a, bv_a) = $A.freeze<byte>(argv_arr)
  val envp_b = $B.create()
  val () = bput(envp_b, "PATH=/usr/bin:/usr/local/bin:/bin")
  val () = $B.put_byte(envp_b, 0)
  val @(envp_arr, _) = $B.to_arr(envp_b)
  val @(fz_e, bv_e) = $A.freeze<byte>(envp_arr)
  val sr = $P.spawn(exec_bv, 524288, bv_a, argc, bv_e, 1,
    $P.dev_null(), $P.dev_null(), $P.pipe_new())
  val () = $A.drop<byte>(fz_a, bv_a)
  val () = $A.free<byte>($A.thaw<byte>(fz_a))
  val () = $A.drop<byte>(fz_e, bv_e)
  val () = $A.free<byte>($A.thaw<byte>(fz_e))
in
  case+ sr of
  | ~$R.ok(sp) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = sp
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(sout_p)
      val+ ~$P.pipe_fd(err_fd) = serr_p
      val eb = $A.alloc<byte>(65536)
      val err_r = $F.file_read(err_fd, eb, 65536)
      val elen = (case+ err_r of
        | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val ecr = $F.file_close(err_fd)
      val () = $R.discard<int><int>(ecr)
      val wr = $P.child_wait(child)
      val ec = (case+ wr of
        | ~$R.ok(n) => n | ~$R.err(_) => ~1): int
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

#pub fn run_patsopt {lph:agz}{lo:agz}{li:agz}
  (ph: !$A.borrow(byte, lph, 512), phlen: int,
   out_bv: !$A.borrow(byte, lo, 524288), out_len: int,
   in_bv: !$A.borrow(byte, li, 524288), in_len: int): int

implement run_patsopt(ph, phlen, out_bv, out_len, in_bv, in_len) = let
  val exec_b = $B.create()
  val () = copy_to_builder(ph, 0, phlen, 512, exec_b,
    $AR.checked_nat(phlen + 1))
  val () = bput(exec_b, "/bin/patsopt")
  val @(exec_arr, exec_len) = $B.to_arr(exec_b)
  val @(fz_exec, bv_exec) = $A.freeze<byte>(exec_arr)
  val argv_b = $B.create()
  val () = bput(argv_b, "patsopt")
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "-IATS")
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "build")
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "-IATS")
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "build/src")
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "-IATS")
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "build/bats_modules")
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "-o")
  val () = $B.put_byte(argv_b, 0)
  val out_clen = out_len - 1
  val () = copy_to_builder(out_bv, 0, out_clen, 524288, argv_b,
    $AR.checked_nat(out_len + 1))
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "-d")
  val () = $B.put_byte(argv_b, 0)
  val in_clen = in_len - 1
  val () = copy_to_builder(in_bv, 0, in_clen, 524288, argv_b,
    $AR.checked_nat(in_len + 1))
  val () = $B.put_byte(argv_b, 0)
  val @(argv_arr, _) = $B.to_arr(argv_b)
  val @(fz_a, bv_a) = $A.freeze<byte>(argv_arr)
  val envp_b = $B.create()
  val () = bput(envp_b, "PATSHOME=")
  val () = copy_to_builder(ph, 0, phlen, 512, envp_b,
    $AR.checked_nat(phlen + 1))
  val () = $B.put_byte(envp_b, 0)
  val @(envp_arr, _) = $B.to_arr(envp_b)
  val @(fz_e, bv_e) = $A.freeze<byte>(envp_arr)
  val _verbose = if is_verbose() then 1 else 0
  val () = (if $AR.gt_int_int(_verbose, 0) then let
    val () = print! ("  + patsopt -o ")
    val () = print_borrow(out_bv, 0, out_len, 524288,
      $AR.checked_nat(out_len + 1))
    val () = print! (" -d ")
    val () = print_borrow(in_bv, 0, in_len, 524288,
      $AR.checked_nat(in_len + 1))
  in print_newline() end else ())
  val sr = $P.spawn(bv_exec, 524288, bv_a, 11, bv_e, 1,
    $P.dev_null(), $P.dev_null(), $P.pipe_new())
  val () = $A.drop<byte>(fz_exec, bv_exec)
  val () = $A.free<byte>($A.thaw<byte>(fz_exec))
  val () = $A.drop<byte>(fz_a, bv_a)
  val () = $A.free<byte>($A.thaw<byte>(fz_a))
  val () = $A.drop<byte>(fz_e, bv_e)
  val () = $A.free<byte>($A.thaw<byte>(fz_e))
in
  case+ sr of
  | ~$R.ok(sp) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = sp
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(sout_p)
      val+ ~$P.pipe_fd(err_fd) = serr_p
      (* Read stderr BEFORE waiting — prevents deadlock if child
         writes more than PIPE_BUF (64KB) to stderr *)
      val eb = $A.alloc<byte>(65536)
      val err_r = $F.file_read(err_fd, eb, 65536)
      val elen = (case+ err_r of
        | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val ecr = $F.file_close(err_fd)
      val () = $R.discard<int><int>(ecr)
      val wr = $P.child_wait(child)
      val ec = (case+ wr of
        | ~$R.ok(n) => n | ~$R.err(_) => ~1): int
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

#pub fn run_cc {lph:agz}{lo:agz}{li:agz}
  (ph: !$A.borrow(byte, lph, 512), phlen: int,
   out_bv: !$A.borrow(byte, lo, 524288), out_len: int,
   in_bv: !$A.borrow(byte, li, 524288), in_len: int,
   rel: int): int

implement run_cc(ph, phlen, out_bv, out_len, in_bv, in_len, rel) = let
  val exec_arr = $A.alloc<byte>(11)
  val () = $A.write_byte(exec_arr, 0, 47)
  val () = $A.write_byte(exec_arr, 1, 117)
  val () = $A.write_byte(exec_arr, 2, 115)
  val () = $A.write_byte(exec_arr, 3, 114)
  val () = $A.write_byte(exec_arr, 4, 47)
  val () = $A.write_byte(exec_arr, 5, 98)
  val () = $A.write_byte(exec_arr, 6, 105)
  val () = $A.write_byte(exec_arr, 7, 110)
  val () = $A.write_byte(exec_arr, 8, 47)
  val () = $A.write_byte(exec_arr, 9, 99)
  val () = $A.write_byte(exec_arr, 10, 99)
  val @(fz_exec, bv_exec) = $A.freeze<byte>(exec_arr)
  val argv_b = $B.create()
  val () = bput(argv_b, "cc")
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "-c")
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "-o")
  val () = $B.put_byte(argv_b, 0)
  val cc_out_clen = out_len - 1
  val () = copy_to_builder(out_bv, 0, cc_out_clen, 524288, argv_b,
    $AR.checked_nat(out_len + 1))
  val () = $B.put_byte(argv_b, 0)
  val cc_in_clen = in_len - 1
  val () = copy_to_builder(in_bv, 0, cc_in_clen, 524288, argv_b,
    $AR.checked_nat(in_len + 1))
  val () = $B.put_byte(argv_b, 0)
  val argc = (if rel > 0 then let
    val () = bput(argv_b, "-O2")
    val () = $B.put_byte(argv_b, 0)
  in 8 end
  else let
    val () = bput(argv_b, "-g")
    val () = $B.put_byte(argv_b, 0)
    val () = bput(argv_b, "-O0")
    val () = $B.put_byte(argv_b, 0)
  in 9 end): int
  val () = bput(argv_b, "-I")
  val () = copy_to_builder(ph, 0, phlen, 512, argv_b,
    $AR.checked_nat(phlen + 1))
  val () = $B.put_byte(argv_b, 0)
  val () = bput(argv_b, "-I")
  val () = copy_to_builder(ph, 0, phlen, 512, argv_b,
    $AR.checked_nat(phlen + 1))
  val () = bput(argv_b, "/ccomp/runtime")
  val () = $B.put_byte(argv_b, 0)
  val @(argv_arr, _) = $B.to_arr(argv_b)
  val @(fz_a, bv_a) = $A.freeze<byte>(argv_arr)
  val envp_b = $B.create()
  val () = bput(envp_b, "PATH=/usr/bin:/usr/local/bin:/bin")
  val () = $B.put_byte(envp_b, 0)
  val @(envp_arr, _) = $B.to_arr(envp_b)
  val @(fz_e, bv_e) = $A.freeze<byte>(envp_arr)
  val _verbose = if is_verbose() then 1 else 0
  val () = (if $AR.gt_int_int(_verbose, 0) then let
    val () = print! ("  + cc -c -o ")
    val () = print_borrow(out_bv, 0, out_len, 524288,
      $AR.checked_nat(out_len + 1))
    val () = print! (" ")
    val () = print_borrow(in_bv, 0, in_len, 524288,
      $AR.checked_nat(in_len + 1))
  in print_newline() end else ())
  val sr = $P.spawn(bv_exec, 11, bv_a, argc, bv_e, 1,
    $P.dev_null(), $P.dev_null(), $P.pipe_new())
  val () = $A.drop<byte>(fz_exec, bv_exec)
  val () = $A.free<byte>($A.thaw<byte>(fz_exec))
  val () = $A.drop<byte>(fz_a, bv_a)
  val () = $A.free<byte>($A.thaw<byte>(fz_a))
  val () = $A.drop<byte>(fz_e, bv_e)
  val () = $A.free<byte>($A.thaw<byte>(fz_e))
in
  case+ sr of
  | ~$R.ok(sp) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = sp
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(sout_p)
      val+ ~$P.pipe_fd(err_fd) = serr_p
      (* Read stderr BEFORE waiting — prevents deadlock if child
         writes more than PIPE_BUF (64KB) to stderr *)
      val eb = $A.alloc<byte>(65536)
      val err_r = $F.file_read(err_fd, eb, 65536)
      val elen = (case+ err_r of
        | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val ecr = $F.file_close(err_fd)
      val () = $R.discard<int><int>(ecr)
      val wr = $P.child_wait(child)
      val ec = (case+ wr of
        | ~$R.ok(n) => n | ~$R.err(_) => ~1): int
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

(* ============================================================
   File I/O
   ============================================================ *)

#pub fn write_file_from_builder {lp:agz}{np:pos | np < 1048576}
  (path_bv: !$A.borrow(byte, lp, np), path_len: int np,
   content_b: $B.builder): int

implement write_file_from_builder(path_bv, path_len, content_b) = let
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

#pub fn str_to_path_arr {sn:nat} (s: string sn): [l:agz] $A.arr(byte, l, 524288)

implement str_to_path_arr(s) = let
  val b = $B.create()
  val () = bput(b, s)
  val () = $B.put_byte(b, 0)
  val @(arr, _) = $B.to_arr(b)
in arr end

#pub fn strip_newline_arr {l:agz}
  (buf: !$A.arr(byte, l, 4096), len: int): int

implement strip_newline_arr(buf, len) =
  if len <= 0 then 0
  else let val last = g1ofg0(len - 1) in
    if last >= 0 then
      if last < 4096 then
        (if byte2int0($A.get<byte>(buf, last)) = 10 then len - 1 else len): int
      else len
    else len
  end

#pub fn strip_newline_arr524288 {l:agz}
  (buf: !$A.arr(byte, l, 524288), len: int): int

implement strip_newline_arr524288(buf, len) =
  if len <= 0 then 0
  else let val last = g1ofg0(len - 1) in
    if last >= 0 then
      if last < 524288 then
        (if byte2int0($A.get<byte>(buf, last)) = 10 then len - 1 else len): int
      else len
    else len
  end

#pub fn strip_newline_arr256 {l:agz}
  (buf: !$A.arr(byte, l, 256), len: int): int

implement strip_newline_arr256(buf, len) =
  if len <= 0 then 0
  else let val last = g1ofg0(len - 1) in
    if last >= 0 then
      if last < 256 then
        (if byte2int0($A.get<byte>(buf, last)) = 10 then len - 1 else len): int
      else len
    else len
  end

(* ============================================================
   String constant builders
   ============================================================ *)

#pub fn make_bats_toml {l:agz}{n:pos | n >= 9}
  (buf: !$A.arr(byte, l, n)): void

implement make_bats_toml(buf) =
  let
    val () = $A.write_byte(buf, 0, 98)
    val () = $A.write_byte(buf, 1, 97)
    val () = $A.write_byte(buf, 2, 116)
    val () = $A.write_byte(buf, 3, 115)
    val () = $A.write_byte(buf, 4, 46)
    val () = $A.write_byte(buf, 5, 116)
    val () = $A.write_byte(buf, 6, 111)
    val () = $A.write_byte(buf, 7, 109)
    val () = $A.write_byte(buf, 8, 108)
  in end

#pub fn make_src_bin {l:agz}{n:pos | n >= 7}
  (buf: !$A.arr(byte, l, n)): void

implement make_src_bin(buf) =
  let
    val () = $A.write_byte(buf, 0, 115)
    val () = $A.write_byte(buf, 1, 114)
    val () = $A.write_byte(buf, 2, 99)
    val () = $A.write_byte(buf, 3, 47)
    val () = $A.write_byte(buf, 4, 98)
    val () = $A.write_byte(buf, 5, 105)
    val () = $A.write_byte(buf, 6, 110)
  in end

#pub fn make_package {l:agz}{n:pos | n >= 7}
  (buf: !$A.arr(byte, l, n)): void

implement make_package(buf) =
  let
    val () = $A.write_byte(buf, 0, 112)
    val () = $A.write_byte(buf, 1, 97)
    val () = $A.write_byte(buf, 2, 99)
    val () = $A.write_byte(buf, 3, 107)
    val () = $A.write_byte(buf, 4, 97)
    val () = $A.write_byte(buf, 5, 103)
    val () = $A.write_byte(buf, 6, 101)
  in end

#pub fn make_name {l:agz}{n:pos | n >= 4}
  (buf: !$A.arr(byte, l, n)): void

implement make_name(buf) =
  let
    val () = $A.write_byte(buf, 0, 110)
    val () = $A.write_byte(buf, 1, 97)
    val () = $A.write_byte(buf, 2, 109)
    val () = $A.write_byte(buf, 3, 101)
  in end

#pub fn make_kind {l:agz}{n:pos | n >= 4}
  (buf: !$A.arr(byte, l, n)): void

implement make_kind(buf) =
  let
    val () = $A.write_byte(buf, 0, 107)
    val () = $A.write_byte(buf, 1, 105)
    val () = $A.write_byte(buf, 2, 110)
    val () = $A.write_byte(buf, 3, 100)
  in end

#pub fn make_proc_cmdline {l:agz}{n:pos | n >= 18}
  (buf: !$A.arr(byte, l, n)): void

implement make_proc_cmdline(buf) =
  let
    val () = $A.write_byte(buf, 0, 47)
    val () = $A.write_byte(buf, 1, 112)
    val () = $A.write_byte(buf, 2, 114)
    val () = $A.write_byte(buf, 3, 111)
    val () = $A.write_byte(buf, 4, 99)
    val () = $A.write_byte(buf, 5, 47)
    val () = $A.write_byte(buf, 6, 115)
    val () = $A.write_byte(buf, 7, 101)
    val () = $A.write_byte(buf, 8, 108)
    val () = $A.write_byte(buf, 9, 102)
    val () = $A.write_byte(buf, 10, 47)
    val () = $A.write_byte(buf, 11, 99)
    val () = $A.write_byte(buf, 12, 109)
    val () = $A.write_byte(buf, 13, 100)
    val () = $A.write_byte(buf, 14, 108)
    val () = $A.write_byte(buf, 15, 105)
    val () = $A.write_byte(buf, 16, 110)
    val () = $A.write_byte(buf, 17, 101)
  in end

(* ============================================================
   Argparse helpers
   ============================================================ *)

#pub fun count_argc_loop {l:agz}{n:pos}{fuel:nat}  (buf: !$A.arr(byte, l, n), pos: int, len: int, max: int n,
   count: int, fuel: int fuel): int

implement count_argc_loop(buf, pos, len, max, count, fuel) =
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

#pub fn count_argc {l:agz}
  (buf: !$A.arr(byte, l, 4096), len: int): int

implement count_argc(buf, len) =
  count_argc_loop(buf, 0, len, 4096, 0, $AR.checked_nat(len + 1))

#pub fun fill_exact {l:agz}{n:pos}{sn:nat}{fuel:nat}  (arr: !$A.arr(byte, l, n), s: string sn, n: int n, slen: int sn,
   i: int, fuel: int fuel): void

implement fill_exact(arr, s, n, slen, i, fuel) =
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

#pub fn str_to_borrow {sn:pos}
  (s: string sn): [l:agz][n:pos] @($A.arr(byte, l, n), int n)

implement str_to_borrow(s) = let
  val slen_sz = string1_length(s)
  val slen = g1u2i(slen_sz)
  val n = $AR.checked_arr_size(g0ofg1(slen))
  val arr = $A.alloc<byte>(n)
  val () = fill_exact(arr, s, n, slen, 0, $AR.checked_nat(g0ofg1(slen) + 1))
in @(arr, n) end

#pub fn ap_flag {sn:pos}{sh:pos}
  (p: $AP.parser, name: string sn, sc: int, help: string sh
  ): @($AP.parser, $AP.arg($AP.bool_val))

implement ap_flag(p, name, sc, help) = let
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

#pub fn ap_string_opt {sn:pos}{sh:pos}
  (p: $AP.parser, name: string sn, sc: int, help: string sh
  ): @($AP.parser, $AP.arg($AP.string_val))

implement ap_string_opt(p, name, sc, help) = let
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

#pub fn ap_string_pos {sn:pos}{sh:pos}
  (p: $AP.parser, name: string sn, help: string sh
  ): @($AP.parser, $AP.arg($AP.string_val))

implement ap_string_pos(p, name, help) = let
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
