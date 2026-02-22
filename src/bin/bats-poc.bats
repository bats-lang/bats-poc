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
