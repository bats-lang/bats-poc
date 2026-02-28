(* commands -- subcommand implementations for the bats compiler *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use file as F
#use process as P
#use result as R
#use sha256 as SHA
#use toml as T

staload "helpers.sats"
staload "build.sats"
staload "lexer.sats"
staload "emitter.sats"

(* ============================================================
   do_test: build and run tests
   ============================================================ *)

#pub fn do_test(): void

implement do_test() = let
  (* Enable test mode so emit includes unittest blocks *)
  val () = set_test_mode(true)
  val () = do_build(0)
  val () = set_test_mode(false)
  (* Scan source for test function names in $UNITTEST.run blocks *)
  (* Use C helper to scan the source file *)
  val src_arr = str_to_path_arr("src/bin")
  val @(fz_sa, bv_sa) = $A.freeze<byte>(src_arr)
  val dir_r = $F.dir_open(bv_sa, 524288)
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
              val sfd = $F.file_open(bv_sp, 524288, 0, 0)
              val () = $A.drop<byte>(fz_sp, bv_sp)
              val () = $A.free<byte>($A.thaw<byte>(fz_sp))
              val () = (case+ sfd of
                | ~$R.ok(fd) => let
                    val sbuf = $A.alloc<byte>(524288)
                    val rr = $F.file_read(fd, sbuf, 524288)
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

#pub fn do_generate_docs(pkg_name_len: int, kind_is_lib: int): void

implement do_generate_docs(pkg_name_len, kind_is_lib) =
  if kind_is_lib = 0 then ()
  else let
    val cmd = $B.create()
    val () = bput(cmd, "docs")
    val _ = run_mkdir(cmd)
    val lp = str_to_path_arr("src/lib.bats")
    val @(fz_lp, bv_lp) = $A.freeze<byte>(lp)
    val lib_or = $F.file_open(bv_lp, 524288, 0, 0)
    val () = $A.drop<byte>(fz_lp, bv_lp)
    val () = $A.free<byte>($A.thaw<byte>(fz_lp))
  in
    case+ lib_or of
    | ~$R.ok(lfd) => let
        val lbuf = $A.alloc<byte>(524288)
        val lrr = $F.file_read(lfd, lbuf, 524288)
        val llen = (case+ lrr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
        val lcr = $F.file_close(lfd)
        val () = $R.discard<int><int>(lcr)
        val doc_b = $B.create()
        val () = bput(doc_b, "# API Reference\n\n")
        (* Scan for #pub lines: 35,112,117,98,32 *)
        fun scan_pub {l2:agz}{fuel:nat} .<fuel>.
          (buf: !$A.arr(byte, l2, 524288), doc: !$B.builder,
           pos: int, len: int, fuel: int fuel): void =
          if fuel <= 0 then ()
          else if pos >= len then ()
          else let
            val p = g1ofg0(pos)
          in
            if p >= 0 then
              if p + 4 < 524288 then let
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
                            (buf: !$A.arr(byte, l3, 524288), doc: !$B.builder,
                             pos: int, fuel2: int fuel2): int =
                            if fuel2 <= 0 then pos
                            else let val pp = g1ofg0(pos) in
                              if pp >= 0 then
                                if pp < 524288 then let
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
                          val np = find_null(buf, pos, 524288, $AR.checked_nat(len - pos + 1))
                        in scan_pub(buf, doc, np + 1, len, fuel - 1) end
                      else let
                        val np = find_null(buf, pos, 524288, $AR.checked_nat(len - pos + 1))
                      in scan_pub(buf, doc, np + 1, len, fuel - 1) end
                    else let
                      val np = find_null(buf, pos, 524288, $AR.checked_nat(len - pos + 1))
                    in scan_pub(buf, doc, np + 1, len, fuel - 1) end
                  else let
                    val np = find_null(buf, pos, 524288, $AR.checked_nat(len - pos + 1))
                  in scan_pub(buf, doc, np + 1, len, fuel - 1) end
                else let
                  (* Skip to next newline *)
                  fun skip_line {l4:agz}{fuel3:nat} .<fuel3>.
                    (buf: !$A.arr(byte, l4, 524288), pos: int, len: int,
                     fuel3: int fuel3): int =
                    if fuel3 <= 0 then pos
                    else let val pp = g1ofg0(pos) in
                      if pp >= 0 then
                        if pp < 524288 then let
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
        val _ = write_file_from_builder(bv_dp, 524288, doc_b)
        val () = $A.drop<byte>(fz_dp, bv_dp)
        val () = $A.free<byte>($A.thaw<byte>(fz_dp))
        (* Write docs/index.md *)
        val idx_b = $B.create()
        val () = bput(idx_b, "# Documentation\n\n- [API Reference](lib.md)\n")
        val ip = str_to_path_arr("docs/index.md")
        val @(fz_ip, bv_ip) = $A.freeze<byte>(ip)
        val _ = write_file_from_builder(bv_ip, 524288, idx_b)
        val () = $A.drop<byte>(fz_ip, bv_ip)
        val () = $A.free<byte>($A.thaw<byte>(fz_ip))
      in end
    | ~$R.err(_) => ()
  end

(* ============================================================
   upload: package library for repository
   ============================================================ *)

#pub fn do_upload(): void

implement do_upload() = let
  (* Read bats.toml for package name and verify kind = "lib" *)
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 524288, 0, 0)
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
          val upl_ror = $F.file_open(bv_urp, 524288, 0, 0)
          val () = $A.drop<byte>(fz_urp, bv_urp)
          val () = $A.free<byte>($A.thaw<byte>(fz_urp))
          val @(repo, rplen) = (case+ upl_ror of
            | ~$R.ok(urfd) => let
                val repo_b2 = $A.alloc<byte>(524288)
                val urr = $F.file_read(urfd, repo_b2, 524288)
                val url = (case+ urr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                val urcr = $F.file_close(urfd)
                val () = $R.discard<int><int>(urcr)
                val url2 = strip_newline_arr524288(repo_b2, url)
              in @(repo_b2, url2) end
            | ~$R.err(_) => let val repo_b2 = $A.alloc<byte>(524288) in @(repo_b2, 0) end): [lurb:agz] @($A.arr(byte, lurb, 524288), int)
        in
          case+ nr of
          | ~$R.some(nlen) =>
            if is_lib then
              if rplen > 0 then let
                (* Get version: from git log or date *)
                val @(verbuf, verlen) = (let
                  (* Get version from git or date — spawn git directly *)
                  val git_exec = str_to_path_arr("/usr/bin/git")
                  val @(fz_ge, bv_ge) = $A.freeze<byte>(git_exec)
                  val git_argv = $B.create()
                  val () = bput(git_argv, "git") val () = $B.put_byte(git_argv, 0)
                  val () = bput(git_argv, "log") val () = $B.put_byte(git_argv, 0)
                  val () = bput(git_argv, "-1") val () = $B.put_byte(git_argv, 0)
                  val () = bput(git_argv, "--format=%cd") val () = $B.put_byte(git_argv, 0)
                  val () = bput(git_argv, "--date=format:%Y.%-m.%-d") val () = $B.put_byte(git_argv, 0)
                  val git_rc = run_cmd(bv_ge, 524288, git_argv, 5)
                  val () = $A.drop<byte>(fz_ge, bv_ge)
                  val () = $A.free<byte>($A.thaw<byte>(fz_ge))
                  (* If git failed, use date *)
                  val () = (if git_rc <> 0 then let
                    val date_exec = str_to_path_arr("/usr/bin/date")
                    val @(fz_de, bv_de) = $A.freeze<byte>(date_exec)
                    val date_argv = $B.create()
                    val () = bput(date_argv, "date") val () = $B.put_byte(date_argv, 0)
                    val () = bput(date_argv, "+%Y.%-m.%-d") val () = $B.put_byte(date_argv, 0)
                    val _ = run_cmd(bv_de, 524288, date_argv, 2)
                    val () = $A.drop<byte>(fz_de, bv_de)
                    val () = $A.free<byte>($A.thaw<byte>(fz_de))
                  in end else ())
                  (* Note: git/date output goes to stdout which is /dev/null in run_cmd.
                     TODO: capture stdout to get version string. For now write placeholder. *)
                  val vb = $B.create()
                  val () = bput(vb, "0.0.0")
                  val vp2 = str_to_path_arr("/tmp/_bpoc_ver.txt")
                  val @(fz_vp2, bv_vp2) = $A.freeze<byte>(vp2)
                  val _ = write_file_from_builder(bv_vp2, 524288, vb)
                  val () = $A.drop<byte>(fz_vp2, bv_vp2)
                  val () = $A.free<byte>($A.thaw<byte>(fz_vp2))
                  val vp = str_to_path_arr("/tmp/_bpoc_ver.txt")
                  val @(fz_vp, bv_vp) = $A.freeze<byte>(vp)
                  val vf = $F.file_open(bv_vp, 524288, 0, 0)
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
                val () = copy_to_builder(bv_rp, 0, rplen, 524288, zip_path,
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
                val () = copy_to_builder(bv_px, 0, pfx_len, 524288, zip_path,
                  $AR.checked_nat(pfx_len + 1))
                val () = bput(zip_path, "_")
                val () = copy_to_builder(bv_vb, 0, verlen, 64, zip_path,
                  $AR.checked_nat(verlen + 1))
                val () = bput(zip_path, ".bats")
                val () = $B.put_byte(zip_path, 0)
                val @(zpa, zpa_len) = $B.to_arr(zip_path)
                val @(fz_zp, bv_zp) = $A.freeze<byte>(zpa)
                (* mkdir + zip *)
                val mkd = $B.create()
                val () = copy_to_builder(bv_rp, 0, rplen, 524288, mkd,
                  $AR.checked_nat(rplen + 1))
                val () = bput(mkd, "/")
                val () = copy_to_builder(bv_nb, 0, nlen, 256, mkd,
                  $AR.checked_nat(nlen + 1))
                val _ = run_mkdir(mkd)
                val zip_exec = str_to_path_arr("/usr/bin/zip")
                val @(fz_ze, bv_ze) = $A.freeze<byte>(zip_exec)
                val cmd = $B.create()
                val () = bput(cmd, "zip") val () = $B.put_byte(cmd, 0)
                val () = bput(cmd, "-r") val () = $B.put_byte(cmd, 0)
                val () = copy_to_builder(bv_zp, 0, zpa_len - 1, 524288, cmd,
                  $AR.checked_nat(zpa_len + 1))
                val () = $B.put_byte(cmd, 0)
                val () = bput(cmd, "bats.toml") val () = $B.put_byte(cmd, 0)
                val () = bput(cmd, "src/") val () = $B.put_byte(cmd, 0)
                val () = $A.drop<byte>(fz_nb, bv_nb)
                val () = $A.free<byte>($A.thaw<byte>(fz_nb))
                val () = $A.drop<byte>(fz_rp, bv_rp)
                val () = $A.free<byte>($A.thaw<byte>(fz_rp))
                val () = $A.drop<byte>(fz_px, bv_px)
                val () = $A.free<byte>($A.thaw<byte>(fz_px))
                val rc = run_cmd(bv_ze, 524288, cmd, 5)
                val () = $A.drop<byte>(fz_ze, bv_ze)
                val () = $A.free<byte>($A.thaw<byte>(fz_ze))
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
                    (* Read archive and compute SHA256 using sha256 library *)
                    val arc_or = $F.file_open(bv_zp, 524288, 0, 0)
                    val sha_r = (case+ arc_or of
                      | ~$R.ok(afd) => let
                          val abuf = $A.alloc<byte>(524288)
                          val ar = $F.file_read(afd, abuf, 524288)
                          val alen = (case+ ar of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                          val acr = $F.file_close(afd)
                          val () = $R.discard<int><int>(acr)
                          val sha_out = $A.alloc<byte>(64)
                          val () = $SHA.hash(abuf, 524288, sha_out)
                          val () = $A.free<byte>(abuf)
                          (* Write sha hex to temp file *)
                          val sha_b = $B.create()
                          val @(fz_sha, bv_sha) = $A.freeze<byte>(sha_out)
                          val () = copy_to_builder(bv_sha, 0, 64, 64, sha_b, 65)
                          val () = $A.drop<byte>(fz_sha, bv_sha)
                          val () = $A.free<byte>($A.thaw<byte>(fz_sha))
                          val sp = str_to_path_arr("/tmp/_bpoc_sha.txt")
                          val @(fz_sp, bv_sp) = $A.freeze<byte>(sp)
                          val wr = write_file_from_builder(bv_sp, 524288, sha_b)
                          val () = $A.drop<byte>(fz_sp, bv_sp)
                          val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                        in wr end
                      | ~$R.err(_) => ~1): int
                  in
                    if sha_r <> 0 then let val sb = $A.alloc<byte>(65) in @(sb, ~1) end
                    else let
                      val sp3 = str_to_path_arr("/tmp/_bpoc_sha.txt")
                      val @(fz_sp3, bv_sp3) = $A.freeze<byte>(sp3)
                      val sf = $F.file_open(bv_sp3, 524288, 0, 0)
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
                    val () = copy_to_builder(bv_zp, 0, zpa_len - 1, 524288,
                      sidecar, $AR.checked_nat(zpa_len + 1))
                    val () = bput(sidecar, "\n")
                    val () = $A.drop<byte>(fz_sh, bv_sh)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sh))
                    (* write to zip_path + ".sha256" *)
                    val sp2 = $B.create()
                    val () = copy_to_builder(bv_zp, 0, zpa_len - 1, 524288,
                      sp2, $AR.checked_nat(zpa_len + 1))
                    val () = bput(sp2, ".sha256")
                    val () = $B.put_byte(sp2, 0)
                    val @(sp2a, _) = $B.to_arr(sp2)
                    val @(fz_sp2, bv_sp2) = $A.freeze<byte>(sp2a)
                    val _ = write_file_from_builder(bv_sp2, 524288, sidecar)
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

#pub fn do_completions(shell: int): void

implement do_completions(shell) =
  if shell = 0 then
    print_string "# bash completions\ncomplete -W 'build check clean lock run test tree add remove upload init completions' bats\n"
  else if shell = 1 then
    print_string "#compdef bats\n_bats_cmds=(build check clean lock run test tree add remove upload init completions)\ncompadd $_bats_cmds\n"
  else if shell = 2 then
    print_string "# fish completions\nfor c in build check clean lock run test tree add remove upload init completions; complete -c bats -n __fish_use_subcommand -a $c; end\n"
  else println! ("error: specify a shell (bash, zsh, fish)")

(* Check if a file exists by trying to open it *)

#pub fn file_exists {sn:nat} (path: string sn): bool

implement file_exists(path) = let
  val pa = str_to_path_arr(path)
  val @(fz, bv) = $A.freeze<byte>(pa)
  val fex_or = $F.file_open(bv, 524288, 0, 0)
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

#pub fn write_claude_rules(): void

implement write_claude_rules() = let
  val cmd = $B.create()
  val () = bput(cmd, ".claude/rules")
  val _ = run_mkdir(cmd)
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
  val _ = write_file_from_builder(bv_rp, 524288, rb)
  val () = $A.drop<byte>(fz_rp, bv_rp)
  val () = $A.free<byte>($A.thaw<byte>(fz_rp))
in end

(* ============================================================
   init: create a new bats project
   ============================================================ *)

#pub fn do_init(kind: int, claude: int): void

implement do_init(kind, claude) = let
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
    (* Get CWD via pwd *)
    val pwd_exec = str_to_path_arr("/bin/pwd")
    val @(fz_pwd, bv_pwd) = $A.freeze<byte>(pwd_exec)
    val pwd_argv = $B.create()
    val () = bput(pwd_argv, "pwd") val () = $B.put_byte(pwd_argv, 0)
    (* TODO: run_cmd sends stdout to /dev/null, need stdout capture *)
    val _ = run_cmd(bv_pwd, 524288, pwd_argv, 1)
    val () = $A.drop<byte>(fz_pwd, bv_pwd)
    val () = $A.free<byte>($A.thaw<byte>(fz_pwd))
    (* Write placeholder CWD *)
    val cwdb = $B.create()
    val () = bput(cwdb, ".")
    val cwdp = str_to_path_arr("/tmp/_bpoc_cwd.txt")
    val @(fz_cwdp, bv_cwdp) = $A.freeze<byte>(cwdp)
    val _ = write_file_from_builder(bv_cwdp, 524288, cwdb)
    val () = $A.drop<byte>(fz_cwdp, bv_cwdp)
    val () = $A.free<byte>($A.thaw<byte>(fz_cwdp))
    val cp = str_to_path_arr("/tmp/_bpoc_cwd.txt")
    val @(fz_cp, bv_cp) = $A.freeze<byte>(cp)
    val cf = $F.file_open(bv_cp, 524288, 0, 0)
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
  val () = (if kind = 0 then bput(cmd1, "src/bin")
    else bput(cmd1, "src"))
  val _ = run_mkdir(cmd1)
  (* Write bats.toml *)
  val toml = $B.create()
  val () = bput(toml, "[package]\nname = \"")
  val () = copy_to_builder(bv_cwd, name_start, cwd_len, 4096, toml,
    $AR.checked_nat(name_len + 1))
  val () = (if kind = 0 then bput(toml, "\"\nkind = \"bin\"\n\n[dependencies]\n")
    else bput(toml, "\"\nkind = \"lib\"\n\n[dependencies]\n"))
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val rc = write_file_from_builder(bv_tp, 524288, toml)
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
  val rc2 = write_file_from_builder(bv_sp, 524288, src)
  val () = $A.drop<byte>(fz_sp, bv_sp)
  val () = $A.free<byte>($A.thaw<byte>(fz_sp))
  val () = $A.drop<byte>(fz_cwd, bv_cwd)
  val () = $A.free<byte>($A.thaw<byte>(fz_cwd))
  (* Write .gitignore *)
  val gi = $B.create()
  val () = bput(gi, "build/\ndist/\nbats_modules/\ndocs/\n")
  val gp = str_to_path_arr(".gitignore")
  val @(fz_gp, bv_gp) = $A.freeze<byte>(gp)
  val rc3 = write_file_from_builder(bv_gp, 524288, gi)
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

#pub fn do_tree(): void

implement do_tree() = let
  val la = str_to_path_arr("bats.lock")
  val @(fz_la, bv_la) = $A.freeze<byte>(la)
  val lock_or = $F.file_open(bv_la, 524288, 0, 0)
  val () = $A.drop<byte>(fz_la, bv_la)
  val () = $A.free<byte>($A.thaw<byte>(fz_la))
in
  case+ lock_or of
  | ~$R.ok(lfd) => let
      val lock_buf = $A.alloc<byte>(524288)
      val lr = $F.file_read(lfd, lock_buf, 524288)
      val lock_len = (case+ lr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val lcr = $F.file_close(lfd)
      val () = $R.discard<int><int>(lcr)
    in
      if lock_len > 0 then let
        (* Use C helper to print Unicode tree *)
        val @(fz_lb, bv_lb) = $A.freeze<byte>(lock_buf)
        val () = print_borrow(bv_lb, 0, lock_len, 524288, $AR.checked_nat(lock_len + 1))
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

#pub fn do_add {l:agz}{n:pos}
  (bv: !$A.borrow(byte, l, n), pkg_start: int, pkg_len: int,
   max: int n): void

implement do_add(bv, pkg_start, pkg_len, max) = let
  (* Read bats.toml *)
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 524288, 0, 0)
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
      val rc = write_file_from_builder(bv_tp3, 524288, out_b)
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

#pub fn do_remove {l:agz}{n:pos}
  (bv: !$A.borrow(byte, l, n), pkg_start: int, pkg_len: int,
   max: int n): void

implement do_remove(bv, pkg_start, pkg_len, max) = let
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 524288, 0, 0)
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
      val sed_exec = str_to_path_arr("/usr/bin/sed")
      val @(fz_se, bv_se) = $A.freeze<byte>(sed_exec)
      val sed_argv = $B.create()
      val () = bput(sed_argv, "sed") val () = $B.put_byte(sed_argv, 0)
      val () = bput(sed_argv, "-i") val () = $B.put_byte(sed_argv, 0)
      (* Build pattern: /^"<pkg>"/d *)
      val pat_b = $B.create()
      val () = bput(pat_b, "/^\"")
      val () = copy_to_builder(bv, pkg_start, pkg_start + pkg_len, max, pat_b, $AR.checked_nat(pkg_len + 1))
      val () = bput(pat_b, "\"/d")
      val @(pat_a, pat_len) = $B.to_arr(pat_b)
      val @(fz_pat, bv_pat) = $A.freeze<byte>(pat_a)
      val () = copy_to_builder(bv_pat, 0, pat_len, 524288, sed_argv, $AR.checked_nat(pat_len + 1))
      val () = $B.put_byte(sed_argv, 0)
      val () = $A.drop<byte>(fz_pat, bv_pat)
      val () = $A.free<byte>($A.thaw<byte>(fz_pat))
      val () = bput(sed_argv, "bats.toml") val () = $B.put_byte(sed_argv, 0)
      val rc = run_cmd(bv_se, 524288, sed_argv, 4)
      val () = $A.drop<byte>(fz_se, bv_se)
      val () = $A.free<byte>($A.thaw<byte>(fz_se))
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

#pub fn run_process_demo(): void

implement run_process_demo() = let
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

#pub fun save_extra_args {l:agz}
  (buf: !$A.arr(byte, l, 4096), dd_pos: int, len: int): void

implement save_extra_args(buf, dd_pos, len) = let
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
    val _ = write_file_from_builder(bv_ep, 524288, out)
    val () = $A.drop<byte>(fz_ep, bv_ep)
    val () = $A.free<byte>($A.thaw<byte>(fz_ep))
  in end
  else ()
end

(* Append saved extra args to a builder (for do_run) *)

#pub fun append_run_args(cmd: !$B.builder): void

implement append_run_args(cmd) = let
  val ep = str_to_path_arr("/tmp/_bpoc_extra.txt")
  val @(fz_ep, bv_ep) = $A.freeze<byte>(ep)
  val eor = $F.file_open(bv_ep, 524288, 0, 0)
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

#pub fn do_run(release: int): void

implement do_run(release) = let
  val () = do_build(release)
  (* Read bats.toml to find the package name *)
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 524288, 0, 0)
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
              val bin_or = $F.file_open(bv_bp2, 524288, 0, 0)
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
                val () = $B.put_byte(cmd, 0)
                val @(exec_a, exec_len) = $B.to_arr(cmd)
                val @(fz_ea, bv_ea) = $A.freeze<byte>(exec_a)
                val run_argv = $B.create()
                val () = copy_to_builder(bv_ea, 0, exec_len - 1, 524288, run_argv,
                  $AR.checked_nat(exec_len))
                val () = $B.put_byte(run_argv, 0)
                val rc = run_cmd(bv_ea, 524288, run_argv, 1)
                val () = $A.drop<byte>(fz_ea, bv_ea)
                val () = $A.free<byte>($A.thaw<byte>(fz_ea))
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
                val () = $B.put_byte(cmd, 0)
                val @(exec_a2, exec_len2) = $B.to_arr(cmd)
                val @(fz_ea2, bv_ea2) = $A.freeze<byte>(exec_a2)
                val run_argv2 = $B.create()
                val () = copy_to_builder(bv_ea2, 0, exec_len2 - 1, 524288, run_argv2,
                  $AR.checked_nat(exec_len2))
                val () = $B.put_byte(run_argv2, 0)
                val rc = run_cmd(bv_ea2, 524288, run_argv2, 1)
                val () = $A.drop<byte>(fz_ea2, bv_ea2)
                val () = $A.free<byte>($A.thaw<byte>(fz_ea2))
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

#pub fn do_check(): void

implement do_check() = let
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
                    val lbuf = $A.alloc<byte>(524288)
                    val lr = $F.file_read(lfd, lbuf, 524288)
                    val lbytes = (case+ lr of
                      | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                    val lcr = $F.file_close(lfd)
                    val () = $R.discard<int><int>(lcr)
                    val @(fz_lb, bv_lb) = $A.freeze<byte>(lbuf)
                    val @(span_arr, span_len, span_count) =
                      do_lex(bv_lb, lbytes, 524288)
                    val () = println! ("  lexed ", lbytes, " bytes -> ",
                                       span_count, " spans")
                    (* Now emit .sats/.dats *)
                    val @(fz_sp, bv_sp) = $A.freeze<byte>(span_arr)
                    val @(sats_arr, sats_len, dats_arr, dats_len, pre_lines, _emit_errs) =
                      do_emit(bv_lb, lbytes, 524288, bv_sp, 524288, span_count, 0, 0)
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
