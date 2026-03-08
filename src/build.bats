(* build -- build pipeline for the bats compiler *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use env as E
#use str as S
#use file as F
#use process as P
#use result as R
#use toml as T

staload "helpers.sats"
staload "lexer.sats"
staload "emitter.sats"

(* Preprocess one .bats file: read -> lex -> emit -> write .sats + .dats
   All three path borrows must be null-terminated builder arrays (524288) *)
#pub fn preprocess_one
  {l1:agz}{l2:agz}{l3:agz}
  (src_bv: !$A.borrow(byte, l1, 524288),
   sats_bv: !$A.borrow(byte, l2, 524288),
   dats_bv: !$A.borrow(byte, l3, 524288),
   build_target: int, is_unsafe: int,
   target_changed: bool): int

implement preprocess_one
  (src_bv, sats_bv, dats_bv, build_target, is_unsafe, target_changed) = let
  (* Cache check: if .sats is newer than .bats source AND target hasn't changed,
     skip preprocessing *)
  val fresh = (if is_newer(sats_bv, src_bv) then ~target_changed else false): bool
in
  if fresh then 0
  else let
  val or = $F.file_open(src_bv, 524288, 0, 0)
in
  case+ or of
  | ~$R.ok(fd) => let
      val buf = $A.alloc<byte>(524288)
      val rr = $F.file_read(fd, buf, 524288)
      val nbytes = (case+ rr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val cr = $F.file_close(fd)
      val () = $R.discard<int><int>(cr)
      val @(fz_src, bv_src) = $A.freeze<byte>(buf)
      val @(span_arr, _span_len, span_count) = do_lex(bv_src, nbytes, 524288)
      val @(fz_sp, bv_sp) = $A.freeze<byte>(span_arr)
      val @(sats_arr, sats_len, dats_arr, dats_len, _pre, safety_errors) =
        do_emit(bv_src, nbytes, 524288, bv_sp, 524288, span_count, build_target, is_unsafe)
      val () = $A.drop<byte>(fz_sp, bv_sp)
      val () = $A.free<byte>($A.thaw<byte>(fz_sp))
      val () = $A.drop<byte>(fz_src, bv_src)
      val () = $A.free<byte>($A.thaw<byte>(fz_src))
      (* Write .sats *)
      var sb : $B.builder_v = $B.create()
      val @(fz_s, bv_s) = $A.freeze<byte>(sats_arr)
      val () = copy_to_builder_v(bv_s, 0, sats_len, 524288, sb)
      val () = $A.drop<byte>(fz_s, bv_s)
      val () = $A.free<byte>($A.thaw<byte>(fz_s))
      val r1 = write_file_from_builder(sats_bv, 524288, sb)
      (* Write .dats - prepend self-staload *)
      var db : $B.builder_v = $B.create()
      val bn_start = find_basename_start(sats_bv, 0, 524288, ~1, 4096)
      val bn_end = $S.find_null_bv(sats_bv, bn_start, 524288, 4096)
      val () = bput_v(db, "staload \"./")
      val () = copy_to_builder_v(sats_bv, bn_start, bn_end, 524288, db)
      val () = bput_v(db, "\"\n")
      val @(fz_d, bv_d) = $A.freeze<byte>(dats_arr)
      val () = copy_to_builder_v(bv_d, 0, dats_len, 524288, db)
      val () = $A.drop<byte>(fz_d, bv_d)
      val () = $A.free<byte>($A.thaw<byte>(fz_d))
      val r2 = write_file_from_builder(dats_bv, 524288, db)
    in
      if safety_errors > 0 then safety_errors
      else if r1 = 0 then (if r2 = 0 then 0 else ~1) else ~1
    end
  | ~$R.err(_) => ~1
end end

(* ============================================================
   Helpers: run patsopt/cc on all extra .dats/.c files in a dir
   ============================================================ *)

(* Run patsopt on all non-lib .dats files in a build src dir.
   dir_bv: null-terminated path like "build/bats_modules/foo/src" *)
fn patsopt_dir_extra
  {ld:agz}{lph:agz}
  (dir_bv: !$A.borrow(byte, ld, 524288), dir_len: int,
   ph: !$A.borrow(byte, lph, 512), phlen: int): void = let
  val dr = $F.dir_open(dir_bv, 524288)
in case+ dr of
  | ~$R.ok(d) => let
      fun loop {fuel:nat} .<fuel>.
        (d: !$F.dir,
         dir_bv: !$A.borrow(byte, ld, 524288), dir_len: int,
         ph: !$A.borrow(byte, lph, 512), phlen: int,
         fuel: int fuel): void =
        if fuel <= 0 then ()
        else let
          val e = $A.alloc<byte>(256)
          val nr = $F.dir_next(d, e, 256)
          val el = $R.option_unwrap_or<int>(nr, ~1)
        in if el < 0 then $A.free<byte>(e)
          else let
            val is_d = has_dats_ext(e, el, 256)
            val is_l = is_lib_dats(e, el, 256)
          in if is_d then
            if is_l then let val () = $A.free<byte>(e)
            in loop(d, dir_bv, dir_len, ph, phlen, fuel - 1) end
            else let
              val stem = el - 5
              val @(fz_e, bv_e) = $A.freeze<byte>(e)
              val dl = dir_len - 1
              var ob : $B.builder_v = $B.create()
              val () = copy_to_builder_v(dir_bv, 0, dl, 524288, ob)
              val () = bput_v(ob, "/")
              val () = copy_to_builder_v(bv_e, 0, stem, 256, ob)
              val () = bput_v(ob, "_dats.c")
              val () = put_char_v(ob, 0)
              val @(oa, ol) = $B.to_arr(ob)
              val @(fz_o, bv_o) = $A.freeze<byte>(oa)
              var ib : $B.builder_v = $B.create()
              val () = copy_to_builder_v(dir_bv, 0, dl, 524288, ib)
              val () = bput_v(ib, "/")
              val () = copy_to_builder_v(bv_e, 0, el, 256, ib)
              val () = put_char_v(ib, 0)
              val @(ia, il) = $B.to_arr(ib)
              val @(fz_i, bv_i) = $A.freeze<byte>(ia)
              val _ = run_patsopt(ph, phlen, bv_o, ol, bv_i, il)
              val () = $A.drop<byte>(fz_o, bv_o)
              val () = $A.free<byte>($A.thaw<byte>(fz_o))
              val () = $A.drop<byte>(fz_i, bv_i)
              val () = $A.free<byte>($A.thaw<byte>(fz_i))
              val () = $A.drop<byte>(fz_e, bv_e)
              val () = $A.free<byte>($A.thaw<byte>(fz_e))
            in loop(d, dir_bv, dir_len, ph, phlen, fuel - 1) end
          else let val () = $A.free<byte>(e)
          in loop(d, dir_bv, dir_len, ph, phlen, fuel - 1) end
          end
        end
      val () = loop(d, dir_bv, dir_len, ph, phlen, 200)
      val dcr = $F.dir_close(d)
      val () = $R.discard<int><int>(dcr)
    in end
  | ~$R.err(_) => ()
end

(* Run cc on all non-lib _dats.c files in a build src dir. *)
fn cc_dir_extra
  {ld:agz}{lph:agz}
  (dir_bv: !$A.borrow(byte, ld, 524288), dir_len: int,
   ph: !$A.borrow(byte, lph, 512), phlen: int,
   rel: int): void = let
  val dr = $F.dir_open(dir_bv, 524288)
in case+ dr of
  | ~$R.ok(d) => let
      fun loop {fuel:nat} .<fuel>.
        (d: !$F.dir,
         dir_bv: !$A.borrow(byte, ld, 524288), dir_len: int,
         ph: !$A.borrow(byte, lph, 512), phlen: int,
         rel: int, fuel: int fuel): void =
        if fuel <= 0 then ()
        else let
          val e = $A.alloc<byte>(256)
          val nr = $F.dir_next(d, e, 256)
          val el = $R.option_unwrap_or<int>(nr, ~1)
        in if el < 0 then $A.free<byte>(e)
          else let
            val is_c = $S.has_suffix(e, el, 256, "_dats.c", 7)
          in if ~is_c then let val () = $A.free<byte>(e)
            in loop(d, dir_bv, dir_len, ph, phlen, rel, fuel - 1) end
          else let
            val is_l = $S.has_suffix(e, el, 256, "lib_dats.c", 10)
          in if is_l then let val () = $A.free<byte>(e)
            in loop(d, dir_bv, dir_len, ph, phlen, rel, fuel - 1) end
            else let
              val stem = el - 2
              val @(fz_e, bv_e) = $A.freeze<byte>(e)
              val dl = dir_len - 1
              var ob : $B.builder_v = $B.create()
              val () = copy_to_builder_v(dir_bv, 0, dl, 524288, ob)
              val () = bput_v(ob, "/")
              val () = copy_to_builder_v(bv_e, 0, stem, 256, ob)
              val () = bput_v(ob, ".o")
              val () = put_char_v(ob, 0)
              val @(oa, ol) = $B.to_arr(ob)
              val @(fz_o, bv_o) = $A.freeze<byte>(oa)
              var ib : $B.builder_v = $B.create()
              val () = copy_to_builder_v(dir_bv, 0, dl, 524288, ib)
              val () = bput_v(ib, "/")
              val () = copy_to_builder_v(bv_e, 0, el, 256, ib)
              val () = put_char_v(ib, 0)
              val @(ia, il) = $B.to_arr(ib)
              val @(fz_i, bv_i) = $A.freeze<byte>(ia)
              val _ = run_cc(ph, phlen, bv_o, ol, bv_i, il, rel)
              val () = $A.drop<byte>(fz_o, bv_o)
              val () = $A.free<byte>($A.thaw<byte>(fz_o))
              val () = $A.drop<byte>(fz_i, bv_i)
              val () = $A.free<byte>($A.thaw<byte>(fz_i))
              val () = $A.drop<byte>(fz_e, bv_e)
              val () = $A.free<byte>($A.thaw<byte>(fz_e))
            in loop(d, dir_bv, dir_len, ph, phlen, rel, fuel - 1) end
            end
          end
        end
      val () = loop(d, dir_bv, dir_len, ph, phlen, rel, 200)
      val dcr = $F.dir_close(d)
      val () = $R.discard<int><int>(dcr)
    in end
  | ~$R.err(_) => ()
end

(* ============================================================
   clean: remove build/ and dist/ directories
   ============================================================ *)
#pub fn do_clean(): void

implement do_clean() = let
  val exec = str_to_path_arr("/bin/rm")
  val @(fz_exec, bv_exec) = $A.freeze<byte>(exec)
  var argv : $B.builder_v = $B.create()
  val () = bput_v(argv, "rm") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-rf") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "build") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "dist") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "docs") val () = put_char_v(argv, 0)
  val rc = run_cmd(bv_exec, 524288, argv, 5)
  val () = $A.drop<byte>(fz_exec, bv_exec)
  val () = $A.free<byte>($A.thaw<byte>(fz_exec))
in
  if rc <> 0 then println! ("error: clean failed")
  else if ~is_quiet() then println! ("cleaned build/, dist/, and docs/")
  else ()
end

(* ============================================================
   lock: read bats.lock and verify it exists
   ============================================================ *)
#pub fn do_lock(dev: int, dry_run: int): void

implement do_lock(dev, dry_run) = let
  (* Check if --repository was specified (stored in /tmp/_bpoc_repo.txt) *)
  val repo_path = str_to_path_arr("/tmp/_bpoc_repo.txt")
  val @(fz_rp2, bv_rp2) = $A.freeze<byte>(repo_path)
  val repo_or = $F.file_open(bv_rp2, 524288, 0, 0)
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
    (* Native lock resolution: read bats.toml deps, find in repo, unzip, write lock *)
    val @(fz_rb3, bv_rb3) = $A.freeze<byte>(repo_buf)
    val bt = str_to_path_arr("bats.toml")
    val @(fz_bt, bv_bt) = $A.freeze<byte>(bt)
    val bt_or = $F.file_open(bv_bt, 524288, 0, 0)
    val () = $A.drop<byte>(fz_bt, bv_bt)
    val () = $A.free<byte>($A.thaw<byte>(fz_bt))
    val () = (case+ bt_or of
      | ~$R.ok(btfd) => let
          val tbl = $A.alloc<byte>(4096)
          val tr = $F.file_read(btfd, tbl, 4096)
          val tl = (case+ tr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
          val tcr = $F.file_close(btfd)
          val () = $R.discard<int><int>(tcr)
          val @(fz_tbl, bv_tbl) = $A.freeze<byte>(tbl)
          val pr = $T.parse(bv_tbl, 4096)
          val () = $A.drop<byte>(fz_tbl, bv_tbl)
          val () = $A.free<byte>($A.thaw<byte>(fz_tbl))
        in case+ pr of
          | ~$R.ok(doc) => let
              val @(dk, dk_sz) = $S.str_to_borrow("dependencies")
              val @(fz_dk, bv_dk) = $A.freeze<byte>(dk)
              val keys = $A.alloc<byte>(4096)
              val kr = $T.keys(doc, bv_dk, dk_sz, keys, 4096)
              val klen = (case+ kr of | ~$R.some(n) => n | ~$R.none() => 0): int
              val () = $A.drop<byte>(fz_dk, bv_dk)
              val () = $A.free<byte>($A.thaw<byte>(fz_dk))
              var mbb : $B.builder_v = $B.create()
              val () = bput_v(mbb, "bats_modules")
              val _ = run_mkdir(mbb)
              var lock_b : $B.builder_v = $B.create()
              (* Resolve each dependency *)
              fun resolve {lk:agz}{lr:agz}{fuel:nat} .<fuel>.
                (ks: !$A.arr(byte, lk, 4096), pos: int, kl: int,
                 rb: !$A.borrow(byte, lr, 4096), rl: int,
                 lb: !$B.builder_v >> $B.builder_v, cnt: int, fuel: int fuel): int =
                if fuel <= 0 then cnt
                else if pos >= kl then cnt
                else let
                  val de = $S.find_null(ks, pos, 4096, 4096)
                  val dl = de - pos
                in if dl <= 0 then resolve(ks, de + 1, kl, rb, rl, lb, cnt, fuel - 1)
                  else let
                    (* Strip quotes from key name *)
                    val first_byte = (if pos >= 0 then if pos < 4096 then
                      byte2int0($A.get<byte>(ks, $AR.checked_idx(pos, 4096))) else 0 else 0): int
                    val dep_start = (if $AR.eq_int_int(first_byte, 34) then pos + 1 else pos): int
                    val last_byte = (if de - 1 >= 0 then if de - 1 < 4096 then
                      byte2int0($A.get<byte>(ks, $AR.checked_idx(de - 1, 4096))) else 0 else 0): int
                    val dep_end = (if $AR.eq_int_int(last_byte, 34) then de - 1 else de): int
                    val dl = dep_end - dep_start
                    (* Check if already resolved: bats_modules/<dep>/bats.toml exists *)
                    var chk_b : $B.builder_v = $B.create()
                    val () = bput_v(chk_b, "bats_modules/")
                    val () = arr_range_to_builder_v(ks, dep_start, dep_end, chk_b)
                    val () = bput_v(chk_b, "/bats.toml")
                    val () = put_char_v(chk_b, 0)
                    val @(chk_a, _) = $B.to_arr(chk_b)
                    val @(fz_chk, bv_chk) = $A.freeze<byte>(chk_a)
                    val chk_or = $F.file_open(bv_chk, 524288, 0, 0)
                    val () = $A.drop<byte>(fz_chk, bv_chk)
                    val () = $A.free<byte>($A.thaw<byte>(fz_chk))
                    val already = (case+ chk_or of
                      | ~$R.ok(cfd) => let
                          val cr = $F.file_close(cfd)
                          val () = $R.discard<int><int>(cr)
                        in true end
                      | ~$R.err(_) => false): bool
                  in if already then resolve(ks, de+1, kl, rb, rl, lb, cnt, fuel-1)
                  else let
                    (* Scan repo/<dep>/ for latest .bats archive *)
                    var dir_b : $B.builder_v = $B.create()
                    val () = copy_to_builder_v(rb, 0, rl, 4096, dir_b)
                    val () = bput_v(dir_b, "/")
                    val () = arr_range_to_builder_v(ks, dep_start, dep_end, dir_b)
                    val () = put_char_v(dir_b, 0)
                    val @(da, _) = $B.to_arr(dir_b)
                    val @(fz_da, bv_da) = $A.freeze<byte>(da)
                    val dr = $F.dir_open(bv_da, 524288)
                    val () = $A.drop<byte>(fz_da, bv_da)
                    val () = $A.free<byte>($A.thaw<byte>(fz_da))
                  in case+ dr of
                    | ~$R.ok(d) => let
                        (* Find a .bats file in dir (any version — first found) *)
                        (* Find latest .bats file: scan all entries, keep last found *)
                        val best_arr = $A.alloc<byte>(256)
                        val best_len = ref<int>(0)
                        (* Extract version number from filename at part index.
                           name_YYYY.M.D.secs.bats — find '_', then parse dot-separated parts *)
                        fun extract_ver_part {la2:agz}{f3:nat} .<f3>.
                          (a: !$A.arr(byte, la2, 256), len: int, part: int, f3: int f3): int =
                          if f3 <= 0 then 0
                          else let
                            (* Find '_' separator *)
                            fun find_under {la3:agz}{f4:nat} .<f4>.
                              (a: !$A.arr(byte, la3, 256), i: int, len: int, f4: int f4): int =
                              if f4 <= 0 then len
                              else if i >= len then len
                              else if i < 0 then len
                              else if $AR.eq_int_int(byte2int0($A.get<byte>(a, $AR.checked_idx(i, 256))), 95) then i
                              else find_under(a, i + 1, len, f4 - 1)
                            val us = find_under(a, 0, len, 256)
                            (* Parse part: skip to the right dot-separated segment *)
                            fun skip_parts {la3:agz}{f4:nat} .<f4>.
                              (a: !$A.arr(byte, la3, 256), pos: int, len: int, remaining: int, f4: int f4): int =
                              if f4 <= 0 then pos
                              else if remaining <= 0 then pos
                              else if pos >= len then pos
                              else if pos < 0 then pos
                              else if $AR.eq_int_int(byte2int0($A.get<byte>(a, $AR.checked_idx(pos, 256))), 46) then
                                skip_parts(a, pos + 1, len, remaining - 1, f4 - 1)
                              else skip_parts(a, pos + 1, len, remaining, f4 - 1)
                            val vstart = skip_parts(a, us + 1, len, part, 256)
                            (* Parse decimal at vstart *)
                            fun parse_num {la3:agz}{f4:nat} .<f4>.
                              (a: !$A.arr(byte, la3, 256), pos: int, len: int, acc: int, f4: int f4): int =
                              if f4 <= 0 then acc
                              else if pos >= len then acc
                              else if pos < 0 then acc
                              else let
                                val b = byte2int0($A.get<byte>(a, $AR.checked_idx(pos, 256)))
                              in if b >= 48 then if b <= 57 then parse_num(a, pos + 1, len, acc * 10 + (b - 48), f4 - 1)
                                else acc else acc
                              end
                          in parse_num(a, vstart, len, 0, 256) end
                        (* Compare two version filenames: returns true if e is newer than b *)
                        fn is_newer_ver {la2:agz}{lb3:agz}
                          (e: !$A.arr(byte, la2, 256), el: int,
                           b: !$A.arr(byte, lb3, 256), bl: int): bool = let
                          val ey = extract_ver_part(e, el, 0, 256)
                          val by = extract_ver_part(b, bl, 0, 256)
                        in
                          if ey > by then true
                          else if ey < by then false
                          else let
                            val em = extract_ver_part(e, el, 1, 256)
                            val bm = extract_ver_part(b, bl, 1, 256)
                          in
                            if em > bm then true
                            else if em < bm then false
                            else let
                              val ed = extract_ver_part(e, el, 2, 256)
                              val bd = extract_ver_part(b, bl, 2, 256)
                            in
                              if ed > bd then true
                              else if ed < bd then false
                              else let
                                val es = extract_ver_part(e, el, 3, 256)
                                val bs = extract_ver_part(b, bl, 3, 256)
                              in es > bs end
                            end
                          end
                        end
                        fun scan_v {lb3:agz}{f2:nat} .<f2>.
                          (d: !$F.dir, b: !$A.arr(byte, lb3, 256), bl: ref(int),
                           f2: int f2): void =
                          if f2 <= 0 then ()
                          else let
                            val e = $A.alloc<byte>(256)
                            val nr = $F.dir_next(d, e, 256)
                            val el = $R.option_unwrap_or<int>(nr, ~1)
                          in if el < 0 then $A.free<byte>(e)
                            else let
                              val ib = $S.has_suffix(e, el, 256, ".bats", 5)
                              val is = $S.has_suffix(e, el, 256, ".sha256", 7)
                            in if ib then if is then let val () = $A.free<byte>(e)
                              in scan_v(d, b, bl, f2 - 1) end
                              else let
                                val cur_bl = !bl
                                val ey = extract_ver_part(e, el, 0, 256)
                                val by = (if cur_bl > 0 then extract_ver_part(b, cur_bl, 0, 256) else 0): int
                                val em = extract_ver_part(e, el, 1, 256)
                                val bm = (if cur_bl > 0 then extract_ver_part(b, cur_bl, 1, 256) else 0): int
                                val ed = extract_ver_part(e, el, 2, 256)
                                val bd = (if cur_bl > 0 then extract_ver_part(b, cur_bl, 2, 256) else 0): int
                                val es = extract_ver_part(e, el, 3, 256)
                                val bs = (if cur_bl > 0 then extract_ver_part(b, cur_bl, 3, 256) else 0): int
                                val newer = (if cur_bl <= 0 then true
                                  else if ey > by then true
                                  else if ey < by then false
                                  else if em > bm then true
                                  else if em < bm then false
                                  else if ed > bd then true
                                  else if ed < bd then false
                                  else es > bs): bool
                              in if newer then let
                                fun cp_name {ls2:agz}{ld2:agz}{f3:nat} .<f3>.
                                  (s: !$A.arr(byte, ls2, 256), d2: !$A.arr(byte, ld2, 256),
                                   i: int, l: int, f3: int f3): void =
                                  if f3 <= 0 then () else if i >= l then ()
                                  else if i < 0 then () else if i >= 256 then ()
                                  else let
                                    val idx = $AR.checked_idx(i, 256)
                                    val v = byte2int0($A.get<byte>(s, idx))
                                    val () = $A.set<byte>(d2, idx, int2byte0(v))
                                  in cp_name(s, d2, i+1, l, f3-1) end
                                val () = cp_name(e, b, 0, el, 256)
                                val () = !bl := el
                                val () = $A.free<byte>(e)
                              in scan_v(d, b, bl, f2 - 1) end
                              else let val () = $A.free<byte>(e)
                              in scan_v(d, b, bl, f2 - 1) end end
                            else let val () = $A.free<byte>(e)
                            in scan_v(d, b, bl, f2 - 1) end end
                          end
                        val () = scan_v(d, best_arr, best_len, 1000)
                        val blen = !best_len
                        val best = best_arr
                        val dcr = $F.dir_close(d)
                        val () = $R.discard<int><int>(dcr)
                      in if blen <= 0 then let
                          val () = print! ("error: no version for ")
                          val () = print_arr(ks, dep_start, dep_end, 4096, 4096)
                          val () = print_newline()
                          val () = $A.free<byte>(best)
                        in resolve(ks, de+1, kl, rb, rl, lb, cnt, fuel-1) end
                        else let
                          (* mkdir + unzip *)
                          var mb : $B.builder_v = $B.create()
                          val () = bput_v(mb, "bats_modules/")
                          val () = arr_range_to_builder_v(ks, dep_start, dep_end, mb)
                          val _ = run_mkdir(mb)
                          val uz = str_to_path_arr("/usr/bin/unzip")
                          val @(fz_uz, bv_uz) = $A.freeze<byte>(uz)
                          var ua : $B.builder_v = $B.create()
                          val () = bput_v(ua, "unzip") val () = put_char_v(ua, 0)
                          val () = bput_v(ua, "-o") val () = put_char_v(ua, 0)
                          val () = bput_v(ua, "-q") val () = put_char_v(ua, 0)
                          val () = copy_to_builder_v(rb, 0, rl, 4096, ua)
                          val () = bput_v(ua, "/")
                          val () = arr_range_to_builder_v(ks, dep_start, dep_end, ua)
                          val () = bput_v(ua, "/")
                          val @(fz_b, bv_b) = $A.freeze<byte>(best)
                          val () = copy_to_builder_v(bv_b, 0, blen, 256, ua)
                          val () = put_char_v(ua, 0)
                          val () = bput_v(ua, "-d") val () = put_char_v(ua, 0)
                          val () = bput_v(ua, "bats_modules/")
                          val () = arr_range_to_builder_v(ks, dep_start, dep_end, ua)
                          val () = put_char_v(ua, 0)
                          val _ = run_cmd(bv_uz, 524288, ua, 6)
                          val () = $A.drop<byte>(fz_uz, bv_uz)
                          val () = $A.free<byte>($A.thaw<byte>(fz_uz))
                          (* Write lock line *)
                          val () = arr_range_to_builder_v(ks, dep_start, dep_end, lb)
                          val () = put_char_v(lb, 32)
                          (* Version from filename *)
                          var pfx : $B.builder_v = $B.create()
                          fun mkp {ls4:agz}{f4:nat} .<f4>.
                            (s: !$A.arr(byte, ls4, 4096), i: int, l: int, d3: !$B.builder_v >> $B.builder_v, f4: int f4): void =
                            if f4 <= 0 then () else if i >= l then ()
                            else if i < 0 then () else if i >= 4096 then ()
                            else let val c = byte2int0($A.get<byte>(s, $AR.checked_idx(i, 4096)))
                            in if $AR.eq_int_int(c,47) then let
                              val () = put_char_v(d3,95)
                            in mkp(s, i+1, l, d3, f4-1) end
                            else let
                              val () = put_char_v(d3,c)
                            in mkp(s, i+1, l, d3, f4-1) end end
                          val () = mkp(ks, dep_start, dep_end, pfx, 4096)
                          val () = put_char_v(pfx, 95)
                          val pl = $B.length(pfx)
                          val () = $B.builder_free(pfx)
                          val vs = pl val ve = blen - 5
                        in if vs < ve then let
                          val () = copy_to_builder_v(bv_b, vs, ve, 256, lb)
                          val () = put_char_v(lb, 32)
                          val () = bput_v(lb, "0")
                          val () = put_char_v(lb, 10)
                          val () = print! ("fetched ")
                          val () = print_arr(ks, dep_start, dep_end, 4096, 4096)
                          val () = print! (" v")
                          val () = print_borrow(bv_b, vs, ve, 256, 256)
                          val () = print_newline()
                          val () = $A.drop<byte>(fz_b, bv_b)
                          val () = $A.free<byte>($A.thaw<byte>(fz_b))
                        in resolve(ks, de+1, kl, rb, rl, lb, cnt+1, fuel-1) end
                        else let
                          val () = bput_v(lb, "unknown")
                          val () = put_char_v(lb, 32)
                          val () = bput_v(lb, "0")
                          val () = put_char_v(lb, 10)
                          val () = print! ("fetched ")
                          val () = print_arr(ks, dep_start, dep_end, 4096, 4096)
                          val () = print! (" vunknown")
                          val () = print_newline()
                          val () = $A.drop<byte>(fz_b, bv_b)
                          val () = $A.free<byte>($A.thaw<byte>(fz_b))
                        in resolve(ks, de+1, kl, rb, rl, lb, cnt+1, fuel-1) end end
                      end
                    | ~$R.err(_) => let
                        val () = print! ("error: package not found: ")
                        val () = print_arr(ks, dep_start, dep_end, 4096, 4096)
                        val () = print_newline()
                      in resolve(ks, de+1, kl, rb, rl, lb, cnt, fuel-1) end
                  end end
                end
              val n = resolve(keys, 0, klen, bv_rb3, rplen, lock_b, 0, 200)
              val () = $A.free<byte>(keys)
              (* Resolve transitive deps by running resolve again on deps found
                 in extracted packages' bats.toml files. Repeat until stable. *)
              fun resolve_pass {lr2:agz}{fuel:nat} .<fuel>.
                (rb2: !$A.borrow(byte, lr2, 4096), rl2: int,
                 lb2: !$B.builder_v >> $B.builder_v, prev_cnt: int, fuel: int fuel): int =
                if fuel <= 0 then prev_cnt
                else let
                  val bmd = str_to_path_arr("bats_modules")
                  val @(fz_bmd, bv_bmd) = $A.freeze<byte>(bmd)
                  val bdr = $F.dir_open(bv_bmd, 524288)
                  val () = $A.drop<byte>(fz_bmd, bv_bmd)
                  val () = $A.free<byte>($A.thaw<byte>(fz_bmd))
                  val new_cnt = (case+ bdr of
                    | ~$R.ok(bd) => let
                        val tk = $A.alloc<byte>(4096)
                        (* Scan each package in bats_modules, resolve its deps immediately *)
                        fun sdt {ltk:agz}{lr3:agz}{f3:nat} .<f3>.
                          (bd: !$F.dir, tk: !$A.arr(byte, ltk, 4096),
                           rb3: !$A.borrow(byte, lr3, 4096), rl3: int,
                           lb3: !$B.builder_v >> $B.builder_v, cnt3: int, f3: int f3): int =
                          if f3 <= 0 then cnt3
                          else let
                            val de = $A.alloc<byte>(256)
                            val nr = $F.dir_next(bd, de, 256)
                            val del = $R.option_unwrap_or<int>(nr, ~1)
                          in if del < 0 then let val () = $A.free<byte>(de) in cnt3 end
                            else let val dd = is_dot_or_dotdot(de, del, 256) in
                              if dd then let val () = $A.free<byte>(de) in sdt(bd, tk, rb3, rl3, lb3, cnt3, f3-1) end
                              else let
                                var tp : $B.builder_v = $B.create()
                                val () = bput_v(tp, "bats_modules/")
                                val @(fz_de, bv_de) = $A.freeze<byte>(de)
                                val () = copy_to_builder_v(bv_de, 0, del, 256, tp)
                                val () = $A.drop<byte>(fz_de, bv_de)
                                val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                val () = bput_v(tp, "/bats.toml")
                                val () = put_char_v(tp, 0)
                                val @(tpa, _) = $B.to_arr(tp)
                                val @(fz_tpa, bv_tpa) = $A.freeze<byte>(tpa)
                                val tfo = $F.file_open(bv_tpa, 524288, 0, 0)
                                val () = $A.drop<byte>(fz_tpa, bv_tpa)
                                val () = $A.free<byte>($A.thaw<byte>(fz_tpa))
                                val cnt4 = (case+ tfo of
                                  | ~$R.ok(tfd) => let
                                      val tb = $A.alloc<byte>(4096)
                                      val tr = $F.file_read(tfd, tb, 4096)
                                      val tl = (case+ tr of | ~$R.ok(n2) => n2 | ~$R.err(_) => 0): int
                                      val tc = $F.file_close(tfd)
                                      val () = $R.discard<int><int>(tc)
                                      val @(fz_tb, bv_tb) = $A.freeze<byte>(tb)
                                      val pr = $T.parse(bv_tb, 4096)
                                      val () = $A.drop<byte>(fz_tb, bv_tb)
                                      val () = $A.free<byte>($A.thaw<byte>(fz_tb))
                                    in case+ pr of
                                      | ~$R.ok(doc2) => let
                                          val @(dka, dksz) = $S.str_to_borrow("dependencies")
                                          val @(fz_dka, bv_dka) = $A.freeze<byte>(dka)
                                          val kr2 = $T.keys(doc2, bv_dka, dksz, tk, 4096)
                                          val tkl2 = (case+ kr2 of
                                            | ~$R.some(kl2) => kl2
                                            | ~$R.none() => 0): int
                                          val () = $A.drop<byte>(fz_dka, bv_dka)
                                          val () = $A.free<byte>($A.thaw<byte>(fz_dka))
                                          val () = $T.toml_free(doc2)
                                          val n2 = resolve(tk, 0, tkl2, rb3, rl3, lb3, cnt3, 200)
                                        in n2 end
                                      | ~$R.err(_) => cnt3
                                    end
                                  | ~$R.err(_) => cnt3): int
                              in sdt(bd, tk, rb3, rl3, lb3, cnt4, f3-1) end
                            end
                          end
                        val cnt_out = sdt(bd, tk, rb2, rl2, lb2, prev_cnt, 200)
                        val dcr3 = $F.dir_close(bd)
                        val () = $R.discard<int><int>(dcr3)
                        val () = $A.free<byte>(tk)
                      in cnt_out end
                    | ~$R.err(_) => prev_cnt): int
                in
                  if new_cnt > prev_cnt then
                    resolve_pass(rb2, rl2, lb2, new_cnt, fuel - 1)
                  else new_cnt
                end
              val n = resolve_pass(bv_rb3, rplen, lock_b, n, 10)
              val lp = str_to_path_arr("bats.lock")
              val @(fz_lp, bv_lp) = $A.freeze<byte>(lp)
              val _ = write_file_from_builder(bv_lp, 524288, lock_b)
              val () = $A.drop<byte>(fz_lp, bv_lp)
              val () = $A.free<byte>($A.thaw<byte>(fz_lp))
              val () = println! ("wrote bats.lock (", n, " dependencies)")
              val () = $T.toml_free(doc)
            in end
          | ~$R.err(e) => println! ("error: cannot parse bats.toml: ", e)
        end
      | ~$R.err(_) => println! ("error: cannot open bats.toml"))
    val () = $A.drop<byte>(fz_rb3, bv_rb3)
    val () = $A.free<byte>($A.thaw<byte>(fz_rb3))
  in end
  else let
    (* No repository - just read existing lockfile *)
    val () = $A.free<byte>(repo_buf)
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
          val @(fz_lb, bv_lb) = $A.freeze<byte>(lock_buf)
          val () = println! ("bats.lock:")
          val () = print_borrow(bv_lb, 0, lock_len, 524288,
            524288)
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
#pub fn write_wasm_runtime_h(): int

implement write_wasm_runtime_h() = let
  var b : $B.builder_v = $B.create()
  val () = bput_v(b, "/* runtime.h -- Freestanding WASM runtime for ATS2 */\n#ifndef BATS_WASM_RUNTIME_H\n#define BATS_WASM_RUNTIME_H\n")
  val () = bput_v(b, "typedef void atstype_void;\ntypedef void atsvoid_t0ype;\ntypedef int atstype_int;\ntypedef unsigned int atstype_uint;\n")
  val () = bput_v(b, "typedef long int atstype_lint;\ntypedef unsigned long int atstype_ulint;\ntypedef long long int atstype_llint;\n")
  val () = bput_v(b, "typedef unsigned long long int atstype_ullint;\ntypedef short int atstype_sint;\ntypedef unsigned short int atstype_usint;\n")
  val () = bput_v(b, "typedef atstype_lint atstype_ssize;\ntypedef atstype_ulint atstype_size;\ntypedef int atstype_bool;\n")
  val () = bput_v(b, "typedef unsigned char atstype_byte;\ntypedef char atstype_char;\ntypedef signed char atstype_schar;\ntypedef unsigned char atstype_uchar;\n")
  val () = bput_v(b, "typedef char *atstype_string;\ntypedef char *atstype_stropt;\ntypedef char *atstype_strptr;\n")
  val () = bput_v(b, "typedef void *atstype_ptr;\ntypedef void *atstype_ptrk;\ntypedef void *atstype_ref;\ntypedef void *atstype_boxed;\n")
  val () = bput_v(b, "typedef void *atstype_datconptr;\ntypedef void *atstype_datcontyp;\ntypedef void *atstype_arrptr;\ntypedef void *atstype_funptr;\ntypedef void *atstype_cloptr;\n")
  val () = bput_v(b, "#define atstkind_type(tk) tk\n#define atstkind_t0ype(tk) tk\n#ifndef _ATSTYPE_VAR_SIZE_\n#define _ATSTYPE_VAR_SIZE_ 0X10000\n#endif\n")
  val () = bput_v(b, "typedef struct { char _[_ATSTYPE_VAR_SIZE_]; } atstype_var[0];\n#define atstyvar_type(a) atstype_var\n#define atstybox_type(hit) atstype_boxed\n")
  val () = bput_v(b, "#define atsrefarg0_type(hit) hit\n#define atsrefarg1_type(hit) atstype_ref\n")
  val () = bput_v(b, "#define atsbool_true 1\n#define atsbool_false 0\n#define atsptr_null ((void*)0)\n#define the_atsptr_null ((void*)0)\n")
  val () = bput_v(b, "#define ATSstruct struct\n#define ATSextern() extern\n#define ATSstatic() static\n#define ATSinline() static inline\n")
  val () = bput_v(b, "#define ATSdynload()\n#define ATSdynloadflag_sta(flag)\n#define ATSdynloadflag_ext(flag) extern int flag\n")
  val () = bput_v(b, "#define ATSdynloadflag_init(flag) int flag = 0\n#define ATSdynloadflag_minit(flag) int flag = 0\n#define ATSdynloadset(flag) flag = 1\n")
  val () = bput_v(b, "#define ATSdynloadfcall(dynloadfun) dynloadfun()\n#define ATSassume(flag) void *flag = (void*)0\n")
  val () = bput_v(b, "#define ATSdyncst_mac(d2c)\n#define ATSdyncst_castfn(d2c)\n#define ATSdyncst_extfun(d2c, targs, tres) extern tres d2c targs\n")
  val () = bput_v(b, "#define ATSdyncst_stafun(d2c, targs, tres) static tres d2c targs\n#define ATSdyncst_valimp(d2c, type) type d2c\n#define ATSdyncst_valdec(d2c, type) extern type d2c\n")
  val () = bput_v(b, "#define ATSif(x) if(x)\n#define ATSthen()\n#define ATSelse() else\n#define ATSifthen(x) if(x)\n#define ATSifnthen(x) if(!(x))\n")
  val () = bput_v(b, "#define ATSreturn(x) return(x)\n#define ATSreturn_void(x) return\n#define ATSfunbody_beg()\n#define ATSfunbody_end()\n")
  val () = bput_v(b, "#define ATSPMVint(i) i\n#define ATSPMVintrep(rep) (rep)\n#define ATSPMVbool_true() atsbool_true\n#define ATSPMVbool_false() atsbool_false\n")
  val () = bput_v(b, "#define ATSPMVchar(c) (c)\n#define ATSPMVstring(str) (str)\n#define ATSPMVi0nt(tok) (tok)\n#define ATSPMVempty()\n")
  val () = bput_v(b, "#define ATSPMVextval(name) (name)\n#define ATSPMVptrof(lval) (&(lval))\n#define ATSPMVptrof_void(lval) ((void*)0)\n")
  val () = bput_v(b, "#define ATSPMVrefarg0(val) (val)\n#define ATSPMVrefarg1(ref) (ref)\n#define ATSPMVsizeof(hit) (sizeof(hit))\n")
  val () = bput_v(b, "#define ATSPMVfunlab(flab) (flab)\n#define ATSPMVcastfn(d2c, hit, arg) ((hit)arg)\n#define ATSPMVtyrep(rep) (rep)\n")
  val () = bput_v(b, "#define ATStyclo() struct{ void *cfun; }\n#define ATSfunclo_fun(pmv, targs, tres) ((tres(*)targs)(pmv))\n")
  val () = bput_v(b, "#define ATSfunclo_clo(pmv, targs, tres) ((tres(*)targs)(((ATStyclo()*)pmv)->cfun))\n")
  val () = bput_v(b, "#define ATSfuncall(fun, funarg) (fun)funarg\n#define ATSextfcall(fun, funarg) (fun)funarg\n#define ATSextmcall(obj, mtd, funarg) (obj->mtd)funarg\n")
  val () = bput_v(b, "#define ATStmpdec(tmp, hit) hit tmp\n#define ATStmpdec_void(tmp)\n#define ATSstatmpdec(tmp, hit) static hit tmp\n#define ATSstatmpdec_void(tmp)\n")
  val () = bput_v(b, "#define ATSderef(pmv, hit) (*(hit*)pmv)\n#define ATSCKnot(x) ((x)==0)\n#define ATSCKiseqz(x) ((x)==0)\n#define ATSCKisneqz(x) ((x)!=0)\n")
  val () = bput_v(b, "#define ATSCKptriscons(x) (0 != (void*)(x))\n#define ATSCKptrisnull(x) (0 == (void*)(x))\n")
  val () = bput_v(b, "#define ATSINSlab(lab) lab\n#define ATSINSgoto(lab) goto lab\n#define ATSINSflab(flab) flab\n#define ATSINSfgoto(flab) goto flab\n")
  val () = bput_v(b, "#define ATSINSmove(tmp, val) (tmp = val)\n#define ATSINSpmove(tmp, hit, val) (*(hit*)tmp = val)\n")
  val () = bput_v(b, "#define ATSINSmove_void(tmp, command) command\n#define ATSINSpmove_void(tmp, hit, command) command\n#define ATSINSmove_nil(tmp) (tmp = ((void*)0))\n")
  val () = bput_v(b, "#define ATSINSupdate_ptrinc(tmp, tyelt) (tmp = (tyelt*)(tmp) + 1)\n#define ATSINSupdate_ptrdec(tmp, tyelt) (tmp = (tyelt*)(tmp) - 1)\n")
  val () = bput_v(b, "#define ATSINSdeadcode_fail() /*deadcode*/\n")
  val () = bput_v(b, "#define ATSSELfltrec(pmv, tyrec, lab) ((pmv).lab)\n#define ATSSELcon(pmv, tycon, lab) (((tycon*)(pmv))->lab)\n#define ATSSELarrptrind(pmv, tyelt, lab) (((tyelt*)pmv)lab)\n")
  val () = bput_v(b, "#define ATSINSmove_con1_beg()\n#define ATSINSmove_con1_new(tmp, tycon) (tmp = ATS_MALLOC(sizeof(tycon)))\n")
  val () = bput_v(b, "#define ATSINSstore_con1_ofs(tmp, tycon, lab, val) (((tycon*)(tmp))->lab = val)\n#define ATSINSmove_con1_end()\n#define ATSINSfreecon(ptr) ATS_MFREE(ptr)\n")
  val () = bput_v(b, "#define ATSSELrecsin(pmv, tyrec, lab) (pmv)\n#define ATSINSstore_con1_tag(dst, tag) (((int*)(dst))[0] = (tag))\n")
  val () = bput_v(b, "#define ATSINSmove_con0(dst, tag) ((dst) = (void*)(tag))\n#define ATSCKpat_con0(p, tag) ((p) == (void*)(tag))\n#define ATSCKpat_con1(p, tag) (((int*)(p))[0] == (tag))\n")
  val () = bput_v(b, "#define ATSINSmove_fltrec_beg()\n#define ATSINSmove_fltrec_end()\n#define ATSINSstore_fltrec_ofs(tmp, tyrec, lab, val) ((tmp).lab = val)\n")
  val () = bput_v(b, "#define ATSINSload(tmp, pmv) (tmp = pmv)\n#define ATSINSstore(pmv1, pmv2) (pmv1 = pmv2)\n#define ATSINSxstore(tmp, pmv1, pmv2) (tmp = pmv1, pmv1 = pmv2, pmv2 = tmp)\n")
  val () = bput_v(b, "#define ATStailcal_beg() do {\n#define ATStailcal_end() } while(0) ;\n#define ATSINSmove_tlcal(apy, tmp) (apy = tmp)\n#define ATSINSargmove_tlcal(arg, apy) (arg = apy)\n")
  val () = bput_v(b, "#define ATSbranch_beg()\n#define ATSbranch_end() break ;\n#define ATScaseof_beg() do {\n#define ATScaseof_end() } while(0) ;\n#define ATSextcode_beg()\n#define ATSextcode_end()\n")
  val () = bput_v(b, "#define atspre_g1uint2int_size_int(x) ((int)(x))\n#define atspre_g0int_add_int(x, y) ((x) + (y))\n#define atspre_g1int_mul_int(x, y) ((x) * (y))\n")
  val () = bput_v(b, "#define atspre_g0int2uint_int_size(x) ((atstype_size)(x))\n#define atspre_g0uint_mul_size(x, y) ((x) * (y))\n#define atspre_add_ptr0_bsz(p, n) ((void*)((char*)(p) + (n)))\n")
  val () = bput_v(b, "#define atspre_g1int2int_int_int(x) (x)\n#define atspre_g1int_lt_int(x, y) ((x) < (y))\n#define atspre_g1int_add_int(x, y) ((x) + (y))\n")
  val () = bput_v(b, "#define atspre_char2int1(c) ((int)(c))\n#define atspre_g0int2int_int_int(x) (x)\n#define atspre_g0int_gt_int(x, y) ((x) > (y))\n")
  val () = bput_v(b, "#define atspre_g1ofg0_int(x) (x)\n#define atspre_g0ofg1_int(x) (x)\n#define atspre_g1int_gt_int(x, y) ((x) > (y))\n#define atspre_g1int_gte_int(x, y) ((x) >= (y))\n")
  val () = bput_v(b, "#define atspre_g1int_lte_int(x, y) ((x) <= (y))\n#define atspre_g1int_sub_int(x, y) ((x) - (y))\n#define atspre_g1int_neg_int(x) (-(x))\n")
  val () = bput_v(b, "#define atspre_g0int_gte_int(x, y) ((x) >= (y))\n#define atspre_g0int_lte_int(x, y) ((x) <= (y))\n#define atspre_g0int_eq_int(x, y) ((x) == (y))\n")
  val () = bput_v(b, "#define atspre_g0int_mul_int(x, y) ((x) * (y))\n#define atspre_g0int_sub_int(x, y) ((x) - (y))\n#define atspre_g0int_neq_int(x, y) ((x) != (y))\n")
  val () = bput_v(b, "#define atspre_g0int_lt_int(x, y) ((x) < (y))\n#define atspre_g0int_div_int(x, y) ((x) / (y))\n#define atspre_g0int_mod_int(x, y) ((x) % (y))\n")
  val () = bput_v(b, "#define atspre_g1int_div_int(x, y) ((x) / (y))\n#define atspre_g1int_eq_int(x, y) ((x) == (y))\n#define atspre_g1int_neq_int(x, y) ((x) != (y))\n")
  val () = bput_v(b, "#define atspre_g0int_asl_int(x, n) ((x) << (n))\n#define atspre_g0int_asr_int(x, n) ((x) >> (n))\n")
  val () = bput_v(b, "#define atspre_lor_int_int(x, y) ((x) | (y))\n#define atspre_land_int_int(x, y) ((x) & (y))\n")
  val () = bput_v(b, "#define atspre_byte2int0(b) ((int)(b))\n#define atspre_int2byte0(i) ((atstype_byte)(i))\n#define atspre_char2int0(c) ((int)(c))\n")
  val () = bput_v(b, "#define atspre_ptr_null() ((void*)0)\n#define atspre_ptr_isnot_null(p) ((p) != 0)\n#define atspre_ptr0_isnot_null atspre_ptr_isnot_null\n")
  val () = bput_v(b, "#define atspre_add_ptr1_bsz(p, n) ((void*)((char*)(p) + (n)))\n#define atspre_g0int_neg_int(x) (-(x))\n#define atspre_g1int_neg_int(x) (-(x))\n")
  val () = bput_v(b, "#define atspre_g1int2uint_int_size(x) ((atstype_size)(x))\n#define atspre_strlen strlen\n")
  val () = bput_v(b, "#define ATS_MALLOC(sz) malloc(sz)\n#define ATS_MFREE(ptr) free(ptr)\n#define ATSINScloptr_make(tmp, sz) (tmp = ATS_MALLOC(sz))\n#define ATSINScloptr_free(tmp) ATS_MFREE(tmp)\n")
  val () = bput_v(b, "#define ATSclosurerize_beg(flab, tenvs, targs, tres)\n#define ATSclosurerize_end()\n#define ATSFCreturn(x) return(x)\n#define ATSFCreturn_void(x) (x); return\n")
  val () = bput_v(b, "#define ATSPMVcfunlab(knd, flab, env) (flab##__closurerize)env\nextern void mainats_0_void(void);\n#define ATSmainats_0_void(err) mainats_0_void()\n")
  val () = bput_v(b, "void *malloc(int size);\nvoid free(void *ptr);\nvoid *memset(void *s, int c, unsigned int n);\nvoid *memcpy(void *dst, const void *src, unsigned int n);\nstatic inline unsigned int strlen(const char *s) { unsigned int n = 0; while (s[n]) n++; return n; }\n")
  val () = bput_v(b, "static inline void *calloc(int n, int sz) { return malloc(n * sz); }\n#endif\n")
  val p = str_to_path_arr("build/_bats_wasm_runtime.h")
  val @(fz_p, bv_p) = $A.freeze<byte>(p)
  val rc = write_file_from_builder(bv_p, 524288, b)
  val () = $A.drop<byte>(fz_p, bv_p)
  val () = $A.free<byte>($A.thaw<byte>(fz_p))
in rc end

#pub fn write_wasm_runtime_c(): int

implement write_wasm_runtime_c() = let
  var b : $B.builder_v = $B.create()
  val () = bput_v(b, "/* runtime.c -- Freestanding WASM: free-list allocator */\nextern unsigned char __heap_base;\nstatic unsigned char *heap_ptr = &__heap_base;\n")
  val () = bput_v(b, "#define WARD_HEADER 8\n#define WARD_NBUCKET 9\nstatic const unsigned int ward_bsz[WARD_NBUCKET] = {32,128,512,4096,8192,16384,524288,262144,1048576};\n")
  val () = bput_v(b, "static void *ward_fl[WARD_NBUCKET] = {0,0,0,0,0,0,0,0,0};\nstatic void *ward_fl_over = 0;\n")
  val () = bput_v(b, "void *memset(void *s,int c,unsigned int n){unsigned char *p=(unsigned char*)s;unsigned char byte=(unsigned char)c;while(n--)*p++=byte;return s;}\n")
  val () = bput_v(b, "void *memcpy(void *dst,const void *src,unsigned int n){unsigned char *d=(unsigned char*)dst;const unsigned char *s=(const unsigned char*)src;while(n--)*d++=*s++;return dst;}\n")
  val () = bput_v(b, "static inline unsigned int ward_hdr_read(void *p){return *(unsigned int*)((char*)p-WARD_HEADER);}\n")
  val () = bput_v(b, "static inline int ward_bucket(unsigned int n){if(n<=32)return 0;if(n<=128)return 1;if(n<=512)return 2;if(n<=4096)return 3;\n")
  val () = bput_v(b, "if(n<=8192)return 4;if(n<=16384)return 5;if(n<=524288)return 6;if(n<=262144)return 7;if(n<=1048576)return 8;return -1;}\n")
  val () = bput_v(b, "static void *ward_bump(unsigned int usable){unsigned long a=(unsigned long)heap_ptr;a=(a+7u)&~7u;unsigned long end=a+WARD_HEADER+usable;\n")
  val () = bput_v(b, "unsigned long limit=(unsigned long)__builtin_wasm_memory_size(0)*524288UL;if(end>limit){unsigned long pages=(end-limit+65535UL)/524288UL;\n")
  val () = bput_v(b, "if(__builtin_wasm_memory_grow(0,pages)==(unsigned long)(-1))return(void*)0;}*(unsigned int*)a=usable;void *p=(void*)(a+WARD_HEADER);heap_ptr=(unsigned char*)end;return p;}\n")
  val () = bput_v(b, "void *malloc(int size){if(size<=0)size=1;unsigned int n=(unsigned int)size;int b=ward_bucket(n);if(b>=0){unsigned int bsz=ward_bsz[b];void *p;\n")
  val () = bput_v(b, "if(ward_fl[b]){p=ward_fl[b];ward_fl[b]=*(void**)p;}else{p=ward_bump(bsz);}memset(p,0,bsz);return p;}\n")
  val () = bput_v(b, "void **prev=&ward_fl_over;void *cur=ward_fl_over;while(cur){unsigned int bsz=ward_hdr_read(cur);if(bsz>=n&&bsz<=2*n){*prev=*(void**)cur;memset(cur,0,bsz);return cur;}\n")
  val () = bput_v(b, "prev=(void**)cur;cur=*(void**)cur;}void *p=ward_bump(n);memset(p,0,n);return p;}\n")
  val () = bput_v(b, "void free(void *ptr){if(!ptr)return;unsigned int sz=ward_hdr_read(ptr);int b=ward_bucket(sz);if(b>=0&&ward_bsz[b]==sz){*(void**)ptr=ward_fl[b];ward_fl[b]=ptr;}\n")
  val () = bput_v(b, "else{*(void**)ptr=ward_fl_over;ward_fl_over=ptr;}}\n")
  val p = str_to_path_arr("build/_bats_wasm_runtime.c")
  val @(fz_p, bv_p) = $A.freeze<byte>(p)
  val rc = write_file_from_builder(bv_p, 524288, b)
  val () = $A.drop<byte>(fz_p, bv_p)
  val () = $A.free<byte>($A.thaw<byte>(fz_p))
in rc end

#pub fn write_wasm_stubs(): int

implement write_wasm_stubs() = let
  var mb : $B.builder_v = $B.create()
  val () = bput_v(mb, "build/_bats_wasm_stubs/libats/libc/CATS/sys")
  val r0 = run_mkdir(mb)
  val stub = "/* stub */\n"
  fn write_stub {sn:nat | sn < $B.BUILDER_CAP} (path: string sn): int = let
    var sb : $B.builder_v = $B.create()
    val () = bput_v(sb, stub)
    val pp = str_to_path_arr(path)
    val @(fz_pp, bv_pp) = $A.freeze<byte>(pp)
    val rc = write_file_from_builder(bv_pp, 524288, sb)
    val () = $A.drop<byte>(fz_pp, bv_pp)
    val () = $A.free<byte>($A.thaw<byte>(fz_pp))
  in rc end
  val _ = write_stub("build/_bats_wasm_stubs/libats/libc/CATS/stdio.cats")
  val _ = write_stub("build/_bats_wasm_stubs/libats/libc/CATS/sys/stat.cats")
  val _ = write_stub("build/_bats_wasm_stubs/libats/libc/CATS/sys/types.cats")
in r0 end

fn compile_wasm_runtime(): int = let
  val exec = str_to_path_arr("/usr/bin/clang")
  val @(fz_exec, bv_exec) = $A.freeze<byte>(exec)
  var argv : $B.builder_v = $B.create()
  val () = bput_v(argv, "clang") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "--target=wasm32") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-O2") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-nostdlib") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-ffreestanding") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-fvisibility=default") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-D_ATS_CCOMP_HEADER_NONE_") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-D_ATS_CCOMP_EXCEPTION_NONE_") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-D_ATS_CCOMP_PRELUDE_NONE_") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-D_ATS_CCOMP_RUNTIME_NONE_") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-include") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "build/_bats_wasm_runtime.h") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-I") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "build/_bats_wasm_stubs") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-c") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-o") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "build/_bats_wasm_runtime.wasm.o") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "build/_bats_wasm_runtime.c") val () = put_char_v(argv, 0)
  val rc = run_cmd(bv_exec, 524288, argv, 19)
  val () = $A.drop<byte>(fz_exec, bv_exec)
  val () = $A.free<byte>($A.thaw<byte>(fz_exec))
in rc end

#pub fn do_build_wasm(release: int): void

fn run_wasm_cc {li:agz}{lo:agz}
  (in_bv: !$A.borrow(byte, li, 524288), in_len: int,
   out_bv: !$A.borrow(byte, lo, 524288), out_len: int): int = let
  val exec = str_to_path_arr("/usr/bin/clang")
  val @(fz_exec, bv_exec) = $A.freeze<byte>(exec)
  var argv : $B.builder_v = $B.create()
  val () = bput_v(argv, "clang") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "--target=wasm32") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-O2") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-nostdlib") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-ffreestanding") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-fvisibility=default") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-D_ATS_CCOMP_HEADER_NONE_") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-D_ATS_CCOMP_EXCEPTION_NONE_") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-D_ATS_CCOMP_PRELUDE_NONE_") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-D_ATS_CCOMP_RUNTIME_NONE_") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-include") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "build/_bats_wasm_runtime.h") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-I") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "build/_bats_wasm_stubs") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-Wno-implicit-function-declaration") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-Wno-int-conversion") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-c") val () = put_char_v(argv, 0)
  val () = bput_v(argv, "-o") val () = put_char_v(argv, 0)
  val oc = out_len - 1
  val () = copy_to_builder_v(out_bv, 0, oc, 524288, argv)
  val () = put_char_v(argv, 0)
  val ic = in_len - 1
  val () = copy_to_builder_v(in_bv, 0, ic, 524288, argv)
  val () = put_char_v(argv, 0)
  val rc = run_cmd(bv_exec, 524288, argv, 21)
  val () = $A.drop<byte>(fz_exec, bv_exec)
  val () = $A.free<byte>($A.thaw<byte>(fz_exec))
in rc end

fn wasm_cc_file {l:agz}
  (path: !$A.borrow(byte, l, 524288), path_len: int): int = let
  (* path is like "build/.../_dats.c", replace .c with .wasm.o for output *)
  var ob : $B.builder_v = $B.create()
  val pl = path_len - 1
  val () = copy_to_builder_v(path, 0, pl - 1, 524288, ob)
  val () = bput_v(ob, "wasm.o")
  val () = put_char_v(ob, 0)
  val @(oa, ol) = $B.to_arr(ob)
  val @(fz_o, bv_o) = $A.freeze<byte>(oa)
  val rc = run_wasm_cc(path, path_len, bv_o, ol)
  val () = $A.drop<byte>(fz_o, bv_o)
  val () = $A.free<byte>($A.thaw<byte>(fz_o))
in rc end

implement do_build_wasm(release) = let
  val _ = write_wasm_runtime_h()
  val _ = write_wasm_runtime_c()
  val _ = write_wasm_stubs()
  val rtrc = compile_wasm_runtime()
  val () = (if rtrc <> 0 then println! ("error: WASM runtime compile failed") else ())
  (* Compile all _dats.c files generated by do_build with WASM target *)
  (* do_build(release, 1) must run first to preprocess and patsopt for WASM *)
  var db : $B.builder_v = $B.create()
  val () = bput_v(db, "build")
  val () = put_char_v(db, 0)
  val @(dba, _) = $B.to_arr(db)
  val @(fz_db, bv_db) = $A.freeze<byte>(dba)
  val () = println! ("  compiling WASM...")
  (* Compile entry *)
  var eb : $B.builder_v = $B.create()
  val () = bput_v(eb, "build/_bats_entry_")
  (* Find the entry file by scanning build/ for _bats_entry_*_dats.c *)
  val dr = $F.dir_open(bv_db, 524288)
  val () = $A.drop<byte>(fz_db, bv_db)
  val () = $A.free<byte>($A.thaw<byte>(fz_db))
  var link_b : $B.builder_v = $B.create()
  val () = bput_v(link_b, "wasm-ld") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--no-entry") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--allow-undefined") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--lto-O2") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "-z") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "stack-size=1048576") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--initial-memory=16777216") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--max-memory=268435456") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--export=mainats_0_void") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--export=malloc") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--export=bats_on_event") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--export=bats_timer_fire") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--export=bats_idb_fire") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--export=bats_idb_fire_get") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--export=bats_measure_set") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--export=bats_on_fetch_complete") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--export=bats_on_file_open") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "--export=bats_on_decompress_complete") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "-o") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "dist/wasm/app.wasm") val () = put_char_v(link_b, 0)
  val () = bput_v(link_b, "build/_bats_wasm_runtime.o") val () = put_char_v(link_b, 0)
  val link_count0 = 22
  val () = (let val @(ea, _) = $B.to_arr(eb) val () = $A.free<byte>(ea) in end)
  val link_count1 = (case+ dr of
    | ~$R.ok(d) => let
        fun scan_build {fuel2:nat} .<fuel2>.
          (d: !$F.dir, lb: !$B.builder_v >> $B.builder_v, lc: int, fuel2: int fuel2): int =
          if fuel2 <= 0 then lc
          else let
            val e = $A.alloc<byte>(256)
            val nr = $F.dir_next(d, e, 256)
            val el = $R.option_unwrap_or<int>(nr, ~1)
          in
            if el < 0 then let val () = $A.free<byte>(e) in lc end
            else let
              val has_c = $S.has_suffix(e, el, 256, "_dats.c", 7)
            in
              if has_c then let
                var pb : $B.builder_v = $B.create()
                val () = bput_v(pb, "build/")
                val @(fz_e, bv_e) = $A.freeze<byte>(e)
                val () = copy_to_builder_v(bv_e, 0, el, 256, pb)
                val () = put_char_v(pb, 0)
                val @(pa, pl) = $B.to_arr(pb)
                val @(fz_p, bv_p) = $A.freeze<byte>(pa)
                val rc = wasm_cc_file(bv_p, pl)
              in if rc <> 0 then let
                  val () = print! ("error: wasm cc failed for ")
                  val () = print_borrow(bv_e, 0, el, 256, 256)
                  val () = print_newline()
                  val () = bput_v(lb, "")
                  val () = $A.drop<byte>(fz_p, bv_p)
                  val () = $A.free<byte>($A.thaw<byte>(fz_p))
                  val () = $A.drop<byte>(fz_e, bv_e)
                  val () = $A.free<byte>($A.thaw<byte>(fz_e))
                in scan_build(d, lb, lc + 1, fuel2 - 1) end
                else let
                  val () = copy_to_builder_v(bv_p, 0, pl - 2, 524288, lb)
                  val () = bput_v(lb, "o")
                  val () = put_char_v(lb, 0)
                  val () = $A.drop<byte>(fz_p, bv_p)
                  val () = $A.free<byte>($A.thaw<byte>(fz_p))
                  val () = $A.drop<byte>(fz_e, bv_e)
                  val () = $A.free<byte>($A.thaw<byte>(fz_e))
                in scan_build(d, lb, lc + 1, fuel2 - 1) end end
              else let
                val () = $A.free<byte>(e)
              in scan_build(d, lb, lc, fuel2 - 1) end
            end
          end
        val nfiles = scan_build(d, link_b, 0, 500)
        val dcr = $F.dir_close(d)
        val () = $R.discard<int><int>(dcr)
      in link_count0 + nfiles end
    | ~$R.err(_) => let val () = bput_v(link_b, "") in link_count0 end): int
  (* Compile dep _dats.c files with wasm cc and add .o to link *)
  var bm : $B.builder_v = $B.create()
  val () = bput_v(bm, "build/bats_modules")
  val () = put_char_v(bm, 0)
  val @(bma, _) = $B.to_arr(bm)
  val @(fz_bm, bv_bm) = $A.freeze<byte>(bma)
  val bm_dr = $F.dir_open(bv_bm, 524288)
  val () = $A.drop<byte>(fz_bm, bv_bm)
  val () = $A.free<byte>($A.thaw<byte>(fz_bm))
  val link_count2 = (case+ bm_dr of
    | ~$R.ok(bm_d) => let
        fun add_dep_objs {fuel3:nat} .<fuel3>.
          (bm_d: !$F.dir, lb: !$B.builder_v >> $B.builder_v, lc: int, fuel3: int fuel3): int =
          if fuel3 <= 0 then lc
          else let
            val e = $A.alloc<byte>(256)
            val nr = $F.dir_next(bm_d, e, 256)
            val el = $R.option_unwrap_or<int>(nr, ~1)
          in if el < 0 then let val () = $A.free<byte>(e) in lc end
            else let
              val dd = is_dot_or_dotdot(e, el, 256)
            in if dd then let val () = $A.free<byte>(e)
              in add_dep_objs(bm_d, lb, lc, fuel3 - 1) end
            else let
              val @(fz_e, bv_e) = $A.freeze<byte>(e)
              (* Open build/bats_modules/<dep>/src/ and compile _dats.c files *)
              var sp : $B.builder_v = $B.create()
              val () = bput_v(sp, "build/bats_modules/")
              val () = copy_to_builder_v(bv_e, 0, el, 256, sp)
              val () = bput_v(sp, "/src")
              val () = put_char_v(sp, 0)
              val @(spa, _) = $B.to_arr(sp)
              val @(fz_sp, bv_sp) = $A.freeze<byte>(spa)
              val sd = $F.dir_open(bv_sp, 524288)
            in (case+ sd of
                | ~$R.ok(sd_d) => let
                    fun compile_dep_c {le2:agz}{fuel4:nat} .<fuel4>.
                      (sd_d: !$F.dir, lb2: !$B.builder_v >> $B.builder_v,
                       bv_e2: !$A.borrow(byte, le2, 256), el2: int,
                       lc: int, fuel4: int fuel4): int =
                      if fuel4 <= 0 then lc
                      else let
                        val oe = $A.alloc<byte>(256)
                        val onr = $F.dir_next(sd_d, oe, 256)
                        val oel = $R.option_unwrap_or<int>(onr, ~1)
                      in if oel < 0 then let val () = $A.free<byte>(oe) in lc end
                        else let
                          val is_c = $S.has_suffix(oe, oel, 256, "_dats.c", 7)
                        in if ~is_c then let val () = $A.free<byte>(oe)
                          in compile_dep_c(sd_d, lb2, bv_e2, el2, lc, fuel4 - 1) end
                        else let
                          val @(fz_oe, bv_oe) = $A.freeze<byte>(oe)
                          var pb : $B.builder_v = $B.create()
                          val () = bput_v(pb, "build/bats_modules/")
                          val () = copy_to_builder_v(bv_e2, 0, el2, 256, pb)
                          val () = bput_v(pb, "/src/")
                          val () = copy_to_builder_v(bv_oe, 0, oel, 256, pb)
                          val () = put_char_v(pb, 0)
                          val @(pa, pl) = $B.to_arr(pb)
                          val @(fz_p, bv_p) = $A.freeze<byte>(pa)
                          val rc = wasm_cc_file(bv_p, pl)
                        in if rc = 0 then let
                            val () = copy_to_builder_v(bv_p, 0, pl - 2, 524288, lb2)
                            val () = bput_v(lb2, "o")
                            val () = put_char_v(lb2, 0)
                            val () = $A.drop<byte>(fz_p, bv_p)
                            val () = $A.free<byte>($A.thaw<byte>(fz_p))
                            val () = $A.drop<byte>(fz_oe, bv_oe)
                            val () = $A.free<byte>($A.thaw<byte>(fz_oe))
                          in compile_dep_c(sd_d, lb2, bv_e2, el2, lc + 1, fuel4 - 1) end
                          else let
                            val () = bput_v(lb2, "")
                            val () = $A.drop<byte>(fz_p, bv_p)
                            val () = $A.free<byte>($A.thaw<byte>(fz_p))
                            val () = $A.drop<byte>(fz_oe, bv_oe)
                            val () = $A.free<byte>($A.thaw<byte>(fz_oe))
                          in compile_dep_c(sd_d, lb2, bv_e2, el2, lc, fuel4 - 1) end end
                        end
                      end
                    val dc = compile_dep_c(sd_d, lb, bv_e, el, lc, 200)
                    val dcr2 = $F.dir_close(sd_d)
                    val () = $R.discard<int><int>(dcr2)
                    val () = $A.drop<byte>(fz_sp, bv_sp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                    val () = $A.drop<byte>(fz_e, bv_e)
                    val () = $A.free<byte>($A.thaw<byte>(fz_e))
                  in add_dep_objs(bm_d, lb, dc, fuel3 - 1) end
                | ~$R.err(_) => let
                    (* Maybe it's a namespace dir — scan sub-packages *)
                    var nsp : $B.builder_v = $B.create()
                    val () = bput_v(nsp, "build/bats_modules/")
                    val () = copy_to_builder_v(bv_e, 0, el, 256, nsp)
                    val () = put_char_v(nsp, 0)
                    val @(nspa, _) = $B.to_arr(nsp)
                    val @(fz_nsp, bv_nsp) = $A.freeze<byte>(nspa)
                    val nsd = $F.dir_open(bv_nsp, 524288)
                    val () = $A.drop<byte>(fz_nsp, bv_nsp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_nsp))
                  in (case+ nsd of
                    | ~$R.ok(nsd_d) => let
                        fun compile_ns_c {lns:agz}{fuel5:nat} .<fuel5>.
                          (nsd_d: !$F.dir, lb3: !$B.builder_v >> $B.builder_v,
                           ns_bv: !$A.borrow(byte, lns, 256), ns_len: int,
                           lc: int, fuel5: int fuel5): int =
                          if fuel5 <= 0 then lc
                          else let
                            val se = $A.alloc<byte>(256)
                            val snr = $F.dir_next(nsd_d, se, 256)
                            val sl = $R.option_unwrap_or<int>(snr, ~1)
                          in if sl < 0 then let val () = $A.free<byte>(se) in lc end
                            else let val sdd = is_dot_or_dotdot(se, sl, 256) in
                              if sdd then let val () = $A.free<byte>(se)
                              in compile_ns_c(nsd_d, lb3, ns_bv, ns_len, lc, fuel5 - 1) end
                              else let
                                val @(fz_se, bv_se) = $A.freeze<byte>(se)
                                var sp2 : $B.builder_v = $B.create()
                                val () = bput_v(sp2, "build/bats_modules/")
                                val () = copy_to_builder_v(ns_bv, 0, ns_len, 256, sp2)
                                val () = bput_v(sp2, "/")
                                val () = copy_to_builder_v(bv_se, 0, sl, 256, sp2)
                                val () = bput_v(sp2, "/src")
                                val () = put_char_v(sp2, 0)
                                val @(sp2a, _) = $B.to_arr(sp2)
                                val @(fz_sp2, bv_sp2) = $A.freeze<byte>(sp2a)
                                val sd2 = $F.dir_open(bv_sp2, 524288)
                              in (case+ sd2 of
                                  | ~$R.ok(sd2_d) => let
                                      fun compile_ns_sub_c {le3:agz}{fuel6:nat} .<fuel6>.
                                        (sd2_d: !$F.dir, lb4: !$B.builder_v >> $B.builder_v,
                                         ns2: !$A.borrow(byte, lns, 256), nl2: int,
                                         sub2: !$A.borrow(byte, le3, 256), sl2: int,
                                         lc: int, fuel6: int fuel6): int =
                                        if fuel6 <= 0 then lc
                                        else let
                                          val oe2 = $A.alloc<byte>(256)
                                          val onr2 = $F.dir_next(sd2_d, oe2, 256)
                                          val oel2 = $R.option_unwrap_or<int>(onr2, ~1)
                                        in if oel2 < 0 then let val () = $A.free<byte>(oe2) in lc end
                                          else let
                                            val is_c2 = $S.has_suffix(oe2, oel2, 256, "_dats.c", 7)
                                          in if ~is_c2 then let val () = $A.free<byte>(oe2)
                                            in compile_ns_sub_c(sd2_d, lb4, ns2, nl2, sub2, sl2, lc, fuel6 - 1) end
                                          else let
                                            val @(fz_oe2, bv_oe2) = $A.freeze<byte>(oe2)
                                            var pb2 : $B.builder_v = $B.create()
                                            val () = bput_v(pb2, "build/bats_modules/")
                                            val () = copy_to_builder_v(ns2, 0, nl2, 256, pb2)
                                            val () = bput_v(pb2, "/")
                                            val () = copy_to_builder_v(sub2, 0, sl2, 256, pb2)
                                            val () = bput_v(pb2, "/src/")
                                            val () = copy_to_builder_v(bv_oe2, 0, oel2, 256, pb2)
                                            val () = put_char_v(pb2, 0)
                                            val @(pa2, pl2) = $B.to_arr(pb2)
                                            val @(fz_p2, bv_p2) = $A.freeze<byte>(pa2)
                                            val rc2 = wasm_cc_file(bv_p2, pl2)
                                          in if rc2 = 0 then let
                                              val () = copy_to_builder_v(bv_p2, 0, pl2 - 2, 524288, lb4)
                                              val () = bput_v(lb4, "o")
                                              val () = put_char_v(lb4, 0)
                                              val () = $A.drop<byte>(fz_p2, bv_p2)
                                              val () = $A.free<byte>($A.thaw<byte>(fz_p2))
                                              val () = $A.drop<byte>(fz_oe2, bv_oe2)
                                              val () = $A.free<byte>($A.thaw<byte>(fz_oe2))
                                            in compile_ns_sub_c(sd2_d, lb4, ns2, nl2, sub2, sl2, lc + 1, fuel6 - 1) end
                                            else let
                                              val () = bput_v(lb4, "")
                                              val () = $A.drop<byte>(fz_p2, bv_p2)
                                              val () = $A.free<byte>($A.thaw<byte>(fz_p2))
                                              val () = $A.drop<byte>(fz_oe2, bv_oe2)
                                              val () = $A.free<byte>($A.thaw<byte>(fz_oe2))
                                            in compile_ns_sub_c(sd2_d, lb4, ns2, nl2, sub2, sl2, lc, fuel6 - 1) end end
                                          end
                                        end
                                      val sc = compile_ns_sub_c(sd2_d, lb3, ns_bv, ns_len, bv_se, sl, lc, 200)
                                      val dcr4 = $F.dir_close(sd2_d)
                                      val () = $R.discard<int><int>(dcr4)
                                      val () = $A.drop<byte>(fz_sp2, bv_sp2)
                                      val () = $A.free<byte>($A.thaw<byte>(fz_sp2))
                                      val () = $A.drop<byte>(fz_se, bv_se)
                                      val () = $A.free<byte>($A.thaw<byte>(fz_se))
                                    in compile_ns_c(nsd_d, lb3, ns_bv, ns_len, sc, fuel5 - 1) end
                                  | ~$R.err(_) => let
                                      val () = bput_v(lb3, "")
                                      val () = $A.drop<byte>(fz_sp2, bv_sp2)
                                      val () = $A.free<byte>($A.thaw<byte>(fz_sp2))
                                      val () = $A.drop<byte>(fz_se, bv_se)
                                      val () = $A.free<byte>($A.thaw<byte>(fz_se))
                                    in compile_ns_c(nsd_d, lb3, ns_bv, ns_len, lc, fuel5 - 1) end) end
                            end
                          end
                        val nc = compile_ns_c(nsd_d, lb, bv_e, el, lc, 100)
                        val dcr5 = $F.dir_close(nsd_d)
                        val () = $R.discard<int><int>(dcr5)
                        val () = $A.drop<byte>(fz_sp, bv_sp)
                        val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                        val () = $A.drop<byte>(fz_e, bv_e)
                        val () = $A.free<byte>($A.thaw<byte>(fz_e))
                      in add_dep_objs(bm_d, lb, nc, fuel3 - 1) end
                    | ~$R.err(_) => let
                        val () = bput_v(lb, "")
                        val () = $A.drop<byte>(fz_sp, bv_sp)
                        val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                        val () = $A.drop<byte>(fz_e, bv_e)
                        val () = $A.free<byte>($A.thaw<byte>(fz_e))
                      in add_dep_objs(bm_d, lb, lc, fuel3 - 1) end)
                  end) end
            end
          end
        val dep_count = add_dep_objs(bm_d, link_b, link_count1, 500)
        val dcr3 = $F.dir_close(bm_d)
        val () = $R.discard<int><int>(dcr3)
      in dep_count end
    | ~$R.err(_) => let val () = bput_v(link_b, "") in link_count1 end): int
  (* Compile src module _dats.c files with wasm cc *)
  val src_dp = str_to_path_arr("build/src")
  val @(fz_sdp, bv_sdp) = $A.freeze<byte>(src_dp)
  val src_dr = $F.dir_open(bv_sdp, 524288)
  val () = $A.drop<byte>(fz_sdp, bv_sdp)
  val () = $A.free<byte>($A.thaw<byte>(fz_sdp))
  val link_count3 = (case+ src_dr of
    | ~$R.ok(sd) => let
        fun wasm_cc_src {fuel7:nat} .<fuel7>.
          (sd: !$F.dir, lb: !$B.builder_v >> $B.builder_v, lc: int, fuel7: int fuel7): int =
          if fuel7 <= 0 then lc
          else let
            val e = $A.alloc<byte>(256)
            val nr = $F.dir_next(sd, e, 256)
            val el = $R.option_unwrap_or<int>(nr, ~1)
          in if el < 0 then let val () = $A.free<byte>(e) in lc end
            else let
              val is_c = $S.has_suffix(e, el, 256, "_dats.c", 7)
            in if ~is_c then let val () = $A.free<byte>(e)
              in wasm_cc_src(sd, lb, lc, fuel7 - 1) end
            else let
              val @(fz_e, bv_e) = $A.freeze<byte>(e)
              var pb : $B.builder_v = $B.create()
              val () = bput_v(pb, "build/src/")
              val () = copy_to_builder_v(bv_e, 0, el, 256, pb)
              val () = put_char_v(pb, 0)
              val @(pa, pl) = $B.to_arr(pb)
              val @(fz_p, bv_p) = $A.freeze<byte>(pa)
              val rc = wasm_cc_file(bv_p, pl)
            in if rc = 0 then let
                val () = copy_to_builder_v(bv_p, 0, pl - 2, 524288, lb)
                val () = bput_v(lb, "o")
                val () = put_char_v(lb, 0)
                val () = $A.drop<byte>(fz_p, bv_p)
                val () = $A.free<byte>($A.thaw<byte>(fz_p))
                val () = $A.drop<byte>(fz_e, bv_e)
                val () = $A.free<byte>($A.thaw<byte>(fz_e))
              in wasm_cc_src(sd, lb, lc + 1, fuel7 - 1) end
              else let
                val () = bput_v(lb, "")
                val () = $A.drop<byte>(fz_p, bv_p)
                val () = $A.free<byte>($A.thaw<byte>(fz_p))
                val () = $A.drop<byte>(fz_e, bv_e)
                val () = $A.free<byte>($A.thaw<byte>(fz_e))
              in wasm_cc_src(sd, lb, lc, fuel7 - 1) end end
            end
          end
        val sc = wasm_cc_src(sd, link_b, link_count2, 200)
        val dcr6 = $F.dir_close(sd)
        val () = $R.discard<int><int>(dcr6)
      in sc end
    | ~$R.err(_) => let val () = bput_v(link_b, "") in link_count2 end): int
  (* Compile src/bin _dats.c files with wasm cc *)
  val bin_dp = str_to_path_arr("build/src/bin")
  val @(fz_bdp, bv_bdp) = $A.freeze<byte>(bin_dp)
  val bin_dr = $F.dir_open(bv_bdp, 524288)
  val () = $A.drop<byte>(fz_bdp, bv_bdp)
  val () = $A.free<byte>($A.thaw<byte>(fz_bdp))
  val link_count4 = (case+ bin_dr of
    | ~$R.ok(bd) => let
        fun wasm_cc_bin {fuel8:nat} .<fuel8>.
          (bd: !$F.dir, lb: !$B.builder_v >> $B.builder_v, lc: int, fuel8: int fuel8): int =
          if fuel8 <= 0 then lc
          else let
            val e = $A.alloc<byte>(256)
            val nr = $F.dir_next(bd, e, 256)
            val el = $R.option_unwrap_or<int>(nr, ~1)
          in if el < 0 then let val () = $A.free<byte>(e) in lc end
            else let
              val is_c = $S.has_suffix(e, el, 256, "_dats.c", 7)
            in if ~is_c then let val () = $A.free<byte>(e)
              in wasm_cc_bin(bd, lb, lc, fuel8 - 1) end
            else let
              val @(fz_e, bv_e) = $A.freeze<byte>(e)
              var pb : $B.builder_v = $B.create()
              val () = bput_v(pb, "build/src/bin/")
              val () = copy_to_builder_v(bv_e, 0, el, 256, pb)
              val () = put_char_v(pb, 0)
              val @(pa, pl) = $B.to_arr(pb)
              val @(fz_p, bv_p) = $A.freeze<byte>(pa)
              val rc = wasm_cc_file(bv_p, pl)
            in if rc = 0 then let
                val () = copy_to_builder_v(bv_p, 0, pl - 2, 524288, lb)
                val () = bput_v(lb, "o")
                val () = put_char_v(lb, 0)
                val () = $A.drop<byte>(fz_p, bv_p)
                val () = $A.free<byte>($A.thaw<byte>(fz_p))
                val () = $A.drop<byte>(fz_e, bv_e)
                val () = $A.free<byte>($A.thaw<byte>(fz_e))
              in wasm_cc_bin(bd, lb, lc + 1, fuel8 - 1) end
              else let
                val () = bput_v(lb, "")
                val () = $A.drop<byte>(fz_p, bv_p)
                val () = $A.free<byte>($A.thaw<byte>(fz_p))
                val () = $A.drop<byte>(fz_e, bv_e)
                val () = $A.free<byte>($A.thaw<byte>(fz_e))
              in wasm_cc_bin(bd, lb, lc, fuel8 - 1) end end
            end
          end
        val bc = wasm_cc_bin(bd, link_b, link_count3, 200)
        val dcr7 = $F.dir_close(bd)
        val () = $R.discard<int><int>(dcr7)
      in bc end
    | ~$R.err(_) => let val () = bput_v(link_b, "") in link_count3 end): int
  val () = println! ("  linking WASM...")
  var mb1 : $B.builder_v = $B.create()
  val () = bput_v(mb1, "dist")
  val _ = run_mkdir(mb1)
  var mb2 : $B.builder_v = $B.create()
  val () = bput_v(mb2, "dist/wasm")
  val _ = run_mkdir(mb2)
  val exec_ld = str_to_path_arr("/usr/bin/wasm-ld")
  val @(fz_ld, bv_ld) = $A.freeze<byte>(exec_ld)
  val lrc = run_cmd(bv_ld, 524288, link_b, link_count4)
  val () = $A.drop<byte>(fz_ld, bv_ld)
  val () = $A.free<byte>($A.thaw<byte>(fz_ld))
  val () = (if lrc <> 0 then println! ("error: wasm-ld failed") else println! ("  built: dist/wasm/app.wasm"))
in end

#pub fn read_unsafe_flag(): int

implement read_unsafe_flag() = let
  val bt = str_to_path_arr("bats.toml")
  val @(fz_bt, bv_bt) = $A.freeze<byte>(bt)
  val r = $F.file_open(bv_bt, 524288, 0, 0)
  val () = $A.drop<byte>(fz_bt, bv_bt)
  val () = $A.free<byte>($A.thaw<byte>(fz_bt))
in case+ r of
  | ~$R.ok(fd) => let
      val buf = $A.alloc<byte>(4096)
      val rr = $F.file_read(fd, buf, 4096)
      val bl = (case+ rr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val cr = $F.file_close(fd)
      val () = $R.discard<int><int>(cr)
      val @(fz_b, bv_b) = $A.freeze<byte>(buf)
      val pr = $T.parse(bv_b, 4096)
      val () = $A.drop<byte>(fz_b, bv_b)
      val () = $A.free<byte>($A.thaw<byte>(fz_b))
    in case+ pr of
      | ~$R.ok(doc) => let
          val @(sk, skl) = $S.str_to_borrow("package")
          val @(fz_sk, bv_sk) = $A.freeze<byte>(sk)
          val @(uk, ukl) = $S.str_to_borrow("unsafe")
          val @(fz_uk, bv_uk) = $A.freeze<byte>(uk)
          val ubuf = $A.alloc<byte>(32)
          val ur = $T.get(doc, bv_sk, skl, bv_uk, ukl, ubuf, 32)
          val () = $A.drop<byte>(fz_uk, bv_uk)
          val () = $A.free<byte>($A.thaw<byte>(fz_uk))
          val () = $A.drop<byte>(fz_sk, bv_sk)
          val () = $A.free<byte>($A.thaw<byte>(fz_sk))
          val result = (case+ ur of
            | ~$R.some(len) => let
                (* Check if value starts with 't' for "true" *)
                val b0 = byte2int0($A.get<byte>(ubuf, 0))
                val () = $A.free<byte>(ubuf)
              in if $AR.eq_int_int(b0, 116) then 1 else 0 end
            | ~$R.none() => let
                val () = $A.free<byte>(ubuf)
              in 0 end): int
          val () = $T.toml_free(doc)
        in result end
      | ~$R.err(_) => 0
    end
  | ~$R.err(_) => 0
end

(* Check if a .bats source file starts with "#target wasm binary" *)
#pub fn check_wasm_binary {l:agz}
  (path: !$A.borrow(byte, l, 524288)): int

implement check_wasm_binary(path) = let
  val r = $F.file_open(path, 524288, 0, 0)
in case+ r of
  | ~$R.ok(fd) => let
      val buf = $A.alloc<byte>(32)
      val rr = $F.file_read(fd, buf, 32)
      val bl = (case+ rr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val cr = $F.file_close(fd)
      val () = $R.discard<int><int>(cr)
      val @(fz_buf, bv_buf) = $A.freeze<byte>(buf)
      (* Check for '#' then "target wasm binary" — split to avoid lexer
         interpreting #target inside the string *)
      val ok = (if bl >= 19 then
        $AR.eq_int_int($S.borrow_byte(bv_buf, 0, 32), 35) &&
        $S.chars_match_borrow(bv_buf, 1, 32, "target wasm binary", 0, 18)
      else false): bool
      val () = $A.drop<byte>(fz_buf, bv_buf)
      val () = $A.free<byte>($A.thaw<byte>(fz_buf))
    in (if ok then 1 else 0) end
  | ~$R.err(_) => 0
end

#pub fn do_build(release: int, build_target: int): void

implement do_build(release, build_target) = let
  val is_unsafe = read_unsafe_flag()
  (* Step 1: mkdir build directories *)
  var mb1 : $B.builder_v = $B.create()
  val () = bput_v(mb1, "build/src/bin")
  val _ = run_mkdir(mb1)
  var mb2 : $B.builder_v = $B.create()
  val () = bput_v(mb2, "build/bats_modules")
  val _ = run_mkdir(mb2)
  var mb3 : $B.builder_v = $B.create()
  val () = bput_v(mb3, "dist/debug")
  val _ = run_mkdir(mb3)
  var mb4 : $B.builder_v = $B.create()
  val () = bput_v(mb4, "dist/release")
  val r0 = run_mkdir(mb4)
  val () = (if r0 <> 0 then println! ("error: mkdir failed") else ())
in
  if r0 <> 0 then ()
  else let
    (* Step 1b: Write and compile native runtime *)
    var nrt_b : $B.builder_v = $B.create()
    val () = bput_v(nrt_b, "/* _bats_native_runtime.c -- ATS2 memory allocator backed by libc */\n")
    val () = bput_v(nrt_b, "#include <stdlib.h>\n")
    val () = bput_v(nrt_b, "void atsruntime_mfree_undef(void *ptr) { free(ptr); }\n")
    val () = bput_v(nrt_b, "void *atsruntime_malloc_undef(size_t bsz) { return malloc(bsz); }\n")
    val () = bput_v(nrt_b, "void *atsruntime_calloc_undef(size_t asz, size_t tsz) { return calloc(asz, tsz); }\n")
    val () = bput_v(nrt_b, "void *atsruntime_realloc_undef(void *ptr, size_t bsz) { return realloc(ptr, bsz); }\n")
    val nrt_path = str_to_path_arr("build/_bats_native_runtime.c")
    val @(fz_nrtp, bv_nrtp) = $A.freeze<byte>(nrt_path)
    val _ = write_file_from_builder(bv_nrtp, 524288, nrt_b)
    val () = $A.drop<byte>(fz_nrtp, bv_nrtp)
    val () = $A.free<byte>($A.thaw<byte>(fz_nrtp))
    val nrt_exec = str_to_path_arr("/usr/bin/clang")
    val @(fz_nrt_exec, bv_nrt_exec) = $A.freeze<byte>(nrt_exec)
    var nrt_argv : $B.builder_v = $B.create()
    val () = bput_v(nrt_argv, "clang") val () = put_char_v(nrt_argv, 0)
    val () = bput_v(nrt_argv, "-c") val () = put_char_v(nrt_argv, 0)
    val () = bput_v(nrt_argv, "-o") val () = put_char_v(nrt_argv, 0)
    val () = bput_v(nrt_argv, "build/_bats_native_runtime.o") val () = put_char_v(nrt_argv, 0)
    val () = bput_v(nrt_argv, "build/_bats_native_runtime.c") val () = put_char_v(nrt_argv, 0)
    val nrt_r = run_cmd(bv_nrt_exec, 524288, nrt_argv, 5)
    val () = $A.drop<byte>(fz_nrt_exec, bv_nrt_exec)
    val () = $A.free<byte>($A.thaw<byte>(fz_nrt_exec))
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
      if pos < 0 then pos
      else if pos + 10 >= 512 then pos
      else let
        val () = $A.set<byte>(buf, $AR.checked_idx(pos,512), int2byte0(47))
        val () = $A.set<byte>(buf, $AR.checked_idx(pos+1,512), int2byte0(46))
        val () = $A.set<byte>(buf, $AR.checked_idx(pos+2,512), int2byte0(98))
        val () = $A.set<byte>(buf, $AR.checked_idx(pos+3,512), int2byte0(97))
        val () = $A.set<byte>(buf, $AR.checked_idx(pos+4,512), int2byte0(116))
        val () = $A.set<byte>(buf, $AR.checked_idx(pos+5,512), int2byte0(115))
        val () = $A.set<byte>(buf, $AR.checked_idx(pos+6,512), int2byte0(47))
        val () = $A.set<byte>(buf, $AR.checked_idx(pos+7,512), int2byte0(97))
        val () = $A.set<byte>(buf, $AR.checked_idx(pos+8,512), int2byte0(116))
        val () = $A.set<byte>(buf, $AR.checked_idx(pos+9,512), int2byte0(115))
        val () = $A.set<byte>(buf, $AR.checked_idx(pos+10,512), int2byte0(50))
      in pos + 11 end
    val phlen = append_bats_path(phbuf, hlen)
    (* Check if patsopt exists, install if not — single freeze *)
    (* Copy arr bytes to builder — uses src_byte to avoid !arr in conditional *)
    fun arr_to_builder {l:agz}{fuel:nat} .<fuel>.
      (buf: !$A.borrow(byte, l, 512), pos: int, len: int,
       dst: !$B.builder_v >> $B.builder_v, fuel: int fuel): void =
      if fuel <= 0 then ()
      else if pos >= len then ()
      else let
        val b = $S.borrow_byte(buf, pos, 512)
        val () = put_char_v(dst, b)
      in arr_to_builder(buf, pos + 1, len, dst, fuel - 1) end
    fn ensure_ats2 {l:agz}
      (buf: !$A.borrow(byte, l, 512), plen: int): void = let
      (* Check if patsopt exists by trying to stat it *)
      var test_path : $B.builder_v = $B.create()
      val () = arr_to_builder(buf, 0, plen, test_path, 512)
      val () = bput_v(test_path, "/bin/patsopt")
      val () = put_char_v(test_path, 0)
      val @(tp_arr, _) = $B.to_arr(test_path)
      val @(fz_tp, bv_tp) = $A.freeze<byte>(tp_arr)
      val exists = (case+ $F.file_mtime(bv_tp, 524288) of
        | ~$R.ok(_) => true | ~$R.err(_) => false): bool
      val () = $A.drop<byte>(fz_tp, bv_tp)
      val () = $A.free<byte>($A.thaw<byte>(fz_tp))
      val rc = (if exists then 0
      else let
        val () = println! ("ATS2 not found, installing...")
        (* mkdir -p <patshome> *)
        var mkb : $B.builder_v = $B.create()
        val () = arr_to_builder(buf, 0, plen, mkb, 512)
        val _ = run_mkdir(mkb)
        (* curl -sL <url> -o /tmp/_bpoc_ats2.tgz *)
        val curl_exec = str_to_path_arr("/usr/bin/curl")
        val @(fz_ce, bv_ce) = $A.freeze<byte>(curl_exec)
        var curl_argv : $B.builder_v = $B.create()
        val () = bput_v(curl_argv, "curl") val () = put_char_v(curl_argv, 0)
        val () = bput_v(curl_argv, "-sL") val () = put_char_v(curl_argv, 0)
        val () = bput_v(curl_argv, "https://raw.githubusercontent.com/ats-lang/ats-lang.github.io/master/FROZEN000/ATS-Postiats/ATS2-Postiats-int-0.4.2.tgz")
        val () = put_char_v(curl_argv, 0)
        val () = bput_v(curl_argv, "-o") val () = put_char_v(curl_argv, 0)
        val () = bput_v(curl_argv, "/tmp/_bpoc_ats2.tgz") val () = put_char_v(curl_argv, 0)
        val r1 = run_cmd(bv_ce, 524288, curl_argv, 5)
        val () = $A.drop<byte>(fz_ce, bv_ce)
        val () = $A.free<byte>($A.thaw<byte>(fz_ce))
        (* tar -xzf /tmp/_bpoc_ats2.tgz --strip-components=1 -C <patshome> *)
        val tar_exec = str_to_path_arr("/usr/bin/tar")
        val @(fz_te, bv_te) = $A.freeze<byte>(tar_exec)
        var tar_argv : $B.builder_v = $B.create()
        val () = bput_v(tar_argv, "tar") val () = put_char_v(tar_argv, 0)
        val () = bput_v(tar_argv, "-xzf") val () = put_char_v(tar_argv, 0)
        val () = bput_v(tar_argv, "/tmp/_bpoc_ats2.tgz") val () = put_char_v(tar_argv, 0)
        val () = bput_v(tar_argv, "--strip-components=1") val () = put_char_v(tar_argv, 0)
        val () = bput_v(tar_argv, "-C") val () = put_char_v(tar_argv, 0)
        val () = arr_to_builder(buf, 0, plen, tar_argv, 512)
        val () = put_char_v(tar_argv, 0)
        val r2 = run_cmd(bv_te, 524288, tar_argv, 6)
        val () = $A.drop<byte>(fz_te, bv_te)
        val () = $A.free<byte>($A.thaw<byte>(fz_te))
        (* rm /tmp/_bpoc_ats2.tgz *)
        val rm_exec = str_to_path_arr("/bin/rm")
        val @(fz_re, bv_re) = $A.freeze<byte>(rm_exec)
        var rm_argv : $B.builder_v = $B.create()
        val () = bput_v(rm_argv, "rm") val () = put_char_v(rm_argv, 0)
        val () = bput_v(rm_argv, "/tmp/_bpoc_ats2.tgz") val () = put_char_v(rm_argv, 0)
        val _ = run_cmd(bv_re, 524288, rm_argv, 2)
        val () = $A.drop<byte>(fz_re, bv_re)
        val () = $A.free<byte>($A.thaw<byte>(fz_re))
        (* make -j4 -C <patshome>/src/CBOOT patsopt PATSHOME=<patshome> *)
        val () = println! ("building ATS2...")
        val make_exec = str_to_path_arr("/usr/bin/make")
        val @(fz_me, bv_me) = $A.freeze<byte>(make_exec)
        var make_argv : $B.builder_v = $B.create()
        val () = bput_v(make_argv, "make") val () = put_char_v(make_argv, 0)
        val () = bput_v(make_argv, "-j4") val () = put_char_v(make_argv, 0)
        val () = bput_v(make_argv, "-C") val () = put_char_v(make_argv, 0)
        val () = arr_to_builder(buf, 0, plen, make_argv, 512)
        val () = bput_v(make_argv, "/src/CBOOT") val () = put_char_v(make_argv, 0)
        val () = bput_v(make_argv, "patsopt") val () = put_char_v(make_argv, 0)
        var phome_arg : $B.builder_v = $B.create()
        val () = bput_v(phome_arg, "PATSHOME=")
        val () = arr_to_builder(buf, 0, plen, phome_arg, 512)
        val @(pha, phl) = $B.to_arr(phome_arg)
        val @(fz_pha, bv_pha) = $A.freeze<byte>(pha)
        val () = copy_to_builder_v(bv_pha, 0, phl, 524288, make_argv)
        val () = put_char_v(make_argv, 0)
        val () = $A.drop<byte>(fz_pha, bv_pha)
        val () = $A.free<byte>($A.thaw<byte>(fz_pha))
        val r3 = run_cmd(bv_me, 524288, make_argv, 6)
        val () = $A.drop<byte>(fz_me, bv_me)
        val () = $A.free<byte>($A.thaw<byte>(fz_me))
        (* mkdir -p <patshome>/bin *)
        var mkb2 : $B.builder_v = $B.create()
        val () = arr_to_builder(buf, 0, plen, mkb2, 512)
        val () = bput_v(mkb2, "/bin")
        val _ = run_mkdir(mkb2)
        (* cp <patshome>/src/CBOOT/patsopt <patshome>/bin/patsopt *)
        val cp_exec = str_to_path_arr("/bin/cp")
        val @(fz_cpe, bv_cpe) = $A.freeze<byte>(cp_exec)
        var cp_argv : $B.builder_v = $B.create()
        val () = bput_v(cp_argv, "cp") val () = put_char_v(cp_argv, 0)
        val () = arr_to_builder(buf, 0, plen, cp_argv, 512)
        val () = bput_v(cp_argv, "/src/CBOOT/patsopt") val () = put_char_v(cp_argv, 0)
        val () = arr_to_builder(buf, 0, plen, cp_argv, 512)
        val () = bput_v(cp_argv, "/bin/patsopt") val () = put_char_v(cp_argv, 0)
        val r4 = run_cmd(bv_cpe, 524288, cp_argv, 3)
        val () = $A.drop<byte>(fz_cpe, bv_cpe)
        val () = $A.free<byte>($A.thaw<byte>(fz_cpe))
        val () = println! ("ATS2 installed successfully")
      in r1 + r2 + r3 + r4 end): int
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

      (* Read old target marker to detect target change, then write new one.
         target_changed is passed to preprocess_one to force reprocessing. *)
      val tgt_path_r = str_to_path_arr("build/.bats_target")
      val @(fz_tgtr, bv_tgtr) = $A.freeze<byte>(tgt_path_r)
      val old_tgt_or = $F.file_open(bv_tgtr, 524288, 0, 0)
      val old_target = (case+ old_tgt_or of
        | ~$R.ok(otfd) => let
            val otb = $A.alloc<byte>(16)
            val otr = $F.file_read(otfd, otb, 16)
            val otl = (case+ otr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
            val otc = $F.file_close(otfd)
            val () = $R.discard<int><int>(otc)
            val ob = byte2int0($A.get<byte>(otb, 0))
            val () = $A.free<byte>(otb)
          in (if otl > 0 then ob - 48 else ~1): int end
        | ~$R.err(_) => ~1): int
      val () = $A.drop<byte>(fz_tgtr, bv_tgtr)
      val () = $A.free<byte>($A.thaw<byte>(fz_tgtr))
      (* If target changed, preprocess_one will force reprocessing *)
      val target_changed = ~($AR.eq_int_int(old_target, build_target))
      (* Now write new target marker *)
      var tgt_b : $B.builder_v = $B.create()
      val () = bput_v(tgt_b, (if $AR.eq_int_int(build_target, 1) then "1" else "0"))
      val tgt_path = str_to_path_arr("build/.bats_target")
      val @(fz_tgtp, bv_tgtp) = $A.freeze<byte>(tgt_path)
      val _ = write_file_from_builder(bv_tgtp, 524288, tgt_b)
      val () = $A.drop<byte>(fz_tgtp, bv_tgtp)
      val () = $A.free<byte>($A.thaw<byte>(fz_tgtp))

      (* Step 3: Scan bats_modules/ for deps and preprocess *)
      val bm_arr = str_to_path_arr("bats_modules")
      val @(fz_bm, bv_bm) = $A.freeze<byte>(bm_arr)
      val bmdir_r = $F.dir_open(bv_bm, 524288)
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
                    (* Check if this is a package (has bats.toml) or a namespace dir *)
                    var chk_b : $B.builder_v = $B.create()
                    val () = bput_v(chk_b, "bats_modules/")
                    val () = copy_to_builder_v(bv_e, 0, elen, 256, chk_b)
                    val () = bput_v(chk_b, "/bats.toml")
                    val () = put_char_v(chk_b, 0)
                    val @(chk_a, _) = $B.to_arr(chk_b)
                    val @(fz_chk, bv_chk) = $A.freeze<byte>(chk_a)
                    val chk_or = $F.file_mtime(bv_chk, 524288)
                    val is_pkg = (case+ chk_or of
                      | ~$R.ok(_) => true | ~$R.err(_) => false): bool
                    val () = $A.drop<byte>(fz_chk, bv_chk)
                    val () = $A.free<byte>($A.thaw<byte>(fz_chk))
                  in
                    if ~is_pkg then let
                      (* Namespace directory: scan subdirs as packages *)
                      var nsd : $B.builder_v = $B.create()
                      val () = bput_v(nsd, "bats_modules/")
                      val () = copy_to_builder_v(bv_e, 0, elen, 256, nsd)
                      val () = put_char_v(nsd, 0)
                      val @(nsd_a, _) = $B.to_arr(nsd)
                      val @(fz_nsd, bv_nsd) = $A.freeze<byte>(nsd_a)
                      val nsd_r = $F.dir_open(bv_nsd, 524288)
                      val () = $A.drop<byte>(fz_nsd, bv_nsd)
                      val () = $A.free<byte>($A.thaw<byte>(fz_nsd))
                      val () = (case+ nsd_r of
                        | ~$R.ok(nsd2) => let
                            (* Process each subdir as if it were a top-level dep
                               with name <namespace>/<subdir> *)
                            fun scan_ns {lph2:agz}{lns:agz}{fuel2:nat} .<fuel2>.
                              (nsd2: !$F.dir, ph2: !$A.borrow(byte, lph2, 512),
                               ns_bv: !$A.borrow(byte, lns, 256), ns_len: int,
                               fuel2: int fuel2): void =
                              if fuel2 <= 0 then ()
                              else let
                                val se = $A.alloc<byte>(256)
                                val snr = $F.dir_next(nsd2, se, 256)
                                val sel = $R.option_unwrap_or<int>(snr, ~1)
                              in
                                if sel < 0 then $A.free<byte>(se)
                                else let
                                  val sdd = is_dot_or_dotdot(se, sel, 256)
                                in
                                  if sdd then let val () = $A.free<byte>(se)
                                  in scan_ns(nsd2, ph2, ns_bv, ns_len, fuel2 - 1) end
                                  else let
                                    val @(fz_se, bv_se) = $A.freeze<byte>(se)
                                    (* Build full dep name: <namespace>/<subdir> *)
                                    (* mkdir build/bats_modules/<namespace>/<subdir>/src *)
                                    var mc2 : $B.builder_v = $B.create()
                                    val () = bput_v(mc2, "build/bats_modules/")
                                    val () = copy_to_builder_v(ns_bv, 0, ns_len, 256, mc2)
                                    val () = bput_v(mc2, "/")
                                    val () = copy_to_builder_v(bv_se, 0, sel, 256, mc2)
                                    val () = bput_v(mc2, "/src")
                                    val _ = run_mkdir(mc2)
                                    (* source *)
                                    var sp2 : $B.builder_v = $B.create()
                                    val () = bput_v(sp2, "bats_modules/")
                                    val () = copy_to_builder_v(ns_bv, 0, ns_len, 256, sp2)
                                    val () = bput_v(sp2, "/")
                                    val () = copy_to_builder_v(bv_se, 0, sel, 256, sp2)
                                    val () = bput_v(sp2, "/src/lib.bats")
                                    val () = put_char_v(sp2, 0)
                                    val @(sa2, _) = $B.to_arr(sp2)
                                    val @(fz_sp2, bv_sp2) = $A.freeze<byte>(sa2)
                                    (* sats *)
                                    var ss2 : $B.builder_v = $B.create()
                                    val () = bput_v(ss2, "build/bats_modules/")
                                    val () = copy_to_builder_v(ns_bv, 0, ns_len, 256, ss2)
                                    val () = bput_v(ss2, "/")
                                    val () = copy_to_builder_v(bv_se, 0, sel, 256, ss2)
                                    val () = bput_v(ss2, "/src/lib.sats")
                                    val () = put_char_v(ss2, 0)
                                    val @(ssa2, _) = $B.to_arr(ss2)
                                    val @(fz_ss2, bv_ss2) = $A.freeze<byte>(ssa2)
                                    (* dats *)
                                    var sd2 : $B.builder_v = $B.create()
                                    val () = bput_v(sd2, "build/bats_modules/")
                                    val () = copy_to_builder_v(ns_bv, 0, ns_len, 256, sd2)
                                    val () = bput_v(sd2, "/")
                                    val () = copy_to_builder_v(bv_se, 0, sel, 256, sd2)
                                    val () = bput_v(sd2, "/src/lib.dats")
                                    val () = put_char_v(sd2, 0)
                                    val @(sda2, _) = $B.to_arr(sd2)
                                    val @(fz_sd2, bv_sd2) = $A.freeze<byte>(sda2)
                                    val pr2 = preprocess_one(bv_sp2, bv_ss2, bv_sd2, build_target, 1, target_changed)
                                    val () = (if pr2 <> 0 then let
                                      val () = print! ("warning: preprocess failed for dep ")
                                      val () = print_borrow(ns_bv, 0, ns_len, 256, 256)
                                      val () = print! ("/")
                                      val () = print_borrow(bv_se, 0, sel, 256, 256)
                                    in print_newline() end
                                    else if ~is_quiet() then let
                                      val () = print! ("  preprocessed dep: ")
                                      val () = print_borrow(ns_bv, 0, ns_len, 256, 256)
                                      val () = print! ("/")
                                      val () = print_borrow(bv_se, 0, sel, 256, 256)
                                    in print_newline() end
                                    else ())
                                    val () = $A.drop<byte>(fz_sp2, bv_sp2)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_sp2))
                                    val () = $A.drop<byte>(fz_ss2, bv_ss2)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_ss2))
                                    val () = $A.drop<byte>(fz_sd2, bv_sd2)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_sd2))
                                    (* Scan extra .bats shared modules for this namespaced dep *)
                                    var nsd_src : $B.builder_v = $B.create()
                                    val () = bput_v(nsd_src, "bats_modules/")
                                    val () = copy_to_builder_v(ns_bv, 0, ns_len, 256, nsd_src)
                                    val () = bput_v(nsd_src, "/")
                                    val () = copy_to_builder_v(bv_se, 0, sel, 256, nsd_src)
                                    val () = bput_v(nsd_src, "/src")
                                    val () = put_char_v(nsd_src, 0)
                                    val @(nsd_sa, _) = $B.to_arr(nsd_src)
                                    val @(fz_nsd, bv_nsd) = $A.freeze<byte>(nsd_sa)
                                    val nsd_dir = $F.dir_open(bv_nsd, 524288)
                                    val () = $A.drop<byte>(fz_nsd, bv_nsd)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_nsd))
                                    val () = (case+ nsd_dir of
                                      | ~$R.ok(d_ns_ex) => let
                                          fun scan_ns_extra
                                            {ld2:agz}{ld3:agz}{fuel_ns:nat} .<fuel_ns>.
                                            (d_ns_ex: !$F.dir,
                                             ns_bv2: !$A.borrow(byte, ld2, 256),
                                             ns_len2: int,
                                             se_bv2: !$A.borrow(byte, ld3, 256),
                                             se_len2: int,
                                             fuel_ns: int fuel_ns): void =
                                            if fuel_ns <= 0 then ()
                                            else let
                                              val ent_ns = $A.alloc<byte>(256)
                                              val nr_ns = $F.dir_next(d_ns_ex, ent_ns, 256)
                                              val elen_ns = $R.option_unwrap_or<int>(nr_ns, ~1)
                                            in
                                              if elen_ns < 0 then $A.free<byte>(ent_ns)
                                              else let
                                                val is_bats_ns = has_bats_ext(ent_ns, elen_ns, 256)
                                                val is_lib_ns = is_lib_bats(ent_ns, elen_ns, 256)
                                              in
                                                if is_bats_ns then
                                                  if is_lib_ns then let
                                                    val () = $A.free<byte>(ent_ns)
                                                  in scan_ns_extra(d_ns_ex, ns_bv2, ns_len2, se_bv2, se_len2, fuel_ns - 1) end
                                                  else let
                                                    val stem_ns = elen_ns - 5
                                                    val @(fz_ens, bv_ens) = $A.freeze<byte>(ent_ns)
                                                    var sp_ns : $B.builder_v = $B.create()
                                                    val () = bput_v(sp_ns, "bats_modules/")
                                                    val () = copy_to_builder_v(ns_bv2, 0, ns_len2, 256, sp_ns)
                                                    val () = bput_v(sp_ns, "/")
                                                    val () = copy_to_builder_v(se_bv2, 0, se_len2, 256, sp_ns)
                                                    val () = bput_v(sp_ns, "/src/")
                                                    val () = copy_to_builder_v(bv_ens, 0, elen_ns, 256, sp_ns)
                                                    val () = put_char_v(sp_ns, 0)
                                                    val @(spa_ns, _) = $B.to_arr(sp_ns)
                                                    val @(fz_spn, bv_spn) = $A.freeze<byte>(spa_ns)
                                                    var ss_ns : $B.builder_v = $B.create()
                                                    val () = bput_v(ss_ns, "build/bats_modules/")
                                                    val () = copy_to_builder_v(ns_bv2, 0, ns_len2, 256, ss_ns)
                                                    val () = bput_v(ss_ns, "/")
                                                    val () = copy_to_builder_v(se_bv2, 0, se_len2, 256, ss_ns)
                                                    val () = bput_v(ss_ns, "/src/")
                                                    val () = copy_to_builder_v(bv_ens, 0, stem_ns, 256, ss_ns)
                                                    val () = bput_v(ss_ns, ".sats")
                                                    val () = put_char_v(ss_ns, 0)
                                                    val @(ssa_ns, _) = $B.to_arr(ss_ns)
                                                    val @(fz_ssn, bv_ssn) = $A.freeze<byte>(ssa_ns)
                                                    var sd_ns : $B.builder_v = $B.create()
                                                    val () = bput_v(sd_ns, "build/bats_modules/")
                                                    val () = copy_to_builder_v(ns_bv2, 0, ns_len2, 256, sd_ns)
                                                    val () = bput_v(sd_ns, "/")
                                                    val () = copy_to_builder_v(se_bv2, 0, se_len2, 256, sd_ns)
                                                    val () = bput_v(sd_ns, "/src/")
                                                    val () = copy_to_builder_v(bv_ens, 0, stem_ns, 256, sd_ns)
                                                    val () = bput_v(sd_ns, ".dats")
                                                    val () = put_char_v(sd_ns, 0)
                                                    val @(sda_ns, _) = $B.to_arr(sd_ns)
                                                    val @(fz_sdn, bv_sdn) = $A.freeze<byte>(sda_ns)
                                                    val pr_ns = preprocess_one(bv_spn, bv_ssn, bv_sdn, build_target, 1, target_changed)
                                                    val () = (if pr_ns <> 0 then ()
                                                    else if ~is_quiet() then let
                                                      val () = print! ("  preprocessed dep extra: ")
                                                      val () = print_borrow(bv_ens, 0, elen_ns, 256, 256)
                                                    in print_newline() end
                                                    else ())
                                                    val () = $A.drop<byte>(fz_spn, bv_spn)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_spn))
                                                    val () = $A.drop<byte>(fz_ssn, bv_ssn)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_ssn))
                                                    val () = $A.drop<byte>(fz_sdn, bv_sdn)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_sdn))
                                                    val () = $A.drop<byte>(fz_ens, bv_ens)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_ens))
                                                  in scan_ns_extra(d_ns_ex, ns_bv2, ns_len2, se_bv2, se_len2, fuel_ns - 1) end
                                                else let
                                                  val () = $A.free<byte>(ent_ns)
                                                in scan_ns_extra(d_ns_ex, ns_bv2, ns_len2, se_bv2, se_len2, fuel_ns - 1) end
                                              end
                                            end
                                        in
                                          scan_ns_extra(d_ns_ex, ns_bv, ns_len, bv_se, sel, 100);
                                          (let val dcr = $F.dir_close(d_ns_ex) val () = $R.discard<int><int>(dcr) in end)
                                        end
                                      | ~$R.err(_) => ())
                                    val () = $A.drop<byte>(fz_se, bv_se)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_se))
                                  in scan_ns(nsd2, ph2, ns_bv, ns_len, fuel2 - 1) end
                                end
                              end
                            val () = scan_ns(nsd2, ph, bv_e, elen, 100)
                            val dcr_ns = $F.dir_close(nsd2)
                            val () = $R.discard<int><int>(dcr_ns)
                          in end
                        | ~$R.err(_) => ())
                      val () = $A.drop<byte>(fz_e, bv_e)
                      val () = $A.free<byte>($A.thaw<byte>(fz_e))
                    in scan_deps(d, ph, fuel - 1) end
                    else let
                    (* Regular package *)
                    (* mkdir -p build/bats_modules/<name>/src *)
                    var mc : $B.builder_v = $B.create()
                    val () = bput_v(mc, "build/bats_modules/")
                    val () = copy_to_builder_v(bv_e, 0, elen, 256, mc)
                    val () = bput_v(mc, "/src")
                    val _ = run_mkdir(mc)
                    (* source: bats_modules/<name>/src/lib.bats *)
                    var sp : $B.builder_v = $B.create()
                    val () = bput_v(sp, "bats_modules/")
                    val () = copy_to_builder_v(bv_e, 0, elen, 256, sp)
                    val () = bput_v(sp, "/src/lib.bats")
                    val () = put_char_v(sp, 0)
                    val @(sa, _) = $B.to_arr(sp)
                    val @(fz_sp, bv_sp) = $A.freeze<byte>(sa)
                    (* sats: build/bats_modules/<name>/src/lib.sats *)
                    var ss : $B.builder_v = $B.create()
                    val () = bput_v(ss, "build/bats_modules/")
                    val () = copy_to_builder_v(bv_e, 0, elen, 256, ss)
                    val () = bput_v(ss, "/src/lib.sats")
                    val () = put_char_v(ss, 0)
                    val @(ssa, _) = $B.to_arr(ss)
                    val @(fz_ss, bv_ss) = $A.freeze<byte>(ssa)
                    (* dats: build/bats_modules/<name>/src/lib.dats *)
                    var sd : $B.builder_v = $B.create()
                    val () = bput_v(sd, "build/bats_modules/")
                    val () = copy_to_builder_v(bv_e, 0, elen, 256, sd)
                    val () = bput_v(sd, "/src/lib.dats")
                    val () = put_char_v(sd, 0)
                    val @(sda, _) = $B.to_arr(sd)
                    val @(fz_sd, bv_sd) = $A.freeze<byte>(sda)
                    val pr = preprocess_one(bv_sp, bv_ss, bv_sd, build_target, 1, target_changed)
                    val () = (if pr <> 0 then let
                      val () = print! ("warning: preprocess failed for dep ")
                      val () = print_borrow(bv_e, 0, elen, 256, 256)
                    in print_newline() end
                    else if ~is_quiet() then let
                      val () = print! ("  preprocessed dep: ")
                      val () = print_borrow(bv_e, 0, elen, 256, 256)
                    in print_newline() end
                    else ())
                    (* Scan additional .bats files in this dep *)
                    var dep_src_b : $B.builder_v = $B.create()
                    val () = bput_v(dep_src_b, "bats_modules/")
                    val () = copy_to_builder_v(bv_e, 0, elen, 256, dep_src_b)
                    val () = bput_v(dep_src_b, "/src")
                    val () = put_char_v(dep_src_b, 0)
                    val @(dsp_arr, _) = $B.to_arr(dep_src_b)
                    val @(fz_dsp, bv_dsp) = $A.freeze<byte>(dsp_arr)
                    val dep_src_dir = $F.dir_open(bv_dsp, 524288)
                    val () = $A.drop<byte>(fz_dsp, bv_dsp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_dsp))
                    val () = (case+ dep_src_dir of
                      | ~$R.ok(d_ex) => let
                          fun scan_extra_bats
                            {ld:agz}{fuel_ex:nat} .<fuel_ex>.
                            (d_ex: !$F.dir,
                             dep_bv: !$A.borrow(byte, ld, 256),
                             dep_len: int,
                             fuel_ex: int fuel_ex): void =
                            if fuel_ex <= 0 then ()
                            else let
                              val ent_ex = $A.alloc<byte>(256)
                              val nr_ex = $F.dir_next(d_ex, ent_ex, 256)
                              val elen_ex = $R.option_unwrap_or<int>(nr_ex, ~1)
                            in
                              if elen_ex < 0 then $A.free<byte>(ent_ex)
                              else let
                                val is_bats = has_bats_ext(ent_ex, elen_ex, 256)
                                val is_lib = is_lib_bats(ent_ex, elen_ex, 256)
                              in
                                if is_bats then
                                  if is_lib then let
                                    val () = $A.free<byte>(ent_ex)
                                  in scan_extra_bats(d_ex, dep_bv, dep_len, fuel_ex - 1) end
                                  else let
                                    val stem_ex = elen_ex - 5
                                    val @(fz_ex, bv_ex) = $A.freeze<byte>(ent_ex)
                                    var sp_ex : $B.builder_v = $B.create()
                                    val () = bput_v(sp_ex, "bats_modules/")
                                    val () = copy_to_builder_v(dep_bv, 0, dep_len, 256, sp_ex)
                                    val () = bput_v(sp_ex, "/src/")
                                    val () = copy_to_builder_v(bv_ex, 0, elen_ex, 256, sp_ex)
                                    val () = put_char_v(sp_ex, 0)
                                    val @(spa_ex, _) = $B.to_arr(sp_ex)
                                    val @(fz_spa, bv_spa) = $A.freeze<byte>(spa_ex)
                                    var ss_ex : $B.builder_v = $B.create()
                                    val () = bput_v(ss_ex, "build/bats_modules/")
                                    val () = copy_to_builder_v(dep_bv, 0, dep_len, 256, ss_ex)
                                    val () = bput_v(ss_ex, "/src/")
                                    val () = copy_to_builder_v(bv_ex, 0, stem_ex, 256, ss_ex)
                                    val () = bput_v(ss_ex, ".sats")
                                    val () = put_char_v(ss_ex, 0)
                                    val @(ssa_ex, _) = $B.to_arr(ss_ex)
                                    val @(fz_ssa, bv_ssa) = $A.freeze<byte>(ssa_ex)
                                    var sd_ex : $B.builder_v = $B.create()
                                    val () = bput_v(sd_ex, "build/bats_modules/")
                                    val () = copy_to_builder_v(dep_bv, 0, dep_len, 256, sd_ex)
                                    val () = bput_v(sd_ex, "/src/")
                                    val () = copy_to_builder_v(bv_ex, 0, stem_ex, 256, sd_ex)
                                    val () = bput_v(sd_ex, ".dats")
                                    val () = put_char_v(sd_ex, 0)
                                    val @(sda_ex, _) = $B.to_arr(sd_ex)
                                    val @(fz_sda, bv_sda) = $A.freeze<byte>(sda_ex)
                                    val pr_ex = preprocess_one(bv_spa, bv_ssa, bv_sda, build_target, 1, target_changed)
                                    val () = (if pr_ex <> 0 then let
                                      val () = print! ("warning: preprocess failed for extra file in dep ")
                                      val () = print_borrow(dep_bv, 0, dep_len, 256, 256)
                                    in print_newline() end
                                    else if ~is_quiet() then let
                                      val () = print! ("  preprocessed dep extra: ")
                                      val () = print_borrow(bv_ex, 0, elen_ex, 256, 256)
                                    in print_newline() end
                                    else ())
                                    val () = $A.drop<byte>(fz_spa, bv_spa)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_spa))
                                    val () = $A.drop<byte>(fz_ssa, bv_ssa)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_ssa))
                                    val () = $A.drop<byte>(fz_sda, bv_sda)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_sda))
                                    val () = $A.drop<byte>(fz_ex, bv_ex)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_ex))
                                  in scan_extra_bats(d_ex, dep_bv, dep_len, fuel_ex - 1) end
                                else let
                                  val () = $A.free<byte>(ent_ex)
                                in scan_extra_bats(d_ex, dep_bv, dep_len, fuel_ex - 1) end
                              end
                            end
                          val () = scan_extra_bats(d_ex, bv_e, elen, 200)
                          val dcr_ex = $F.dir_close(d_ex)
                          val () = $R.discard<int><int>(dcr_ex)
                        in end
                      | ~$R.err(_) => ())
                    val () = $A.drop<byte>(fz_sp, bv_sp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                    val () = $A.drop<byte>(fz_ss, bv_ss)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ss))
                    val () = $A.drop<byte>(fz_sd, bv_sd)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sd))
                    val () = $A.drop<byte>(fz_e, bv_e)
                    val () = $A.free<byte>($A.thaw<byte>(fz_e))
                  in scan_deps(d, ph, fuel - 1) end
                  end (* if ~is_pkg *)
                end
              end
            val () = scan_deps(d, bv_patshome, 200)
            val dcr = $F.dir_close(d)
            val () = $R.discard<int><int>(dcr)
          in end
        | ~$R.err(_) =>
            println! ("warning: no bats_modules/ directory"))

      (* Step 3b: Preprocess src/*.bats shared modules *)
      val sm_arr = str_to_path_arr("src")
      val @(fz_sm, bv_sm) = $A.freeze<byte>(sm_arr)
      val smdir_r = $F.dir_open(bv_sm, 524288)
      val () = $A.drop<byte>(fz_sm, bv_sm)
      val () = $A.free<byte>($A.thaw<byte>(fz_sm))
      val () = (case+ smdir_r of
        | ~$R.ok(d_sm) => let
            fun scan_src_modules {fuel_sm:nat} .<fuel_sm>.
              (d_sm: !$F.dir, fuel_sm: int fuel_sm): void =
              if fuel_sm <= 0 then ()
              else let
                val ent_sm = $A.alloc<byte>(256)
                val nr_sm = $F.dir_next(d_sm, ent_sm, 256)
                val elen_sm = $R.option_unwrap_or<int>(nr_sm, ~1)
              in
                if elen_sm < 0 then $A.free<byte>(ent_sm)
                else let
                  val dd_sm = is_dot_or_dotdot(ent_sm, elen_sm, 256)
                  val bb_sm = has_bats_ext(ent_sm, elen_sm, 256)
                in
                  if dd_sm then let
                    val () = $A.free<byte>(ent_sm)
                  in scan_src_modules(d_sm, fuel_sm - 1) end
                  else if bb_sm then let
                    val stem_sm = elen_sm - 5
                    val @(fz_esm, bv_esm) = $A.freeze<byte>(ent_sm)
                    (* source: src/<name>.bats *)
                    var sp_sm : $B.builder_v = $B.create()
                    val () = bput_v(sp_sm, "src/")
                    val () = copy_to_builder_v(bv_esm, 0, elen_sm, 256, sp_sm)
                    val () = put_char_v(sp_sm, 0)
                    val @(spa_sm, _) = $B.to_arr(sp_sm)
                    val @(fz_spa_sm, bv_spa_sm) = $A.freeze<byte>(spa_sm)
                    (* sats: build/src/<stem>.sats *)
                    var ss_sm : $B.builder_v = $B.create()
                    val () = bput_v(ss_sm, "build/src/")
                    val () = copy_to_builder_v(bv_esm, 0, stem_sm, 256, ss_sm)
                    val () = bput_v(ss_sm, ".sats")
                    val () = put_char_v(ss_sm, 0)
                    val @(ssa_sm, _) = $B.to_arr(ss_sm)
                    val @(fz_ssa_sm, bv_ssa_sm) = $A.freeze<byte>(ssa_sm)
                    (* dats: build/src/<stem>.dats *)
                    var sd_sm : $B.builder_v = $B.create()
                    val () = bput_v(sd_sm, "build/src/")
                    val () = copy_to_builder_v(bv_esm, 0, stem_sm, 256, sd_sm)
                    val () = bput_v(sd_sm, ".dats")
                    val () = put_char_v(sd_sm, 0)
                    val @(sda_sm, _) = $B.to_arr(sd_sm)
                    val @(fz_sda_sm, bv_sda_sm) = $A.freeze<byte>(sda_sm)
                    val pr_sm = preprocess_one(bv_spa_sm, bv_ssa_sm, bv_sda_sm, build_target, is_unsafe, target_changed)
                    val () = (if pr_sm <> 0 then let
                      val () = print! ("warning: preprocess failed for src/")
                      val () = print_borrow(bv_esm, 0, elen_sm, 256, 256)
                    in print_newline() end
                    else if ~is_quiet() then let
                      val () = print! ("  preprocessed: src/")
                      val () = print_borrow(bv_esm, 0, elen_sm, 256, 256)
                    in print_newline() end
                    else ())
                    val () = $A.drop<byte>(fz_spa_sm, bv_spa_sm)
                    val () = $A.free<byte>($A.thaw<byte>(fz_spa_sm))
                    val () = $A.drop<byte>(fz_ssa_sm, bv_ssa_sm)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ssa_sm))
                    val () = $A.drop<byte>(fz_sda_sm, bv_sda_sm)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sda_sm))
                    val () = $A.drop<byte>(fz_esm, bv_esm)
                    val () = $A.free<byte>($A.thaw<byte>(fz_esm))
                  in scan_src_modules(d_sm, fuel_sm - 1) end
                  else let
                    val () = $A.free<byte>(ent_sm)
                  in scan_src_modules(d_sm, fuel_sm - 1) end
                end
              end
            val () = scan_src_modules(d_sm, 200)
            val dcr_sm = $F.dir_close(d_sm)
            val () = $R.discard<int><int>(dcr_sm)
          in end
        | ~$R.err(_) => ())

      (* Step 4: Preprocess src/bin/*.bats *)
      val sb_arr = str_to_path_arr("src/bin")
      val @(fz_sb, bv_sb) = $A.freeze<byte>(sb_arr)
      val sbdir_r = $F.dir_open(bv_sb, 524288)
      val () = $A.drop<byte>(fz_sb, bv_sb)
      val () = $A.free<byte>($A.thaw<byte>(fz_sb))
      val () = (case+ sbdir_r of
        | ~$R.ok(d2) => let
            (* === Staload-chain scanning helpers === *)
            fun skip_to_nl {lb2:agz}{fuel_sn:nat} .<fuel_sn>.
              (buf: !$A.borrow(byte, lb2, 524288), p: int, nb: int,
               fuel_sn: int fuel_sn): int =
              if fuel_sn <= 0 then p
              else if p >= nb then p
              else let
                val b = $S.borrow_byte(buf,
                  $AR.checked_idx(p, 524288), 524288)
              in if $AR.eq_int_int(b, 10) then p + 1
                else skip_to_nl(buf, p + 1, nb, fuel_sn - 1) end

            fun find_dquote {lb2:agz}{fuel_fq:nat} .<fuel_fq>.
              (buf: !$A.borrow(byte, lb2, 524288), p: int, nb: int,
               fuel_fq: int fuel_fq): int =
              if fuel_fq <= 0 then p
              else if p >= nb then p
              else let
                val b = $S.borrow_byte(buf,
                  $AR.checked_idx(p, 524288), 524288)
              in if $AR.eq_int_int(b, 34) then p
                else find_dquote(buf, p + 1, nb, fuel_fq - 1) end

            fun borrow_eq_arr {lb2:agz}{ls2:agz}{fuel_be:nat} .<fuel_be>.
              (buf: !$A.borrow(byte, lb2, 524288), boff: int,
               arr2: !$A.arr(byte, ls2, 16384), aoff: int,
               len: int, fuel_be: int fuel_be): bool =
              if fuel_be <= 0 then len <= 0
              else if len <= 0 then true
              else let
                val bb = $S.borrow_byte(buf,
                  $AR.checked_idx(boff, 524288), 524288)
                val ab = byte2int0($A.get<byte>(arr2,
                  $AR.checked_idx(aoff, 16384)))
              in if $AR.eq_int_int(bb, ab) then
                borrow_eq_arr(buf, boff+1, arr2, aoff+1, len-1, fuel_be-1)
              else false end

            fun arr_entry_len {ls2:agz}{fuel_el:nat} .<fuel_el>.
              (arr2: !$A.arr(byte, ls2, 16384), pos: int,
               fuel_el: int fuel_el): int =
              if fuel_el <= 0 then 0
              else if pos >= 16384 then 0
              else let
                val b = byte2int0($A.get<byte>(arr2,
                  $AR.checked_idx(pos, 16384)))
              in if $AR.eq_int_int(b, 0) then 0
                else 1 + arr_entry_len(arr2, pos + 1, fuel_el - 1) end

            fun is_dep_seen {lb2:agz}{ls2:agz}{fuel_ds:nat} .<fuel_ds>.
              (buf: !$A.borrow(byte, lb2, 524288), boff: int, blen: int,
               seen2: !$A.arr(byte, ls2, 16384), spos: int,
               scan: int, fuel_ds: int fuel_ds): bool =
              if fuel_ds <= 0 then false
              else if scan >= spos then false
              else let
                val elen = arr_entry_len(seen2, scan, 256)
              in if $AR.eq_int_int(elen, blen) then
                if borrow_eq_arr(buf, boff, seen2, scan, blen,
                  256) then true
                else is_dep_seen(buf, boff, blen, seen2, spos,
                  scan + elen + 1, fuel_ds - 1)
              else is_dep_seen(buf, boff, blen, seen2, spos,
                scan + elen + 1, fuel_ds - 1) end

            fun copy_borrow_to_arr {lb2:agz}{ls2:agz}{fuel_cb:nat} .<fuel_cb>.
              (buf: !$A.borrow(byte, lb2, 524288), boff: int,
               dst2: !$A.arr(byte, ls2, 16384), doff: int,
               len: int, fuel_cb: int fuel_cb): void =
              if fuel_cb <= 0 then ()
              else if len <= 0 then ()
              else let
                val b = $S.borrow_byte(buf,
                  $AR.checked_idx(boff, 524288), 524288)
                val () = $A.set<byte>(dst2,
                  $AR.checked_idx(doff, 16384), int2byte0(b))
              in copy_borrow_to_arr(buf, boff+1, dst2, doff+1, len-1, fuel_cb-1) end

            fun copy_arr_to_bld {ls2:agz}{fuel_ca:nat} .<fuel_ca>.
              (src2: !$A.arr(byte, ls2, 16384), start: int,
               len: int, dst2: !$B.builder_v >> $B.builder_v,
               fuel_ca: int fuel_ca): void =
              if fuel_ca <= 0 then ()
              else if len <= 0 then ()
              else let
                val b = byte2int0($A.get<byte>(src2,
                  $AR.checked_idx(start, 16384)))
                val () = put_char_v(dst2, b)
              in copy_arr_to_bld(src2, start+1, len-1, dst2, fuel_ca-1) end

            (* Scan .dats buffer for staload dep references, add to seen *)
            fun scan_staload_deps {lb2:agz}{ls2:agz}{fuel_sc:nat} .<fuel_sc>.
              (buf: !$A.borrow(byte, lb2, 524288), nbytes: int,
               seen2: !$A.arr(byte, ls2, 16384), spos: int,
               pos: int, fuel_sc: int fuel_sc): int =
              if fuel_sc <= 0 then spos
              else if pos >= nbytes then spos
              else if pos + 9 > nbytes then spos
              else let
                val is_stal = $S.chars_match_borrow(buf, pos, 524288,
                  "staload \"", 0, 9)
              in if ~is_stal then let
                val next = skip_to_nl(buf, pos, nbytes, 524288)
              in scan_staload_deps(buf, nbytes, seen2, spos, next, fuel_sc - 1) end
              else let
                val is_self = (if pos + 11 <= nbytes then
                  $S.chars_match_borrow(buf, pos + 9, 524288, "./", 0, 2)
                  else false): bool
              in if is_self then let
                val next = skip_to_nl(buf, pos + 9, nbytes, 524288)
              in scan_staload_deps(buf, nbytes, seen2, spos, next, fuel_sc - 1) end
              else let
                val qpos = find_dquote(buf, pos + 9, nbytes, 524288)
                val path_start = pos + 9
                val path_len = qpos - path_start
                val is_lib_dep = (if path_len > 13 then
                  $S.chars_match_borrow(buf, qpos - 13, 524288,
                    "/src/lib.dats", 0, 13)
                  else false): bool
              in if ~is_lib_dep then let
                val next = skip_to_nl(buf, qpos, nbytes, 524288)
              in scan_staload_deps(buf, nbytes, seen2, spos, next, fuel_sc - 1) end
              else let
                val dep_start = path_start
                val dep_len = path_len - 13
                val already = is_dep_seen(buf, dep_start, dep_len,
                  seen2, spos, 0, 200)
              in if already then let
                val next = skip_to_nl(buf, qpos, nbytes, 524288)
              in scan_staload_deps(buf, nbytes, seen2, spos, next, fuel_sc - 1) end
              else if spos + dep_len + 1 > 16384 then spos
              else let
                val () = copy_borrow_to_arr(buf, dep_start, seen2,
                  spos, dep_len, 256)
                val () = $A.set<byte>(seen2,
                  $AR.checked_idx(spos + dep_len, 16384),
                  int2byte0(0))
                val new_spos = spos + dep_len + 1
                val next = skip_to_nl(buf, qpos, nbytes, 524288)
              in scan_staload_deps(buf, nbytes, seen2, new_spos, next, fuel_sc - 1) end
              end
              end
              end
              end

            (* Collect transitive deps by reading each dep's lib.dats *)
            fun collect_trans_deps {ls2:agz}{fuel_ct:nat} .<fuel_ct>.
              (seen2: !$A.arr(byte, ls2, 16384), spos: int,
               scan_from: int, fuel_ct: int fuel_ct): int =
              if fuel_ct <= 0 then spos
              else if scan_from >= spos then spos
              else let
                val elen = arr_entry_len(seen2, scan_from, 256)
                val next_scan = scan_from + elen + 1
                var pb : $B.builder_v = $B.create()
                val () = bput_v(pb, "build/bats_modules/")
                val () = copy_arr_to_bld(seen2, scan_from, elen, pb,
                  256)
                val () = bput_v(pb, "/src/lib.dats")
                val () = put_char_v(pb, 0)
                val @(pba, _) = $B.to_arr(pb)
                val @(fz_pb, bv_pb) = $A.freeze<byte>(pba)
                val tor = $F.file_open(bv_pb, 524288, 0, 0)
                val () = $A.drop<byte>(fz_pb, bv_pb)
                val () = $A.free<byte>($A.thaw<byte>(fz_pb))
                val new_spos = (case+ tor of
                  | ~$R.ok(tfd) => let
                      val tbuf = $A.alloc<byte>(524288)
                      val trr = $F.file_read(tfd, tbuf, 524288)
                      val tn = (case+ trr of
                        | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                      val tcr = $F.file_close(tfd)
                      val () = $R.discard<int><int>(tcr)
                      val @(fz_tb, bv_tb) = $A.freeze<byte>(tbuf)
                      val ns = scan_staload_deps(bv_tb, tn, seen2, spos, 0, 500)
                      val () = $A.drop<byte>(fz_tb, bv_tb)
                      val () = $A.free<byte>($A.thaw<byte>(fz_tb))
                    in ns end
                  | ~$R.err(_) => spos
                ): int
              in collect_trans_deps(seen2, new_spos, next_scan, fuel_ct - 1) end

            (* Emit dynload for each dep in closure + extra .dats shared modules *)
            fun emit_closure_dynloads {ls2:agz}{fuel_ed:nat} .<fuel_ed>.
              (seen2: !$A.arr(byte, ls2, 16384), spos: int,
               pos: int, eb: !$B.builder_v >> $B.builder_v,
               fuel_ed: int fuel_ed): void =
              if fuel_ed <= 0 then ()
              else if pos >= spos then ()
              else let
                val elen = arr_entry_len(seen2, pos, 256)
                (* dynload "./bats_modules/DEP/src/lib.dats" *)
                val () = bput_v(eb, "dynload \"./bats_modules/")
                val () = copy_arr_to_bld(seen2, pos, elen, eb,
                  256)
                val () = bput_v(eb, "/src/lib.dats\"\n")
                (* Scan build/bats_modules/DEP/src/ for extra .dats *)
                var dsb : $B.builder_v = $B.create()
                val () = bput_v(dsb, "build/bats_modules/")
                val () = copy_arr_to_bld(seen2, pos, elen, dsb,
                  256)
                val () = bput_v(dsb, "/src")
                val () = put_char_v(dsb, 0)
                val @(dsba, _) = $B.to_arr(dsb)
                val @(fz_dsb, bv_dsb) = $A.freeze<byte>(dsba)
                val ext_dir = $F.dir_open(bv_dsb, 524288)
                val () = $A.drop<byte>(fz_dsb, bv_dsb)
                val () = $A.free<byte>($A.thaw<byte>(fz_dsb))
                val () = (case+ ext_dir of
                  | ~$R.ok(d_ext) => let
                      fun scan_extra {ls3:agz}{fuel_se:nat} .<fuel_se>.
                        (d_ext2: !$F.dir,
                         seen3: !$A.arr(byte, ls3, 16384),
                         dep_pos: int, dep_len: int,
                         eb2: !$B.builder_v >> $B.builder_v,
                         fuel_se: int fuel_se): void =
                        if fuel_se <= 0 then ()
                        else let
                          val de = $A.alloc<byte>(256)
                          val nr = $F.dir_next(d_ext2, de, 256)
                          val dl = $R.option_unwrap_or<int>(nr, ~1)
                        in if dl < 0 then $A.free<byte>(de)
                        else let
                          val is_d = has_dats_ext(de, dl, 256)
                          val is_l = is_lib_dats(de, dl, 256)
                        in if is_d then
                          if is_l then let
                            val () = $A.free<byte>(de)
                          in scan_extra(d_ext2, seen3, dep_pos, dep_len, eb2, fuel_se-1) end
                          else let
                            val @(fz_de, bv_de) = $A.freeze<byte>(de)
                            val () = bput_v(eb2, "dynload \"./bats_modules/")
                            val () = copy_arr_to_bld(seen3, dep_pos, dep_len, eb2,
                              256)
                            val () = bput_v(eb2, "/src/")
                            val () = copy_to_builder_v(bv_de, 0, dl, 256,
                              eb2)
                            val () = bput_v(eb2, "\"\n")
                            val () = $A.drop<byte>(fz_de, bv_de)
                            val () = $A.free<byte>($A.thaw<byte>(fz_de))
                          in scan_extra(d_ext2, seen3, dep_pos, dep_len, eb2, fuel_se-1) end
                        else let
                          val () = $A.free<byte>(de)
                        in scan_extra(d_ext2, seen3, dep_pos, dep_len, eb2, fuel_se-1) end
                        end
                        end
                      val () = scan_extra(d_ext, seen2, pos, elen, eb, 200)
                      val dcr = $F.dir_close(d_ext)
                      val () = $R.discard<int><int>(dcr)
                    in end
                  | ~$R.err(_) => ())
                val next = pos + elen + 1
              in emit_closure_dynloads(seen2, spos, next, eb, fuel_ed - 1) end

            (* Scan shared modules (build/src/*.dats) for dep references *)
            fun scan_shared_module_deps {ls2:agz}{fuel_sm:nat} .<fuel_sm>.
              (seen2: !$A.arr(byte, ls2, 16384), spos: int,
               d_sm: !$F.dir, fuel_sm: int fuel_sm): int =
              if fuel_sm <= 0 then spos
              else let
                val sme = $A.alloc<byte>(256)
                val snr = $F.dir_next(d_sm, sme, 256)
                val sel = $R.option_unwrap_or<int>(snr, ~1)
              in if sel < 0 then let
                val () = $A.free<byte>(sme)
              in spos end
              else let
                val is_dats = $S.has_suffix(sme, sel, 256, ".dats", 5)
              in if ~is_dats then let
                val () = $A.free<byte>(sme)
              in scan_shared_module_deps(seen2, spos, d_sm, fuel_sm - 1) end
              else let
                (* Build path: build/src/NAME.dats *)
                var smpath : $B.builder_v = $B.create()
                val () = bput_v(smpath, "build/src/")
                val @(fz_sme, bv_sme) = $A.freeze<byte>(sme)
                val () = copy_to_builder_v(bv_sme, 0, sel, 256, smpath)
                val () = $A.drop<byte>(fz_sme, bv_sme)
                val () = $A.free<byte>($A.thaw<byte>(fz_sme))
                val () = put_char_v(smpath, 0)
                val @(smpa, _) = $B.to_arr(smpath)
                val @(fz_smp, bv_smp) = $A.freeze<byte>(smpa)
                val smor = $F.file_open(bv_smp, 524288, 0, 0)
                val () = $A.drop<byte>(fz_smp, bv_smp)
                val () = $A.free<byte>($A.thaw<byte>(fz_smp))
                val new_spos = (case+ smor of
                  | ~$R.ok(smfd) => let
                      val smbuf = $A.alloc<byte>(524288)
                      val smrr = $F.file_read(smfd, smbuf, 524288)
                      val smnb = (case+ smrr of
                        | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                      val smcr = $F.file_close(smfd)
                      val () = $R.discard<int><int>(smcr)
                      val @(fz_smb, bv_smb) = $A.freeze<byte>(smbuf)
                      val ns = scan_staload_deps(bv_smb, smnb, seen2,
                        spos, 0, 500)
                      val () = $A.drop<byte>(fz_smb, bv_smb)
                      val () = $A.free<byte>($A.thaw<byte>(fz_smb))
                    in ns end
                  | ~$R.err(_) => spos): int
              in scan_shared_module_deps(seen2, new_spos, d_sm,
                fuel_sm - 1) end
              end
              end

            (* Link .o files for deps in the staload-chain closure *)
            fun link_closure_deps {ls2:agz}{fuel_ld:nat} .<fuel_ld>.
              (seen2: !$A.arr(byte, ls2, 16384), spos: int,
               pos: int, lb: !$B.builder_v >> $B.builder_v,
               fuel_ld: int fuel_ld): void =
              if fuel_ld <= 0 then ()
              else if pos >= spos then ()
              else let
                val elen = arr_entry_len(seen2, pos, 256)
                (* Add " build/bats_modules/DEP/src/lib_dats.o" *)
                val () = bput_v(lb, " build/bats_modules/")
                val () = copy_arr_to_bld(seen2, pos, elen, lb,
                  256)
                val () = bput_v(lb, "/src/lib_dats.o")
                (* Also link extra _dats.o files *)
                var ldsb : $B.builder_v = $B.create()
                val () = bput_v(ldsb, "build/bats_modules/")
                val () = copy_arr_to_bld(seen2, pos, elen, ldsb,
                  256)
                val () = bput_v(ldsb, "/src")
                val () = put_char_v(ldsb, 0)
                val @(ldsba, _) = $B.to_arr(ldsb)
                val @(fz_ldsb, bv_ldsb) = $A.freeze<byte>(ldsba)
                val ld_dir = $F.dir_open(bv_ldsb, 524288)
                val () = $A.drop<byte>(fz_ldsb, bv_ldsb)
                val () = $A.free<byte>($A.thaw<byte>(fz_ldsb))
                val () = (case+ ld_dir of
                  | ~$R.ok(d_ld) => let
                      fun link_extra_o {ls3:agz}{fuel_le:nat} .<fuel_le>.
                        (d_ld2: !$F.dir,
                         seen3: !$A.arr(byte, ls3, 16384),
                         dep_pos: int, dep_len: int,
                         lb2: !$B.builder_v >> $B.builder_v,
                         fuel_le: int fuel_le): void =
                        if fuel_le <= 0 then ()
                        else let
                          val le = $A.alloc<byte>(256)
                          val lnr = $F.dir_next(d_ld2, le, 256)
                          val lel = $R.option_unwrap_or<int>(lnr, ~1)
                        in if lel < 0 then $A.free<byte>(le)
                        else let
                          val is_o = $S.has_suffix(le, lel, 256, "_dats.o", 7)
                          val is_l = $S.has_suffix(le, lel, 256, "lib_dats.o", 10)
                        in if is_o then
                          if is_l then let
                            val () = $A.free<byte>(le)
                          in link_extra_o(d_ld2, seen3, dep_pos, dep_len, lb2, fuel_le-1) end
                          else let
                            val @(fz_le, bv_le) = $A.freeze<byte>(le)
                            val () = bput_v(lb2, " build/bats_modules/")
                            val () = copy_arr_to_bld(seen3, dep_pos, dep_len, lb2,
                              256)
                            val () = bput_v(lb2, "/src/")
                            val () = copy_to_builder_v(bv_le, 0, lel, 256,
                              lb2)
                            val () = $A.drop<byte>(fz_le, bv_le)
                            val () = $A.free<byte>($A.thaw<byte>(fz_le))
                          in link_extra_o(d_ld2, seen3, dep_pos, dep_len, lb2, fuel_le-1) end
                        else let
                          val () = $A.free<byte>(le)
                        in link_extra_o(d_ld2, seen3, dep_pos, dep_len, lb2, fuel_le-1) end
                        end
                        end
                      val () = link_extra_o(d_ld, seen2, pos, elen, lb, 200)
                      val dcr = $F.dir_close(d_ld)
                      val () = $R.discard<int><int>(dcr)
                    in end
                  | ~$R.err(_) => ())
                val next = pos + elen + 1
              in link_closure_deps(seen2, spos, next, lb, fuel_ld - 1) end

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
                  else if ~bb then let
                    val () = $A.free<byte>(ent)
                  in scan_bins(d, ph, phlen, rel, fuel - 1) end
                  else let
                    val @(fz_e, bv_e) = $A.freeze<byte>(ent)
                    val stem_len = elen - 5
                    var sp : $B.builder_v = $B.create()
                    val () = bput_v(sp, "src/bin/")
                    val () = copy_to_builder_v(bv_e, 0, elen, 256, sp)
                    val () = put_char_v(sp, 0)
                    val @(sa, _) = $B.to_arr(sp)
                    val @(fz_sp, bv_sp) = $A.freeze<byte>(sa)
                    val is_wasm_bin = check_wasm_binary(bv_sp)
                    (* Skip: wasm binary during native pass, or native binary during wasm pass *)
                    val skip_bin = (if is_wasm_bin > 0 then
                      $AR.eq_int_int(build_target, 0)
                    else $AR.eq_int_int(build_target, 1)): bool
                  in if skip_bin then let
                    val () = $A.drop<byte>(fz_sp, bv_sp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                    val () = $A.drop<byte>(fz_e, bv_e)
                    val () = $A.free<byte>($A.thaw<byte>(fz_e))
                  in scan_bins(d, ph, phlen, rel, fuel - 1) end
                  else let
                    val bin_bt = (if is_wasm_bin > 0 then 1 else 0): int
                    var ss : $B.builder_v = $B.create()
                    val () = bput_v(ss, "build/src/bin/")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ss)
                    val () = bput_v(ss, ".sats")
                    val () = put_char_v(ss, 0)
                    val @(ssa, _) = $B.to_arr(ss)
                    val @(fz_ss, bv_ss) = $A.freeze<byte>(ssa)
                    (* dats: build/src/bin/<name>.dats *)
                    var sd : $B.builder_v = $B.create()
                    val () = bput_v(sd, "build/src/bin/")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, sd)
                    val () = bput_v(sd, ".dats")
                    val () = put_char_v(sd, 0)
                    val @(sda, _) = $B.to_arr(sd)
                    val @(fz_sd, bv_sd) = $A.freeze<byte>(sda)
                    val pr = preprocess_one(bv_sp, bv_ss, bv_sd, bin_bt, is_unsafe, target_changed)
                    val () = (if pr <> 0 then let
                      val () = print! ("error: preprocess failed for ")
                      val () = print_borrow(bv_e, 0, elen, 256, 256)
                    in print_newline() end
                    else if ~is_quiet() then let
                      val () = print! ("  preprocessed: src/bin/")
                      val () = print_borrow(bv_e, 0, elen, 256, 256)
                    in print_newline() end
                    else ())
                    (* Step 5: Generate synthetic entry *)
                    var entry : $B.builder_v = $B.create()
                    val () = bput_v(entry, "staload \"./src/bin/")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, entry)
                    val () = bput_v(entry, ".sats\"\n")
                    (* dynload deps via staload-chain scanning *)
                    val dor = $F.file_open(bv_sd, 524288, 0, 0)
                    val () = (case+ dor of
                      | ~$R.ok(dfd) => let
                          val dep_buf = $A.alloc<byte>(524288)
                          val drr = $F.file_read(dfd, dep_buf, 524288)
                          val dep_nb = (case+ drr of
                            | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                          val dcr = $F.file_close(dfd)
                          val () = $R.discard<int><int>(dcr)
                          val @(fz_db, bv_db) = $A.freeze<byte>(dep_buf)
                          val dep_seen = $A.alloc<byte>(16384)
                          val sp1 = scan_staload_deps(bv_db, dep_nb,
                            dep_seen, 0, 0, 500)
                          val () = $A.drop<byte>(fz_db, bv_db)
                          val () = $A.free<byte>($A.thaw<byte>(fz_db))
                          (* Also scan shared modules for deps *)
                          val sm_dir_arr = str_to_path_arr("build/src")
                          val @(fz_smd, bv_smd) = $A.freeze<byte>(sm_dir_arr)
                          val sm_dir_r = $F.dir_open(bv_smd, 524288)
                          val () = $A.drop<byte>(fz_smd, bv_smd)
                          val () = $A.free<byte>($A.thaw<byte>(fz_smd))
                          val () = (case+ sm_dir_r of
                            | ~$R.ok(smd) => let
                                val sp2 = scan_shared_module_deps(dep_seen,
                                  sp1, smd, 100)
                                val dcr_sm = $F.dir_close(smd)
                                val () = $R.discard<int><int>(dcr_sm)
                                val fsp = collect_trans_deps(dep_seen, sp2, 0, 200)
                                val () = emit_closure_dynloads(dep_seen, fsp,
                                  0, entry, 200)
                                val () = $A.free<byte>(dep_seen)
                              in end
                            | ~$R.err(_) => let
                                val fsp = collect_trans_deps(dep_seen, sp1, 0, 200)
                                val () = emit_closure_dynloads(dep_seen, fsp,
                                  0, entry, 200)
                                val () = $A.free<byte>(dep_seen)
                              in end)
                        in end
                      | ~$R.err(_) => ())
                    (* dynload src/*.dats shared modules *)
                    val dyn_sm_arr = str_to_path_arr("build/src")
                    val @(fz_dsm, bv_dsm) = $A.freeze<byte>(dyn_sm_arr)
                    val dyn_sm_dir = $F.dir_open(bv_dsm, 524288)
                    val () = $A.drop<byte>(fz_dsm, bv_dsm)
                    val () = $A.free<byte>($A.thaw<byte>(fz_dsm))
                    val () = (case+ dyn_sm_dir of
                      | ~$R.ok(d_dsm) => let
                          fun add_src_dynloads {fuel_dsm:nat} .<fuel_dsm>.
                            (d_dsm: !$F.dir, eb: !$B.builder_v >> $B.builder_v,
                             fuel_dsm: int fuel_dsm): void =
                            if fuel_dsm <= 0 then ()
                            else let
                              val de_sm = $A.alloc<byte>(256)
                              val nr_sm = $F.dir_next(d_dsm, de_sm, 256)
                              val dl_sm = $R.option_unwrap_or<int>(nr_sm, ~1)
                            in
                              if dl_sm < 0 then $A.free<byte>(de_sm)
                              else let
                                val is_d = has_dats_ext(de_sm, dl_sm, 256)
                              in
                                if is_d then let
                                  val @(fz_dsme, bv_dsme) = $A.freeze<byte>(de_sm)
                                  val () = bput_v(eb, "dynload \"./src/")
                                  val () = copy_to_builder_v(bv_dsme, 0, dl_sm, 256,
                                    eb)
                                  val () = bput_v(eb, "\"\n")
                                  val () = $A.drop<byte>(fz_dsme, bv_dsme)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_dsme))
                                in add_src_dynloads(d_dsm, eb, fuel_dsm - 1) end
                                else let
                                  val () = $A.free<byte>(de_sm)
                                in add_src_dynloads(d_dsm, eb, fuel_dsm - 1) end
                              end
                            end
                          val () = add_src_dynloads(d_dsm, entry, 200)
                          val dcr_dsm = $F.dir_close(d_dsm)
                          val () = $R.discard<int><int>(dcr_dsm)
                        in end
                      | ~$R.err(_) => ())
                    val () = bput_v(entry, "dynload \"./src/bin/")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, entry)
                    val () = bput_v(entry, ".dats\"\n")
                    val () = bput_v(entry, "implement ")
                    val () = bput_v(entry, "main0 () = __BATS_main0 ()\n")
                    (* Write synthetic entry *)
                    var ep : $B.builder_v = $B.create()
                    val () = bput_v(ep, "build/_bats_entry_")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ep)
                    val () = bput_v(ep, ".dats")
                    val () = put_char_v(ep, 0)
                    val @(epa, _) = $B.to_arr(ep)
                    val @(fz_ep, bv_ep) = $A.freeze<byte>(epa)
                    val ew = write_file_from_builder(bv_ep, 524288, entry)
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
                    val bdir3 = $F.dir_open(bv_bm3, 524288)
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
                                  (* Check if package (has bats.toml) — skip namespace dirs *)
                                  var pk_b : $B.builder_v = $B.create()
                                  val () = bput_v(pk_b, "bats_modules/")
                                  val () = copy_to_builder_v(bv_de, 0, dlen, 256, pk_b)
                                  val () = bput_v(pk_b, "/bats.toml")
                                  val () = put_char_v(pk_b, 0)
                                  val @(pka, _) = $B.to_arr(pk_b)
                                  val @(fz_pk, bv_pk) = $A.freeze<byte>(pka)
                                  val pk_r = $F.file_mtime(bv_pk, 524288)
                                  val is_p = (case+ pk_r of | ~$R.ok(_) => true | ~$R.err(_) => false): bool
                                  val () = $A.drop<byte>(fz_pk, bv_pk)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_pk))
                                in
                                  if ~is_p then let
                                    (* Namespace dir — iterate subdirs *)
                                    var ns_d : $B.builder_v = $B.create()
                                    val () = bput_v(ns_d, "bats_modules/")
                                    val () = copy_to_builder_v(bv_de, 0, dlen, 256, ns_d)
                                    val () = put_char_v(ns_d, 0)
                                    val @(ns_da, _) = $B.to_arr(ns_d)
                                    val @(fz_nsd, bv_nsd) = $A.freeze<byte>(ns_da)
                                    val ns_r = $F.dir_open(bv_nsd, 524288)
                                    val () = $A.drop<byte>(fz_nsd, bv_nsd)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_nsd))
                                    val () = (case+ ns_r of
                                      | ~$R.ok(nsd) => let
                                          fun patsopt_ns {lph2:agz}{lns2:agz}{fuel_ns:nat} .<fuel_ns>.
                                            (nsd: !$F.dir, ph2: !$A.borrow(byte, lph2, 512), ph2len: int,
                                             ns_name: !$A.borrow(byte, lns2, 256), ns_len: int,
                                             fuel_ns: int fuel_ns): void =
                                            if fuel_ns <= 0 then ()
                                            else let
                                              val sde = $A.alloc<byte>(256)
                                              val snr = $F.dir_next(nsd, sde, 256)
                                              val sel = $R.option_unwrap_or<int>(snr, ~1)
                                            in if sel < 0 then $A.free<byte>(sde)
                                              else let val sdd = is_dot_or_dotdot(sde, sel, 256) in
                                                if sdd then let val () = $A.free<byte>(sde)
                                                in patsopt_ns(nsd, ph2, ph2len, ns_name, ns_len, fuel_ns-1) end
                                                else let
                                                  val @(fz_sde, bv_sde) = $A.freeze<byte>(sde)
                                                  (* Build paths: build/bats_modules/<ns>/<sub>/src/lib.dats *)
                                                  var po : $B.builder_v = $B.create()
                                                  val () = bput_v(po, "build/bats_modules/")
                                                  val () = copy_to_builder_v(ns_name, 0, ns_len, 256, po)
                                                  val () = bput_v(po, "/")
                                                  val () = copy_to_builder_v(bv_sde, 0, sel, 256, po)
                                                  val () = bput_v(po, "/src/lib_dats.c")
                                                  val () = put_char_v(po, 0)
                                                  val @(poa, po_len) = $B.to_arr(po)
                                                  val @(fz_po, bv_po) = $A.freeze<byte>(poa)
                                                  var pi : $B.builder_v = $B.create()
                                                  val () = bput_v(pi, "build/bats_modules/")
                                                  val () = copy_to_builder_v(ns_name, 0, ns_len, 256, pi)
                                                  val () = bput_v(pi, "/")
                                                  val () = copy_to_builder_v(bv_sde, 0, sel, 256, pi)
                                                  val () = bput_v(pi, "/src/lib.dats")
                                                  val () = put_char_v(pi, 0)
                                                  val @(pia, pi_len) = $B.to_arr(pi)
                                                  val @(fz_pi, bv_pi) = $A.freeze<byte>(pia)
                                                  val rc_ns = run_patsopt(ph2, ph2len, bv_po, po_len, bv_pi, pi_len)
                                                  val () = $A.drop<byte>(fz_po, bv_po)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_po))
                                                  val () = $A.drop<byte>(fz_pi, bv_pi)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_pi))
                                                  val () = (if rc_ns <> 0 then let
                                                    val () = print! ("error: patsopt failed for dep ")
                                                    val () = print_borrow(ns_name, 0, ns_len, 256, 256)
                                                    val () = print! ("/")
                                                    val () = print_borrow(bv_sde, 0, sel, 256, 256)
                                                  in print_newline() end
                                                  else if ~is_quiet() then let
                                                    val () = print! ("  patsopt: ")
                                                    val () = print_borrow(ns_name, 0, ns_len, 256, 256)
                                                    val () = print! ("/")
                                                    val () = print_borrow(bv_sde, 0, sel, 256, 256)
                                                  in print_newline() end
                                                  else ())
                                                  (* patsopt extra .dats in this sub-package *)
                                                  var peb : $B.builder_v = $B.create()
                                                  val () = bput_v(peb, "build/bats_modules/")
                                                  val () = copy_to_builder_v(ns_name, 0, ns_len, 256, peb)
                                                  val () = bput_v(peb, "/")
                                                  val () = copy_to_builder_v(bv_sde, 0, sel, 256, peb)
                                                  val () = bput_v(peb, "/src")
                                                  val () = put_char_v(peb, 0)
                                                  val @(pea, pel) = $B.to_arr(peb)
                                                  val @(fz_pe, bv_pe) = $A.freeze<byte>(pea)
                                                  val () = patsopt_dir_extra(bv_pe, pel, ph2, ph2len)
                                                  val () = $A.drop<byte>(fz_pe, bv_pe)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_pe))
                                                  val () = $A.drop<byte>(fz_sde, bv_sde)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_sde))
                                                in patsopt_ns(nsd, ph2, ph2len, ns_name, ns_len, fuel_ns-1) end
                                              end
                                            end
                                          val () = patsopt_ns(nsd, ph, phlen, bv_de, dlen, 100)
                                          val dcr_ns = $F.dir_close(nsd)
                                          val () = $R.discard<int><int>(dcr_ns)
                                        in end
                                      | ~$R.err(_) => ())
                                    val () = $A.drop<byte>(fz_de, bv_de)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                  in patsopt_deps(dd3, ph, phlen, fuel3 - 1) end
                                  else let
                                  val pats_fresh = let
                                    var ob : $B.builder_v = $B.create()
                                    val () = bput_v(ob, "build/bats_modules/")
                                    val () = copy_to_builder_v(bv_de, 0, dlen, 256, ob)
                                    val () = bput_v(ob, "/src/lib_dats.c")
                                    val () = put_char_v(ob, 0)
                                    var ib : $B.builder_v = $B.create()
                                    val () = bput_v(ib, "build/bats_modules/")
                                    val () = copy_to_builder_v(bv_de, 0, dlen, 256, ib)
                                    val () = bput_v(ib, "/src/lib.dats")
                                    val () = put_char_v(ib, 0)
                                  in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                                  val () = (if pats_fresh > 0 then ()
                                  else let
                                  var po_b : $B.builder_v = $B.create()
                                  val () = bput_v(po_b, "build/bats_modules/")
                                  val () = copy_to_builder_v(bv_de, 0, dlen, 256, po_b)
                                  val () = bput_v(po_b, "/src/lib_dats.c")
                                  val () = put_char_v(po_b, 0)
                                  val @(po_a, po_len) = $B.to_arr(po_b)
                                  val @(fz_po, bv_po) = $A.freeze<byte>(po_a)
                                  var pi_b : $B.builder_v = $B.create()
                                  val () = bput_v(pi_b, "build/bats_modules/")
                                  val () = copy_to_builder_v(bv_de, 0, dlen, 256, pi_b)
                                  val () = bput_v(pi_b, "/src/lib.dats")
                                  val () = put_char_v(pi_b, 0)
                                  val @(pi_a, pi_len) = $B.to_arr(pi_b)
                                  val @(fz_pi, bv_pi) = $A.freeze<byte>(pi_a)
                                  val rc = run_patsopt(ph, phlen, bv_po, po_len, bv_pi, pi_len)
                                  val () = $A.drop<byte>(fz_po, bv_po)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_po))
                                  val () = $A.drop<byte>(fz_pi, bv_pi)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_pi))
                                  in (if rc <> 0 then let
                                    val () = print! ("error: patsopt failed for dep ")
                                    val () = print_borrow(bv_de, 0, dlen, 256, 256)
                                  in print_newline() end
                                  else if ~is_quiet() then let
                                    val () = print! ("  patsopt: ")
                                    val () = print_borrow(bv_de, 0, dlen, 256, 256)
                                  in print_newline() end
                                  else ()) end)
                                  (* patsopt extra .dats files for this dep *)
                                  var pats_src_b : $B.builder_v = $B.create()
                                  val () = bput_v(pats_src_b, "build/bats_modules/")
                                  val () = copy_to_builder_v(bv_de, 0, dlen, 256, pats_src_b)
                                  val () = bput_v(pats_src_b, "/src")
                                  val () = put_char_v(pats_src_b, 0)
                                  val @(ps_a, _) = $B.to_arr(pats_src_b)
                                  val @(fz_ps, bv_ps) = $A.freeze<byte>(ps_a)
                                  val pats_dir = $F.dir_open(bv_ps, 524288)
                                  val () = $A.drop<byte>(fz_ps, bv_ps)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_ps))
                                  val () = (case+ pats_dir of
                                    | ~$R.ok(d_pt) => let
                                        fun patsopt_extra
                                          {lph2:agz}{ld3:agz}{fuel_p:nat} .<fuel_p>.
                                          (d_pt: !$F.dir,
                                           ph2: !$A.borrow(byte, lph2, 512), ph2len: int,
                                           dep3: !$A.borrow(byte, ld3, 256), dep3_len: int,
                                           fuel_p: int fuel_p): void =
                                          if fuel_p <= 0 then ()
                                          else let
                                            val de3 = $A.alloc<byte>(256)
                                            val nr3 = $F.dir_next(d_pt, de3, 256)
                                            val dl3 = $R.option_unwrap_or<int>(nr3, ~1)
                                          in
                                            if dl3 < 0 then $A.free<byte>(de3)
                                            else let
                                              val is_d = has_dats_ext(de3, dl3, 256)
                                              val is_l = is_lib_dats(de3, dl3, 256)
                                            in
                                              if is_d then
                                                if is_l then let
                                                  val () = $A.free<byte>(de3)
                                                in patsopt_extra(d_pt, ph2, ph2len, dep3, dep3_len, fuel_p - 1) end
                                                else let
                                                  val stem3 = dl3 - 5
                                                  val @(fz_d3, bv_d3) = $A.freeze<byte>(de3)
                                                  (* freshness: _dats.c vs .dats *)
                                                  val pf = let
                                                    var fo : $B.builder_v = $B.create()
                                                    val () = bput_v(fo, "build/bats_modules/")
                                                    val () = copy_to_builder_v(dep3, 0, dep3_len, 256, fo)
                                                    val () = bput_v(fo, "/src/")
                                                    val () = copy_to_builder_v(bv_d3, 0, stem3, 256, fo)
                                                    val () = bput_v(fo, "_dats.c")
                                                    val () = put_char_v(fo, 0)
                                                    var fi : $B.builder_v = $B.create()
                                                    val () = bput_v(fi, "build/bats_modules/")
                                                    val () = copy_to_builder_v(dep3, 0, dep3_len, 256, fi)
                                                    val () = bput_v(fi, "/src/")
                                                    val () = copy_to_builder_v(bv_d3, 0, dl3, 256, fi)
                                                    val () = put_char_v(fi, 0)
                                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                                  val () = (if pf > 0 then ()
                                                  else let
                                                    var eo : $B.builder_v = $B.create()
                                                    val () = bput_v(eo, "build/bats_modules/")
                                                    val () = copy_to_builder_v(dep3, 0, dep3_len, 256, eo)
                                                    val () = bput_v(eo, "/src/")
                                                    val () = copy_to_builder_v(bv_d3, 0, stem3, 256, eo)
                                                    val () = bput_v(eo, "_dats.c")
                                                    val () = put_char_v(eo, 0)
                                                    val @(eoa, eo_len) = $B.to_arr(eo)
                                                    val @(fz_eo, bv_eo) = $A.freeze<byte>(eoa)
                                                    var ei : $B.builder_v = $B.create()
                                                    val () = bput_v(ei, "build/bats_modules/")
                                                    val () = copy_to_builder_v(dep3, 0, dep3_len, 256, ei)
                                                    val () = bput_v(ei, "/src/")
                                                    val () = copy_to_builder_v(bv_d3, 0, dl3, 256, ei)
                                                    val () = put_char_v(ei, 0)
                                                    val @(eia, ei_len) = $B.to_arr(ei)
                                                    val @(fz_ei, bv_ei) = $A.freeze<byte>(eia)
                                                    val rc3 = run_patsopt(ph2, ph2len, bv_eo, eo_len, bv_ei, ei_len)
                                                    val () = $A.drop<byte>(fz_eo, bv_eo)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_eo))
                                                    val () = $A.drop<byte>(fz_ei, bv_ei)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_ei))
                                                  in (if rc3 <> 0 then let
                                                    val () = print! ("error: patsopt failed for extra ")
                                                    val () = print_borrow(bv_d3, 0, dl3, 256, 256)
                                                  in print_newline() end
                                                  else if ~is_quiet() then let
                                                    val () = print! ("  patsopt extra: ")
                                                    val () = print_borrow(bv_d3, 0, dl3, 256, 256)
                                                  in print_newline() end
                                                  else ()) end)
                                                  val () = $A.drop<byte>(fz_d3, bv_d3)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_d3))
                                                in patsopt_extra(d_pt, ph2, ph2len, dep3, dep3_len, fuel_p - 1) end
                                              else let
                                                val () = $A.free<byte>(de3)
                                              in patsopt_extra(d_pt, ph2, ph2len, dep3, dep3_len, fuel_p - 1) end
                                            end
                                          end
                                        val () = patsopt_extra(d_pt, ph, phlen, bv_de, dlen, 200)
                                        val dcr_pt = $F.dir_close(d_pt)
                                        val () = $R.discard<int><int>(dcr_pt)
                                      in end
                                    | ~$R.err(_) => ())
                                  val () = $A.drop<byte>(fz_de, bv_de)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                in patsopt_deps(dd3, ph, phlen, fuel3 - 1) end
                                  end (* if ~is_p *)
                              end
                            end
                          val () = patsopt_deps(dd3, ph, phlen, 200)
                          val dcr3 = $F.dir_close(dd3)
                          val () = $R.discard<int><int>(dcr3)
                        in end
                      | ~$R.err(_) => ())

                    (* patsopt for src/*.dats shared modules *)
                    val psm_arr = str_to_path_arr("build/src")
                    val @(fz_psm, bv_psm) = $A.freeze<byte>(psm_arr)
                    val psm_dir = $F.dir_open(bv_psm, 524288)
                    val () = $A.drop<byte>(fz_psm, bv_psm)
                    val () = $A.free<byte>($A.thaw<byte>(fz_psm))
                    val () = (case+ psm_dir of
                      | ~$R.ok(d_psm) => let
                          fun patsopt_src_modules
                            {lph_sm:agz}{fuel_psm:nat} .<fuel_psm>.
                            (d_psm: !$F.dir,
                             ph_sm: !$A.borrow(byte, lph_sm, 512), ph_sm_len: int,
                             fuel_psm: int fuel_psm): void =
                            if fuel_psm <= 0 then ()
                            else let
                              val de_psm = $A.alloc<byte>(256)
                              val nr_psm = $F.dir_next(d_psm, de_psm, 256)
                              val dl_psm = $R.option_unwrap_or<int>(nr_psm, ~1)
                            in
                              if dl_psm < 0 then $A.free<byte>(de_psm)
                              else let
                                val is_d = has_dats_ext(de_psm, dl_psm, 256)
                              in
                                if is_d then let
                                  val stem_psm = dl_psm - 5
                                  val @(fz_dpsm, bv_dpsm) = $A.freeze<byte>(de_psm)
                                  val pf_sm = let
                                    var fo : $B.builder_v = $B.create()
                                    val () = bput_v(fo, "build/src/")
                                    val () = copy_to_builder_v(bv_dpsm, 0, stem_psm, 256, fo)
                                    val () = bput_v(fo, "_dats.c")
                                    val () = put_char_v(fo, 0)
                                    var fi : $B.builder_v = $B.create()
                                    val () = bput_v(fi, "build/src/")
                                    val () = copy_to_builder_v(bv_dpsm, 0, dl_psm, 256, fi)
                                    val () = put_char_v(fi, 0)
                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                  val () = (if pf_sm > 0 then ()
                                  else let
                                    var eo_sm : $B.builder_v = $B.create()
                                    val () = bput_v(eo_sm, "build/src/")
                                    val () = copy_to_builder_v(bv_dpsm, 0, stem_psm, 256, eo_sm)
                                    val () = bput_v(eo_sm, "_dats.c")
                                    val () = put_char_v(eo_sm, 0)
                                    val @(eoa_sm, eo_sm_len) = $B.to_arr(eo_sm)
                                    val @(fz_eosm, bv_eosm) = $A.freeze<byte>(eoa_sm)
                                    var ei_sm : $B.builder_v = $B.create()
                                    val () = bput_v(ei_sm, "build/src/")
                                    val () = copy_to_builder_v(bv_dpsm, 0, dl_psm, 256, ei_sm)
                                    val () = put_char_v(ei_sm, 0)
                                    val @(eia_sm, ei_sm_len) = $B.to_arr(ei_sm)
                                    val @(fz_eism, bv_eism) = $A.freeze<byte>(eia_sm)
                                    val rc_sm = run_patsopt(ph_sm, ph_sm_len, bv_eosm, eo_sm_len, bv_eism, ei_sm_len)
                                    val () = $A.drop<byte>(fz_eosm, bv_eosm)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_eosm))
                                    val () = $A.drop<byte>(fz_eism, bv_eism)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_eism))
                                  in (if rc_sm <> 0 then let
                                    val () = print! ("error: patsopt failed for src module ")
                                    val () = print_borrow(bv_dpsm, 0, dl_psm, 256, 256)
                                  in print_newline() end
                                  else if ~is_quiet() then let
                                    val () = print! ("  patsopt: src/")
                                    val () = print_borrow(bv_dpsm, 0, dl_psm, 256, 256)
                                  in print_newline() end
                                  else ()) end)
                                  val () = $A.drop<byte>(fz_dpsm, bv_dpsm)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_dpsm))
                                in patsopt_src_modules(d_psm, ph_sm, ph_sm_len, fuel_psm - 1) end
                                else let
                                  val () = $A.free<byte>(de_psm)
                                in patsopt_src_modules(d_psm, ph_sm, ph_sm_len, fuel_psm - 1) end
                              end
                            end
                          val () = patsopt_src_modules(d_psm, ph, phlen, 200)
                          val dcr_psm = $F.dir_close(d_psm)
                          val () = $R.discard<int><int>(dcr_psm)
                        in end
                      | ~$R.err(_) => ())

                    (* patsopt for the binary *)
                    val bin_pats_fresh = let
                      var ob : $B.builder_v = $B.create()
                      val () = bput_v(ob, "build/src/bin/")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ob)
                      val () = bput_v(ob, "_dats.c")
                      val () = put_char_v(ob, 0)
                      var ib : $B.builder_v = $B.create()
                      val () = bput_v(ib, "build/src/bin/")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ib)
                      val () = bput_v(ib, ".dats")
                      val () = put_char_v(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if bin_pats_fresh > 0 then ()
                    else let
                    var po_b : $B.builder_v = $B.create()
                    val () = bput_v(po_b, "build/src/bin/")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, po_b)
                    val () = bput_v(po_b, "_dats.c")
                    val () = put_char_v(po_b, 0)
                    val @(po_a, po_len) = $B.to_arr(po_b)
                    val @(fz_po, bv_po) = $A.freeze<byte>(po_a)
                    var pi_b : $B.builder_v = $B.create()
                    val () = bput_v(pi_b, "build/src/bin/")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, pi_b)
                    val () = bput_v(pi_b, ".dats")
                    val () = put_char_v(pi_b, 0)
                    val @(pi_a, pi_len) = $B.to_arr(pi_b)
                    val @(fz_pi, bv_pi) = $A.freeze<byte>(pi_a)
                    val rbp = run_patsopt(ph, phlen, bv_po, po_len, bv_pi, pi_len)
                    val () = $A.drop<byte>(fz_po, bv_po)
                    val () = $A.free<byte>($A.thaw<byte>(fz_po))
                    val () = $A.drop<byte>(fz_pi, bv_pi)
                    val () = $A.free<byte>($A.thaw<byte>(fz_pi))
                    in (if rbp <> 0 then
                      println! ("error: patsopt failed for binary")
                      else if ~is_quiet() then println! ("  patsopt: binary")
                      else ()) end)

                    (* patsopt for synthetic entry *)
                    val ent_pats_fresh = let
                      var ob : $B.builder_v = $B.create()
                      val () = bput_v(ob, "build/_bats_entry_")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ob)
                      val () = bput_v(ob, "_dats.c")
                      val () = put_char_v(ob, 0)
                      var ib : $B.builder_v = $B.create()
                      val () = bput_v(ib, "build/_bats_entry_")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ib)
                      val () = bput_v(ib, ".dats")
                      val () = put_char_v(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if ent_pats_fresh > 0 then ()
                    else let
                    var eo_b : $B.builder_v = $B.create()
                    val () = bput_v(eo_b, "build/_bats_entry_")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, eo_b)
                    val () = bput_v(eo_b, "_dats.c")
                    val () = put_char_v(eo_b, 0)
                    val @(eo_a, eo_len) = $B.to_arr(eo_b)
                    val @(fz_eo, bv_eo) = $A.freeze<byte>(eo_a)
                    var ei_b : $B.builder_v = $B.create()
                    val () = bput_v(ei_b, "build/_bats_entry_")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ei_b)
                    val () = bput_v(ei_b, ".dats")
                    val () = put_char_v(ei_b, 0)
                    val @(ei_a, ei_len) = $B.to_arr(ei_b)
                    val @(fz_ei, bv_ei) = $A.freeze<byte>(ei_a)
                    val rep = run_patsopt(ph, phlen, bv_eo, eo_len, bv_ei, ei_len)
                    val () = $A.drop<byte>(fz_eo, bv_eo)
                    val () = $A.free<byte>($A.thaw<byte>(fz_eo))
                    val () = $A.drop<byte>(fz_ei, bv_ei)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ei))
                    in (if rep <> 0 then
                      println! ("error: patsopt failed for entry")
                      else if ~is_quiet() then println! ("  patsopt: entry")
                      else ()) end)

                    (* Step 7: clang compile all _dats.c -- skip when --to-c *)
                    val rl = (if is_to_c() then 0 else let
                    (* Compile deps *)
                    val bm4_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm4, bv_bm4) = $A.freeze<byte>(bm4_arr)
                    val bdir4 = $F.dir_open(bv_bm4, 524288)
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
                                  var pk_b3 : $B.builder_v = $B.create()
                                  val () = bput_v(pk_b3, "bats_modules/")
                                  val () = copy_to_builder_v(bv_de, 0, dlen, 256, pk_b3)
                                  val () = bput_v(pk_b3, "/bats.toml")
                                  val () = put_char_v(pk_b3, 0)
                                  val @(pka3, _) = $B.to_arr(pk_b3)
                                  val @(fz_pk3, bv_pk3) = $A.freeze<byte>(pka3)
                                  val pk_r3 = $F.file_mtime(bv_pk3, 524288)
                                  val is_p3 = (case+ pk_r3 of | ~$R.ok(_) => true | ~$R.err(_) => false): bool
                                  val () = $A.drop<byte>(fz_pk3, bv_pk3)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_pk3))
                                in
                                  if ~is_p3 then let
                                    (* Namespace dir — iterate subdirs for clang *)
                                    var ns_cd : $B.builder_v = $B.create()
                                    val () = bput_v(ns_cd, "bats_modules/")
                                    val () = copy_to_builder_v(bv_de, 0, dlen, 256, ns_cd)
                                    val () = put_char_v(ns_cd, 0)
                                    val @(ns_cda, _) = $B.to_arr(ns_cd)
                                    val @(fz_nscd, bv_nscd) = $A.freeze<byte>(ns_cda)
                                    val ns_cr = $F.dir_open(bv_nscd, 524288)
                                    val () = $A.drop<byte>(fz_nscd, bv_nscd)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_nscd))
                                    val () = (case+ ns_cr of
                                      | ~$R.ok(nscd) => let
                                          fun clang_ns {lph3:agz}{lns3:agz}{fuel_cn:nat} .<fuel_cn>.
                                            (nscd: !$F.dir, ph3: !$A.borrow(byte, lph3, 512), ph3len: int,
                                             ns3: !$A.borrow(byte, lns3, 256), ns3len: int,
                                             rr3: int, fuel_cn: int fuel_cn): void =
                                            if fuel_cn <= 0 then ()
                                            else let
                                              val sde = $A.alloc<byte>(256)
                                              val snr = $F.dir_next(nscd, sde, 256)
                                              val sel = $R.option_unwrap_or<int>(snr, ~1)
                                            in if sel < 0 then $A.free<byte>(sde)
                                              else let val sdd = is_dot_or_dotdot(sde, sel, 256) in
                                                if sdd then let val () = $A.free<byte>(sde)
                                                in clang_ns(nscd, ph3, ph3len, ns3, ns3len, rr3, fuel_cn-1) end
                                                else let
                                                  val @(fz_sde, bv_sde) = $A.freeze<byte>(sde)
                                                  var co : $B.builder_v = $B.create()
                                                  val () = bput_v(co, "build/bats_modules/")
                                                  val () = copy_to_builder_v(ns3, 0, ns3len, 256, co)
                                                  val () = bput_v(co, "/")
                                                  val () = copy_to_builder_v(bv_sde, 0, sel, 256, co)
                                                  val () = bput_v(co, "/src/lib_dats.o")
                                                  val () = put_char_v(co, 0)
                                                  val @(coa, co_len) = $B.to_arr(co)
                                                  val @(fz_co, bv_co) = $A.freeze<byte>(coa)
                                                  var ci : $B.builder_v = $B.create()
                                                  val () = bput_v(ci, "build/bats_modules/")
                                                  val () = copy_to_builder_v(ns3, 0, ns3len, 256, ci)
                                                  val () = bput_v(ci, "/")
                                                  val () = copy_to_builder_v(bv_sde, 0, sel, 256, ci)
                                                  val () = bput_v(ci, "/src/lib_dats.c")
                                                  val () = put_char_v(ci, 0)
                                                  val @(cia, ci_len) = $B.to_arr(ci)
                                                  val @(fz_ci, bv_ci) = $A.freeze<byte>(cia)
                                                  val _ = run_cc(ph3, ph3len, bv_co, co_len, bv_ci, ci_len, rr3)
                                                  val () = $A.drop<byte>(fz_co, bv_co)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_co))
                                                  val () = $A.drop<byte>(fz_ci, bv_ci)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_ci))
                                                  (* cc extra _dats.c in this sub-package *)
                                                  var ceb : $B.builder_v = $B.create()
                                                  val () = bput_v(ceb, "build/bats_modules/")
                                                  val () = copy_to_builder_v(ns3, 0, ns3len, 256, ceb)
                                                  val () = bput_v(ceb, "/")
                                                  val () = copy_to_builder_v(bv_sde, 0, sel, 256, ceb)
                                                  val () = bput_v(ceb, "/src")
                                                  val () = put_char_v(ceb, 0)
                                                  val @(cea, cel) = $B.to_arr(ceb)
                                                  val @(fz_ce, bv_ce) = $A.freeze<byte>(cea)
                                                  val () = cc_dir_extra(bv_ce, cel, ph3, ph3len, rr3)
                                                  val () = $A.drop<byte>(fz_ce, bv_ce)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_ce))
                                                  val () = $A.drop<byte>(fz_sde, bv_sde)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_sde))
                                                in clang_ns(nscd, ph3, ph3len, ns3, ns3len, rr3, fuel_cn-1) end
                                              end
                                            end
                                          val () = clang_ns(nscd, ph, phlen, bv_de, dlen, rr, 100)
                                          val dcr_cn = $F.dir_close(nscd)
                                          val () = $R.discard<int><int>(dcr_cn)
                                        in end
                                      | ~$R.err(_) => ())
                                    val () = $A.drop<byte>(fz_de, bv_de)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                  in clang_deps(dd4, ph, phlen, rr, fuel4 - 1) end
                                  else let
                                  val cc_fresh = let
                                    var ob : $B.builder_v = $B.create()
                                    val () = bput_v(ob, "build/bats_modules/")
                                    val () = copy_to_builder_v(bv_de, 0, dlen, 256, ob)
                                    val () = bput_v(ob, "/src/lib_dats.o")
                                    val () = put_char_v(ob, 0)
                                    var ib : $B.builder_v = $B.create()
                                    val () = bput_v(ib, "build/bats_modules/")
                                    val () = copy_to_builder_v(bv_de, 0, dlen, 256, ib)
                                    val () = bput_v(ib, "/src/lib_dats.c")
                                    val () = put_char_v(ib, 0)
                                  in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                                  val () = (if cc_fresh > 0 then ()
                                  else let
                                  var co_b : $B.builder_v = $B.create()
                                  val () = bput_v(co_b, "build/bats_modules/")
                                  val () = copy_to_builder_v(bv_de, 0, dlen, 256, co_b)
                                  val () = bput_v(co_b, "/src/lib_dats.o")
                                  val () = put_char_v(co_b, 0)
                                  val @(co_a, co_len) = $B.to_arr(co_b)
                                  val @(fz_co, bv_co) = $A.freeze<byte>(co_a)
                                  var ci_b : $B.builder_v = $B.create()
                                  val () = bput_v(ci_b, "build/bats_modules/")
                                  val () = copy_to_builder_v(bv_de, 0, dlen, 256, ci_b)
                                  val () = bput_v(ci_b, "/src/lib_dats.c")
                                  val () = put_char_v(ci_b, 0)
                                  val @(ci_a, ci_len) = $B.to_arr(ci_b)
                                  val @(fz_ci, bv_ci) = $A.freeze<byte>(ci_a)
                                  val rc = run_cc(ph, phlen, bv_co, co_len, bv_ci, ci_len, rr)
                                  val () = $A.drop<byte>(fz_co, bv_co)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_co))
                                  val () = $A.drop<byte>(fz_ci, bv_ci)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_ci))
                                  in (if rc <> 0 then let
                                    val () = print! ("error: cc failed for dep ")
                                    val () = print_borrow(bv_de, 0, dlen, 256, 256)
                                  in print_newline() end else ()) end)
                                  (* compile extra _dats.c files for this dep *)
                                  var cc_src_b : $B.builder_v = $B.create()
                                  val () = bput_v(cc_src_b, "build/bats_modules/")
                                  val () = copy_to_builder_v(bv_de, 0, dlen, 256, cc_src_b)
                                  val () = bput_v(cc_src_b, "/src")
                                  val () = put_char_v(cc_src_b, 0)
                                  val @(cs_a, _) = $B.to_arr(cc_src_b)
                                  val @(fz_cs, bv_cs) = $A.freeze<byte>(cs_a)
                                  val cc_dir = $F.dir_open(bv_cs, 524288)
                                  val () = $A.drop<byte>(fz_cs, bv_cs)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_cs))
                                  val () = (case+ cc_dir of
                                    | ~$R.ok(d_cc) => let
                                        fun clang_extra
                                          {lph2:agz}{ld4:agz}{fuel_c:nat} .<fuel_c>.
                                          (d_cc: !$F.dir,
                                           ph2: !$A.borrow(byte, lph2, 512), ph2len: int,
                                           dep4: !$A.borrow(byte, ld4, 256), dep4_len: int,
                                           rr2: int, fuel_c: int fuel_c): void =
                                          if fuel_c <= 0 then ()
                                          else let
                                            val de4 = $A.alloc<byte>(256)
                                            val nr4 = $F.dir_next(d_cc, de4, 256)
                                            val dl4 = $R.option_unwrap_or<int>(nr4, ~1)
                                          in
                                            if dl4 < 0 then $A.free<byte>(de4)
                                            else let
                                              val is_c = has_dats_c_ext(de4, dl4, 256)
                                              val is_l = is_lib_dats_c(de4, dl4, 256)
                                            in
                                              if is_c then
                                                if is_l then let
                                                  val () = $A.free<byte>(de4)
                                                in clang_extra(d_cc, ph2, ph2len, dep4, dep4_len, rr2, fuel_c - 1) end
                                                else let
                                                  val stem4 = dl4 - 7
                                                  val @(fz_d4, bv_d4) = $A.freeze<byte>(de4)
                                                  val cf = let
                                                    var fo : $B.builder_v = $B.create()
                                                    val () = bput_v(fo, "build/bats_modules/")
                                                    val () = copy_to_builder_v(dep4, 0, dep4_len, 256, fo)
                                                    val () = bput_v(fo, "/src/")
                                                    val () = copy_to_builder_v(bv_d4, 0, stem4, 256, fo)
                                                    val () = bput_v(fo, "_dats.o")
                                                    val () = put_char_v(fo, 0)
                                                    var fi : $B.builder_v = $B.create()
                                                    val () = bput_v(fi, "build/bats_modules/")
                                                    val () = copy_to_builder_v(dep4, 0, dep4_len, 256, fi)
                                                    val () = bput_v(fi, "/src/")
                                                    val () = copy_to_builder_v(bv_d4, 0, dl4, 256, fi)
                                                    val () = put_char_v(fi, 0)
                                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                                  val () = (if cf > 0 then ()
                                                  else let
                                                    var xo : $B.builder_v = $B.create()
                                                    val () = bput_v(xo, "build/bats_modules/")
                                                    val () = copy_to_builder_v(dep4, 0, dep4_len, 256, xo)
                                                    val () = bput_v(xo, "/src/")
                                                    val () = copy_to_builder_v(bv_d4, 0, stem4, 256, xo)
                                                    val () = bput_v(xo, "_dats.o")
                                                    val () = put_char_v(xo, 0)
                                                    val @(xoa, xo_len) = $B.to_arr(xo)
                                                    val @(fz_xo, bv_xo) = $A.freeze<byte>(xoa)
                                                    var xi : $B.builder_v = $B.create()
                                                    val () = bput_v(xi, "build/bats_modules/")
                                                    val () = copy_to_builder_v(dep4, 0, dep4_len, 256, xi)
                                                    val () = bput_v(xi, "/src/")
                                                    val () = copy_to_builder_v(bv_d4, 0, dl4, 256, xi)
                                                    val () = put_char_v(xi, 0)
                                                    val @(xia, xi_len) = $B.to_arr(xi)
                                                    val @(fz_xi, bv_xi) = $A.freeze<byte>(xia)
                                                    val rc4 = run_cc(ph2, ph2len, bv_xo, xo_len, bv_xi, xi_len, rr2)
                                                    val () = $A.drop<byte>(fz_xo, bv_xo)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_xo))
                                                    val () = $A.drop<byte>(fz_xi, bv_xi)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_xi))
                                                  in (if rc4 <> 0 then let
                                                    val () = print! ("error: cc failed for extra ")
                                                    val () = print_borrow(bv_d4, 0, dl4, 256, 256)
                                                  in print_newline() end else ()) end)
                                                  val () = $A.drop<byte>(fz_d4, bv_d4)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_d4))
                                                in clang_extra(d_cc, ph2, ph2len, dep4, dep4_len, rr2, fuel_c - 1) end
                                              else let
                                                val () = $A.free<byte>(de4)
                                              in clang_extra(d_cc, ph2, ph2len, dep4, dep4_len, rr2, fuel_c - 1) end
                                            end
                                          end
                                        val () = clang_extra(d_cc, ph, phlen, bv_de, dlen, rr, 200)
                                        val dcr_cc = $F.dir_close(d_cc)
                                        val () = $R.discard<int><int>(dcr_cc)
                                      in end
                                    | ~$R.err(_) => ())
                                  val () = $A.drop<byte>(fz_de, bv_de)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                in clang_deps(dd4, ph, phlen, rr, fuel4 - 1) end
                                  end (* if ~is_p3 *)
                              end
                            end
                          val () = clang_deps(dd4, ph, phlen, rel, 200)
                          val dcr4 = $F.dir_close(dd4)
                          val () = $R.discard<int><int>(dcr4)
                        in end
                      | ~$R.err(_) => ())

                    (* Compile src/*.dats shared modules *)
                    val csm_arr = str_to_path_arr("build/src")
                    val @(fz_csm, bv_csm) = $A.freeze<byte>(csm_arr)
                    val csm_dir = $F.dir_open(bv_csm, 524288)
                    val () = $A.drop<byte>(fz_csm, bv_csm)
                    val () = $A.free<byte>($A.thaw<byte>(fz_csm))
                    val () = (case+ csm_dir of
                      | ~$R.ok(d_csm) => let
                          fun clang_src_modules
                            {lph_cm:agz}{fuel_csm:nat} .<fuel_csm>.
                            (d_csm: !$F.dir,
                             ph_cm: !$A.borrow(byte, lph_cm, 512), ph_cm_len: int,
                             rr_cm: int, fuel_csm: int fuel_csm): void =
                            if fuel_csm <= 0 then ()
                            else let
                              val de_csm = $A.alloc<byte>(256)
                              val nr_csm = $F.dir_next(d_csm, de_csm, 256)
                              val dl_csm = $R.option_unwrap_or<int>(nr_csm, ~1)
                            in
                              if dl_csm < 0 then $A.free<byte>(de_csm)
                              else let
                                val is_c = has_dats_c_ext(de_csm, dl_csm, 256)
                              in
                                if is_c then let
                                  val stem_csm = dl_csm - 7
                                  val @(fz_dcsm, bv_dcsm) = $A.freeze<byte>(de_csm)
                                  val cf_sm = let
                                    var fo : $B.builder_v = $B.create()
                                    val () = bput_v(fo, "build/src/")
                                    val () = copy_to_builder_v(bv_dcsm, 0, stem_csm, 256, fo)
                                    val () = bput_v(fo, "_dats.o")
                                    val () = put_char_v(fo, 0)
                                    var fi : $B.builder_v = $B.create()
                                    val () = bput_v(fi, "build/src/")
                                    val () = copy_to_builder_v(bv_dcsm, 0, dl_csm, 256, fi)
                                    val () = put_char_v(fi, 0)
                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                  val () = (if cf_sm > 0 then ()
                                  else let
                                    var xo_sm : $B.builder_v = $B.create()
                                    val () = bput_v(xo_sm, "build/src/")
                                    val () = copy_to_builder_v(bv_dcsm, 0, stem_csm, 256, xo_sm)
                                    val () = bput_v(xo_sm, "_dats.o")
                                    val () = put_char_v(xo_sm, 0)
                                    val @(xoa_sm, xo_sm_len) = $B.to_arr(xo_sm)
                                    val @(fz_xosm, bv_xosm) = $A.freeze<byte>(xoa_sm)
                                    var xi_sm : $B.builder_v = $B.create()
                                    val () = bput_v(xi_sm, "build/src/")
                                    val () = copy_to_builder_v(bv_dcsm, 0, dl_csm, 256, xi_sm)
                                    val () = put_char_v(xi_sm, 0)
                                    val @(xia_sm, xi_sm_len) = $B.to_arr(xi_sm)
                                    val @(fz_xism, bv_xism) = $A.freeze<byte>(xia_sm)
                                    val rc_csm = run_cc(ph_cm, ph_cm_len, bv_xosm, xo_sm_len, bv_xism, xi_sm_len, rr_cm)
                                    val () = $A.drop<byte>(fz_xosm, bv_xosm)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_xosm))
                                    val () = $A.drop<byte>(fz_xism, bv_xism)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_xism))
                                  in (if rc_csm <> 0 then let
                                    val () = print! ("error: cc failed for src module ")
                                    val () = print_borrow(bv_dcsm, 0, dl_csm, 256, 256)
                                  in print_newline() end else ()) end)
                                  val () = $A.drop<byte>(fz_dcsm, bv_dcsm)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_dcsm))
                                in clang_src_modules(d_csm, ph_cm, ph_cm_len, rr_cm, fuel_csm - 1) end
                                else let
                                  val () = $A.free<byte>(de_csm)
                                in clang_src_modules(d_csm, ph_cm, ph_cm_len, rr_cm, fuel_csm - 1) end
                              end
                            end
                          val () = clang_src_modules(d_csm, ph, phlen, rel, 200)
                          val dcr_csm = $F.dir_close(d_csm)
                          val () = $R.discard<int><int>(dcr_csm)
                        in end
                      | ~$R.err(_) => ())

                    (* WASM cc+link for wasm binaries, native cc+link otherwise *)
                    val rl = (if bin_bt > 0 then let
                      val _ = write_wasm_runtime_h()
                      val _ = write_wasm_runtime_c()
                      val _ = write_wasm_stubs()
                      val wrt_rc = compile_wasm_runtime()
                      val () = (if wrt_rc <> 0 then println! ("error: WASM runtime compile failed") else ())
                      val () = println! ("  compiling WASM...")
                      (* Compile entry _dats.c *)
                      var we_b : $B.builder_v = $B.create()
                      val () = bput_v(we_b, "build/_bats_entry_")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, we_b)
                      val () = bput_v(we_b, "_dats.c")
                      val () = put_char_v(we_b, 0)
                      val @(wea, we_len) = $B.to_arr(we_b)
                      val @(fz_we, bv_we) = $A.freeze<byte>(wea)
                      val _ = wasm_cc_file(bv_we, we_len)
                      val () = $A.drop<byte>(fz_we, bv_we)
                      val () = $A.free<byte>($A.thaw<byte>(fz_we))
                      (* Compile binary _dats.c *)
                      var wb_b : $B.builder_v = $B.create()
                      val () = bput_v(wb_b, "build/src/bin/")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, wb_b)
                      val () = bput_v(wb_b, "_dats.c")
                      val () = put_char_v(wb_b, 0)
                      val @(wba, wb_len) = $B.to_arr(wb_b)
                      val @(fz_wb, bv_wb) = $A.freeze<byte>(wba)
                      val _ = wasm_cc_file(bv_wb, wb_len)
                      val () = $A.drop<byte>(fz_wb, bv_wb)
                      val () = $A.free<byte>($A.thaw<byte>(fz_wb))
                      (* Build wasm-ld argv *)
                      var wl : $B.builder_v = $B.create()
                      val () = bput_v(wl, "wasm-ld") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--no-entry") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--allow-undefined") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--lto-O2") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "-z") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "stack-size=1048576") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--initial-memory=16777216") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--max-memory=268435456") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=mainats_0_void") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=malloc") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_on_event") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_timer_fire") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_idb_fire") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_idb_fire_get") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_measure_set") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_on_fetch_complete") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_on_file_open") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_on_decompress_complete") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_bridge_stash_set_int") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_bridge_stash_get_int") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_listener_get") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_on_popstate") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_on_clipboard_complete") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_on_clipboard_read_complete") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_on_permission_result") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_on_push_subscribe") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "--export=bats_on_media_change") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "-o") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "dist/wasm/app.wasm") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "build/_bats_wasm_runtime.wasm.o") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "build/_bats_entry_")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, wl)
                      val () = bput_v(wl, "_dats.wasm.o") val () = put_char_v(wl, 0)
                      val () = bput_v(wl, "build/src/bin/")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, wl)
                      val () = bput_v(wl, "_dats.wasm.o") val () = put_char_v(wl, 0)
                      val wl_argc0 = 32
                      (* Compile deps from staload chain and add .o to link *)
                      val w_dor = $F.file_open(bv_sd, 524288, 0, 0)
                      val wl_dep_cnt = ref<int>(0)
                      val () = (case+ w_dor of
                        | ~$R.ok(w_dfd) => let
                            val w_buf = $A.alloc<byte>(524288)
                            val w_rr = $F.file_read(w_dfd, w_buf, 524288)
                            val w_nb = (case+ w_rr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                            val w_cr = $F.file_close(w_dfd)
                            val () = $R.discard<int><int>(w_cr)
                            val @(fz_wbuf, bv_wbuf) = $A.freeze<byte>(w_buf)
                            val w_seen = $A.alloc<byte>(16384)
                            val w_sp1 = scan_staload_deps(bv_wbuf, w_nb, w_seen, 0, 0, 500)
                            val () = $A.drop<byte>(fz_wbuf, bv_wbuf)
                            val () = $A.free<byte>($A.thaw<byte>(fz_wbuf))
                            val w_smd = str_to_path_arr("build/src")
                            val @(fz_wsmd, bv_wsmd) = $A.freeze<byte>(w_smd)
                            val w_smd_r = $F.dir_open(bv_wsmd, 524288)
                            val () = $A.drop<byte>(fz_wsmd, bv_wsmd)
                            val () = $A.free<byte>($A.thaw<byte>(fz_wsmd))
                            fun wcc_deps {ls2:agz}{fuel:nat} .<fuel>.
                              (seen: !$A.arr(byte, ls2, 16384), spos: int, pos: int,
                               lb: !$B.builder_v >> $B.builder_v, cnt: int, fuel: int fuel): int =
                              if fuel <= 0 then cnt
                              else if pos >= spos then cnt
                              else let
                                val elen = arr_entry_len(seen, pos, 256)
                                var wdc : $B.builder_v = $B.create()
                                val () = bput_v(wdc, "build/bats_modules/")
                                val () = copy_arr_to_bld(seen, pos, elen, wdc, 256)
                                val () = bput_v(wdc, "/src/lib_dats.c")
                                val () = put_char_v(wdc, 0)
                                val @(wdca, wdc_len) = $B.to_arr(wdc)
                                val @(fz_wdc, bv_wdc) = $A.freeze<byte>(wdca)
                                val rc = wasm_cc_file(bv_wdc, wdc_len)
                                val () = $A.drop<byte>(fz_wdc, bv_wdc)
                                val () = $A.free<byte>($A.thaw<byte>(fz_wdc))
                                val cnt2 = (if rc = 0 then let
                                  val () = bput_v(lb, "build/bats_modules/")
                                  val () = copy_arr_to_bld(seen, pos, elen, lb, 256)
                                  val () = bput_v(lb, "/src/lib_dats.wasm.o")
                                  val () = put_char_v(lb, 0)
                                in cnt + 1 end else cnt): int
                                var wds : $B.builder_v = $B.create()
                                val () = bput_v(wds, "build/bats_modules/")
                                val () = copy_arr_to_bld(seen, pos, elen, wds, 256)
                                val () = bput_v(wds, "/src")
                                val () = put_char_v(wds, 0)
                                val @(wdsa, _) = $B.to_arr(wds)
                                val @(fz_wds, bv_wds) = $A.freeze<byte>(wdsa)
                                val wd_dr = $F.dir_open(bv_wds, 524288)
                                val () = $A.drop<byte>(fz_wds, bv_wds)
                                val () = $A.free<byte>($A.thaw<byte>(fz_wds))
                                val cnt3 = (case+ wd_dr of
                                  | ~$R.ok(wd) => let
                                      fun wcc_ex {ls3:agz}{fuel2:nat} .<fuel2>.
                                        (wd2: !$F.dir, s: !$A.arr(byte, ls3, 16384),
                                         dp: int, dl: int,
                                         lb2: !$B.builder_v >> $B.builder_v,
                                         c: int, fuel2: int fuel2): int =
                                        if fuel2 <= 0 then c
                                        else let
                                          val ef = $A.alloc<byte>(256)
                                          val enr = $F.dir_next(wd2, ef, 256)
                                          val el = $R.option_unwrap_or<int>(enr, ~1)
                                        in if el < 0 then let val () = $A.free<byte>(ef) in c end
                                        else let
                                          val ic = $S.has_suffix(ef, el, 256, "_dats.c", 7)
                                          val il = $S.has_suffix(ef, el, 256, "lib_dats.c", 10)
                                        in if ic then if il then let val () = $A.free<byte>(ef)
                                          in wcc_ex(wd2, s, dp, dl, lb2, c, fuel2-1) end
                                          else let
                                            val @(fz_ef, bv_ef) = $A.freeze<byte>(ef)
                                            var wp : $B.builder_v = $B.create()
                                            val () = bput_v(wp, "build/bats_modules/")
                                            val () = copy_arr_to_bld(s, dp, dl, wp, 256)
                                            val () = bput_v(wp, "/src/")
                                            val () = copy_to_builder_v(bv_ef, 0, el, 256, wp)
                                            val () = put_char_v(wp, 0)
                                            val @(wpa, wp_len) = $B.to_arr(wp)
                                            val @(fz_wp, bv_wp) = $A.freeze<byte>(wpa)
                                            val rc2 = wasm_cc_file(bv_wp, wp_len)
                                            val c2 = (if rc2 = 0 then let
                                              val () = copy_to_builder_v(bv_wp, 0, wp_len - 2, 524288, lb2)
                                              val () = bput_v(lb2, "wasm.o")
                                              val () = put_char_v(lb2, 0)
                                            in c + 1 end else c): int
                                            val () = $A.drop<byte>(fz_wp, bv_wp)
                                            val () = $A.free<byte>($A.thaw<byte>(fz_wp))
                                            val () = $A.drop<byte>(fz_ef, bv_ef)
                                            val () = $A.free<byte>($A.thaw<byte>(fz_ef))
                                          in wcc_ex(wd2, s, dp, dl, lb2, c2, fuel2-1) end
                                        else let val () = $A.free<byte>(ef)
                                        in wcc_ex(wd2, s, dp, dl, lb2, c, fuel2-1) end
                                        end
                                        end
                                      val cx = wcc_ex(wd, seen, pos, elen, lb, cnt2, 200)
                                      val dcr_wd = $F.dir_close(wd)
                                      val () = $R.discard<int><int>(dcr_wd)
                                    in cx end
                                  | ~$R.err(_) => cnt2): int
                                val next = pos + elen + 1
                              in wcc_deps(seen, spos, next, lb, cnt3, fuel - 1) end
                            val () = (case+ w_smd_r of
                              | ~$R.ok(wsmd) => let
                                  val w_sp2 = scan_shared_module_deps(w_seen, w_sp1, wsmd, 100)
                                  val dcr_wsm = $F.dir_close(wsmd)
                                  val () = $R.discard<int><int>(dcr_wsm)
                                  val w_fsp = collect_trans_deps(w_seen, w_sp2, 0, 200)
                                  val dc = wcc_deps(w_seen, w_fsp, 0, wl, 0, 200)
                                  val () = !wl_dep_cnt := dc
                                  val () = $A.free<byte>(w_seen)
                                in end
                              | ~$R.err(_) => let
                                  val w_fsp = collect_trans_deps(w_seen, w_sp1, 0, 200)
                                  val dc = wcc_deps(w_seen, w_fsp, 0, wl, 0, 200)
                                  val () = !wl_dep_cnt := dc
                                  val () = $A.free<byte>(w_seen)
                                in end)
                          in end
                        | ~$R.err(_) => ())
                      val wl_argc1 = wl_argc0 + !wl_dep_cnt
                      (* Compile src modules and add .o to link *)
                      val wsm_a = str_to_path_arr("build/src")
                      val @(fz_wsma, bv_wsma) = $A.freeze<byte>(wsm_a)
                      val wsm_dr = $F.dir_open(bv_wsma, 524288)
                      val () = $A.drop<byte>(fz_wsma, bv_wsma)
                      val () = $A.free<byte>($A.thaw<byte>(fz_wsma))
                      val wl_sm_cnt = ref<int>(0)
                      val () = (case+ wsm_dr of
                        | ~$R.ok(wsm_d) => let
                            fun wcc_sm {fuel3:nat} .<fuel3>.
                              (d: !$F.dir, lb: !$B.builder_v >> $B.builder_v,
                               c: int, fuel3: int fuel3): int =
                              if fuel3 <= 0 then c
                              else let
                                val se = $A.alloc<byte>(256)
                                val snr = $F.dir_next(d, se, 256)
                                val sl = $R.option_unwrap_or<int>(snr, ~1)
                              in if sl < 0 then let val () = $A.free<byte>(se) in c end
                              else let
                                val isc = $S.has_suffix(se, sl, 256, "_dats.c", 7)
                              in if ~isc then let val () = $A.free<byte>(se)
                                in wcc_sm(d, lb, c, fuel3 - 1) end
                              else let
                                val @(fz_se2, bv_se2) = $A.freeze<byte>(se)
                                var smp : $B.builder_v = $B.create()
                                val () = bput_v(smp, "build/src/")
                                val () = copy_to_builder_v(bv_se2, 0, sl, 256, smp)
                                val () = put_char_v(smp, 0)
                                val @(smpa, smpl) = $B.to_arr(smp)
                                val @(fz_smp, bv_smp) = $A.freeze<byte>(smpa)
                                val rc = wasm_cc_file(bv_smp, smpl)
                                val c2 = (if rc = 0 then let
                                  val () = copy_to_builder_v(bv_smp, 0, smpl - 2, 524288, lb)
                                  val () = bput_v(lb, "wasm.o")
                                  val () = put_char_v(lb, 0)
                                in c + 1 end else c): int
                                val () = $A.drop<byte>(fz_smp, bv_smp)
                                val () = $A.free<byte>($A.thaw<byte>(fz_smp))
                                val () = $A.drop<byte>(fz_se2, bv_se2)
                                val () = $A.free<byte>($A.thaw<byte>(fz_se2))
                              in wcc_sm(d, lb, c2, fuel3 - 1) end
                              end
                              end
                            val sc = wcc_sm(wsm_d, wl, 0, 200)
                            val () = !wl_sm_cnt := sc
                            val dcr_wsm2 = $F.dir_close(wsm_d)
                            val () = $R.discard<int><int>(dcr_wsm2)
                          in end
                        | ~$R.err(_) => ())
                      val wl_argc2 = wl_argc1 + !wl_sm_cnt
                      var mb_w1 : $B.builder_v = $B.create()
                      val () = bput_v(mb_w1, "dist")
                      val _ = run_mkdir(mb_w1)
                      var mb_w2 : $B.builder_v = $B.create()
                      val () = bput_v(mb_w2, "dist/wasm")
                      val _ = run_mkdir(mb_w2)
                      val () = println! ("  linking WASM...")
                      val wld_exec = str_to_path_arr("/usr/bin/wasm-ld")
                      val @(fz_wld, bv_wld) = $A.freeze<byte>(wld_exec)
                      val wlr = run_cmd(bv_wld, 524288, wl, wl_argc2)
                      val () = $A.drop<byte>(fz_wld, bv_wld)
                      val () = $A.free<byte>($A.thaw<byte>(fz_wld))
                    in wlr end else let

                    (* Compile binary *)
                    val bin_cc_fresh = let
                      var ob : $B.builder_v = $B.create()
                      val () = bput_v(ob, "build/src/bin/")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ob)
                      val () = bput_v(ob, "_dats.o")
                      val () = put_char_v(ob, 0)
                      var ib : $B.builder_v = $B.create()
                      val () = bput_v(ib, "build/src/bin/")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ib)
                      val () = bput_v(ib, "_dats.c")
                      val () = put_char_v(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if bin_cc_fresh > 0 then ()
                    else let
                    var co_b : $B.builder_v = $B.create()
                    val () = bput_v(co_b, "build/src/bin/")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, co_b)
                    val () = bput_v(co_b, "_dats.o")
                    val () = put_char_v(co_b, 0)
                    val @(co_a, co_len) = $B.to_arr(co_b)
                    val @(fz_co, bv_co) = $A.freeze<byte>(co_a)
                    var ci_b : $B.builder_v = $B.create()
                    val () = bput_v(ci_b, "build/src/bin/")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ci_b)
                    val () = bput_v(ci_b, "_dats.c")
                    val () = put_char_v(ci_b, 0)
                    val @(ci_a, ci_len) = $B.to_arr(ci_b)
                    val @(fz_ci, bv_ci) = $A.freeze<byte>(ci_a)
                    val _ = run_cc(ph, phlen, bv_co, co_len, bv_ci, ci_len, rel)
                    val () = $A.drop<byte>(fz_co, bv_co)
                    val () = $A.free<byte>($A.thaw<byte>(fz_co))
                    val () = $A.drop<byte>(fz_ci, bv_ci)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ci))
                    in end)

                    (* Compile entry *)
                    val ent_cc_fresh = let
                      var ob : $B.builder_v = $B.create()
                      val () = bput_v(ob, "build/_bats_entry_")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ob)
                      val () = bput_v(ob, "_dats.o")
                      val () = put_char_v(ob, 0)
                      var ib : $B.builder_v = $B.create()
                      val () = bput_v(ib, "build/_bats_entry_")
                      val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ib)
                      val () = bput_v(ib, "_dats.c")
                      val () = put_char_v(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if ent_cc_fresh > 0 then ()
                    else let
                    var ceo_b : $B.builder_v = $B.create()
                    val () = bput_v(ceo_b, "build/_bats_entry_")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, ceo_b)
                    val () = bput_v(ceo_b, "_dats.o")
                    val () = put_char_v(ceo_b, 0)
                    val @(ceo_a, ceo_len) = $B.to_arr(ceo_b)
                    val @(fz_ceo, bv_ceo) = $A.freeze<byte>(ceo_a)
                    var cei_b : $B.builder_v = $B.create()
                    val () = bput_v(cei_b, "build/_bats_entry_")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, cei_b)
                    val () = bput_v(cei_b, "_dats.c")
                    val () = put_char_v(cei_b, 0)
                    val @(cei_a, cei_len) = $B.to_arr(cei_b)
                    val @(fz_cei, bv_cei) = $A.freeze<byte>(cei_a)
                    val _ = run_cc(ph, phlen, bv_ceo, ceo_len, bv_cei, cei_len, rel)
                    val () = $A.drop<byte>(fz_ceo, bv_ceo)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ceo))
                    val () = $A.drop<byte>(fz_cei, bv_cei)
                    val () = $A.free<byte>($A.thaw<byte>(fz_cei))
                    in end)

                    (* Step 8: Link *)
                    var link : $B.builder_v = $B.create()
                    val () = (if rel > 0 then
                      bput_v(link, "clang -o dist/release/")
                      else bput_v(link, "clang -o dist/debug/"))
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, link)
                    val () = bput_v(link, " build/_bats_entry_")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, link)
                    val () = bput_v(link, "_dats.o build/src/bin/")
                    val () = copy_to_builder_v(bv_e, 0, stem_len, 256, link)
                    val () = bput_v(link, "_dats.o build/_bats_native_runtime.o")
                    (* Add dep .o files via staload-chain scanning *)
                    val lk_dor = $F.file_open(bv_sd, 524288, 0, 0)
                    val () = (case+ lk_dor of
                      | ~$R.ok(lk_dfd) => let
                          val lk_dep_buf = $A.alloc<byte>(524288)
                          val lk_drr = $F.file_read(lk_dfd, lk_dep_buf, 524288)
                          val lk_dep_nb = (case+ lk_drr of
                            | ~$R.ok(n) => n | ~$R.err(_) => 0): int
                          val lk_dcr = $F.file_close(lk_dfd)
                          val () = $R.discard<int><int>(lk_dcr)
                          val @(fz_ldb, bv_ldb) = $A.freeze<byte>(lk_dep_buf)
                          val lk_dep_seen = $A.alloc<byte>(16384)
                          val lk_sp1 = scan_staload_deps(bv_ldb, lk_dep_nb,
                            lk_dep_seen, 0, 0, 500)
                          val () = $A.drop<byte>(fz_ldb, bv_ldb)
                          val () = $A.free<byte>($A.thaw<byte>(fz_ldb))
                          (* Also scan shared modules for deps *)
                          val lk_smd_arr = str_to_path_arr("build/src")
                          val @(fz_lksmd, bv_lksmd) = $A.freeze<byte>(lk_smd_arr)
                          val lk_smd_r = $F.dir_open(bv_lksmd, 524288)
                          val () = $A.drop<byte>(fz_lksmd, bv_lksmd)
                          val () = $A.free<byte>($A.thaw<byte>(fz_lksmd))
                          val () = (case+ lk_smd_r of
                            | ~$R.ok(lksmd) => let
                                val lk_sp2 = scan_shared_module_deps(lk_dep_seen,
                                  lk_sp1, lksmd, 100)
                                val dcr_lksm = $F.dir_close(lksmd)
                                val () = $R.discard<int><int>(dcr_lksm)
                                val lk_fsp = collect_trans_deps(lk_dep_seen, lk_sp2, 0, 200)
                                val () = link_closure_deps(lk_dep_seen, lk_fsp,
                                  0, link, 200)
                                val () = $A.free<byte>(lk_dep_seen)
                              in end
                            | ~$R.err(_) => let
                                val lk_fsp = collect_trans_deps(lk_dep_seen, lk_sp1, 0, 200)
                                val () = link_closure_deps(lk_dep_seen, lk_fsp,
                                  0, link, 200)
                                val () = $A.free<byte>(lk_dep_seen)
                              in end)
                        in end
                      | ~$R.err(_) => bput_v(link, ""))
                    (* Link src/*.dats shared module .o files *)
                    val lsm_arr = str_to_path_arr("build/src")
                    val @(fz_lsm, bv_lsm) = $A.freeze<byte>(lsm_arr)
                    val lsm_dir = $F.dir_open(bv_lsm, 524288)
                    val () = $A.drop<byte>(fz_lsm, bv_lsm)
                    val () = $A.free<byte>($A.thaw<byte>(fz_lsm))
                    val () = (case+ lsm_dir of
                      | ~$R.ok(d_lsm) => let
                          fun link_src_modules {fuel_lsm:nat} .<fuel_lsm>.
                            (d_lsm: !$F.dir, lb: !$B.builder_v >> $B.builder_v,
                             fuel_lsm: int fuel_lsm): void =
                            if fuel_lsm <= 0 then ()
                            else let
                              val de_lsm = $A.alloc<byte>(256)
                              val nr_lsm = $F.dir_next(d_lsm, de_lsm, 256)
                              val dl_lsm = $R.option_unwrap_or<int>(nr_lsm, ~1)
                            in
                              if dl_lsm < 0 then $A.free<byte>(de_lsm)
                              else let
                                val is_o = has_dats_o_ext(de_lsm, dl_lsm, 256)
                              in
                                if is_o then let
                                  val @(fz_dlsm, bv_dlsm) = $A.freeze<byte>(de_lsm)
                                  val () = bput_v(lb, " build/src/")
                                  val () = copy_to_builder_v(bv_dlsm, 0, dl_lsm, 256,
                                    lb)
                                  val () = $A.drop<byte>(fz_dlsm, bv_dlsm)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_dlsm))
                                in link_src_modules(d_lsm, lb, fuel_lsm - 1) end
                                else let
                                  val () = $A.free<byte>(de_lsm)
                                in link_src_modules(d_lsm, lb, fuel_lsm - 1) end
                              end
                            end
                          val () = link_src_modules(d_lsm, link, 200)
                          val dcr_lsm = $F.dir_close(d_lsm)
                          val () = $R.discard<int><int>(dcr_lsm)
                        in end
                      | ~$R.err(_) => ())
                    val () = (if rel > 0 then bput_v(link, " -O2")
                      else bput_v(link, " -g -O0"))
                    (* Convert space-separated link command to null-separated argv *)
                    val @(link_arr, link_len) = $B.to_arr(link)
                    val @(fz_la, bv_la) = $A.freeze<byte>(link_arr)
                    var link_argv : $B.builder_v = $B.create()
                    fun split_spaces {l2:agz}{fuel:nat} .<fuel>.
                      (bv: !$A.borrow(byte, l2, 524288), i: int, len: int,
                       dst: !$B.builder_v >> $B.builder_v, argc: int, in_arg: int,
                       fuel: int fuel): int =
                      if fuel <= 0 then argc
                      else if i >= len then
                        (if in_arg > 0 then let
                          val () = put_char_v(dst, 0)
                        in argc + 1 end else argc)
                      else let
                        val b = $S.borrow_byte(bv, i, 524288)
                      in
                        if $AR.eq_int_int(b, 32) then
                          if in_arg > 0 then let
                            val () = put_char_v(dst, 0)
                          in split_spaces(bv, i + 1, len, dst, argc + 1, 0, fuel - 1) end
                          else split_spaces(bv, i + 1, len, dst, argc, 0, fuel - 1)
                        else let
                          val () = put_char_v(dst, b)
                        in split_spaces(bv, i + 1, len, dst, argc, 1, fuel - 1) end
                      end
                    val link_argc = split_spaces(bv_la, 0, link_len, link_argv, 0, 0,
                      524288)
                    val () = $A.drop<byte>(fz_la, bv_la)
                    val () = $A.free<byte>($A.thaw<byte>(fz_la))
                    val cc_exec = str_to_path_arr("/usr/bin/clang")
                    val @(fz_cce, bv_cce) = $A.freeze<byte>(cc_exec)
                    (* Remove the first "PATH=..." token and "cc" token,
                       start argv from "cc" *)
                    val lr = run_cmd(bv_cce, 524288, link_argv, link_argc)
                    val () = $A.drop<byte>(fz_cce, bv_cce)
                    val () = $A.free<byte>($A.thaw<byte>(fz_cce))
                    in lr end): int
                    in rl end): int

                    val () = $A.drop<byte>(fz_sp, bv_sp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                    val () = $A.drop<byte>(fz_ss, bv_ss)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ss))
                    val () = $A.drop<byte>(fz_sd, bv_sd)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sd))
                    val () = (if is_to_c() then ()
                    else if rl = 0 then
                      if ~is_quiet() then
                        if bin_bt > 0 then println! ("  built: dist/wasm/app.wasm")
                        else let
                          val () = (if rel > 0 then print! ("  built: dist/release/")
                            else print! ("  built: dist/debug/"))
                          val () = print_borrow(bv_e, 0, stem_len, 256, 256)
                        in print_newline() end
                      else ()
                    else println! ("error: link failed"))
                    val () = $A.drop<byte>(fz_e, bv_e)
                    val () = $A.free<byte>($A.thaw<byte>(fz_e))
                  in scan_bins(d, ph, phlen, rel, fuel - 1) end
                end
              end
              end
            val () = scan_bins(d2, bv_patshome, phlen, release, 100)
            val dcr2 = $F.dir_close(d2)
            val () = $R.discard<int><int>(dcr2)
          in end
        | ~$R.err(_) => ())

      (* Run patsopt on src/lib.bats if scan_src_modules preprocessed it *)
      val lib_d_path = str_to_path_arr("build/src/lib.dats")
      val @(fz_ldp, bv_ldp) = $A.freeze<byte>(lib_d_path)
      val lib_or = $F.file_open(bv_ldp, 524288, 0, 0)
      val () = $A.drop<byte>(fz_ldp, bv_ldp)
      val () = $A.free<byte>($A.thaw<byte>(fz_ldp))
      val lib_exists = (case+ lib_or of
        | ~$R.ok(fd) => let
            val cr = $F.file_close(fd)
            val () = $R.discard<int><int>(cr)
          in true end
        | ~$R.err(_) => false): bool
      val () = (if lib_exists then let
          var lc_b : $B.builder_v = $B.create()
          val () = bput_v(lc_b, "build/src/lib_dats.c")
          val () = put_char_v(lc_b, 0)
          val @(lib_c_out, lc_len) = $B.to_arr(lc_b)
          val @(fz_lc, bv_lc) = $A.freeze<byte>(lib_c_out)
          var ld_b : $B.builder_v = $B.create()
          val () = bput_v(ld_b, "build/src/lib.dats")
          val () = put_char_v(ld_b, 0)
          val @(lib_d_in, ld_len) = $B.to_arr(ld_b)
          val @(fz_ld, bv_ld) = $A.freeze<byte>(lib_d_in)
          val lrc = run_patsopt(bv_patshome, phlen, bv_lc, lc_len, bv_ld, ld_len)
          val () = $A.drop<byte>(fz_lc, bv_lc)
          val () = $A.free<byte>($A.thaw<byte>(fz_lc))
          val () = $A.drop<byte>(fz_ld, bv_ld)
          val () = $A.free<byte>($A.thaw<byte>(fz_ld))
          val () = (if lrc <> 0 then
            println! ("error: patsopt failed for src/lib.bats")
          else if ~is_quiet() then println! ("  patsopt: src/lib.bats")
          else ())
        in end
        else ())

      (* --to-c: copy C files and generate Makefile *)
      val () = (if is_to_c() then if get_to_c_done() = 0 then let
        val () = set_to_c_done(1)
        val tc_p = str_to_path_arr("/tmp/_bpoc_to_c.txt")
        val @(fz_tcp, bv_tcp) = $A.freeze<byte>(tc_p)
        val tc_or = $F.file_open(bv_tcp, 524288, 0, 0)
        val () = $A.drop<byte>(fz_tcp, bv_tcp)
        val () = $A.free<byte>($A.thaw<byte>(fz_tcp))
        val () = (case+ tc_or of
          | ~$R.ok(tcfd) => let
              val tcb = $A.alloc<byte>(4096)
              val tcr2 = $F.file_read(tcfd, tcb, 4096)
              val tcl = (case+ tcr2 of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
              val tcc = $F.file_close(tcfd)
              val () = $R.discard<int><int>(tcc)
              val tcl2 = strip_newline_arr(tcb, tcl)
              val @(fz_tcb, bv_tcb) = $A.freeze<byte>(tcb)
            in
              if tcl2 > 0 then let
                (* mkdir target *)
                var md : $B.builder_v = $B.create()
                val () = copy_to_builder_v(bv_tcb, 0, tcl2, 4096, md)
                val _ = run_mkdir(md)
                (* cp -r build/ <target>/ — copy all C files *)
                val cp_exec = str_to_path_arr("/bin/cp")
                val @(fz_cpe, bv_cpe) = $A.freeze<byte>(cp_exec)
                var cp_argv : $B.builder_v = $B.create()
                val () = bput_v(cp_argv, "cp") val () = put_char_v(cp_argv, 0)
                val () = bput_v(cp_argv, "-r") val () = put_char_v(cp_argv, 0)
                val () = bput_v(cp_argv, "build/.") val () = put_char_v(cp_argv, 0)
                val () = copy_to_builder_v(bv_tcb, 0, tcl2, 4096, cp_argv)
                val () = bput_v(cp_argv, "/") val () = put_char_v(cp_argv, 0)
                val _ = run_cmd(bv_cpe, 524288, cp_argv, 4)
                val () = $A.drop<byte>(fz_cpe, bv_cpe)
                val () = $A.free<byte>($A.thaw<byte>(fz_cpe))
                (* Generate Makefile *)
                var mf : $B.builder_v = $B.create()
                val () = bput_v(mf, "PATSHOME ?= $(HOME)/.bats/ats2\n")
                val () = bput_v(mf, "CC ?= cc\n\n")
                val () = bput_v(mf, "%_debug.o: %.c\n\t$(CC) -c -o $@ $< -g -O0 -I$(PATSHOME) -I$(PATSHOME)/ccomp/runtime\n\n")
                val () = bput_v(mf, "%_release.o: %.c\n\t$(CC) -c -o $@ $< -O2 -I$(PATSHOME) -I$(PATSHOME)/ccomp/runtime\n\n")
                val () = bput_v(mf, "SRCS := $(shell find . -name '*_dats.c') _bats_native_runtime.c\n")
                val () = bput_v(mf, "DEBUG_OBJS := $(SRCS:.c=_debug.o)\n")
                val () = bput_v(mf, "RELEASE_OBJS := $(SRCS:.c=_release.o)\n\n")
                val () = bput_v(mf, "all: debug/bats release/bats\n\n")
                val () = bput_v(mf, "debug/bats: $(DEBUG_OBJS)\n\tmkdir -p debug\n\t$(CC) -o $@ $^ -g -O0\n\n")
                val () = bput_v(mf, "release/bats: $(RELEASE_OBJS)\n\tmkdir -p release\n\t$(CC) -o $@ $^ -O2\n\n")
                val () = bput_v(mf, "clean:\n\trm -f *.o\n\trm -rf debug release\n")
                var mfp : $B.builder_v = $B.create()
                val () = copy_to_builder_v(bv_tcb, 0, tcl2, 4096, mfp)
                val () = bput_v(mfp, "/Makefile")
                val () = put_char_v(mfp, 0)
                val @(mfpa, _) = $B.to_arr(mfp)
                val @(fz_mfp, bv_mfp) = $A.freeze<byte>(mfpa)
                val _ = write_file_from_builder(bv_mfp, 524288, mf)
                val () = $A.drop<byte>(fz_mfp, bv_mfp)
                val () = $A.free<byte>($A.thaw<byte>(fz_mfp))
                val () = $A.drop<byte>(fz_tcb, bv_tcb)
                val () = $A.free<byte>($A.thaw<byte>(fz_tcb))
                val () = (if ~is_quiet() then println! ("  to-c: generated") else ())
              in end
              else let
                val () = $A.drop<byte>(fz_tcb, bv_tcb)
                val () = $A.free<byte>($A.thaw<byte>(fz_tcb))
              in end
            end
          | ~$R.err(_) => ())
      in end else () else ())

      val () = $A.drop<byte>(fz_patshome, bv_patshome)
      val () = $A.free<byte>($A.thaw<byte>(fz_patshome))
    in end
  end
end
