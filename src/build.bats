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
   build_target: int, is_unsafe: int): int

implement preprocess_one
  (src_bv, sats_bv, dats_bv, build_target, is_unsafe) = let
  (* Cache check: if .sats is newer than .bats source, skip preprocessing *)
  val fresh = (if is_newer(sats_bv, src_bv) then 1 else 0): int
in
  if fresh > 0 then 0
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
      val sb = $B.create()
      val @(fz_s, bv_s) = $A.freeze<byte>(sats_arr)
      val () = copy_to_builder(bv_s, 0, sats_len, 524288, sb,
        $AR.checked_nat(sats_len + 1))
      val () = $A.drop<byte>(fz_s, bv_s)
      val () = $A.free<byte>($A.thaw<byte>(fz_s))
      val r1 = write_file_from_builder(sats_bv, 524288, sb)
      (* Write .dats - prepend self-staload *)
      val db = $B.create()
      val bn_start = find_basename_start(sats_bv, 0, 524288, ~1, 4096)
      val bn_end = $S.find_null_bv(sats_bv, bn_start, 524288, 4096)
      val () = $B.bput(db, "staload \"./")
      val () = copy_to_builder(sats_bv, bn_start, bn_end, 524288, db,
        $AR.checked_nat(bn_end - bn_start + 1))
      val () = $B.bput(db, "\"\n")
      val @(fz_d, bv_d) = $A.freeze<byte>(dats_arr)
      val () = copy_to_builder(bv_d, 0, dats_len, 524288, db,
        $AR.checked_nat(dats_len + 1))
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
   clean: remove build/ and dist/ directories
   ============================================================ *)
#pub fn do_clean(): void

implement do_clean() = let
  val exec = str_to_path_arr("/bin/rm")
  val @(fz_exec, bv_exec) = $A.freeze<byte>(exec)
  val argv = $B.create()
  val () = $B.bput(argv, "rm") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-rf") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "build") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "dist") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "docs") val () = $B.put_byte(argv, 0)
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
              val mbb = $B.create()
              val () = $B.bput(mbb, "bats_modules")
              val _ = run_mkdir(mbb)
              val lock_b = $B.create()
              (* Resolve each dependency *)
              fun resolve {lk:agz}{lr:agz}{fuel:nat} .<fuel>.
                (ks: !$A.arr(byte, lk, 4096), pos: int, kl: int,
                 rb: !$A.borrow(byte, lr, 4096), rl: int,
                 lb: !$B.builder, cnt: int, fuel: int fuel): int =
                if fuel <= 0 then cnt
                else if pos >= kl then cnt
                else let
                  val de = $S.find_null(ks, pos, 4096, $AR.checked_nat(kl - pos + 1))
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
                    (* Scan repo/<dep>/ for latest .bats archive *)
                    val dir_b = $B.create()
                    val () = copy_to_builder(rb, 0, rl, 4096, dir_b, $AR.checked_nat(rl + 1))
                    val () = $B.bput(dir_b, "/")
                    val () = arr_range_to_builder(ks, dep_start, dep_end, dir_b, $AR.checked_nat(dl + 1))
                    val () = $B.put_byte(dir_b, 0)
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
                            val us = find_under(a, 0, len, $AR.checked_nat(len + 1))
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
                            val vstart = skip_parts(a, us + 1, len, part, $AR.checked_nat(len + 1))
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
                          in parse_num(a, vstart, len, 0, $AR.checked_nat(len + 1)) end
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
                                val () = cp_name(e, b, 0, el, $AR.checked_nat(el+1))
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
                          val () = print_arr(ks, dep_start, dep_end, 4096, $AR.checked_nat(dl + 1))
                          val () = print_newline()
                          val () = $A.free<byte>(best)
                        in resolve(ks, de+1, kl, rb, rl, lb, cnt, fuel-1) end
                        else let
                          (* mkdir + unzip *)
                          val mb = $B.create()
                          val () = $B.bput(mb, "bats_modules/")
                          val () = arr_range_to_builder(ks, dep_start, dep_end, mb, $AR.checked_nat(dl+1))
                          val _ = run_mkdir(mb)
                          val uz = str_to_path_arr("/usr/bin/unzip")
                          val @(fz_uz, bv_uz) = $A.freeze<byte>(uz)
                          val ua = $B.create()
                          val () = $B.bput(ua, "unzip") val () = $B.put_byte(ua, 0)
                          val () = $B.bput(ua, "-o") val () = $B.put_byte(ua, 0)
                          val () = $B.bput(ua, "-q") val () = $B.put_byte(ua, 0)
                          val () = copy_to_builder(rb, 0, rl, 4096, ua, $AR.checked_nat(rl+1))
                          val () = $B.bput(ua, "/")
                          val () = arr_range_to_builder(ks, dep_start, dep_end, ua, $AR.checked_nat(dl+1))
                          val () = $B.bput(ua, "/")
                          val @(fz_b, bv_b) = $A.freeze<byte>(best)
                          val () = copy_to_builder(bv_b, 0, blen, 256, ua, $AR.checked_nat(blen+1))
                          val () = $B.put_byte(ua, 0)
                          val () = $B.bput(ua, "-d") val () = $B.put_byte(ua, 0)
                          val () = $B.bput(ua, "bats_modules/")
                          val () = arr_range_to_builder(ks, dep_start, dep_end, ua, $AR.checked_nat(dl+1))
                          val () = $B.put_byte(ua, 0)
                          val _ = run_cmd(bv_uz, 524288, ua, 6)
                          val () = $A.drop<byte>(fz_uz, bv_uz)
                          val () = $A.free<byte>($A.thaw<byte>(fz_uz))
                          (* Write lock line *)
                          val () = arr_range_to_builder(ks, dep_start, dep_end, lb, $AR.checked_nat(dl+1))
                          val () = $B.put_byte(lb, 32)
                          (* Version from filename *)
                          val pfx = $B.create()
                          fun mkp {ls4:agz}{f4:nat} .<f4>.
                            (s: !$A.arr(byte, ls4, 4096), i: int, l: int, d3: !$B.builder, f4: int f4): void =
                            if f4 <= 0 then () else if i >= l then ()
                            else if i < 0 then () else if i >= 4096 then ()
                            else let val c = byte2int0($A.get<byte>(s, $AR.checked_idx(i, 4096)))
                            in (if $AR.eq_int_int(c,47) then $B.put_byte(d3,95) else $B.put_byte(d3,c));
                              mkp(s, i+1, l, d3, f4-1) end
                          val () = mkp(ks, dep_start, dep_end, pfx, $AR.checked_nat(dl+1))
                          val () = $B.put_byte(pfx, 95)
                          val pl = $B.length(pfx)
                          val () = $B.builder_free(pfx)
                          val vs = pl val ve = blen - 5
                          val () = (if vs < ve then
                            copy_to_builder(bv_b, vs, ve, 256, lb, $AR.checked_nat(ve-vs+1))
                          else $B.bput(lb, "unknown"))
                          val () = $B.put_byte(lb, 32)
                          val () = $B.bput(lb, "0") (* TODO: compute sha256 *)
                          val () = $B.put_byte(lb, 10)
                          val () = print! ("fetched ")
                          val () = print_arr(ks, dep_start, dep_end, 4096, $AR.checked_nat(dl+1))
                          val () = print! (" v")
                          val () = (if vs < ve then
                            print_borrow(bv_b, vs, ve, 256, $AR.checked_nat(ve-vs+1))
                          else print! ("unknown"))
                          val () = print_newline()
                          val () = $A.drop<byte>(fz_b, bv_b)
                          val () = $A.free<byte>($A.thaw<byte>(fz_b))
                        in resolve(ks, de+1, kl, rb, rl, lb, cnt+1, fuel-1) end
                      end
                    | ~$R.err(_) => let
                        val () = print! ("error: package not found: ")
                        val () = print_arr(ks, dep_start, dep_end, 4096, $AR.checked_nat(dl+1))
                        val () = print_newline()
                      in resolve(ks, de+1, kl, rb, rl, lb, cnt, fuel-1) end
                  end
                end
              val n = resolve(keys, 0, klen, bv_rb3, rplen, lock_b, 0, 200)
              val () = $A.free<byte>(keys)
              (* Resolve transitive deps by running resolve again on deps found
                 in extracted packages' bats.toml files. Repeat until stable. *)
              fun resolve_pass {lr2:agz}{fuel:nat} .<fuel>.
                (rb2: !$A.borrow(byte, lr2, 4096), rl2: int,
                 lb2: !$B.builder, prev_cnt: int, fuel: int fuel): int =
                if fuel <= 0 then prev_cnt
                else let
                  val bmd = str_to_path_arr("bats_modules")
                  val @(fz_bmd, bv_bmd) = $A.freeze<byte>(bmd)
                  val bdr = $F.dir_open(bv_bmd, 524288)
                  val () = $A.drop<byte>(fz_bmd, bv_bmd)
                  val () = $A.free<byte>($A.thaw<byte>(fz_bmd))
                  val @(tk, tkl2) = (case+ bdr of
                    | ~$R.ok(bd) => let
                        val tk = $A.alloc<byte>(4096)
                        val tkl = ref<int>(0)
                        fun sdt {ltk:agz}{f3:nat} .<f3>.
                          (bd: !$F.dir, tk: !$A.arr(byte, ltk, 4096), tkl: ref(int), f3: int f3): void =
                          if f3 <= 0 then ()
                          else let
                            val de = $A.alloc<byte>(256)
                            val nr = $F.dir_next(bd, de, 256)
                            val del = $R.option_unwrap_or<int>(nr, ~1)
                          in if del < 0 then $A.free<byte>(de)
                            else let val dd = is_dot_or_dotdot(de, del, 256) in
                              if dd then let val () = $A.free<byte>(de) in sdt(bd, tk, tkl, f3-1) end
                              else let
                                val tp = $B.create()
                                val () = $B.bput(tp, "bats_modules/")
                                val @(fz_de, bv_de) = $A.freeze<byte>(de)
                                val () = copy_to_builder(bv_de, 0, del, 256, tp, $AR.checked_nat(del+1))
                                val () = $A.drop<byte>(fz_de, bv_de)
                                val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                val () = $B.bput(tp, "/bats.toml")
                                val () = $B.put_byte(tp, 0)
                                val @(tpa, _) = $B.to_arr(tp)
                                val @(fz_tpa, bv_tpa) = $A.freeze<byte>(tpa)
                                val tfo = $F.file_open(bv_tpa, 524288, 0, 0)
                                val () = $A.drop<byte>(fz_tpa, bv_tpa)
                                val () = $A.free<byte>($A.thaw<byte>(fz_tpa))
                                val () = (case+ tfo of
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
                                          val () = (case+ kr2 of
                                            | ~$R.some(kl2) => !tkl := kl2
                                            | ~$R.none() => ())
                                          val () = $A.drop<byte>(fz_dka, bv_dka)
                                          val () = $A.free<byte>($A.thaw<byte>(fz_dka))
                                          val () = $T.toml_free(doc2)
                                        in end
                                      | ~$R.err(_) => ()
                                    end
                                  | ~$R.err(_) => ())
                                (* TODO: also scan src/lib.bats for #use directives *)
                              in sdt(bd, tk, tkl, f3-1) end
                            end
                          end
                        val () = sdt(bd, tk, tkl, 200)
                        val dcr3 = $F.dir_close(bd)
                        val () = $R.discard<int><int>(dcr3)
                        val tklv = !tkl
                      in @(tk, tklv) end
                    | ~$R.err(_) => let
                        val z = $A.alloc<byte>(4096)
                      in @(z, 0) end): [ltk:agz] @($A.arr(byte, ltk, 4096), int)
                  val new_cnt = resolve(tk, 0, tkl2, rb2, rl2, lb2, prev_cnt, 200)
                  val () = $A.free<byte>(tk)
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
#pub fn write_wasm_runtime_h(): int

implement write_wasm_runtime_h() = let
  val b = $B.create()
  val () = $B.bput(b, "/* runtime.h -- Freestanding WASM runtime for ATS2 */\n#ifndef BATS_WASM_RUNTIME_H\n#define BATS_WASM_RUNTIME_H\n")
  val () = $B.bput(b, "typedef void atstype_void;\ntypedef void atsvoid_t0ype;\ntypedef int atstype_int;\ntypedef unsigned int atstype_uint;\n")
  val () = $B.bput(b, "typedef long int atstype_lint;\ntypedef unsigned long int atstype_ulint;\ntypedef long long int atstype_llint;\n")
  val () = $B.bput(b, "typedef unsigned long long int atstype_ullint;\ntypedef short int atstype_sint;\ntypedef unsigned short int atstype_usint;\n")
  val () = $B.bput(b, "typedef atstype_lint atstype_ssize;\ntypedef atstype_ulint atstype_size;\ntypedef int atstype_bool;\n")
  val () = $B.bput(b, "typedef unsigned char atstype_byte;\ntypedef char atstype_char;\ntypedef signed char atstype_schar;\ntypedef unsigned char atstype_uchar;\n")
  val () = $B.bput(b, "typedef char *atstype_string;\ntypedef char *atstype_stropt;\ntypedef char *atstype_strptr;\n")
  val () = $B.bput(b, "typedef void *atstype_ptr;\ntypedef void *atstype_ptrk;\ntypedef void *atstype_ref;\ntypedef void *atstype_boxed;\n")
  val () = $B.bput(b, "typedef void *atstype_datconptr;\ntypedef void *atstype_datcontyp;\ntypedef void *atstype_arrptr;\ntypedef void *atstype_funptr;\ntypedef void *atstype_cloptr;\n")
  val () = $B.bput(b, "#define atstkind_type(tk) tk\n#define atstkind_t0ype(tk) tk\n#ifndef _ATSTYPE_VAR_SIZE_\n#define _ATSTYPE_VAR_SIZE_ 0X10000\n#endif\n")
  val () = $B.bput(b, "typedef struct { char _[_ATSTYPE_VAR_SIZE_]; } atstype_var[0];\n#define atstyvar_type(a) atstype_var\n#define atstybox_type(hit) atstype_boxed\n")
  val () = $B.bput(b, "#define atsrefarg0_type(hit) hit\n#define atsrefarg1_type(hit) atstype_ref\n")
  val () = $B.bput(b, "#define atsbool_true 1\n#define atsbool_false 0\n#define atsptr_null ((void*)0)\n#define the_atsptr_null ((void*)0)\n")
  val () = $B.bput(b, "#define ATSstruct struct\n#define ATSextern() extern\n#define ATSstatic() static\n#define ATSinline() static inline\n")
  val () = $B.bput(b, "#define ATSdynload()\n#define ATSdynloadflag_sta(flag)\n#define ATSdynloadflag_ext(flag) extern int flag\n")
  val () = $B.bput(b, "#define ATSdynloadflag_init(flag) int flag = 0\n#define ATSdynloadflag_minit(flag) int flag = 0\n#define ATSdynloadset(flag) flag = 1\n")
  val () = $B.bput(b, "#define ATSdynloadfcall(dynloadfun) dynloadfun()\n#define ATSassume(flag) void *flag = (void*)0\n")
  val () = $B.bput(b, "#define ATSdyncst_mac(d2c)\n#define ATSdyncst_castfn(d2c)\n#define ATSdyncst_extfun(d2c, targs, tres) extern tres d2c targs\n")
  val () = $B.bput(b, "#define ATSdyncst_stafun(d2c, targs, tres) static tres d2c targs\n#define ATSdyncst_valimp(d2c, type) type d2c\n#define ATSdyncst_valdec(d2c, type) extern type d2c\n")
  val () = $B.bput(b, "#define ATSif(x) if(x)\n#define ATSthen()\n#define ATSelse() else\n#define ATSifthen(x) if(x)\n#define ATSifnthen(x) if(!(x))\n")
  val () = $B.bput(b, "#define ATSreturn(x) return(x)\n#define ATSreturn_void(x) return\n#define ATSfunbody_beg()\n#define ATSfunbody_end()\n")
  val () = $B.bput(b, "#define ATSPMVint(i) i\n#define ATSPMVintrep(rep) (rep)\n#define ATSPMVbool_true() atsbool_true\n#define ATSPMVbool_false() atsbool_false\n")
  val () = $B.bput(b, "#define ATSPMVchar(c) (c)\n#define ATSPMVstring(str) (str)\n#define ATSPMVi0nt(tok) (tok)\n#define ATSPMVempty()\n")
  val () = $B.bput(b, "#define ATSPMVextval(name) (name)\n#define ATSPMVptrof(lval) (&(lval))\n#define ATSPMVptrof_void(lval) ((void*)0)\n")
  val () = $B.bput(b, "#define ATSPMVrefarg0(val) (val)\n#define ATSPMVrefarg1(ref) (ref)\n#define ATSPMVsizeof(hit) (sizeof(hit))\n")
  val () = $B.bput(b, "#define ATSPMVfunlab(flab) (flab)\n#define ATSPMVcastfn(d2c, hit, arg) ((hit)arg)\n#define ATSPMVtyrep(rep) (rep)\n")
  val () = $B.bput(b, "#define ATStyclo() struct{ void *cfun; }\n#define ATSfunclo_fun(pmv, targs, tres) ((tres(*)targs)(pmv))\n")
  val () = $B.bput(b, "#define ATSfunclo_clo(pmv, targs, tres) ((tres(*)targs)(((ATStyclo()*)pmv)->cfun))\n")
  val () = $B.bput(b, "#define ATSfuncall(fun, funarg) (fun)funarg\n#define ATSextfcall(fun, funarg) (fun)funarg\n#define ATSextmcall(obj, mtd, funarg) (obj->mtd)funarg\n")
  val () = $B.bput(b, "#define ATStmpdec(tmp, hit) hit tmp\n#define ATStmpdec_void(tmp)\n#define ATSstatmpdec(tmp, hit) static hit tmp\n#define ATSstatmpdec_void(tmp)\n")
  val () = $B.bput(b, "#define ATSderef(pmv, hit) (*(hit*)pmv)\n#define ATSCKnot(x) ((x)==0)\n#define ATSCKiseqz(x) ((x)==0)\n#define ATSCKisneqz(x) ((x)!=0)\n")
  val () = $B.bput(b, "#define ATSCKptriscons(x) (0 != (void*)(x))\n#define ATSCKptrisnull(x) (0 == (void*)(x))\n")
  val () = $B.bput(b, "#define ATSINSlab(lab) lab\n#define ATSINSgoto(lab) goto lab\n#define ATSINSflab(flab) flab\n#define ATSINSfgoto(flab) goto flab\n")
  val () = $B.bput(b, "#define ATSINSmove(tmp, val) (tmp = val)\n#define ATSINSpmove(tmp, hit, val) (*(hit*)tmp = val)\n")
  val () = $B.bput(b, "#define ATSINSmove_void(tmp, command) command\n#define ATSINSpmove_void(tmp, hit, command) command\n#define ATSINSmove_nil(tmp) (tmp = ((void*)0))\n")
  val () = $B.bput(b, "#define ATSSELfltrec(pmv, tyrec, lab) ((pmv).lab)\n#define ATSSELcon(pmv, tycon, lab) (((tycon*)(pmv))->lab)\n")
  val () = $B.bput(b, "#define ATSINSmove_con1_beg()\n#define ATSINSmove_con1_new(tmp, tycon) (tmp = ATS_MALLOC(sizeof(tycon)))\n")
  val () = $B.bput(b, "#define ATSINSstore_con1_ofs(tmp, tycon, lab, val) (((tycon*)(tmp))->lab = val)\n#define ATSINSmove_con1_end()\n#define ATSINSfreecon(ptr) ATS_MFREE(ptr)\n")
  val () = $B.bput(b, "#define ATSSELrecsin(pmv, tyrec, lab) (pmv)\n#define ATSINSstore_con1_tag(dst, tag) (((int*)(dst))[0] = (tag))\n")
  val () = $B.bput(b, "#define ATSINSmove_con0(dst, tag) ((dst) = (void*)(tag))\n#define ATSCKpat_con0(p, tag) ((p) == (void*)(tag))\n#define ATSCKpat_con1(p, tag) (((int*)(p))[0] == (tag))\n")
  val () = $B.bput(b, "#define ATSINSmove_fltrec_beg()\n#define ATSINSmove_fltrec_end()\n#define ATSINSstore_fltrec_ofs(tmp, tyrec, lab, val) ((tmp).lab = val)\n")
  val () = $B.bput(b, "#define ATSINSload(tmp, pmv) (tmp = pmv)\n#define ATSINSstore(pmv1, pmv2) (pmv1 = pmv2)\n#define ATSINSxstore(tmp, pmv1, pmv2) (tmp = pmv1, pmv1 = pmv2, pmv2 = tmp)\n")
  val () = $B.bput(b, "#define ATStailcal_beg() do {\n#define ATStailcal_end() } while(0) ;\n#define ATSINSmove_tlcal(apy, tmp) (apy = tmp)\n#define ATSINSargmove_tlcal(arg, apy) (arg = apy)\n")
  val () = $B.bput(b, "#define ATSbranch_beg()\n#define ATSbranch_end() break ;\n#define ATScaseof_beg() do {\n#define ATScaseof_end() } while(0) ;\n#define ATSextcode_beg()\n#define ATSextcode_end()\n")
  val () = $B.bput(b, "#define atspre_g1uint2int_size_int(x) ((int)(x))\n#define atspre_g0int_add_int(x, y) ((x) + (y))\n#define atspre_g1int_mul_int(x, y) ((x) * (y))\n")
  val () = $B.bput(b, "#define atspre_g0int2uint_int_size(x) ((atstype_size)(x))\n#define atspre_g0uint_mul_size(x, y) ((x) * (y))\n#define atspre_add_ptr0_bsz(p, n) ((void*)((char*)(p) + (n)))\n")
  val () = $B.bput(b, "#define atspre_g1int2int_int_int(x) (x)\n#define atspre_g1int_lt_int(x, y) ((x) < (y))\n#define atspre_g1int_add_int(x, y) ((x) + (y))\n")
  val () = $B.bput(b, "#define atspre_char2int1(c) ((int)(c))\n#define atspre_g0int2int_int_int(x) (x)\n#define atspre_g0int_gt_int(x, y) ((x) > (y))\n")
  val () = $B.bput(b, "#define atspre_g1ofg0_int(x) (x)\n#define atspre_g0ofg1_int(x) (x)\n#define atspre_g1int_gt_int(x, y) ((x) > (y))\n#define atspre_g1int_gte_int(x, y) ((x) >= (y))\n")
  val () = $B.bput(b, "#define atspre_g1int_lte_int(x, y) ((x) <= (y))\n#define atspre_g1int_sub_int(x, y) ((x) - (y))\n#define atspre_g1int_neg_int(x) (-(x))\n")
  val () = $B.bput(b, "#define atspre_g0int_gte_int(x, y) ((x) >= (y))\n#define atspre_g0int_lte_int(x, y) ((x) <= (y))\n#define atspre_g0int_eq_int(x, y) ((x) == (y))\n")
  val () = $B.bput(b, "#define atspre_g0int_mul_int(x, y) ((x) * (y))\n#define atspre_g0int_sub_int(x, y) ((x) - (y))\n#define atspre_g0int_neq_int(x, y) ((x) != (y))\n")
  val () = $B.bput(b, "#define atspre_g0int_lt_int(x, y) ((x) < (y))\n#define atspre_g0int_div_int(x, y) ((x) / (y))\n#define atspre_g0int_mod_int(x, y) ((x) % (y))\n")
  val () = $B.bput(b, "#define atspre_g1int_div_int(x, y) ((x) / (y))\n#define atspre_g1int_eq_int(x, y) ((x) == (y))\n#define atspre_g1int_neq_int(x, y) ((x) != (y))\n")
  val () = $B.bput(b, "#define atspre_g0int_asl_int(x, n) ((x) << (n))\n#define atspre_g0int_asr_int(x, n) ((x) >> (n))\n")
  val () = $B.bput(b, "#define atspre_lor_int_int(x, y) ((x) | (y))\n#define atspre_land_int_int(x, y) ((x) & (y))\n")
  val () = $B.bput(b, "#define atspre_byte2int0(b) ((int)(b))\n#define atspre_ptr_null() ((void*)0)\n#define atspre_ptr_isnot_null(p) ((p) != 0)\n#define atspre_ptr0_isnot_null atspre_ptr_isnot_null\n")
  val () = $B.bput(b, "#define ATS_MALLOC(sz) malloc(sz)\n#define ATS_MFREE(ptr) free(ptr)\n#define ATSINScloptr_make(tmp, sz) (tmp = ATS_MALLOC(sz))\n#define ATSINScloptr_free(tmp) ATS_MFREE(tmp)\n")
  val () = $B.bput(b, "#define ATSclosurerize_beg(flab, tenvs, targs, tres)\n#define ATSclosurerize_end()\n#define ATSFCreturn(x) return(x)\n#define ATSFCreturn_void(x) (x); return\n")
  val () = $B.bput(b, "#define ATSPMVcfunlab(knd, flab, env) (flab##__closurerize)env\nextern void mainats_0_void(void);\n#define ATSmainats_0_void(err) mainats_0_void()\n")
  val () = $B.bput(b, "void *malloc(int size);\nvoid free(void *ptr);\nvoid *memset(void *s, int c, unsigned int n);\nvoid *memcpy(void *dst, const void *src, unsigned int n);\n")
  val () = $B.bput(b, "static inline void *calloc(int n, int sz) { return malloc(n * sz); }\n#endif\n")
  val p = str_to_path_arr("build/_bats_wasm_runtime.h")
  val @(fz_p, bv_p) = $A.freeze<byte>(p)
  val rc = write_file_from_builder(bv_p, 524288, b)
  val () = $A.drop<byte>(fz_p, bv_p)
  val () = $A.free<byte>($A.thaw<byte>(fz_p))
in rc end

#pub fn write_wasm_runtime_c(): int

implement write_wasm_runtime_c() = let
  val b = $B.create()
  val () = $B.bput(b, "/* runtime.c -- Freestanding WASM: free-list allocator */\nextern unsigned char __heap_base;\nstatic unsigned char *heap_ptr = &__heap_base;\n")
  val () = $B.bput(b, "#define WARD_HEADER 8\n#define WARD_NBUCKET 9\nstatic const unsigned int ward_bsz[WARD_NBUCKET] = {32,128,512,4096,8192,16384,524288,262144,1048576};\n")
  val () = $B.bput(b, "static void *ward_fl[WARD_NBUCKET] = {0,0,0,0,0,0,0,0,0};\nstatic void *ward_fl_over = 0;\n")
  val () = $B.bput(b, "void *memset(void *s,int c,unsigned int n){unsigned char *p=(unsigned char*)s;unsigned char byte=(unsigned char)c;while(n--)*p++=byte;return s;}\n")
  val () = $B.bput(b, "void *memcpy(void *dst,const void *src,unsigned int n){unsigned char *d=(unsigned char*)dst;const unsigned char *s=(const unsigned char*)src;while(n--)*d++=*s++;return dst;}\n")
  val () = $B.bput(b, "static inline unsigned int ward_hdr_read(void *p){return *(unsigned int*)((char*)p-WARD_HEADER);}\n")
  val () = $B.bput(b, "static inline int ward_bucket(unsigned int n){if(n<=32)return 0;if(n<=128)return 1;if(n<=512)return 2;if(n<=4096)return 3;\n")
  val () = $B.bput(b, "if(n<=8192)return 4;if(n<=16384)return 5;if(n<=524288)return 6;if(n<=262144)return 7;if(n<=1048576)return 8;return -1;}\n")
  val () = $B.bput(b, "static void *ward_bump(unsigned int usable){unsigned long a=(unsigned long)heap_ptr;a=(a+7u)&~7u;unsigned long end=a+WARD_HEADER+usable;\n")
  val () = $B.bput(b, "unsigned long limit=(unsigned long)__builtin_wasm_memory_size(0)*524288UL;if(end>limit){unsigned long pages=(end-limit+65535UL)/524288UL;\n")
  val () = $B.bput(b, "if(__builtin_wasm_memory_grow(0,pages)==(unsigned long)(-1))return(void*)0;}*(unsigned int*)a=usable;void *p=(void*)(a+WARD_HEADER);heap_ptr=(unsigned char*)end;return p;}\n")
  val () = $B.bput(b, "void *malloc(int size){if(size<=0)size=1;unsigned int n=(unsigned int)size;int b=ward_bucket(n);if(b>=0){unsigned int bsz=ward_bsz[b];void *p;\n")
  val () = $B.bput(b, "if(ward_fl[b]){p=ward_fl[b];ward_fl[b]=*(void**)p;}else{p=ward_bump(bsz);}memset(p,0,bsz);return p;}\n")
  val () = $B.bput(b, "void **prev=&ward_fl_over;void *cur=ward_fl_over;while(cur){unsigned int bsz=ward_hdr_read(cur);if(bsz>=n&&bsz<=2*n){*prev=*(void**)cur;memset(cur,0,bsz);return cur;}\n")
  val () = $B.bput(b, "prev=(void**)cur;cur=*(void**)cur;}void *p=ward_bump(n);memset(p,0,n);return p;}\n")
  val () = $B.bput(b, "void free(void *ptr){if(!ptr)return;unsigned int sz=ward_hdr_read(ptr);int b=ward_bucket(sz);if(b>=0&&ward_bsz[b]==sz){*(void**)ptr=ward_fl[b];ward_fl[b]=ptr;}\n")
  val () = $B.bput(b, "else{*(void**)ptr=ward_fl_over;ward_fl_over=ptr;}}\n")
  val p = str_to_path_arr("build/_bats_wasm_runtime.c")
  val @(fz_p, bv_p) = $A.freeze<byte>(p)
  val rc = write_file_from_builder(bv_p, 524288, b)
  val () = $A.drop<byte>(fz_p, bv_p)
  val () = $A.free<byte>($A.thaw<byte>(fz_p))
in rc end

#pub fn write_wasm_stubs(): int

implement write_wasm_stubs() = let
  val mb = $B.create()
  val () = $B.bput(mb, "build/_bats_wasm_stubs/libats/libc/CATS/sys")
  val r0 = run_mkdir(mb)
  val stub = "/* stub */\n"
  fn write_stub {sn:nat} (path: string sn): int = let
    val sb = $B.create()
    val () = $B.bput(sb, stub)
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
  val argv = $B.create()
  val () = $B.bput(argv, "clang") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "--target=wasm32") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-O2") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-nostdlib") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-ffreestanding") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-fvisibility=default") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-D_ATS_CCOMP_HEADER_NONE_") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-D_ATS_CCOMP_EXCEPTION_NONE_") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-D_ATS_CCOMP_PRELUDE_NONE_") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-D_ATS_CCOMP_RUNTIME_NONE_") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-include") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "build/_bats_wasm_runtime.h") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-I") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "build/_bats_wasm_stubs") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-c") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-o") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "build/_bats_wasm_runtime.o") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "build/_bats_wasm_runtime.c") val () = $B.put_byte(argv, 0)
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
  val argv = $B.create()
  val () = $B.bput(argv, "clang") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "--target=wasm32") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-O2") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-nostdlib") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-ffreestanding") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-fvisibility=default") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-D_ATS_CCOMP_HEADER_NONE_") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-D_ATS_CCOMP_EXCEPTION_NONE_") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-D_ATS_CCOMP_PRELUDE_NONE_") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-D_ATS_CCOMP_RUNTIME_NONE_") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-include") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "build/_bats_wasm_runtime.h") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-I") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "build/_bats_wasm_stubs") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-c") val () = $B.put_byte(argv, 0)
  val () = $B.bput(argv, "-o") val () = $B.put_byte(argv, 0)
  val oc = out_len - 1
  val () = copy_to_builder(out_bv, 0, oc, 524288, argv, $AR.checked_nat(out_len + 1))
  val () = $B.put_byte(argv, 0)
  val ic = in_len - 1
  val () = copy_to_builder(in_bv, 0, ic, 524288, argv, $AR.checked_nat(in_len + 1))
  val () = $B.put_byte(argv, 0)
  val rc = run_cmd(bv_exec, 524288, argv, 18)
  val () = $A.drop<byte>(fz_exec, bv_exec)
  val () = $A.free<byte>($A.thaw<byte>(fz_exec))
in rc end

fn wasm_cc_file {l:agz}
  (path: !$A.borrow(byte, l, 524288), path_len: int): int = let
  (* path is like "build/.../_dats.c", replace .c with .o for output *)
  val ob = $B.create()
  val pl = path_len - 1
  val () = copy_to_builder(path, 0, pl - 1, 524288, ob, $AR.checked_nat(pl))
  val () = $B.bput(ob, "o")
  val () = $B.put_byte(ob, 0)
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
  (* Compile all _dats.c files found during the native patsopt pass *)
  (* We rely on the native build having already run patsopt to generate C files *)
  val db = $B.create()
  val () = $B.bput(db, "build")
  val () = $B.put_byte(db, 0)
  val @(dba, _) = $B.to_arr(db)
  val @(fz_db, bv_db) = $A.freeze<byte>(dba)
  val () = println! ("  compiling WASM...")
  (* Compile entry *)
  val eb = $B.create()
  val () = $B.bput(eb, "build/_bats_entry_")
  (* Find the entry file by scanning build/ for _bats_entry_*_dats.c *)
  val dr = $F.dir_open(bv_db, 524288)
  val () = $A.drop<byte>(fz_db, bv_db)
  val () = $A.free<byte>($A.thaw<byte>(fz_db))
  val link_b = $B.create()
  val () = $B.bput(link_b, "wasm-ld") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--no-entry") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--allow-undefined") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--lto-O2") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "-z") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "stack-size=1048576") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--initial-memory=16777216") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--max-memory=268435456") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--export=mainats_0_void") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--export=malloc") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--export=bats_on_event") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--export=bats_timer_fire") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--export=bats_idb_fire") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--export=bats_idb_fire_get") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--export=bats_measure_set") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--export=bats_on_fetch_complete") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--export=bats_on_file_open") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "--export=bats_on_decompress_complete") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "-o") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "dist/wasm/app.wasm") val () = $B.put_byte(link_b, 0)
  val () = $B.bput(link_b, "build/_bats_wasm_runtime.o") val () = $B.put_byte(link_b, 0)
  val link_count = 22
  val () = (let val @(ea, _) = $B.to_arr(eb) val () = $A.free<byte>(ea) in end)
  val () = (case+ dr of
    | ~$R.ok(d) => let
        fun scan_build {fuel2:nat} .<fuel2>.
          (d: !$F.dir, lb: !$B.builder, lc: int, fuel2: int fuel2): int =
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
                val pb = $B.create()
                val () = $B.bput(pb, "build/")
                val @(fz_e, bv_e) = $A.freeze<byte>(e)
                val () = copy_to_builder(bv_e, 0, el, 256, pb, $AR.checked_nat(el + 1))
                val () = $B.put_byte(pb, 0)
                val @(pa, pl) = $B.to_arr(pb)
                val @(fz_p, bv_p) = $A.freeze<byte>(pa)
                val rc = wasm_cc_file(bv_p, pl)
                val () = (if rc <> 0 then let
                  val () = print! ("error: wasm cc failed for ")
                  val () = print_borrow(bv_e, 0, el, 256, $AR.checked_nat(el + 1))
                in print_newline() end else let
                  (* Add .o to link list *)
                  val () = copy_to_builder(bv_p, 0, pl - 2, 524288, lb, $AR.checked_nat(pl))
                  val () = $B.bput(lb, "o")
                  val () = $B.put_byte(lb, 0)
                in end)
                val () = $A.drop<byte>(fz_p, bv_p)
                val () = $A.free<byte>($A.thaw<byte>(fz_p))
                val () = $A.drop<byte>(fz_e, bv_e)
                val () = $A.free<byte>($A.thaw<byte>(fz_e))
              in scan_build(d, lb, lc + 1, fuel2 - 1) end
              else let
                val () = $A.free<byte>(e)
              in scan_build(d, lb, lc, fuel2 - 1) end
            end
          end
        val nfiles = scan_build(d, link_b, 0, 500)
        val dcr = $F.dir_close(d)
        val () = $R.discard<int><int>(dcr)
      in end
    | ~$R.err(_) => ())
  (* TODO: also scan subdirectories for dep and src .o files *)
  (* For now, just link what we found in build/ *)
  val () = println! ("  linking WASM...")
  val mb1 = $B.create()
  val () = $B.bput(mb1, "dist")
  val _ = run_mkdir(mb1)
  val mb2 = $B.create()
  val () = $B.bput(mb2, "dist/wasm")
  val _ = run_mkdir(mb2)
  val exec_ld = str_to_path_arr("/usr/bin/wasm-ld")
  val @(fz_ld, bv_ld) = $A.freeze<byte>(exec_ld)
  val lrc = run_cmd(bv_ld, 524288, link_b, link_count + 10)
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

#pub fn do_build(release: int): void

implement do_build(release) = let
  val is_unsafe = read_unsafe_flag()
  (* Step 1: mkdir build directories *)
  val mb1 = $B.create()
  val () = $B.bput(mb1, "build/src/bin")
  val _ = run_mkdir(mb1)
  val mb2 = $B.create()
  val () = $B.bput(mb2, "build/bats_modules")
  val _ = run_mkdir(mb2)
  val mb3 = $B.create()
  val () = $B.bput(mb3, "dist/debug")
  val _ = run_mkdir(mb3)
  val mb4 = $B.create()
  val () = $B.bput(mb4, "dist/release")
  val r0 = run_mkdir(mb4)
  val () = (if r0 <> 0 then println! ("error: mkdir failed") else ())
in
  if r0 <> 0 then ()
  else let
    (* Step 1b: Write and compile native runtime *)
    val nrt_b = $B.create()
    val () = $B.bput(nrt_b, "/* _bats_native_runtime.c -- ATS2 memory allocator backed by libc */\n")
    val () = $B.bput(nrt_b, "#include <stdlib.h>\n")
    val () = $B.bput(nrt_b, "void atsruntime_mfree_undef(void *ptr) { free(ptr); }\n")
    val () = $B.bput(nrt_b, "void *atsruntime_malloc_undef(size_t bsz) { return malloc(bsz); }\n")
    val () = $B.bput(nrt_b, "void *atsruntime_calloc_undef(size_t asz, size_t tsz) { return calloc(asz, tsz); }\n")
    val () = $B.bput(nrt_b, "void *atsruntime_realloc_undef(void *ptr, size_t bsz) { return realloc(ptr, bsz); }\n")
    val nrt_path = str_to_path_arr("build/_bats_native_runtime.c")
    val @(fz_nrtp, bv_nrtp) = $A.freeze<byte>(nrt_path)
    val _ = write_file_from_builder(bv_nrtp, 524288, nrt_b)
    val () = $A.drop<byte>(fz_nrtp, bv_nrtp)
    val () = $A.free<byte>($A.thaw<byte>(fz_nrtp))
    val nrt_exec = str_to_path_arr("/usr/bin/cc")
    val @(fz_nrt_exec, bv_nrt_exec) = $A.freeze<byte>(nrt_exec)
    val nrt_argv = $B.create()
    val () = $B.bput(nrt_argv, "cc") val () = $B.put_byte(nrt_argv, 0)
    val () = $B.bput(nrt_argv, "-c") val () = $B.put_byte(nrt_argv, 0)
    val () = $B.bput(nrt_argv, "-o") val () = $B.put_byte(nrt_argv, 0)
    val () = $B.bput(nrt_argv, "build/_bats_native_runtime.o") val () = $B.put_byte(nrt_argv, 0)
    val () = $B.bput(nrt_argv, "build/_bats_native_runtime.c") val () = $B.put_byte(nrt_argv, 0)
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
       dst: !$B.builder, fuel: int fuel): void =
      if fuel <= 0 then ()
      else if pos >= len then ()
      else let
        val b = $S.borrow_byte(buf, pos, 512)
        val () = $B.put_byte(dst, b)
      in arr_to_builder(buf, pos + 1, len, dst, fuel - 1) end
    fn ensure_ats2 {l:agz}
      (buf: !$A.borrow(byte, l, 512), plen: int): void = let
      (* Check if patsopt exists by trying to stat it *)
      val test_path = $B.create()
      val () = arr_to_builder(buf, 0, plen, test_path, $AR.checked_nat(plen + 1))
      val () = $B.bput(test_path, "/bin/patsopt")
      val () = $B.put_byte(test_path, 0)
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
        val mkb = $B.create()
        val () = arr_to_builder(buf, 0, plen, mkb, $AR.checked_nat(plen + 1))
        val _ = run_mkdir(mkb)
        (* curl -sL <url> -o /tmp/_bpoc_ats2.tgz *)
        val curl_exec = str_to_path_arr("/usr/bin/curl")
        val @(fz_ce, bv_ce) = $A.freeze<byte>(curl_exec)
        val curl_argv = $B.create()
        val () = $B.bput(curl_argv, "curl") val () = $B.put_byte(curl_argv, 0)
        val () = $B.bput(curl_argv, "-sL") val () = $B.put_byte(curl_argv, 0)
        val () = $B.bput(curl_argv, "https://raw.githubusercontent.com/ats-lang/ats-lang.github.io/master/FROZEN000/ATS-Postiats/ATS2-Postiats-int-0.4.2.tgz")
        val () = $B.put_byte(curl_argv, 0)
        val () = $B.bput(curl_argv, "-o") val () = $B.put_byte(curl_argv, 0)
        val () = $B.bput(curl_argv, "/tmp/_bpoc_ats2.tgz") val () = $B.put_byte(curl_argv, 0)
        val r1 = run_cmd(bv_ce, 524288, curl_argv, 5)
        val () = $A.drop<byte>(fz_ce, bv_ce)
        val () = $A.free<byte>($A.thaw<byte>(fz_ce))
        (* tar -xzf /tmp/_bpoc_ats2.tgz --strip-components=1 -C <patshome> *)
        val tar_exec = str_to_path_arr("/usr/bin/tar")
        val @(fz_te, bv_te) = $A.freeze<byte>(tar_exec)
        val tar_argv = $B.create()
        val () = $B.bput(tar_argv, "tar") val () = $B.put_byte(tar_argv, 0)
        val () = $B.bput(tar_argv, "-xzf") val () = $B.put_byte(tar_argv, 0)
        val () = $B.bput(tar_argv, "/tmp/_bpoc_ats2.tgz") val () = $B.put_byte(tar_argv, 0)
        val () = $B.bput(tar_argv, "--strip-components=1") val () = $B.put_byte(tar_argv, 0)
        val () = $B.bput(tar_argv, "-C") val () = $B.put_byte(tar_argv, 0)
        val () = arr_to_builder(buf, 0, plen, tar_argv, $AR.checked_nat(plen + 1))
        val () = $B.put_byte(tar_argv, 0)
        val r2 = run_cmd(bv_te, 524288, tar_argv, 6)
        val () = $A.drop<byte>(fz_te, bv_te)
        val () = $A.free<byte>($A.thaw<byte>(fz_te))
        (* rm /tmp/_bpoc_ats2.tgz *)
        val rm_exec = str_to_path_arr("/bin/rm")
        val @(fz_re, bv_re) = $A.freeze<byte>(rm_exec)
        val rm_argv = $B.create()
        val () = $B.bput(rm_argv, "rm") val () = $B.put_byte(rm_argv, 0)
        val () = $B.bput(rm_argv, "/tmp/_bpoc_ats2.tgz") val () = $B.put_byte(rm_argv, 0)
        val _ = run_cmd(bv_re, 524288, rm_argv, 2)
        val () = $A.drop<byte>(fz_re, bv_re)
        val () = $A.free<byte>($A.thaw<byte>(fz_re))
        (* make -j4 -C <patshome>/src/CBOOT patsopt PATSHOME=<patshome> *)
        val () = println! ("building ATS2...")
        val make_exec = str_to_path_arr("/usr/bin/make")
        val @(fz_me, bv_me) = $A.freeze<byte>(make_exec)
        val make_argv = $B.create()
        val () = $B.bput(make_argv, "make") val () = $B.put_byte(make_argv, 0)
        val () = $B.bput(make_argv, "-j4") val () = $B.put_byte(make_argv, 0)
        val () = $B.bput(make_argv, "-C") val () = $B.put_byte(make_argv, 0)
        val () = arr_to_builder(buf, 0, plen, make_argv, $AR.checked_nat(plen + 1))
        val () = $B.bput(make_argv, "/src/CBOOT") val () = $B.put_byte(make_argv, 0)
        val () = $B.bput(make_argv, "patsopt") val () = $B.put_byte(make_argv, 0)
        val phome_arg = $B.create()
        val () = $B.bput(phome_arg, "PATSHOME=")
        val () = arr_to_builder(buf, 0, plen, phome_arg, $AR.checked_nat(plen + 1))
        val @(pha, phl) = $B.to_arr(phome_arg)
        val @(fz_pha, bv_pha) = $A.freeze<byte>(pha)
        val () = copy_to_builder(bv_pha, 0, phl, 524288, make_argv, $AR.checked_nat(phl + 1))
        val () = $B.put_byte(make_argv, 0)
        val () = $A.drop<byte>(fz_pha, bv_pha)
        val () = $A.free<byte>($A.thaw<byte>(fz_pha))
        val r3 = run_cmd(bv_me, 524288, make_argv, 6)
        val () = $A.drop<byte>(fz_me, bv_me)
        val () = $A.free<byte>($A.thaw<byte>(fz_me))
        (* mkdir -p <patshome>/bin *)
        val mkb2 = $B.create()
        val () = arr_to_builder(buf, 0, plen, mkb2, $AR.checked_nat(plen + 1))
        val () = $B.bput(mkb2, "/bin")
        val _ = run_mkdir(mkb2)
        (* cp <patshome>/src/CBOOT/patsopt <patshome>/bin/patsopt *)
        val cp_exec = str_to_path_arr("/bin/cp")
        val @(fz_cpe, bv_cpe) = $A.freeze<byte>(cp_exec)
        val cp_argv = $B.create()
        val () = $B.bput(cp_argv, "cp") val () = $B.put_byte(cp_argv, 0)
        val () = arr_to_builder(buf, 0, plen, cp_argv, $AR.checked_nat(plen + 1))
        val () = $B.bput(cp_argv, "/src/CBOOT/patsopt") val () = $B.put_byte(cp_argv, 0)
        val () = arr_to_builder(buf, 0, plen, cp_argv, $AR.checked_nat(plen + 1))
        val () = $B.bput(cp_argv, "/bin/patsopt") val () = $B.put_byte(cp_argv, 0)
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
                    val chk_b = $B.create()
                    val () = $B.bput(chk_b, "bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, chk_b, $AR.checked_nat(elen + 1))
                    val () = $B.bput(chk_b, "/bats.toml")
                    val () = $B.put_byte(chk_b, 0)
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
                      val nsd = $B.create()
                      val () = $B.bput(nsd, "bats_modules/")
                      val () = copy_to_builder(bv_e, 0, elen, 256, nsd, $AR.checked_nat(elen + 1))
                      val () = $B.put_byte(nsd, 0)
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
                                    val mc2 = $B.create()
                                    val () = $B.bput(mc2, "build/bats_modules/")
                                    val () = copy_to_builder(ns_bv, 0, ns_len, 256, mc2, $AR.checked_nat(ns_len + 1))
                                    val () = $B.bput(mc2, "/")
                                    val () = copy_to_builder(bv_se, 0, sel, 256, mc2, $AR.checked_nat(sel + 1))
                                    val () = $B.bput(mc2, "/src")
                                    val _ = run_mkdir(mc2)
                                    (* source *)
                                    val sp2 = $B.create()
                                    val () = $B.bput(sp2, "bats_modules/")
                                    val () = copy_to_builder(ns_bv, 0, ns_len, 256, sp2, $AR.checked_nat(ns_len + 1))
                                    val () = $B.bput(sp2, "/")
                                    val () = copy_to_builder(bv_se, 0, sel, 256, sp2, $AR.checked_nat(sel + 1))
                                    val () = $B.bput(sp2, "/src/lib.bats")
                                    val () = $B.put_byte(sp2, 0)
                                    val @(sa2, _) = $B.to_arr(sp2)
                                    val @(fz_sp2, bv_sp2) = $A.freeze<byte>(sa2)
                                    (* sats *)
                                    val ss2 = $B.create()
                                    val () = $B.bput(ss2, "build/bats_modules/")
                                    val () = copy_to_builder(ns_bv, 0, ns_len, 256, ss2, $AR.checked_nat(ns_len + 1))
                                    val () = $B.bput(ss2, "/")
                                    val () = copy_to_builder(bv_se, 0, sel, 256, ss2, $AR.checked_nat(sel + 1))
                                    val () = $B.bput(ss2, "/src/lib.sats")
                                    val () = $B.put_byte(ss2, 0)
                                    val @(ssa2, _) = $B.to_arr(ss2)
                                    val @(fz_ss2, bv_ss2) = $A.freeze<byte>(ssa2)
                                    (* dats *)
                                    val sd2 = $B.create()
                                    val () = $B.bput(sd2, "build/bats_modules/")
                                    val () = copy_to_builder(ns_bv, 0, ns_len, 256, sd2, $AR.checked_nat(ns_len + 1))
                                    val () = $B.bput(sd2, "/")
                                    val () = copy_to_builder(bv_se, 0, sel, 256, sd2, $AR.checked_nat(sel + 1))
                                    val () = $B.bput(sd2, "/src/lib.dats")
                                    val () = $B.put_byte(sd2, 0)
                                    val @(sda2, _) = $B.to_arr(sd2)
                                    val @(fz_sd2, bv_sd2) = $A.freeze<byte>(sda2)
                                    val pr2 = preprocess_one(bv_sp2, bv_ss2, bv_sd2, 0, 1)
                                    val () = (if pr2 <> 0 then let
                                      val () = print! ("warning: preprocess failed for dep ")
                                      val () = print_borrow(ns_bv, 0, ns_len, 256, $AR.checked_nat(ns_len + 1))
                                      val () = print! ("/")
                                      val () = print_borrow(bv_se, 0, sel, 256, $AR.checked_nat(sel + 1))
                                    in print_newline() end
                                    else if ~is_quiet() then let
                                      val () = print! ("  preprocessed dep: ")
                                      val () = print_borrow(ns_bv, 0, ns_len, 256, $AR.checked_nat(ns_len + 1))
                                      val () = print! ("/")
                                      val () = print_borrow(bv_se, 0, sel, 256, $AR.checked_nat(sel + 1))
                                    in print_newline() end
                                    else ())
                                    val () = $A.drop<byte>(fz_sp2, bv_sp2)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_sp2))
                                    val () = $A.drop<byte>(fz_ss2, bv_ss2)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_ss2))
                                    val () = $A.drop<byte>(fz_sd2, bv_sd2)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_sd2))
                                    (* Scan extra .bats shared modules for this namespaced dep *)
                                    val nsd_src = $B.create()
                                    val () = $B.bput(nsd_src, "bats_modules/")
                                    val () = copy_to_builder(ns_bv, 0, ns_len, 256, nsd_src, $AR.checked_nat(ns_len + 1))
                                    val () = $B.bput(nsd_src, "/")
                                    val () = copy_to_builder(bv_se, 0, sel, 256, nsd_src, $AR.checked_nat(sel + 1))
                                    val () = $B.bput(nsd_src, "/src")
                                    val () = $B.put_byte(nsd_src, 0)
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
                                                    val sp_ns = $B.create()
                                                    val () = $B.bput(sp_ns, "bats_modules/")
                                                    val () = copy_to_builder(ns_bv2, 0, ns_len2, 256, sp_ns, $AR.checked_nat(ns_len2 + 1))
                                                    val () = $B.bput(sp_ns, "/")
                                                    val () = copy_to_builder(se_bv2, 0, se_len2, 256, sp_ns, $AR.checked_nat(se_len2 + 1))
                                                    val () = $B.bput(sp_ns, "/src/")
                                                    val () = copy_to_builder(bv_ens, 0, elen_ns, 256, sp_ns, $AR.checked_nat(elen_ns + 1))
                                                    val () = $B.put_byte(sp_ns, 0)
                                                    val @(spa_ns, _) = $B.to_arr(sp_ns)
                                                    val @(fz_spn, bv_spn) = $A.freeze<byte>(spa_ns)
                                                    val ss_ns = $B.create()
                                                    val () = $B.bput(ss_ns, "build/bats_modules/")
                                                    val () = copy_to_builder(ns_bv2, 0, ns_len2, 256, ss_ns, $AR.checked_nat(ns_len2 + 1))
                                                    val () = $B.bput(ss_ns, "/")
                                                    val () = copy_to_builder(se_bv2, 0, se_len2, 256, ss_ns, $AR.checked_nat(se_len2 + 1))
                                                    val () = $B.bput(ss_ns, "/src/")
                                                    val () = copy_to_builder(bv_ens, 0, stem_ns, 256, ss_ns, $AR.checked_nat(stem_ns + 1))
                                                    val () = $B.bput(ss_ns, ".sats")
                                                    val () = $B.put_byte(ss_ns, 0)
                                                    val @(ssa_ns, _) = $B.to_arr(ss_ns)
                                                    val @(fz_ssn, bv_ssn) = $A.freeze<byte>(ssa_ns)
                                                    val sd_ns = $B.create()
                                                    val () = $B.bput(sd_ns, "build/bats_modules/")
                                                    val () = copy_to_builder(ns_bv2, 0, ns_len2, 256, sd_ns, $AR.checked_nat(ns_len2 + 1))
                                                    val () = $B.bput(sd_ns, "/")
                                                    val () = copy_to_builder(se_bv2, 0, se_len2, 256, sd_ns, $AR.checked_nat(se_len2 + 1))
                                                    val () = $B.bput(sd_ns, "/src/")
                                                    val () = copy_to_builder(bv_ens, 0, stem_ns, 256, sd_ns, $AR.checked_nat(stem_ns + 1))
                                                    val () = $B.bput(sd_ns, ".dats")
                                                    val () = $B.put_byte(sd_ns, 0)
                                                    val @(sda_ns, _) = $B.to_arr(sd_ns)
                                                    val @(fz_sdn, bv_sdn) = $A.freeze<byte>(sda_ns)
                                                    val pr_ns = preprocess_one(bv_spn, bv_ssn, bv_sdn, 0, 1)
                                                    val () = (if pr_ns <> 0 then ()
                                                    else if ~is_quiet() then let
                                                      val () = print! ("  preprocessed dep extra: ")
                                                      val () = print_borrow(bv_ens, 0, elen_ns, 256, $AR.checked_nat(elen_ns + 1))
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
                                    (* Append staload for shared modules to dep lib.dats *)
                                    val dats_path = $B.create()
                                    val () = $B.bput(dats_path, "build/bats_modules/")
                                    val () = copy_to_builder(ns_bv, 0, ns_len, 256, dats_path, $AR.checked_nat(ns_len + 1))
                                    val () = $B.bput(dats_path, "/")
                                    val () = copy_to_builder(bv_se, 0, sel, 256, dats_path, $AR.checked_nat(sel + 1))
                                    val () = $B.bput(dats_path, "/src")
                                    val () = $B.put_byte(dats_path, 0)
                                    val @(dp_a, _) = $B.to_arr(dats_path)
                                    val @(fz_dp, bv_dp) = $A.freeze<byte>(dp_a)
                                    val sd_dir = $F.dir_open(bv_dp, 524288)
                                    val () = $A.drop<byte>(fz_dp, bv_dp)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_dp))
                                    val staload_b = $B.create()
                                    val () = (case+ sd_dir of
                                      | ~$R.ok(sd_d) => let
                                          fun find_shared_dats {fuel_sd:nat} .<fuel_sd>.
                                            (sd_d: !$F.dir, sb: !$B.builder, fuel_sd: int fuel_sd): void =
                                            if fuel_sd <= 0 then ()
                                            else let
                                              val se2 = $A.alloc<byte>(256)
                                              val snr = $F.dir_next(sd_d, se2, 256)
                                              val sl2 = $R.option_unwrap_or<int>(snr, ~1)
                                            in
                                              if sl2 < 0 then $A.free<byte>(se2)
                                              else let
                                                val is_d = has_dats_ext(se2, sl2, 256)
                                                val is_l = is_lib_dats(se2, sl2, 256)
                                              in
                                                if is_d then
                                                  if is_l then let
                                                    val () = $A.free<byte>(se2)
                                                  in find_shared_dats(sd_d, sb, fuel_sd - 1) end
                                                  else let
                                                    val @(fz_se2, bv_se2) = $A.freeze<byte>(se2)
                                                    val () = $B.bput(sb, "staload \"src/")
                                                    val () = copy_to_builder(bv_se2, 0, sl2, 256, sb, $AR.checked_nat(sl2 + 1))
                                                    val () = $B.bput(sb, "\"\n")
                                                    val () = $A.drop<byte>(fz_se2, bv_se2)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_se2))
                                                  in find_shared_dats(sd_d, sb, fuel_sd - 1) end
                                                else let
                                                  val () = $A.free<byte>(se2)
                                                in find_shared_dats(sd_d, sb, fuel_sd - 1) end
                                              end
                                            end
                                        in
                                          find_shared_dats(sd_d, staload_b, 100);
                                          (let val dcr2 = $F.dir_close(sd_d) val () = $R.discard<int><int>(dcr2) in end)
                                        end
                                      | ~$R.err(_) => ())
                                    (* Write staload lines to dep lib.dats *)
                                    val @(sl_a, sl_len) = $B.to_arr(staload_b)
                                    val () = (if sl_len > 0 then let
                                      val lib_dats = $B.create()
                                      val () = $B.bput(lib_dats, "build/bats_modules/")
                                      val () = copy_to_builder(ns_bv, 0, ns_len, 256, lib_dats, $AR.checked_nat(ns_len + 1))
                                      val () = $B.bput(lib_dats, "/")
                                      val () = copy_to_builder(bv_se, 0, sel, 256, lib_dats, $AR.checked_nat(sel + 1))
                                      val () = $B.bput(lib_dats, "/src/lib.dats")
                                      val () = $B.put_byte(lib_dats, 0)
                                      val @(ld_a, ld_len) = $B.to_arr(lib_dats)
                                      val @(fz_ld, bv_ld) = $A.freeze<byte>(ld_a)
                                      (* Open lib.dats for append (flags: O_WRONLY|O_APPEND = 1025) *)
                                      val fr = $F.file_open(bv_ld, 524288, 1025, 420)
                                      val () = (case+ fr of
                                        | ~$R.ok(fd) => let
                                            val @(fz_sl, bv_sl) = $A.freeze<byte>(sl_a)
                                            val wr = $F.file_write(fd, bv_sl, 524288)
                                            val () = $R.discard<int><int>(wr)
                                            val cr = $F.file_close(fd)
                                            val () = $R.discard<int><int>(cr)
                                            val () = $A.drop<byte>(fz_sl, bv_sl)
                                            val () = $A.free<byte>($A.thaw<byte>(fz_sl))
                                          in end
                                        | ~$R.err(_) => $A.free<byte>(sl_a))
                                      val () = $A.drop<byte>(fz_ld, bv_ld)
                                      val () = $A.free<byte>($A.thaw<byte>(fz_ld))
                                    in end
                                    else $A.free<byte>(sl_a))
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
                    val mc = $B.create()
                    val () = $B.bput(mc, "build/bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, mc,
                      $AR.checked_nat(elen + 1))
                    val () = $B.bput(mc, "/src")
                    val _ = run_mkdir(mc)
                    (* source: bats_modules/<name>/src/lib.bats *)
                    val sp = $B.create()
                    val () = $B.bput(sp, "bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, sp,
                      $AR.checked_nat(elen + 1))
                    val () = $B.bput(sp, "/src/lib.bats")
                    val () = $B.put_byte(sp, 0)
                    val @(sa, _) = $B.to_arr(sp)
                    val @(fz_sp, bv_sp) = $A.freeze<byte>(sa)
                    (* sats: build/bats_modules/<name>/src/lib.sats *)
                    val ss = $B.create()
                    val () = $B.bput(ss, "build/bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, ss,
                      $AR.checked_nat(elen + 1))
                    val () = $B.bput(ss, "/src/lib.sats")
                    val () = $B.put_byte(ss, 0)
                    val @(ssa, _) = $B.to_arr(ss)
                    val @(fz_ss, bv_ss) = $A.freeze<byte>(ssa)
                    (* dats: build/bats_modules/<name>/src/lib.dats *)
                    val sd = $B.create()
                    val () = $B.bput(sd, "build/bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, sd,
                      $AR.checked_nat(elen + 1))
                    val () = $B.bput(sd, "/src/lib.dats")
                    val () = $B.put_byte(sd, 0)
                    val @(sda, _) = $B.to_arr(sd)
                    val @(fz_sd, bv_sd) = $A.freeze<byte>(sda)
                    val pr = preprocess_one(bv_sp, bv_ss, bv_sd, 0, 1)
                    val () = (if pr <> 0 then let
                      val () = print! ("warning: preprocess failed for dep ")
                      val () = print_borrow(bv_e, 0, elen, 256, $AR.checked_nat(elen + 1))
                    in print_newline() end
                    else if ~is_quiet() then let
                      val () = print! ("  preprocessed dep: ")
                      val () = print_borrow(bv_e, 0, elen, 256, $AR.checked_nat(elen + 1))
                    in print_newline() end
                    else ())
                    (* Scan additional .bats files in this dep *)
                    val dep_src_b = $B.create()
                    val () = $B.bput(dep_src_b, "bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, dep_src_b,
                      $AR.checked_nat(elen + 1))
                    val () = $B.bput(dep_src_b, "/src")
                    val () = $B.put_byte(dep_src_b, 0)
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
                                    val sp_ex = $B.create()
                                    val () = $B.bput(sp_ex, "bats_modules/")
                                    val () = copy_to_builder(dep_bv, 0, dep_len, 256, sp_ex,
                                      $AR.checked_nat(dep_len + 1))
                                    val () = $B.bput(sp_ex, "/src/")
                                    val () = copy_to_builder(bv_ex, 0, elen_ex, 256, sp_ex,
                                      $AR.checked_nat(elen_ex + 1))
                                    val () = $B.put_byte(sp_ex, 0)
                                    val @(spa_ex, _) = $B.to_arr(sp_ex)
                                    val @(fz_spa, bv_spa) = $A.freeze<byte>(spa_ex)
                                    val ss_ex = $B.create()
                                    val () = $B.bput(ss_ex, "build/bats_modules/")
                                    val () = copy_to_builder(dep_bv, 0, dep_len, 256, ss_ex,
                                      $AR.checked_nat(dep_len + 1))
                                    val () = $B.bput(ss_ex, "/src/")
                                    val () = copy_to_builder(bv_ex, 0, stem_ex, 256, ss_ex,
                                      $AR.checked_nat(stem_ex + 1))
                                    val () = $B.bput(ss_ex, ".sats")
                                    val () = $B.put_byte(ss_ex, 0)
                                    val @(ssa_ex, _) = $B.to_arr(ss_ex)
                                    val @(fz_ssa, bv_ssa) = $A.freeze<byte>(ssa_ex)
                                    val sd_ex = $B.create()
                                    val () = $B.bput(sd_ex, "build/bats_modules/")
                                    val () = copy_to_builder(dep_bv, 0, dep_len, 256, sd_ex,
                                      $AR.checked_nat(dep_len + 1))
                                    val () = $B.bput(sd_ex, "/src/")
                                    val () = copy_to_builder(bv_ex, 0, stem_ex, 256, sd_ex,
                                      $AR.checked_nat(stem_ex + 1))
                                    val () = $B.bput(sd_ex, ".dats")
                                    val () = $B.put_byte(sd_ex, 0)
                                    val @(sda_ex, _) = $B.to_arr(sd_ex)
                                    val @(fz_sda, bv_sda) = $A.freeze<byte>(sda_ex)
                                    val pr_ex = preprocess_one(bv_spa, bv_ssa, bv_sda, 0, 1)
                                    val () = (if pr_ex <> 0 then let
                                      val () = print! ("warning: preprocess failed for extra file in dep ")
                                      val () = print_borrow(dep_bv, 0, dep_len, 256,
                                        $AR.checked_nat(dep_len + 1))
                                    in print_newline() end
                                    else if ~is_quiet() then let
                                      val () = print! ("  preprocessed dep extra: ")
                                      val () = print_borrow(bv_ex, 0, elen_ex, 256,
                                        $AR.checked_nat(elen_ex + 1))
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
                    val sp_sm = $B.create()
                    val () = $B.bput(sp_sm, "src/")
                    val () = copy_to_builder(bv_esm, 0, elen_sm, 256, sp_sm,
                      $AR.checked_nat(elen_sm + 1))
                    val () = $B.put_byte(sp_sm, 0)
                    val @(spa_sm, _) = $B.to_arr(sp_sm)
                    val @(fz_spa_sm, bv_spa_sm) = $A.freeze<byte>(spa_sm)
                    (* sats: build/src/<stem>.sats *)
                    val ss_sm = $B.create()
                    val () = $B.bput(ss_sm, "build/src/")
                    val () = copy_to_builder(bv_esm, 0, stem_sm, 256, ss_sm,
                      $AR.checked_nat(stem_sm + 1))
                    val () = $B.bput(ss_sm, ".sats")
                    val () = $B.put_byte(ss_sm, 0)
                    val @(ssa_sm, _) = $B.to_arr(ss_sm)
                    val @(fz_ssa_sm, bv_ssa_sm) = $A.freeze<byte>(ssa_sm)
                    (* dats: build/src/<stem>.dats *)
                    val sd_sm = $B.create()
                    val () = $B.bput(sd_sm, "build/src/")
                    val () = copy_to_builder(bv_esm, 0, stem_sm, 256, sd_sm,
                      $AR.checked_nat(stem_sm + 1))
                    val () = $B.bput(sd_sm, ".dats")
                    val () = $B.put_byte(sd_sm, 0)
                    val @(sda_sm, _) = $B.to_arr(sd_sm)
                    val @(fz_sda_sm, bv_sda_sm) = $A.freeze<byte>(sda_sm)
                    val pr_sm = preprocess_one(bv_spa_sm, bv_ssa_sm, bv_sda_sm, 0, is_unsafe)
                    val () = (if pr_sm <> 0 then let
                      val () = print! ("warning: preprocess failed for src/")
                      val () = print_borrow(bv_esm, 0, elen_sm, 256,
                        $AR.checked_nat(elen_sm + 1))
                    in print_newline() end
                    else if ~is_quiet() then let
                      val () = print! ("  preprocessed: src/")
                      val () = print_borrow(bv_esm, 0, elen_sm, 256,
                        $AR.checked_nat(elen_sm + 1))
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
                    val () = $B.bput(sp, "src/bin/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, sp,
                      $AR.checked_nat(elen + 1))
                    val () = $B.put_byte(sp, 0)
                    val @(sa, _) = $B.to_arr(sp)
                    val @(fz_sp, bv_sp) = $A.freeze<byte>(sa)
                    (* sats: build/src/bin/<name>.sats *)
                    val ss = $B.create()
                    val () = $B.bput(ss, "build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, ss,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(ss, ".sats")
                    val () = $B.put_byte(ss, 0)
                    val @(ssa, _) = $B.to_arr(ss)
                    val @(fz_ss, bv_ss) = $A.freeze<byte>(ssa)
                    (* dats: build/src/bin/<name>.dats *)
                    val sd = $B.create()
                    val () = $B.bput(sd, "build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, sd,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(sd, ".dats")
                    val () = $B.put_byte(sd, 0)
                    val @(sda, _) = $B.to_arr(sd)
                    val @(fz_sd, bv_sd) = $A.freeze<byte>(sda)
                    val pr = preprocess_one(bv_sp, bv_ss, bv_sd, 0, is_unsafe)
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
                    val () = $B.bput(entry, "staload \"./src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, entry,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(entry, ".sats\"\n")
                    (* dynload all dep modules *)
                    val bm2_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm2, bv_bm2) = $A.freeze<byte>(bm2_arr)
                    val bdir2 = $F.dir_open(bv_bm2, 524288)
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
                                  (* Skip namespace dirs *)
                                  val pk_b2 = $B.create()
                                  val () = $B.bput(pk_b2, "bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pk_b2, $AR.checked_nat(dlen+1))
                                  val () = $B.bput(pk_b2, "/bats.toml")
                                  val () = $B.put_byte(pk_b2, 0)
                                  val @(pka2, _) = $B.to_arr(pk_b2)
                                  val @(fz_pk2, bv_pk2) = $A.freeze<byte>(pka2)
                                  val pk_r2 = $F.file_mtime(bv_pk2, 524288)
                                  val is_p2 = (case+ pk_r2 of | ~$R.ok(_) => true | ~$R.err(_) => false): bool
                                  val () = $A.drop<byte>(fz_pk2, bv_pk2)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_pk2))
                                in
                                  if ~is_p2 then let
                                    (* Namespace dir — iterate subdirs for dynloads *)
                                    val ns_dd = $B.create()
                                    val () = $B.bput(ns_dd, "bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ns_dd, $AR.checked_nat(dlen+1))
                                    val () = $B.put_byte(ns_dd, 0)
                                    val @(ns_dda, _) = $B.to_arr(ns_dd)
                                    val @(fz_nsdd, bv_nsdd) = $A.freeze<byte>(ns_dda)
                                    val ns_dr = $F.dir_open(bv_nsdd, 524288)
                                    val () = $A.drop<byte>(fz_nsdd, bv_nsdd)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_nsdd))
                                    val () = (case+ ns_dr of
                                      | ~$R.ok(nsdd) => let
                                          fun dynload_ns {lns5:agz}{fuel_dn:nat} .<fuel_dn>.
                                            (nsdd: !$F.dir, eb2: !$B.builder,
                                             ns5: !$A.borrow(byte, lns5, 256), ns5len: int,
                                             fuel_dn: int fuel_dn): void =
                                            if fuel_dn <= 0 then ()
                                            else let
                                              val sde = $A.alloc<byte>(256)
                                              val snr = $F.dir_next(nsdd, sde, 256)
                                              val sel = $R.option_unwrap_or<int>(snr, ~1)
                                            in if sel < 0 then $A.free<byte>(sde)
                                              else let val sdd = is_dot_or_dotdot(sde, sel, 256) in
                                                if sdd then let val () = $A.free<byte>(sde)
                                                in dynload_ns(nsdd, eb2, ns5, ns5len, fuel_dn-1) end
                                                else let
                                                  val @(fz_sde, bv_sde) = $A.freeze<byte>(sde)
                                                  val () = $B.bput(eb2, "dynload \"./bats_modules/")
                                                  val () = copy_to_builder(ns5, 0, ns5len, 256, eb2, $AR.checked_nat(ns5len+1))
                                                  val () = $B.bput(eb2, "/")
                                                  val () = copy_to_builder(bv_sde, 0, sel, 256, eb2, $AR.checked_nat(sel+1))
                                                  val () = $B.bput(eb2, "/src/lib.dats\"\n")
                                                  val () = $A.drop<byte>(fz_sde, bv_sde)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_sde))
                                                in dynload_ns(nsdd, eb2, ns5, ns5len, fuel_dn-1) end
                                              end
                                            end
                                          val () = dynload_ns(nsdd, eb, bv_de, dlen, 100)
                                          val dcr_dn = $F.dir_close(nsdd)
                                          val () = $R.discard<int><int>(dcr_dn)
                                        in end
                                      | ~$R.err(_) => ())
                                    val () = $A.drop<byte>(fz_de, bv_de)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                  in add_dynloads(dd, eb, fuel2 - 1) end
                                  else let
                                  val () = $B.bput(eb, "dynload \"./bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256,
                                    eb, $AR.checked_nat(dlen + 1))
                                  val () = $B.bput(eb, "/src/lib.dats\"\n")
                                  (* dynload extra .dats files for this dep *)
                                  val dyn_src_b = $B.create()
                                  val () = $B.bput(dyn_src_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, dyn_src_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = $B.bput(dyn_src_b, "/src")
                                  val () = $B.put_byte(dyn_src_b, 0)
                                  val @(dyn_sa, _) = $B.to_arr(dyn_src_b)
                                  val @(fz_ds, bv_ds) = $A.freeze<byte>(dyn_sa)
                                  val dyn_dir = $F.dir_open(bv_ds, 524288)
                                  val () = $A.drop<byte>(fz_ds, bv_ds)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_ds))
                                  val () = (case+ dyn_dir of
                                    | ~$R.ok(d_dyn) => let
                                        fun add_extra_dynloads
                                          {ld2:agz}{fuel_d:nat} .<fuel_d>.
                                          (d_dyn: !$F.dir, eb2: !$B.builder,
                                           dep2: !$A.borrow(byte, ld2, 256),
                                           dep2_len: int,
                                           fuel_d: int fuel_d): void =
                                          if fuel_d <= 0 then ()
                                          else let
                                            val de2 = $A.alloc<byte>(256)
                                            val nr2 = $F.dir_next(d_dyn, de2, 256)
                                            val dl2 = $R.option_unwrap_or<int>(nr2, ~1)
                                          in
                                            if dl2 < 0 then $A.free<byte>(de2)
                                            else let
                                              val is_d = has_dats_ext(de2, dl2, 256)
                                              val is_l = is_lib_dats(de2, dl2, 256)
                                            in
                                              if is_d then
                                                if is_l then let
                                                  val () = $A.free<byte>(de2)
                                                in add_extra_dynloads(d_dyn, eb2, dep2, dep2_len, fuel_d - 1) end
                                                else let
                                                  val @(fz_d2, bv_d2) = $A.freeze<byte>(de2)
                                                  val () = $B.bput(eb2, "dynload \"./bats_modules/")
                                                  val () = copy_to_builder(dep2, 0, dep2_len, 256,
                                                    eb2, $AR.checked_nat(dep2_len + 1))
                                                  val () = $B.bput(eb2, "/src/")
                                                  val () = copy_to_builder(bv_d2, 0, dl2, 256,
                                                    eb2, $AR.checked_nat(dl2 + 1))
                                                  val () = $B.bput(eb2, "\"\n")
                                                  val () = $A.drop<byte>(fz_d2, bv_d2)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_d2))
                                                in add_extra_dynloads(d_dyn, eb2, dep2, dep2_len, fuel_d - 1) end
                                              else let
                                                val () = $A.free<byte>(de2)
                                              in add_extra_dynloads(d_dyn, eb2, dep2, dep2_len, fuel_d - 1) end
                                            end
                                          end
                                        val () = add_extra_dynloads(d_dyn, eb, bv_de, dlen, 200)
                                        val dcr_dyn = $F.dir_close(d_dyn)
                                        val () = $R.discard<int><int>(dcr_dyn)
                                      in end
                                    | ~$R.err(_) => ())
                                  val () = $A.drop<byte>(fz_de, bv_de)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                in add_dynloads(dd, eb, fuel2 - 1) end
                                  end (* if ~is_p2 *)
                              end
                            end
                          val () = add_dynloads(dd, entry, 200)
                          val dcr2 = $F.dir_close(dd)
                          val () = $R.discard<int><int>(dcr2)
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
                            (d_dsm: !$F.dir, eb: !$B.builder,
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
                                  val () = $B.bput(eb, "dynload \"./src/")
                                  val () = copy_to_builder(bv_dsme, 0, dl_sm, 256,
                                    eb, $AR.checked_nat(dl_sm + 1))
                                  val () = $B.bput(eb, "\"\n")
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
                    val () = $B.bput(entry, "dynload \"./src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, entry,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(entry, ".dats\"\n")
                    val () = $B.bput(entry, "implement ")
                    val () = $B.bput(entry, "main0 () = __BATS_main0 ()\n")
                    (* Write synthetic entry *)
                    val ep = $B.create()
                    val () = $B.bput(ep, "build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, ep,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(ep, ".dats")
                    val () = $B.put_byte(ep, 0)
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
                                  val pk_b = $B.create()
                                  val () = $B.bput(pk_b, "bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pk_b, $AR.checked_nat(dlen+1))
                                  val () = $B.bput(pk_b, "/bats.toml")
                                  val () = $B.put_byte(pk_b, 0)
                                  val @(pka, _) = $B.to_arr(pk_b)
                                  val @(fz_pk, bv_pk) = $A.freeze<byte>(pka)
                                  val pk_r = $F.file_mtime(bv_pk, 524288)
                                  val is_p = (case+ pk_r of | ~$R.ok(_) => true | ~$R.err(_) => false): bool
                                  val () = $A.drop<byte>(fz_pk, bv_pk)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_pk))
                                in
                                  if ~is_p then let
                                    (* Namespace dir — iterate subdirs *)
                                    val ns_d = $B.create()
                                    val () = $B.bput(ns_d, "bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ns_d, $AR.checked_nat(dlen+1))
                                    val () = $B.put_byte(ns_d, 0)
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
                                                  val po = $B.create()
                                                  val () = $B.bput(po, "build/bats_modules/")
                                                  val () = copy_to_builder(ns_name, 0, ns_len, 256, po, $AR.checked_nat(ns_len+1))
                                                  val () = $B.bput(po, "/")
                                                  val () = copy_to_builder(bv_sde, 0, sel, 256, po, $AR.checked_nat(sel+1))
                                                  val () = $B.bput(po, "/src/lib_dats.c")
                                                  val () = $B.put_byte(po, 0)
                                                  val @(poa, po_len) = $B.to_arr(po)
                                                  val @(fz_po, bv_po) = $A.freeze<byte>(poa)
                                                  val pi = $B.create()
                                                  val () = $B.bput(pi, "build/bats_modules/")
                                                  val () = copy_to_builder(ns_name, 0, ns_len, 256, pi, $AR.checked_nat(ns_len+1))
                                                  val () = $B.bput(pi, "/")
                                                  val () = copy_to_builder(bv_sde, 0, sel, 256, pi, $AR.checked_nat(sel+1))
                                                  val () = $B.bput(pi, "/src/lib.dats")
                                                  val () = $B.put_byte(pi, 0)
                                                  val @(pia, pi_len) = $B.to_arr(pi)
                                                  val @(fz_pi, bv_pi) = $A.freeze<byte>(pia)
                                                  val rc_ns = run_patsopt(ph2, ph2len, bv_po, po_len, bv_pi, pi_len)
                                                  val () = $A.drop<byte>(fz_po, bv_po)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_po))
                                                  val () = $A.drop<byte>(fz_pi, bv_pi)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_pi))
                                                  val () = (if rc_ns <> 0 then let
                                                    val () = print! ("error: patsopt failed for dep ")
                                                    val () = print_borrow(ns_name, 0, ns_len, 256, $AR.checked_nat(ns_len+1))
                                                    val () = print! ("/")
                                                    val () = print_borrow(bv_sde, 0, sel, 256, $AR.checked_nat(sel+1))
                                                  in print_newline() end
                                                  else if ~is_quiet() then let
                                                    val () = print! ("  patsopt: ")
                                                    val () = print_borrow(ns_name, 0, ns_len, 256, $AR.checked_nat(ns_len+1))
                                                    val () = print! ("/")
                                                    val () = print_borrow(bv_sde, 0, sel, 256, $AR.checked_nat(sel+1))
                                                  in print_newline() end
                                                  else ())
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
                                    val ob = $B.create()
                                    val () = $B.bput(ob, "build/bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ob, $AR.checked_nat(dlen+1))
                                    val () = $B.bput(ob, "/src/lib_dats.c")
                                    val () = $B.put_byte(ob, 0)
                                    val ib = $B.create()
                                    val () = $B.bput(ib, "build/bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ib, $AR.checked_nat(dlen+1))
                                    val () = $B.bput(ib, "/src/lib.dats")
                                    val () = $B.put_byte(ib, 0)
                                  in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                                  val () = (if pats_fresh > 0 then ()
                                  else let
                                  val po_b = $B.create()
                                  val () = $B.bput(po_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, po_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = $B.bput(po_b, "/src/lib_dats.c")
                                  val () = $B.put_byte(po_b, 0)
                                  val @(po_a, po_len) = $B.to_arr(po_b)
                                  val @(fz_po, bv_po) = $A.freeze<byte>(po_a)
                                  val pi_b = $B.create()
                                  val () = $B.bput(pi_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pi_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = $B.bput(pi_b, "/src/lib.dats")
                                  val () = $B.put_byte(pi_b, 0)
                                  val @(pi_a, pi_len) = $B.to_arr(pi_b)
                                  val @(fz_pi, bv_pi) = $A.freeze<byte>(pi_a)
                                  val rc = run_patsopt(ph, phlen, bv_po, po_len, bv_pi, pi_len)
                                  val () = $A.drop<byte>(fz_po, bv_po)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_po))
                                  val () = $A.drop<byte>(fz_pi, bv_pi)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_pi))
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
                                  (* patsopt extra .dats files for this dep *)
                                  val pats_src_b = $B.create()
                                  val () = $B.bput(pats_src_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pats_src_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = $B.bput(pats_src_b, "/src")
                                  val () = $B.put_byte(pats_src_b, 0)
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
                                                    val fo = $B.create()
                                                    val () = $B.bput(fo, "build/bats_modules/")
                                                    val () = copy_to_builder(dep3, 0, dep3_len, 256, fo, $AR.checked_nat(dep3_len+1))
                                                    val () = $B.bput(fo, "/src/")
                                                    val () = copy_to_builder(bv_d3, 0, stem3, 256, fo, $AR.checked_nat(stem3+1))
                                                    val () = $B.bput(fo, "_dats.c")
                                                    val () = $B.put_byte(fo, 0)
                                                    val fi = $B.create()
                                                    val () = $B.bput(fi, "build/bats_modules/")
                                                    val () = copy_to_builder(dep3, 0, dep3_len, 256, fi, $AR.checked_nat(dep3_len+1))
                                                    val () = $B.bput(fi, "/src/")
                                                    val () = copy_to_builder(bv_d3, 0, dl3, 256, fi, $AR.checked_nat(dl3+1))
                                                    val () = $B.put_byte(fi, 0)
                                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                                  val () = (if pf > 0 then ()
                                                  else let
                                                    val eo = $B.create()
                                                    val () = $B.bput(eo, "build/bats_modules/")
                                                    val () = copy_to_builder(dep3, 0, dep3_len, 256, eo, $AR.checked_nat(dep3_len+1))
                                                    val () = $B.bput(eo, "/src/")
                                                    val () = copy_to_builder(bv_d3, 0, stem3, 256, eo, $AR.checked_nat(stem3+1))
                                                    val () = $B.bput(eo, "_dats.c")
                                                    val () = $B.put_byte(eo, 0)
                                                    val @(eoa, eo_len) = $B.to_arr(eo)
                                                    val @(fz_eo, bv_eo) = $A.freeze<byte>(eoa)
                                                    val ei = $B.create()
                                                    val () = $B.bput(ei, "build/bats_modules/")
                                                    val () = copy_to_builder(dep3, 0, dep3_len, 256, ei, $AR.checked_nat(dep3_len+1))
                                                    val () = $B.bput(ei, "/src/")
                                                    val () = copy_to_builder(bv_d3, 0, dl3, 256, ei, $AR.checked_nat(dl3+1))
                                                    val () = $B.put_byte(ei, 0)
                                                    val @(eia, ei_len) = $B.to_arr(ei)
                                                    val @(fz_ei, bv_ei) = $A.freeze<byte>(eia)
                                                    val rc3 = run_patsopt(ph2, ph2len, bv_eo, eo_len, bv_ei, ei_len)
                                                    val () = $A.drop<byte>(fz_eo, bv_eo)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_eo))
                                                    val () = $A.drop<byte>(fz_ei, bv_ei)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_ei))
                                                  in (if rc3 <> 0 then let
                                                    val () = print! ("error: patsopt failed for extra ")
                                                    val () = print_borrow(bv_d3, 0, dl3, 256,
                                                      $AR.checked_nat(dl3 + 1))
                                                  in print_newline() end
                                                  else if ~is_quiet() then let
                                                    val () = print! ("  patsopt extra: ")
                                                    val () = print_borrow(bv_d3, 0, dl3, 256,
                                                      $AR.checked_nat(dl3 + 1))
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
                                    val fo = $B.create()
                                    val () = $B.bput(fo, "build/src/")
                                    val () = copy_to_builder(bv_dpsm, 0, stem_psm, 256, fo, $AR.checked_nat(stem_psm+1))
                                    val () = $B.bput(fo, "_dats.c")
                                    val () = $B.put_byte(fo, 0)
                                    val fi = $B.create()
                                    val () = $B.bput(fi, "build/src/")
                                    val () = copy_to_builder(bv_dpsm, 0, dl_psm, 256, fi, $AR.checked_nat(dl_psm+1))
                                    val () = $B.put_byte(fi, 0)
                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                  val () = (if pf_sm > 0 then ()
                                  else let
                                    val eo_sm = $B.create()
                                    val () = $B.bput(eo_sm, "build/src/")
                                    val () = copy_to_builder(bv_dpsm, 0, stem_psm, 256, eo_sm, $AR.checked_nat(stem_psm+1))
                                    val () = $B.bput(eo_sm, "_dats.c")
                                    val () = $B.put_byte(eo_sm, 0)
                                    val @(eoa_sm, eo_sm_len) = $B.to_arr(eo_sm)
                                    val @(fz_eosm, bv_eosm) = $A.freeze<byte>(eoa_sm)
                                    val ei_sm = $B.create()
                                    val () = $B.bput(ei_sm, "build/src/")
                                    val () = copy_to_builder(bv_dpsm, 0, dl_psm, 256, ei_sm, $AR.checked_nat(dl_psm+1))
                                    val () = $B.put_byte(ei_sm, 0)
                                    val @(eia_sm, ei_sm_len) = $B.to_arr(ei_sm)
                                    val @(fz_eism, bv_eism) = $A.freeze<byte>(eia_sm)
                                    val rc_sm = run_patsopt(ph_sm, ph_sm_len, bv_eosm, eo_sm_len, bv_eism, ei_sm_len)
                                    val () = $A.drop<byte>(fz_eosm, bv_eosm)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_eosm))
                                    val () = $A.drop<byte>(fz_eism, bv_eism)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_eism))
                                  in (if rc_sm <> 0 then let
                                    val () = print! ("error: patsopt failed for src module ")
                                    val () = print_borrow(bv_dpsm, 0, dl_psm, 256,
                                      $AR.checked_nat(dl_psm + 1))
                                  in print_newline() end
                                  else if ~is_quiet() then let
                                    val () = print! ("  patsopt: src/")
                                    val () = print_borrow(bv_dpsm, 0, dl_psm, 256,
                                      $AR.checked_nat(dl_psm + 1))
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
                      val ob = $B.create()
                      val () = $B.bput(ob, "build/src/bin/")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ob, $AR.checked_nat(stem_len+1))
                      val () = $B.bput(ob, "_dats.c")
                      val () = $B.put_byte(ob, 0)
                      val ib = $B.create()
                      val () = $B.bput(ib, "build/src/bin/")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ib, $AR.checked_nat(stem_len+1))
                      val () = $B.bput(ib, ".dats")
                      val () = $B.put_byte(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if bin_pats_fresh > 0 then ()
                    else let
                    val po_b = $B.create()
                    val () = $B.bput(po_b, "build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, po_b,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(po_b, "_dats.c")
                    val () = $B.put_byte(po_b, 0)
                    val @(po_a, po_len) = $B.to_arr(po_b)
                    val @(fz_po, bv_po) = $A.freeze<byte>(po_a)
                    val pi_b = $B.create()
                    val () = $B.bput(pi_b, "build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, pi_b,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(pi_b, ".dats")
                    val () = $B.put_byte(pi_b, 0)
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
                      val ob = $B.create()
                      val () = $B.bput(ob, "build/_bats_entry_")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ob, $AR.checked_nat(stem_len+1))
                      val () = $B.bput(ob, "_dats.c")
                      val () = $B.put_byte(ob, 0)
                      val ib = $B.create()
                      val () = $B.bput(ib, "build/_bats_entry_")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ib, $AR.checked_nat(stem_len+1))
                      val () = $B.bput(ib, ".dats")
                      val () = $B.put_byte(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if ent_pats_fresh > 0 then ()
                    else let
                    val eo_b = $B.create()
                    val () = $B.bput(eo_b, "build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, eo_b,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(eo_b, "_dats.c")
                    val () = $B.put_byte(eo_b, 0)
                    val @(eo_a, eo_len) = $B.to_arr(eo_b)
                    val @(fz_eo, bv_eo) = $A.freeze<byte>(eo_a)
                    val ei_b = $B.create()
                    val () = $B.bput(ei_b, "build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, ei_b,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(ei_b, ".dats")
                    val () = $B.put_byte(ei_b, 0)
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
                                  val pk_b3 = $B.create()
                                  val () = $B.bput(pk_b3, "bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pk_b3, $AR.checked_nat(dlen+1))
                                  val () = $B.bput(pk_b3, "/bats.toml")
                                  val () = $B.put_byte(pk_b3, 0)
                                  val @(pka3, _) = $B.to_arr(pk_b3)
                                  val @(fz_pk3, bv_pk3) = $A.freeze<byte>(pka3)
                                  val pk_r3 = $F.file_mtime(bv_pk3, 524288)
                                  val is_p3 = (case+ pk_r3 of | ~$R.ok(_) => true | ~$R.err(_) => false): bool
                                  val () = $A.drop<byte>(fz_pk3, bv_pk3)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_pk3))
                                in
                                  if ~is_p3 then let
                                    (* Namespace dir — iterate subdirs for clang *)
                                    val ns_cd = $B.create()
                                    val () = $B.bput(ns_cd, "bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ns_cd, $AR.checked_nat(dlen+1))
                                    val () = $B.put_byte(ns_cd, 0)
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
                                                  val co = $B.create()
                                                  val () = $B.bput(co, "build/bats_modules/")
                                                  val () = copy_to_builder(ns3, 0, ns3len, 256, co, $AR.checked_nat(ns3len+1))
                                                  val () = $B.bput(co, "/")
                                                  val () = copy_to_builder(bv_sde, 0, sel, 256, co, $AR.checked_nat(sel+1))
                                                  val () = $B.bput(co, "/src/lib_dats.o")
                                                  val () = $B.put_byte(co, 0)
                                                  val @(coa, co_len) = $B.to_arr(co)
                                                  val @(fz_co, bv_co) = $A.freeze<byte>(coa)
                                                  val ci = $B.create()
                                                  val () = $B.bput(ci, "build/bats_modules/")
                                                  val () = copy_to_builder(ns3, 0, ns3len, 256, ci, $AR.checked_nat(ns3len+1))
                                                  val () = $B.bput(ci, "/")
                                                  val () = copy_to_builder(bv_sde, 0, sel, 256, ci, $AR.checked_nat(sel+1))
                                                  val () = $B.bput(ci, "/src/lib_dats.c")
                                                  val () = $B.put_byte(ci, 0)
                                                  val @(cia, ci_len) = $B.to_arr(ci)
                                                  val @(fz_ci, bv_ci) = $A.freeze<byte>(cia)
                                                  val _ = run_cc(ph3, ph3len, bv_co, co_len, bv_ci, ci_len, rr3)
                                                  val () = $A.drop<byte>(fz_co, bv_co)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_co))
                                                  val () = $A.drop<byte>(fz_ci, bv_ci)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_ci))
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
                                    val ob = $B.create()
                                    val () = $B.bput(ob, "build/bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ob, $AR.checked_nat(dlen+1))
                                    val () = $B.bput(ob, "/src/lib_dats.o")
                                    val () = $B.put_byte(ob, 0)
                                    val ib = $B.create()
                                    val () = $B.bput(ib, "build/bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ib, $AR.checked_nat(dlen+1))
                                    val () = $B.bput(ib, "/src/lib_dats.c")
                                    val () = $B.put_byte(ib, 0)
                                  in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                                  val () = (if cc_fresh > 0 then ()
                                  else let
                                  val co_b = $B.create()
                                  val () = $B.bput(co_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, co_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = $B.bput(co_b, "/src/lib_dats.o")
                                  val () = $B.put_byte(co_b, 0)
                                  val @(co_a, co_len) = $B.to_arr(co_b)
                                  val @(fz_co, bv_co) = $A.freeze<byte>(co_a)
                                  val ci_b = $B.create()
                                  val () = $B.bput(ci_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, ci_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = $B.bput(ci_b, "/src/lib_dats.c")
                                  val () = $B.put_byte(ci_b, 0)
                                  val @(ci_a, ci_len) = $B.to_arr(ci_b)
                                  val @(fz_ci, bv_ci) = $A.freeze<byte>(ci_a)
                                  val rc = run_cc(ph, phlen, bv_co, co_len, bv_ci, ci_len, rr)
                                  val () = $A.drop<byte>(fz_co, bv_co)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_co))
                                  val () = $A.drop<byte>(fz_ci, bv_ci)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_ci))
                                  in (if rc <> 0 then let
                                    val () = print! ("error: cc failed for dep ")
                                    val () = print_borrow(bv_de, 0, dlen, 256,
                                      $AR.checked_nat(dlen + 1))
                                  in print_newline() end else ()) end)
                                  (* compile extra _dats.c files for this dep *)
                                  val cc_src_b = $B.create()
                                  val () = $B.bput(cc_src_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, cc_src_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = $B.bput(cc_src_b, "/src")
                                  val () = $B.put_byte(cc_src_b, 0)
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
                                                    val fo = $B.create()
                                                    val () = $B.bput(fo, "build/bats_modules/")
                                                    val () = copy_to_builder(dep4, 0, dep4_len, 256, fo, $AR.checked_nat(dep4_len+1))
                                                    val () = $B.bput(fo, "/src/")
                                                    val () = copy_to_builder(bv_d4, 0, stem4, 256, fo, $AR.checked_nat(stem4+1))
                                                    val () = $B.bput(fo, "_dats.o")
                                                    val () = $B.put_byte(fo, 0)
                                                    val fi = $B.create()
                                                    val () = $B.bput(fi, "build/bats_modules/")
                                                    val () = copy_to_builder(dep4, 0, dep4_len, 256, fi, $AR.checked_nat(dep4_len+1))
                                                    val () = $B.bput(fi, "/src/")
                                                    val () = copy_to_builder(bv_d4, 0, dl4, 256, fi, $AR.checked_nat(dl4+1))
                                                    val () = $B.put_byte(fi, 0)
                                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                                  val () = (if cf > 0 then ()
                                                  else let
                                                    val xo = $B.create()
                                                    val () = $B.bput(xo, "build/bats_modules/")
                                                    val () = copy_to_builder(dep4, 0, dep4_len, 256, xo, $AR.checked_nat(dep4_len+1))
                                                    val () = $B.bput(xo, "/src/")
                                                    val () = copy_to_builder(bv_d4, 0, stem4, 256, xo, $AR.checked_nat(stem4+1))
                                                    val () = $B.bput(xo, "_dats.o")
                                                    val () = $B.put_byte(xo, 0)
                                                    val @(xoa, xo_len) = $B.to_arr(xo)
                                                    val @(fz_xo, bv_xo) = $A.freeze<byte>(xoa)
                                                    val xi = $B.create()
                                                    val () = $B.bput(xi, "build/bats_modules/")
                                                    val () = copy_to_builder(dep4, 0, dep4_len, 256, xi, $AR.checked_nat(dep4_len+1))
                                                    val () = $B.bput(xi, "/src/")
                                                    val () = copy_to_builder(bv_d4, 0, dl4, 256, xi, $AR.checked_nat(dl4+1))
                                                    val () = $B.put_byte(xi, 0)
                                                    val @(xia, xi_len) = $B.to_arr(xi)
                                                    val @(fz_xi, bv_xi) = $A.freeze<byte>(xia)
                                                    val rc4 = run_cc(ph2, ph2len, bv_xo, xo_len, bv_xi, xi_len, rr2)
                                                    val () = $A.drop<byte>(fz_xo, bv_xo)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_xo))
                                                    val () = $A.drop<byte>(fz_xi, bv_xi)
                                                    val () = $A.free<byte>($A.thaw<byte>(fz_xi))
                                                  in (if rc4 <> 0 then let
                                                    val () = print! ("error: cc failed for extra ")
                                                    val () = print_borrow(bv_d4, 0, dl4, 256,
                                                      $AR.checked_nat(dl4 + 1))
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
                                    val fo = $B.create()
                                    val () = $B.bput(fo, "build/src/")
                                    val () = copy_to_builder(bv_dcsm, 0, stem_csm, 256, fo, $AR.checked_nat(stem_csm+1))
                                    val () = $B.bput(fo, "_dats.o")
                                    val () = $B.put_byte(fo, 0)
                                    val fi = $B.create()
                                    val () = $B.bput(fi, "build/src/")
                                    val () = copy_to_builder(bv_dcsm, 0, dl_csm, 256, fi, $AR.checked_nat(dl_csm+1))
                                    val () = $B.put_byte(fi, 0)
                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                  val () = (if cf_sm > 0 then ()
                                  else let
                                    val xo_sm = $B.create()
                                    val () = $B.bput(xo_sm, "build/src/")
                                    val () = copy_to_builder(bv_dcsm, 0, stem_csm, 256, xo_sm, $AR.checked_nat(stem_csm+1))
                                    val () = $B.bput(xo_sm, "_dats.o")
                                    val () = $B.put_byte(xo_sm, 0)
                                    val @(xoa_sm, xo_sm_len) = $B.to_arr(xo_sm)
                                    val @(fz_xosm, bv_xosm) = $A.freeze<byte>(xoa_sm)
                                    val xi_sm = $B.create()
                                    val () = $B.bput(xi_sm, "build/src/")
                                    val () = copy_to_builder(bv_dcsm, 0, dl_csm, 256, xi_sm, $AR.checked_nat(dl_csm+1))
                                    val () = $B.put_byte(xi_sm, 0)
                                    val @(xia_sm, xi_sm_len) = $B.to_arr(xi_sm)
                                    val @(fz_xism, bv_xism) = $A.freeze<byte>(xia_sm)
                                    val rc_csm = run_cc(ph_cm, ph_cm_len, bv_xosm, xo_sm_len, bv_xism, xi_sm_len, rr_cm)
                                    val () = $A.drop<byte>(fz_xosm, bv_xosm)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_xosm))
                                    val () = $A.drop<byte>(fz_xism, bv_xism)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_xism))
                                  in (if rc_csm <> 0 then let
                                    val () = print! ("error: cc failed for src module ")
                                    val () = print_borrow(bv_dcsm, 0, dl_csm, 256,
                                      $AR.checked_nat(dl_csm + 1))
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

                    (* Compile binary *)
                    val bin_cc_fresh = let
                      val ob = $B.create()
                      val () = $B.bput(ob, "build/src/bin/")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ob, $AR.checked_nat(stem_len+1))
                      val () = $B.bput(ob, "_dats.o")
                      val () = $B.put_byte(ob, 0)
                      val ib = $B.create()
                      val () = $B.bput(ib, "build/src/bin/")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ib, $AR.checked_nat(stem_len+1))
                      val () = $B.bput(ib, "_dats.c")
                      val () = $B.put_byte(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if bin_cc_fresh > 0 then ()
                    else let
                    val co_b = $B.create()
                    val () = $B.bput(co_b, "build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, co_b,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(co_b, "_dats.o")
                    val () = $B.put_byte(co_b, 0)
                    val @(co_a, co_len) = $B.to_arr(co_b)
                    val @(fz_co, bv_co) = $A.freeze<byte>(co_a)
                    val ci_b = $B.create()
                    val () = $B.bput(ci_b, "build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, ci_b,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(ci_b, "_dats.c")
                    val () = $B.put_byte(ci_b, 0)
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
                      val ob = $B.create()
                      val () = $B.bput(ob, "build/_bats_entry_")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ob, $AR.checked_nat(stem_len+1))
                      val () = $B.bput(ob, "_dats.o")
                      val () = $B.put_byte(ob, 0)
                      val ib = $B.create()
                      val () = $B.bput(ib, "build/_bats_entry_")
                      val () = copy_to_builder(bv_e, 0, stem_len, 256, ib, $AR.checked_nat(stem_len+1))
                      val () = $B.bput(ib, "_dats.c")
                      val () = $B.put_byte(ib, 0)
                    in (if freshness_check_bv(ob, ib) then 1 else 0): int end
                    val () = (if ent_cc_fresh > 0 then ()
                    else let
                    val ceo_b = $B.create()
                    val () = $B.bput(ceo_b, "build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, ceo_b,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(ceo_b, "_dats.o")
                    val () = $B.put_byte(ceo_b, 0)
                    val @(ceo_a, ceo_len) = $B.to_arr(ceo_b)
                    val @(fz_ceo, bv_ceo) = $A.freeze<byte>(ceo_a)
                    val cei_b = $B.create()
                    val () = $B.bput(cei_b, "build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, cei_b,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(cei_b, "_dats.c")
                    val () = $B.put_byte(cei_b, 0)
                    val @(cei_a, cei_len) = $B.to_arr(cei_b)
                    val @(fz_cei, bv_cei) = $A.freeze<byte>(cei_a)
                    val _ = run_cc(ph, phlen, bv_ceo, ceo_len, bv_cei, cei_len, rel)
                    val () = $A.drop<byte>(fz_ceo, bv_ceo)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ceo))
                    val () = $A.drop<byte>(fz_cei, bv_cei)
                    val () = $A.free<byte>($A.thaw<byte>(fz_cei))
                    in end)

                    (* Step 8: Link *)
                    val link = $B.create()
                    val () = (if rel > 0 then
                      $B.bput(link, "cc -o dist/release/")
                      else $B.bput(link, "cc -o dist/debug/"))
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, link,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(link, " build/_bats_entry_")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, link,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(link, "_dats.o build/src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, link,
                      $AR.checked_nat(stem_len + 1))
                    val () = $B.bput(link, "_dats.o build/_bats_native_runtime.o")
                    (* Add all dep .o files *)
                    val bm5_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm5, bv_bm5) = $A.freeze<byte>(bm5_arr)
                    val bdir5 = $F.dir_open(bv_bm5, 524288)
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
                                  val pk_b4 = $B.create()
                                  val () = $B.bput(pk_b4, "bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pk_b4, $AR.checked_nat(dlen+1))
                                  val () = $B.bput(pk_b4, "/bats.toml")
                                  val () = $B.put_byte(pk_b4, 0)
                                  val @(pka4, _) = $B.to_arr(pk_b4)
                                  val @(fz_pk4, bv_pk4) = $A.freeze<byte>(pka4)
                                  val pk_r4 = $F.file_mtime(bv_pk4, 524288)
                                  val is_p4 = (case+ pk_r4 of | ~$R.ok(_) => true | ~$R.err(_) => false): bool
                                  val () = $A.drop<byte>(fz_pk4, bv_pk4)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_pk4))
                                in
                                  if ~is_p4 then let
                                    (* Namespace dir — iterate subdirs for link *)
                                    val ns_ld = $B.create()
                                    val () = $B.bput(ns_ld, "bats_modules/")
                                    val () = copy_to_builder(bv_de, 0, dlen, 256, ns_ld, $AR.checked_nat(dlen+1))
                                    val () = $B.put_byte(ns_ld, 0)
                                    val @(ns_lda, _) = $B.to_arr(ns_ld)
                                    val @(fz_nsld, bv_nsld) = $A.freeze<byte>(ns_lda)
                                    val ns_lr = $F.dir_open(bv_nsld, 524288)
                                    val () = $A.drop<byte>(fz_nsld, bv_nsld)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_nsld))
                                    val () = (case+ ns_lr of
                                      | ~$R.ok(nsld) => let
                                          fun link_ns {lns4:agz}{fuel_ln:nat} .<fuel_ln>.
                                            (nsld: !$F.dir, lb2: !$B.builder,
                                             ns4: !$A.borrow(byte, lns4, 256), ns4len: int,
                                             fuel_ln: int fuel_ln): void =
                                            if fuel_ln <= 0 then ()
                                            else let
                                              val sde = $A.alloc<byte>(256)
                                              val snr = $F.dir_next(nsld, sde, 256)
                                              val sel = $R.option_unwrap_or<int>(snr, ~1)
                                            in if sel < 0 then $A.free<byte>(sde)
                                              else let val sdd = is_dot_or_dotdot(sde, sel, 256) in
                                                if sdd then let val () = $A.free<byte>(sde)
                                                in link_ns(nsld, lb2, ns4, ns4len, fuel_ln-1) end
                                                else let
                                                  val @(fz_sde, bv_sde) = $A.freeze<byte>(sde)
                                                  val () = $B.bput(lb2, " build/bats_modules/")
                                                  val () = copy_to_builder(ns4, 0, ns4len, 256, lb2, $AR.checked_nat(ns4len+1))
                                                  val () = $B.bput(lb2, "/")
                                                  val () = copy_to_builder(bv_sde, 0, sel, 256, lb2, $AR.checked_nat(sel+1))
                                                  val () = $B.bput(lb2, "/src/lib_dats.o")
                                                  val () = $A.drop<byte>(fz_sde, bv_sde)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_sde))
                                                in link_ns(nsld, lb2, ns4, ns4len, fuel_ln-1) end
                                              end
                                            end
                                          val () = link_ns(nsld, lb, bv_de, dlen, 100)
                                          val dcr_ln = $F.dir_close(nsld)
                                          val () = $R.discard<int><int>(dcr_ln)
                                        in end
                                      | ~$R.err(_) => ())
                                    val () = $A.drop<byte>(fz_de, bv_de)
                                    val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                  in link_deps(dd5, lb, fuel5 - 1) end
                                  else let
                                  val () = $B.bput(lb, " build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256,
                                    lb, $AR.checked_nat(dlen + 1))
                                  val () = $B.bput(lb, "/src/lib_dats.o")
                                  (* link extra _dats.o files for this dep *)
                                  val lk_src_b = $B.create()
                                  val () = $B.bput(lk_src_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, lk_src_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = $B.bput(lk_src_b, "/src")
                                  val () = $B.put_byte(lk_src_b, 0)
                                  val @(lk_a, _) = $B.to_arr(lk_src_b)
                                  val @(fz_lk, bv_lk) = $A.freeze<byte>(lk_a)
                                  val lk_dir = $F.dir_open(bv_lk, 524288)
                                  val () = $A.drop<byte>(fz_lk, bv_lk)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_lk))
                                  val () = (case+ lk_dir of
                                    | ~$R.ok(d_lk) => let
                                        fun link_extra
                                          {ld5:agz}{fuel_l:nat} .<fuel_l>.
                                          (d_lk: !$F.dir, lb2: !$B.builder,
                                           dep5: !$A.borrow(byte, ld5, 256),
                                           dep5_len: int,
                                           fuel_l: int fuel_l): void =
                                          if fuel_l <= 0 then ()
                                          else let
                                            val de5 = $A.alloc<byte>(256)
                                            val nr5 = $F.dir_next(d_lk, de5, 256)
                                            val dl5 = $R.option_unwrap_or<int>(nr5, ~1)
                                          in
                                            if dl5 < 0 then $A.free<byte>(de5)
                                            else let
                                              val is_o = has_dats_o_ext(de5, dl5, 256)
                                              val is_l = is_lib_dats_o(de5, dl5, 256)
                                            in
                                              if is_o then
                                                if is_l then let
                                                  val () = $A.free<byte>(de5)
                                                in link_extra(d_lk, lb2, dep5, dep5_len, fuel_l - 1) end
                                                else let
                                                  val @(fz_d5, bv_d5) = $A.freeze<byte>(de5)
                                                  val () = $B.bput(lb2, " build/bats_modules/")
                                                  val () = copy_to_builder(dep5, 0, dep5_len, 256,
                                                    lb2, $AR.checked_nat(dep5_len + 1))
                                                  val () = $B.bput(lb2, "/src/")
                                                  val () = copy_to_builder(bv_d5, 0, dl5, 256,
                                                    lb2, $AR.checked_nat(dl5 + 1))
                                                  val () = $A.drop<byte>(fz_d5, bv_d5)
                                                  val () = $A.free<byte>($A.thaw<byte>(fz_d5))
                                                in link_extra(d_lk, lb2, dep5, dep5_len, fuel_l - 1) end
                                              else let
                                                val () = $A.free<byte>(de5)
                                              in link_extra(d_lk, lb2, dep5, dep5_len, fuel_l - 1) end
                                            end
                                          end
                                        val () = link_extra(d_lk, lb, bv_de, dlen, 200)
                                        val dcr_lk = $F.dir_close(d_lk)
                                        val () = $R.discard<int><int>(dcr_lk)
                                      in end
                                    | ~$R.err(_) => ())
                                  val () = $A.drop<byte>(fz_de, bv_de)
                                  val () = $A.free<byte>($A.thaw<byte>(fz_de))
                                in link_deps(dd5, lb, fuel5 - 1) end
                                  end (* if ~is_p4 *)
                              end
                            end
                          val () = link_deps(dd5, link, 200)
                          val dcr5 = $F.dir_close(dd5)
                          val () = $R.discard<int><int>(dcr5)
                        in end
                      | ~$R.err(_) => ())
                    (* Link src/*.dats shared module .o files *)
                    val lsm_arr = str_to_path_arr("build/src")
                    val @(fz_lsm, bv_lsm) = $A.freeze<byte>(lsm_arr)
                    val lsm_dir = $F.dir_open(bv_lsm, 524288)
                    val () = $A.drop<byte>(fz_lsm, bv_lsm)
                    val () = $A.free<byte>($A.thaw<byte>(fz_lsm))
                    val () = (case+ lsm_dir of
                      | ~$R.ok(d_lsm) => let
                          fun link_src_modules {fuel_lsm:nat} .<fuel_lsm>.
                            (d_lsm: !$F.dir, lb: !$B.builder,
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
                                  val () = $B.bput(lb, " build/src/")
                                  val () = copy_to_builder(bv_dlsm, 0, dl_lsm, 256,
                                    lb, $AR.checked_nat(dl_lsm + 1))
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
                    val () = (if rel > 0 then $B.bput(link, " -O2")
                      else $B.bput(link, " -g -O0"))
                    (* Convert space-separated link command to null-separated argv *)
                    val @(link_arr, link_len) = $B.to_arr(link)
                    val @(fz_la, bv_la) = $A.freeze<byte>(link_arr)
                    val link_argv = $B.create()
                    fun split_spaces {l2:agz}{fuel:nat} .<fuel>.
                      (bv: !$A.borrow(byte, l2, 524288), i: int, len: int,
                       dst: !$B.builder, argc: int, in_arg: int,
                       fuel: int fuel): int =
                      if fuel <= 0 then argc
                      else if i >= len then
                        (if in_arg > 0 then let
                          val () = $B.put_byte(dst, 0)
                        in argc + 1 end else argc)
                      else let
                        val b = $S.borrow_byte(bv, i, 524288)
                      in
                        if $AR.eq_int_int(b, 32) then
                          if in_arg > 0 then let
                            val () = $B.put_byte(dst, 0)
                          in split_spaces(bv, i + 1, len, dst, argc + 1, 0, fuel - 1) end
                          else split_spaces(bv, i + 1, len, dst, argc, 0, fuel - 1)
                        else let
                          val () = $B.put_byte(dst, b)
                        in split_spaces(bv, i + 1, len, dst, argc, 1, fuel - 1) end
                      end
                    val link_argc = split_spaces(bv_la, 0, link_len, link_argv, 0, 0,
                      $AR.checked_nat(link_len + 1))
                    val () = $A.drop<byte>(fz_la, bv_la)
                    val () = $A.free<byte>($A.thaw<byte>(fz_la))
                    (* First arg is "cc" or "PATH=... cc" — extract the exec path *)
                    val cc_exec = str_to_path_arr("/usr/bin/cc")
                    val @(fz_cce, bv_cce) = $A.freeze<byte>(cc_exec)
                    (* Remove the first "PATH=..." token and "cc" token,
                       start argv from "cc" *)
                    val rl = run_cmd(bv_cce, 524288, link_argv, link_argc)
                    val () = $A.drop<byte>(fz_cce, bv_cce)
                    val () = $A.free<byte>($A.thaw<byte>(fz_cce))
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
                val md = $B.create()
                val () = copy_to_builder(bv_tcb, 0, tcl2, 4096, md, $AR.checked_nat(tcl2+1))
                val _ = run_mkdir(md)
                (* cp -r build/ <target>/ — copy all C files *)
                val cp_exec = str_to_path_arr("/bin/cp")
                val @(fz_cpe, bv_cpe) = $A.freeze<byte>(cp_exec)
                val cp_argv = $B.create()
                val () = $B.bput(cp_argv, "cp") val () = $B.put_byte(cp_argv, 0)
                val () = $B.bput(cp_argv, "-r") val () = $B.put_byte(cp_argv, 0)
                val () = $B.bput(cp_argv, "build/.") val () = $B.put_byte(cp_argv, 0)
                val () = copy_to_builder(bv_tcb, 0, tcl2, 4096, cp_argv, $AR.checked_nat(tcl2+1))
                val () = $B.bput(cp_argv, "/") val () = $B.put_byte(cp_argv, 0)
                val _ = run_cmd(bv_cpe, 524288, cp_argv, 4)
                val () = $A.drop<byte>(fz_cpe, bv_cpe)
                val () = $A.free<byte>($A.thaw<byte>(fz_cpe))
                (* Generate Makefile *)
                val mf = $B.create()
                val () = $B.bput(mf, "PATSHOME ?= $(HOME)/.bats/ats2\n")
                val () = $B.bput(mf, "CC ?= cc\n\n")
                val () = $B.bput(mf, "%_debug.o: %.c\n\t$(CC) -c -o $@ $< -g -O0 -I$(PATSHOME) -I$(PATSHOME)/ccomp/runtime\n\n")
                val () = $B.bput(mf, "%_release.o: %.c\n\t$(CC) -c -o $@ $< -O2 -I$(PATSHOME) -I$(PATSHOME)/ccomp/runtime\n\n")
                val () = $B.bput(mf, "SRCS := $(shell find . -name '*_dats.c') _bats_native_runtime.c\n")
                val () = $B.bput(mf, "DEBUG_OBJS := $(SRCS:.c=_debug.o)\n")
                val () = $B.bput(mf, "RELEASE_OBJS := $(SRCS:.c=_release.o)\n\n")
                val () = $B.bput(mf, "all: debug/bats release/bats\n\n")
                val () = $B.bput(mf, "debug/bats: $(DEBUG_OBJS)\n\tmkdir -p debug\n\t$(CC) -o $@ $^ -g -O0\n\n")
                val () = $B.bput(mf, "release/bats: $(RELEASE_OBJS)\n\tmkdir -p release\n\t$(CC) -o $@ $^ -O2\n\n")
                val () = $B.bput(mf, "clean:\n\trm -f *.o\n\trm -rf debug release\n")
                val mfp = $B.create()
                val () = copy_to_builder(bv_tcb, 0, tcl2, 4096, mfp, $AR.checked_nat(tcl2+1))
                val () = $B.bput(mfp, "/Makefile")
                val () = $B.put_byte(mfp, 0)
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
