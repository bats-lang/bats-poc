(* build -- build pipeline for the bats compiler *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use env as E
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
   dats_bv: !$A.borrow(byte, l3, 524288)): int

implement preprocess_one
  (src_bv, sats_bv, dats_bv) = let
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
      val @(sats_arr, sats_len, dats_arr, dats_len, _pre) =
        do_emit(bv_src, nbytes, 524288, bv_sp, 524288, span_count)
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
      val bn_end = find_null_bv(sats_bv, bn_start, 524288, 4096)
      val () = bput(db, "staload \"./")
      val () = copy_to_builder(sats_bv, bn_start, bn_end, 524288, db,
        $AR.checked_nat(bn_end - bn_start + 1))
      val () = bput(db, "\"\n")
      val @(fz_d, bv_d) = $A.freeze<byte>(dats_arr)
      val () = copy_to_builder(bv_d, 0, dats_len, 524288, db,
        $AR.checked_nat(dats_len + 1))
      val () = $A.drop<byte>(fz_d, bv_d)
      val () = $A.free<byte>($A.thaw<byte>(fz_d))
      val r2 = write_file_from_builder(dats_bv, 524288, db)
    in
      if r1 = 0 then (if r2 = 0 then 0 else ~1) else ~1
    end
  | ~$R.err(_) => ~1
end end

(* ============================================================
   clean: remove build/ and dist/ directories
   ============================================================ *)
#pub fn do_clean(): void

implement do_clean() = let
  val cmd = $B.create()
  val () = bput(cmd, "rm -rf build dist docs")
  val rc = run_sh(cmd, 0)
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
  val rc = write_file_from_builder(bv_p, 524288, b)
  val () = $A.drop<byte>(fz_p, bv_p)
  val () = $A.free<byte>($A.thaw<byte>(fz_p))
in rc end

#pub fn write_wasm_runtime_c(): int

implement write_wasm_runtime_c() = let
  val b = $B.create()
  val () = bput(b, "/* runtime.c -- Freestanding WASM: free-list allocator */\nextern unsigned char __heap_base;\nstatic unsigned char *heap_ptr = &__heap_base;\n")
  val () = bput(b, "#define WARD_HEADER 8\n#define WARD_NBUCKET 9\nstatic const unsigned int ward_bsz[WARD_NBUCKET] = {32,128,512,4096,8192,16384,524288,262144,1048576};\n")
  val () = bput(b, "static void *ward_fl[WARD_NBUCKET] = {0,0,0,0,0,0,0,0,0};\nstatic void *ward_fl_over = 0;\n")
  val () = bput(b, "void *memset(void *s,int c,unsigned int n){unsigned char *p=(unsigned char*)s;unsigned char byte=(unsigned char)c;while(n--)*p++=byte;return s;}\n")
  val () = bput(b, "void *memcpy(void *dst,const void *src,unsigned int n){unsigned char *d=(unsigned char*)dst;const unsigned char *s=(const unsigned char*)src;while(n--)*d++=*s++;return dst;}\n")
  val () = bput(b, "static inline unsigned int ward_hdr_read(void *p){return *(unsigned int*)((char*)p-WARD_HEADER);}\n")
  val () = bput(b, "static inline int ward_bucket(unsigned int n){if(n<=32)return 0;if(n<=128)return 1;if(n<=512)return 2;if(n<=4096)return 3;\n")
  val () = bput(b, "if(n<=8192)return 4;if(n<=16384)return 5;if(n<=524288)return 6;if(n<=262144)return 7;if(n<=1048576)return 8;return -1;}\n")
  val () = bput(b, "static void *ward_bump(unsigned int usable){unsigned long a=(unsigned long)heap_ptr;a=(a+7u)&~7u;unsigned long end=a+WARD_HEADER+usable;\n")
  val () = bput(b, "unsigned long limit=(unsigned long)__builtin_wasm_memory_size(0)*524288UL;if(end>limit){unsigned long pages=(end-limit+65535UL)/524288UL;\n")
  val () = bput(b, "if(__builtin_wasm_memory_grow(0,pages)==(unsigned long)(-1))return(void*)0;}*(unsigned int*)a=usable;void *p=(void*)(a+WARD_HEADER);heap_ptr=(unsigned char*)end;return p;}\n")
  val () = bput(b, "void *malloc(int size){if(size<=0)size=1;unsigned int n=(unsigned int)size;int b=ward_bucket(n);if(b>=0){unsigned int bsz=ward_bsz[b];void *p;\n")
  val () = bput(b, "if(ward_fl[b]){p=ward_fl[b];ward_fl[b]=*(void**)p;}else{p=ward_bump(bsz);}memset(p,0,bsz);return p;}\n")
  val () = bput(b, "void **prev=&ward_fl_over;void *cur=ward_fl_over;while(cur){unsigned int bsz=ward_hdr_read(cur);if(bsz>=n&&bsz<=2*n){*prev=*(void**)cur;memset(cur,0,bsz);return cur;}\n")
  val () = bput(b, "prev=(void**)cur;cur=*(void**)cur;}void *p=ward_bump(n);memset(p,0,n);return p;}\n")
  val () = bput(b, "void free(void *ptr){if(!ptr)return;unsigned int sz=ward_hdr_read(ptr);int b=ward_bucket(sz);if(b>=0&&ward_bsz[b]==sz){*(void**)ptr=ward_fl[b];ward_fl[b]=ptr;}\n")
  val () = bput(b, "else{*(void**)ptr=ward_fl_over;ward_fl_over=ptr;}}\n")
  val p = str_to_path_arr("build/_bats_wasm_runtime.c")
  val @(fz_p, bv_p) = $A.freeze<byte>(p)
  val rc = write_file_from_builder(bv_p, 524288, b)
  val () = $A.drop<byte>(fz_p, bv_p)
  val () = $A.free<byte>($A.thaw<byte>(fz_p))
in rc end

#pub fn write_wasm_stubs(): int

implement write_wasm_stubs() = let
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

#pub fn do_build_wasm(release: int): void

implement do_build_wasm(release) = let
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
    val () = bput(wasm_link, "-z stack-size=524288 --initial-memory=16777216 --max-memory=268435456 ")
    val () = bput(wasm_link, "-o ../dist/")
    val () = (if release > 0 then bput(wasm_link, "release/") else bput(wasm_link, "debug/"))
    val () = bput(wasm_link, "output.wasm _bats_wasm_runtime.o $(find . -name '*.wasm.o' 2>/dev/null)")
    val wrc2 = run_sh(wasm_link, 0)
  in
    if wrc2 <> 0 then println! ("error: wasm linking failed")
    else (if ~is_quiet() then println! ("  built wasm binary") else ())
  end
end

#pub fn do_build(release: int): void

implement do_build(release) = let
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
    val _ = write_file_from_builder(bv_nrtp, 524288, nrt_b)
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
                    (* Scan additional .bats files in this dep *)
                    val dep_src_b = $B.create()
                    val () = bput(dep_src_b, "bats_modules/")
                    val () = copy_to_builder(bv_e, 0, elen, 256, dep_src_b,
                      $AR.checked_nat(elen + 1))
                    val () = bput(dep_src_b, "/src")
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
                                    val () = bput(sp_ex, "bats_modules/")
                                    val () = copy_to_builder(dep_bv, 0, dep_len, 256, sp_ex,
                                      $AR.checked_nat(dep_len + 1))
                                    val () = bput(sp_ex, "/src/")
                                    val () = copy_to_builder(bv_ex, 0, elen_ex, 256, sp_ex,
                                      $AR.checked_nat(elen_ex + 1))
                                    val () = $B.put_byte(sp_ex, 0)
                                    val @(spa_ex, _) = $B.to_arr(sp_ex)
                                    val @(fz_spa, bv_spa) = $A.freeze<byte>(spa_ex)
                                    val ss_ex = $B.create()
                                    val () = bput(ss_ex, "build/bats_modules/")
                                    val () = copy_to_builder(dep_bv, 0, dep_len, 256, ss_ex,
                                      $AR.checked_nat(dep_len + 1))
                                    val () = bput(ss_ex, "/src/")
                                    val () = copy_to_builder(bv_ex, 0, stem_ex, 256, ss_ex,
                                      $AR.checked_nat(stem_ex + 1))
                                    val () = bput(ss_ex, ".sats")
                                    val () = $B.put_byte(ss_ex, 0)
                                    val @(ssa_ex, _) = $B.to_arr(ss_ex)
                                    val @(fz_ssa, bv_ssa) = $A.freeze<byte>(ssa_ex)
                                    val sd_ex = $B.create()
                                    val () = bput(sd_ex, "build/bats_modules/")
                                    val () = copy_to_builder(dep_bv, 0, dep_len, 256, sd_ex,
                                      $AR.checked_nat(dep_len + 1))
                                    val () = bput(sd_ex, "/src/")
                                    val () = copy_to_builder(bv_ex, 0, stem_ex, 256, sd_ex,
                                      $AR.checked_nat(stem_ex + 1))
                                    val () = bput(sd_ex, ".dats")
                                    val () = $B.put_byte(sd_ex, 0)
                                    val @(sda_ex, _) = $B.to_arr(sd_ex)
                                    val @(fz_sda, bv_sda) = $A.freeze<byte>(sda_ex)
                                    val pr_ex = preprocess_one(bv_spa, bv_ssa, bv_sda)
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
                    val () = bput(sp_sm, "src/")
                    val () = copy_to_builder(bv_esm, 0, elen_sm, 256, sp_sm,
                      $AR.checked_nat(elen_sm + 1))
                    val () = $B.put_byte(sp_sm, 0)
                    val @(spa_sm, _) = $B.to_arr(sp_sm)
                    val @(fz_spa_sm, bv_spa_sm) = $A.freeze<byte>(spa_sm)
                    (* sats: build/src/<stem>.sats *)
                    val ss_sm = $B.create()
                    val () = bput(ss_sm, "build/src/")
                    val () = copy_to_builder(bv_esm, 0, stem_sm, 256, ss_sm,
                      $AR.checked_nat(stem_sm + 1))
                    val () = bput(ss_sm, ".sats")
                    val () = $B.put_byte(ss_sm, 0)
                    val @(ssa_sm, _) = $B.to_arr(ss_sm)
                    val @(fz_ssa_sm, bv_ssa_sm) = $A.freeze<byte>(ssa_sm)
                    (* dats: build/src/<stem>.dats *)
                    val sd_sm = $B.create()
                    val () = bput(sd_sm, "build/src/")
                    val () = copy_to_builder(bv_esm, 0, stem_sm, 256, sd_sm,
                      $AR.checked_nat(stem_sm + 1))
                    val () = bput(sd_sm, ".dats")
                    val () = $B.put_byte(sd_sm, 0)
                    val @(sda_sm, _) = $B.to_arr(sd_sm)
                    val @(fz_sda_sm, bv_sda_sm) = $A.freeze<byte>(sda_sm)
                    val pr_sm = preprocess_one(bv_spa_sm, bv_ssa_sm, bv_sda_sm)
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
                                  val () = bput(eb, "dynload \"./bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256,
                                    eb, $AR.checked_nat(dlen + 1))
                                  val () = bput(eb, "/src/lib.dats\"\n")
                                  (* dynload extra .dats files for this dep *)
                                  val dyn_src_b = $B.create()
                                  val () = bput(dyn_src_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, dyn_src_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(dyn_src_b, "/src")
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
                                                  val () = bput(eb2, "dynload \"./bats_modules/")
                                                  val () = copy_to_builder(dep2, 0, dep2_len, 256,
                                                    eb2, $AR.checked_nat(dep2_len + 1))
                                                  val () = bput(eb2, "/src/")
                                                  val () = copy_to_builder(bv_d2, 0, dl2, 256,
                                                    eb2, $AR.checked_nat(dl2 + 1))
                                                  val () = bput(eb2, "\"\n")
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
                                  val () = bput(eb, "dynload \"./src/")
                                  val () = copy_to_builder(bv_dsme, 0, dl_sm, 256,
                                    eb, $AR.checked_nat(dl_sm + 1))
                                  val () = bput(eb, "\"\n")
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
                                  val po_b = $B.create()
                                  val () = bput(po_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, po_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(po_b, "/src/lib_dats.c")
                                  val () = $B.put_byte(po_b, 0)
                                  val @(po_a, po_len) = $B.to_arr(po_b)
                                  val @(fz_po, bv_po) = $A.freeze<byte>(po_a)
                                  val pi_b = $B.create()
                                  val () = bput(pi_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pi_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(pi_b, "/src/lib.dats")
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
                                  val () = bput(pats_src_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pats_src_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(pats_src_b, "/src")
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
                                                    val () = bput(fo, "build/bats_modules/")
                                                    val () = copy_to_builder(dep3, 0, dep3_len, 256, fo, $AR.checked_nat(dep3_len+1))
                                                    val () = bput(fo, "/src/")
                                                    val () = copy_to_builder(bv_d3, 0, stem3, 256, fo, $AR.checked_nat(stem3+1))
                                                    val () = bput(fo, "_dats.c")
                                                    val () = $B.put_byte(fo, 0)
                                                    val fi = $B.create()
                                                    val () = bput(fi, "build/bats_modules/")
                                                    val () = copy_to_builder(dep3, 0, dep3_len, 256, fi, $AR.checked_nat(dep3_len+1))
                                                    val () = bput(fi, "/src/")
                                                    val () = copy_to_builder(bv_d3, 0, dl3, 256, fi, $AR.checked_nat(dl3+1))
                                                    val () = $B.put_byte(fi, 0)
                                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                                  val () = (if pf > 0 then ()
                                                  else let
                                                    val eo = $B.create()
                                                    val () = bput(eo, "build/bats_modules/")
                                                    val () = copy_to_builder(dep3, 0, dep3_len, 256, eo, $AR.checked_nat(dep3_len+1))
                                                    val () = bput(eo, "/src/")
                                                    val () = copy_to_builder(bv_d3, 0, stem3, 256, eo, $AR.checked_nat(stem3+1))
                                                    val () = bput(eo, "_dats.c")
                                                    val () = $B.put_byte(eo, 0)
                                                    val @(eoa, eo_len) = $B.to_arr(eo)
                                                    val @(fz_eo, bv_eo) = $A.freeze<byte>(eoa)
                                                    val ei = $B.create()
                                                    val () = bput(ei, "build/bats_modules/")
                                                    val () = copy_to_builder(dep3, 0, dep3_len, 256, ei, $AR.checked_nat(dep3_len+1))
                                                    val () = bput(ei, "/src/")
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
                                    val () = bput(fo, "build/src/")
                                    val () = copy_to_builder(bv_dpsm, 0, stem_psm, 256, fo, $AR.checked_nat(stem_psm+1))
                                    val () = bput(fo, "_dats.c")
                                    val () = $B.put_byte(fo, 0)
                                    val fi = $B.create()
                                    val () = bput(fi, "build/src/")
                                    val () = copy_to_builder(bv_dpsm, 0, dl_psm, 256, fi, $AR.checked_nat(dl_psm+1))
                                    val () = $B.put_byte(fi, 0)
                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                  val () = (if pf_sm > 0 then ()
                                  else let
                                    val eo_sm = $B.create()
                                    val () = bput(eo_sm, "build/src/")
                                    val () = copy_to_builder(bv_dpsm, 0, stem_psm, 256, eo_sm, $AR.checked_nat(stem_psm+1))
                                    val () = bput(eo_sm, "_dats.c")
                                    val () = $B.put_byte(eo_sm, 0)
                                    val @(eoa_sm, eo_sm_len) = $B.to_arr(eo_sm)
                                    val @(fz_eosm, bv_eosm) = $A.freeze<byte>(eoa_sm)
                                    val ei_sm = $B.create()
                                    val () = bput(ei_sm, "build/src/")
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
                                  val co_b = $B.create()
                                  val () = bput(co_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, co_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(co_b, "/src/lib_dats.o")
                                  val () = $B.put_byte(co_b, 0)
                                  val @(co_a, co_len) = $B.to_arr(co_b)
                                  val @(fz_co, bv_co) = $A.freeze<byte>(co_a)
                                  val ci_b = $B.create()
                                  val () = bput(ci_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, ci_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(ci_b, "/src/lib_dats.c")
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
                                  val () = bput(cc_src_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, cc_src_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(cc_src_b, "/src")
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
                                                    val () = bput(fo, "build/bats_modules/")
                                                    val () = copy_to_builder(dep4, 0, dep4_len, 256, fo, $AR.checked_nat(dep4_len+1))
                                                    val () = bput(fo, "/src/")
                                                    val () = copy_to_builder(bv_d4, 0, stem4, 256, fo, $AR.checked_nat(stem4+1))
                                                    val () = bput(fo, "_dats.o")
                                                    val () = $B.put_byte(fo, 0)
                                                    val fi = $B.create()
                                                    val () = bput(fi, "build/bats_modules/")
                                                    val () = copy_to_builder(dep4, 0, dep4_len, 256, fi, $AR.checked_nat(dep4_len+1))
                                                    val () = bput(fi, "/src/")
                                                    val () = copy_to_builder(bv_d4, 0, dl4, 256, fi, $AR.checked_nat(dl4+1))
                                                    val () = $B.put_byte(fi, 0)
                                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                                  val () = (if cf > 0 then ()
                                                  else let
                                                    val xo = $B.create()
                                                    val () = bput(xo, "build/bats_modules/")
                                                    val () = copy_to_builder(dep4, 0, dep4_len, 256, xo, $AR.checked_nat(dep4_len+1))
                                                    val () = bput(xo, "/src/")
                                                    val () = copy_to_builder(bv_d4, 0, stem4, 256, xo, $AR.checked_nat(stem4+1))
                                                    val () = bput(xo, "_dats.o")
                                                    val () = $B.put_byte(xo, 0)
                                                    val @(xoa, xo_len) = $B.to_arr(xo)
                                                    val @(fz_xo, bv_xo) = $A.freeze<byte>(xoa)
                                                    val xi = $B.create()
                                                    val () = bput(xi, "build/bats_modules/")
                                                    val () = copy_to_builder(dep4, 0, dep4_len, 256, xi, $AR.checked_nat(dep4_len+1))
                                                    val () = bput(xi, "/src/")
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
                                    val () = bput(fo, "build/src/")
                                    val () = copy_to_builder(bv_dcsm, 0, stem_csm, 256, fo, $AR.checked_nat(stem_csm+1))
                                    val () = bput(fo, "_dats.o")
                                    val () = $B.put_byte(fo, 0)
                                    val fi = $B.create()
                                    val () = bput(fi, "build/src/")
                                    val () = copy_to_builder(bv_dcsm, 0, dl_csm, 256, fi, $AR.checked_nat(dl_csm+1))
                                    val () = $B.put_byte(fi, 0)
                                  in (if freshness_check_bv(fo, fi) then 1 else 0): int end
                                  val () = (if cf_sm > 0 then ()
                                  else let
                                    val xo_sm = $B.create()
                                    val () = bput(xo_sm, "build/src/")
                                    val () = copy_to_builder(bv_dcsm, 0, stem_csm, 256, xo_sm, $AR.checked_nat(stem_csm+1))
                                    val () = bput(xo_sm, "_dats.o")
                                    val () = $B.put_byte(xo_sm, 0)
                                    val @(xoa_sm, xo_sm_len) = $B.to_arr(xo_sm)
                                    val @(fz_xosm, bv_xosm) = $A.freeze<byte>(xoa_sm)
                                    val xi_sm = $B.create()
                                    val () = bput(xi_sm, "build/src/")
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
                                  val () = bput(lb, " build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256,
                                    lb, $AR.checked_nat(dlen + 1))
                                  val () = bput(lb, "/src/lib_dats.o")
                                  (* link extra _dats.o files for this dep *)
                                  val lk_src_b = $B.create()
                                  val () = bput(lk_src_b, "build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, lk_src_b,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(lk_src_b, "/src")
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
                                                  val () = bput(lb2, " build/bats_modules/")
                                                  val () = copy_to_builder(dep5, 0, dep5_len, 256,
                                                    lb2, $AR.checked_nat(dep5_len + 1))
                                                  val () = bput(lb2, "/src/")
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
                                  val () = bput(lb, " build/src/")
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
      val () = (if is_to_c() then if get_to_c_done() = 0 then let
        val () = set_to_c_done(1)
        val cmd = $B.create()
        (* Read DIR and copy files *)
        val () = bput(cmd, "DIR=$(tr -d '")
        val () = $B.put_byte(cmd, 92) (* backslash *)
        val () = bput(cmd, "n' < /tmp/_bpoc_to_c.txt) && mkdir -p $DIR && ")
        val () = bput(cmd, "cp build/_bats_native_runtime.c $DIR/ && ")
        val () = bput(cmd, "for d in bats_modules/*/; do [ -d \"$d\" ] && dep=$(basename \"$d\") && ")
        val () = bput(cmd, "cp \"build/bats_modules/$dep/src/lib_dats.c\" \"$DIR/${dep}_lib_dats.c\" 2>/dev/null && ")
        val () = bput(cmd, "for f in \"build/bats_modules/$dep/src/\"*_dats.c; do [ -f \"$f\" ] && bn=$(basename \"$f\") && ")
        val () = bput(cmd, "[ \"$bn\" != \"lib_dats.c\" ] && cp \"$f\" \"$DIR/${dep}_${bn}\" 2>/dev/null; done; done; ")
        val () = bput(cmd, "for f in build/src/*_dats.c; do [ -f \"$f\" ] && bn=$(basename \"$f\") && cp \"$f\" \"$DIR/src_${bn}\"; done; ")
        val () = bput(cmd, "for f in build/src/bin/*_dats.c; do [ -f \"$f\" ] && cp \"$f\" \"$DIR/\"; done; ")
        val () = bput(cmd, "for f in build/_bats_entry_*_dats.c; do [ -f \"$f\" ] && cp \"$f\" \"$DIR/\"; done;\n")
        val () = bput(cmd, "cd $DIR &&\n")
        (* Compute common deps *)
        val () = bput(cmd, "COMMON=\"\";\n")
        val () = bput(cmd, "for f in _bats_native_runtime.c *_dats.c; do [ -f \"$f\" ] || continue; case \"$f\" in _bats_entry_*) continue;; esac;\n")
        val () = bput(cmd, "base=${f%_dats.c}; [ -f \"_bats_entry_${base}_dats.c\" ] && continue;\n")
        val () = bput(cmd, "COMMON=\"$COMMON $f\"; done;\n")
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
