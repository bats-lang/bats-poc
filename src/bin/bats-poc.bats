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

$UNSAFE begin

%{
#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
static int _bpoc_g_verbose = 0;
static int _bpoc_g_quiet = 0;
static char _bpoc_g_repo[4096] = "";
static int _bpoc_g_repo_len = 0;
static int _bpoc_is_verbose(void) { return _bpoc_g_verbose; }
static int _bpoc_is_quiet(void) { return _bpoc_g_quiet; }
static void _bpoc_set_verbose(int v) { _bpoc_g_verbose = v; }
static void _bpoc_set_quiet(int v) { _bpoc_g_quiet = v; }
static void _bpoc_set_repo(const char *r, int len) {
  if (len > 0 && len < 4096) { memcpy(_bpoc_g_repo, r, len); _bpoc_g_repo[len] = '\0'; _bpoc_g_repo_len = len; }
}
static int _bpoc_get_repo(char *out, int max) {
  if (_bpoc_g_repo_len > 0 && _bpoc_g_repo_len < max) { memcpy(out, _bpoc_g_repo, _bpoc_g_repo_len); out[_bpoc_g_repo_len] = '\0'; return _bpoc_g_repo_len; }
  return 0;
}
static char _bpoc_g_bin[256] = "";
static int _bpoc_g_bin_len = 0;
static void _bpoc_set_bin(const char *b, int len) {
  if (len > 0 && len < 256) { memcpy(_bpoc_g_bin, b, len); _bpoc_g_bin[len] = '\0'; _bpoc_g_bin_len = len; }
}
static int _bpoc_get_bin(char *out, int max) {
  if (_bpoc_g_bin_len > 0 && _bpoc_g_bin_len < max) { memcpy(out, _bpoc_g_bin, _bpoc_g_bin_len); return _bpoc_g_bin_len; }
  return 0;
}
/* Handle --run-in <dir> flag: if first arg is "--run-in", chdir and return
   offset past the dir arg. Otherwise return first_start unchanged. */
static int _bpoc_handle_run_in(const char *buf, int len,
                                int fs, int fe, int fl) {
  if (fl == 8 && memcmp(buf + fs, "--run-in", 8) == 0) {
    int dir_start = fe + 1;
    /* dir_start points to null-terminated dir string in buf */
    if (chdir(buf + dir_start) != 0) {
      fprintf(stderr, "error: cannot change to '%s'\n", buf + dir_start);
    }
    /* Locate dir token terminator */
    int de = dir_start;
    while (de < len && buf[de] != '\0') de++;
    return de + 1;
  }
  return fs;
}
static int _bpoc_byte_at(const char *s, int i) {
  return (unsigned char)s[i];
}
static int _bpoc_slen(const char *s) {
  int len = 0;
  while (s[len] != '\0') len++;
  return len;
}
static int _bpoc_write_file(const char *path, const char *data, int len) {
  int fd = open(path, O_WRONLY|O_CREAT|O_TRUNC, 0644);
  if (fd < 0) return -1;
  int written = (int)write(fd, data, (unsigned)len);
  close(fd);
  return (written == len) ? 0 : -1;
}
static void _bpoc_remap_errors(const char *buf, int len, int offset) {
  int i = 0;
  while (i < len) {
    int ls = i, j;
    while (i < len && buf[i] != '\n') i++;
    int le = i;
    if (i < len) i++;
    int skip = 0;
    for (j = ls; j + 11 <= le; j++)
      if (memcmp(buf + j, "_bats_entry", 11) == 0) { skip = 1; break; }
    if (skip) { fwrite(buf + ls, 1, le - ls, stderr); fputc('\n', stderr); continue; }
    int has_dats = 0;
    for (j = ls; j + 5 <= le; j++)
      if (memcmp(buf + j, ".dats", 5) == 0) { has_dats = 1; break; }
    for (j = ls; j < le; ) {
      if (j + 6 <= le && memcmp(buf + j, "build/", 6) == 0) { j += 6; continue; }
      if (j + 5 <= le && memcmp(buf + j, ".sats", 5) == 0) { fputs(".bats", stderr); j += 5; continue; }
      if (j + 5 <= le && memcmp(buf + j, ".dats", 5) == 0) { fputs(".bats", stderr); j += 5; continue; }
      if (has_dats && j + 5 <= le && memcmp(buf + j, "line=", 5) == 0) {
        int num = 0, k = j + 5;
        while (k < le && buf[k] >= '0' && buf[k] <= '9') { num = num * 10 + (buf[k] - '0'); k++; }
        num = num > offset ? num - offset : 0;
        fprintf(stderr, "line=%d", num);
        j = k; continue;
      }
      fputc(buf[j], stderr);
      j++;
    }
    if (le > ls) fputc('\n', stderr);
  }
}
static void _bpoc_handle_stderr(const char *buf, int len, int offset) {
  if (offset > 0) _bpoc_remap_errors(buf, len, offset);
  else write(2, buf, (unsigned)len);
}
/* Check if a flag appears in null-separated cmdline tokens after position */
static int _bpoc_has_flag(const char *buf, int len, int after, const char *flag) {
  int flen = _bpoc_slen(flag);
  int pos = after;
  while (pos < len) {
    int te = pos;
    while (te < len && buf[te] != '\0') te++;
    if (te - pos == flen && memcmp(buf + pos, flag, flen) == 0) return 1;
    pos = te + 1;
  }
  return 0;
}
/* Get value of a flag (next token after the flag). Returns length, 0 if not found */
static int _bpoc_get_flag_val(const char *buf, int len, int after,
                               const char *flag, char *out, int out_max) {
  int flen = _bpoc_slen(flag);
  int pos = after;
  while (pos < len) {
    int te = pos;
    while (te < len && buf[te] != '\0') te++;
    if (te - pos == flen && memcmp(buf + pos, flag, flen) == 0) {
      int vs = te + 1, ve = vs;
      while (ve < len && buf[ve] != '\0') ve++;
      int vl = ve - vs;
      if (vl > 0 && vl < out_max) { memcpy(out, buf + vs, vl); out[vl] = '\0'; return vl; }
      return 0;
    }
    pos = te + 1;
  }
  return 0;
}
/* Inject or update a dependency in bats.toml content.
   Returns new length, or -1 on error. Writes result to out. */
static int _bpoc_inject_dep(const char *src, int slen,
                             const char *pkg, int plen,
                             const char *cst, int clen,
                             char *out, int omax) {
  int oi = 0, si = 0, in_deps = 0, replaced = 0, has_deps = 0;
  char dep_line[512];
  int dlen = 0;
  dep_line[dlen++] = '"';
  for (int j = 0; j < plen; j++) dep_line[dlen++] = pkg[j];
  dep_line[dlen++] = '"';
  dep_line[dlen++] = ' ';
  dep_line[dlen++] = '=';
  dep_line[dlen++] = ' ';
  dep_line[dlen++] = '"';
  for (int j = 0; j < clen; j++) dep_line[dlen++] = cst[j];
  dep_line[dlen++] = '"';
  dep_line[dlen++] = '\n';
  while (si < slen) {
    int ls = si;
    while (si < slen && src[si] != '\n') si++;
    int le = si;
    if (si < slen) si++; /* skip newline */
    int ll = le - ls;
    /* Check for [dependencies] */
    if (ll == 14 && memcmp(src + ls, "[dependencies]", 14) == 0) {
      has_deps = 1; in_deps = 1;
      if (oi + ll + 1 >= omax) return -1;
      memcpy(out + oi, src + ls, ll); oi += ll;
      out[oi++] = '\n';
      continue;
    }
    /* Check for new section start */
    if (ll > 0 && src[ls] == '[') {
      if (in_deps && !replaced) {
        if (oi + dlen >= omax) return -1;
        memcpy(out + oi, dep_line, dlen); oi += dlen;
        replaced = 1;
      }
      in_deps = 0;
    }
    /* Check if line starts with "pkg" = (replace it) */
    if (in_deps && ll > plen + 2 && src[ls] == '"'
        && memcmp(src + ls + 1, pkg, plen) == 0
        && src[ls + 1 + plen] == '"') {
      if (oi + dlen >= omax) return -1;
      memcpy(out + oi, dep_line, dlen); oi += dlen;
      replaced = 1;
      continue;
    }
    /* Copy line as-is */
    if (oi + ll + 1 >= omax) return -1;
    memcpy(out + oi, src + ls, ll); oi += ll;
    out[oi++] = '\n';
  }
  if (in_deps && !replaced) {
    if (oi + dlen >= omax) return -1;
    memcpy(out + oi, dep_line, dlen); oi += dlen;
  }
  if (!has_deps) {
    const char *sect = "\n[dependencies]\n";
    int sectl = 16;
    if (oi + sectl + dlen >= omax) return -1;
    memcpy(out + oi, sect, sectl); oi += sectl;
    memcpy(out + oi, dep_line, dlen); oi += dlen;
  }
  return oi;
}
/* Strip a dependency from bats.toml content.
   Returns new length, or -1 if not found. */
static int _bpoc_strip_dep(const char *src, int slen,
                            const char *pkg, int plen,
                            char *out, int omax) {
  int oi = 0, si = 0, in_deps = 0, found = 0;
  while (si < slen) {
    int ls = si;
    while (si < slen && src[si] != '\n') si++;
    int le = si;
    if (si < slen) si++;
    int ll = le - ls;
    if (ll == 14 && memcmp(src + ls, "[dependencies]", 14) == 0)
      in_deps = 1;
    else if (ll > 0 && src[ls] == '[')
      in_deps = 0;
    if (in_deps && ll > plen + 2 && src[ls] == '"'
        && memcmp(src + ls + 1, pkg, plen) == 0
        && src[ls + 1 + plen] == '"') {
      found = 1;
      continue; /* skip this line */
    }
    if (oi + ll + 1 >= omax) return -1;
    memcpy(out + oi, src + ls, ll); oi += ll;
    out[oi++] = '\n';
  }
  return found ? oi : -1;
}
/* Build cache: check if output is fresh given input mtime */
#include <sys/stat.h>
static long _bpoc_file_mtime(const char *path) {
  struct stat st;
  if (stat(path, &st) == 0) return (long)st.st_mtime;
  return -1;
}
/* Cache file: build/.bats_build_cache
   Format: header line, then input\toutput\tmtime per entry
   Returns 1 if cached and fresh, 0 if needs rebuild */
static int _bpoc_cache_fresh(const char *cache_path,
                              const char *input, const char *output) {
  long cur_mtime = _bpoc_file_mtime(input);
  if (cur_mtime < 0) return 0;
  struct stat ost;
  if (stat(output, &ost) != 0) return 0;
  int cfd = open(cache_path, O_RDONLY);
  if (cfd < 0) return 0;
  char buf[65536];
  int nr = (int)read(cfd, buf, sizeof(buf) - 1);
  close(cfd);
  if (nr <= 0) return 0;
  buf[nr] = '\0';
  int ilen = _bpoc_slen(input);
  int olen = _bpoc_slen(output);
  int i = 0;
  while (i < nr && buf[i] != '\n') i++;
  if (i < nr) i++;
  while (i < nr) {
    int ls = i;
    while (i < nr && buf[i] != '\n') i++;
    int le = i;
    if (i < nr) i++;
    int t1 = ls;
    while (t1 < le && buf[t1] != '\t') t1++;
    if (t1 >= le) continue;
    int t2 = t1 + 1;
    while (t2 < le && buf[t2] != '\t') t2++;
    if (t2 >= le) continue;
    if (t1 - ls != ilen) continue;
    if (memcmp(buf + ls, input, ilen) != 0) continue;
    if (t2 - (t1 + 1) != olen) continue;
    if (memcmp(buf + t1 + 1, output, olen) != 0) continue;
    long cached_mt = 0;
    int k = t2 + 1;
    while (k < le && buf[k] >= '0' && buf[k] <= '9') {
      cached_mt = cached_mt * 10 + (buf[k] - '0');
      k++;
    }
    if (cached_mt == cur_mtime) return 1;
  }
  return 0;
}
/* Record a cache entry (appends to file, creating with header if new) */
static void _bpoc_cache_record(const char *cache_path,
                                const char *input, const char *output) {
  long mt = _bpoc_file_mtime(input);
  if (mt < 0) return;
  struct stat cst;
  int needs_hdr = (stat(cache_path, &cst) != 0);
  int fd = open(cache_path, O_WRONLY|O_CREAT|O_APPEND, 0644);
  if (fd < 0) return;
  if (needs_hdr) {
    const char *hdr = "bats-poc 0.1.0\n";
    write(fd, hdr, _bpoc_slen(hdr));
  }
  write(fd, input, _bpoc_slen(input));
  write(fd, "\t", 1);
  write(fd, output, _bpoc_slen(output));
  write(fd, "\t", 1);
  char mtbuf[32];
  int mi = 0;
  long tmp = mt;
  if (tmp == 0) mtbuf[mi++] = '0';
  else {
    char rev[32]; int ri = 0;
    while (tmp > 0) { rev[ri++] = '0' + (int)(tmp % 10); tmp /= 10; }
    while (ri > 0) mtbuf[mi++] = rev[--ri];
  }
  write(fd, mtbuf, mi);
  write(fd, "\n", 1);
  close(fd);
}
/* Quick freshness check: returns 1 if output exists and is newer than input */
static int _bpoc_is_newer(const char *output, const char *input) {
  long out_mt = _bpoc_file_mtime(output);
  long in_mt = _bpoc_file_mtime(input);
  if (out_mt < 0 || in_mt < 0) return 0;
  return (out_mt >= in_mt) ? 1 : 0;
}
/* Scan a .bats file for #use directives and enqueue package names */
static void _bpoc_scan_uses_to_queue(const char *fpath,
    char queue[][256], int *qt_ptr, int max_q) {
  int fd2 = open(fpath, O_RDONLY);
  if (fd2 < 0) return;
  char fbuf[65536];
  int flen = (int)read(fd2, fbuf, sizeof(fbuf) - 1);
  close(fd2);
  if (flen <= 0) return;
  fbuf[flen] = '\0';
  int fi = 0;
  while (fi < flen) {
    int fls = fi;
    while (fi < flen && fbuf[fi] != '\n') fi++;
    int fle = fi;
    if (fi < flen) fi++;
    int fll = fle - fls;
    if (fll < 8 || fbuf[fls] != '#') continue;
    if (memcmp(fbuf + fls, "#use ", 5) != 0) continue;
    int ups = fls + 5;
    while (ups < fle && fbuf[ups] == ' ') ups++;
    int upe = ups;
    while (upe < fle && fbuf[upe] != ' ') upe++;
    int uplen = upe - ups;
    if (uplen <= 0 || uplen >= 256) continue;
    char upkg[256];
    memcpy(upkg, fbuf + ups, uplen);
    upkg[uplen] = '\0';
    int qt = *qt_ptr;
    int udup = 0;
    for (int q = 0; q < qt; q++) {
      if (strcmp(queue[q], upkg) == 0) { udup = 1; break; }
    }
    if (!udup && qt < max_q) {
      strcpy(queue[qt], upkg);
      *qt_ptr = qt + 1;
    }
  }
}

/* Lock resolution: resolve deps from repository, extract, write bats.lock.
   repo_path: null-terminated path to repository directory.
   Returns 0 on success, -1 on error. */
#include <dirent.h>
static int _bpoc_version_cmp(const char *a, const char *b) {
  /* Compare dot-separated numeric versions */
  while (*a && *b) {
    int va = 0, vb = 0;
    while (*a >= '0' && *a <= '9') { va = va * 10 + (*a - '0'); a++; }
    while (*b >= '0' && *b <= '9') { vb = vb * 10 + (*b - '0'); b++; }
    if (va != vb) return va - vb;
    if (*a == '.') a++;
    if (*b == '.') b++;
    /* If one has 'dev' suffix, it's less than a clean version */
    if (*a == 'd' && *b != 'd') return -1;
    if (*b == 'd' && *a != 'd') return 1;
    if (*a == 'd' && *b == 'd') {
      /* Both dev: compare as strings */
      return strcmp(a, b);
    }
  }
  if (*a) return 1;
  if (*b) return -1;
  return 0;
}

/* Resolved package entry */
typedef struct {
  char name[256];
  char version[64];
} _bpoc_resolved_t;

static int _bpoc_resolve_lock(const char *repo_path) {
  /* Read bats.toml to get [dependencies] */
  int tfd = open("bats.toml", O_RDONLY);
  if (tfd < 0) { fprintf(stderr, "error: cannot open bats.toml\n"); return -1; }
  char toml[8192];
  int tlen = (int)read(tfd, toml, sizeof(toml) - 1);
  close(tfd);
  if (tlen <= 0) { fprintf(stderr, "error: empty bats.toml\n"); return -1; }
  toml[tlen] = '\0';

  /* Parse [dependencies] section to find package names */
  char deps[64][256]; /* max 64 deps */
  int ndeps = 0;

  int in_deps = 0;
  int si = 0;
  while (si < tlen && ndeps < 64) {
    int ls = si;
    while (si < tlen && toml[si] != '\n') si++;
    int le = si;
    if (si < tlen) si++;
    int ll = le - ls;
    if (ll == 14 && memcmp(toml + ls, "[dependencies]", 14) == 0) {
      in_deps = 1; continue;
    }
    if (ll > 0 && toml[ls] == '[') { in_deps = 0; continue; }
    if (!in_deps || ll < 3) continue;
    /* Line should be "pkgname" = "constraint" */
    if (toml[ls] != '"') continue;
    int ne = ls + 1;
    while (ne < le && toml[ne] != '"') ne++;
    int nlen = ne - ls - 1;
    if (nlen <= 0 || nlen >= 256) continue;
    memcpy(deps[ndeps], toml + ls + 1, nlen);
    deps[ndeps][nlen] = '\0';
    ndeps++;
  }

  /* Resolve each dependency */
  _bpoc_resolved_t resolved[256];
  int nresolved = 0;
  char queue[256][256];
  int qh = 0, qt = 0;

  /* Enqueue direct deps from bats.toml */
  for (int i = 0; i < ndeps && qt < 256; i++) {
    strcpy(queue[qt++], deps[i]);
  }

  /* Also scan own source files for #use directives */
  _bpoc_scan_uses_to_queue("src/lib.bats", queue, &qt, 256);
  {
    DIR *bd = opendir("src/bin");
    if (bd) {
      struct dirent *be;
      while ((be = readdir(bd)) != NULL) {
        const char *bn = be->d_name;
        int bnlen = _bpoc_slen(bn);
        if (bnlen > 5 && memcmp(bn + bnlen - 5, ".bats", 5) == 0) {
          char bpath[512];
          snprintf(bpath, sizeof(bpath), "src/bin/%s", bn);
          _bpoc_scan_uses_to_queue(bpath, queue, &qt, 256);
        }
      }
      closedir(bd);
    }
  }

  if (qt == 0) {
    _bpoc_write_file("bats.lock", "", 0);
    fprintf(stderr, "locked 0 packages\n");
    return 0;
  }

  while (qh < qt && nresolved < 256) {
    char pkg[256];
    strcpy(pkg, queue[qh++]);

    /* Check if already resolved */
    int already = 0;
    for (int r = 0; r < nresolved; r++) {
      if (strcmp(resolved[r].name, pkg) == 0) { already = 1; break; }
    }
    if (already) continue;

    /* Build repository path: repo_path/pkg/ */
    char pkg_dir[4096];
    snprintf(pkg_dir, sizeof(pkg_dir), "%s/%s", repo_path, pkg);

    /* Scan for latest version */
    DIR *d = opendir(pkg_dir);
    if (!d) {
      fprintf(stderr, "error: package '%s' not found in repository\n", pkg);
      return -1;
    }

    /* Build prefix: replace / with _ in pkg name */
    char prefix[256];
    int pi = 0;
    for (int j = 0; pkg[j] && pi < 254; j++) {
      prefix[pi++] = (pkg[j] == '/') ? '_' : pkg[j];
    }
    prefix[pi] = '\0';
    int prefix_len = pi;

    char best_ver[64] = "";
    char best_file[4096] = "";
    struct dirent *de_ptr;
    while ((de_ptr = readdir(d)) != NULL) {
      const char *fn = de_ptr->d_name;
      int fnlen = _bpoc_slen(fn);
      /* Match: prefix_VERSION.bats (not .sha256) */
      if (fnlen < prefix_len + 7) continue; /* prefix_ + X.bats */
      if (memcmp(fn, prefix, prefix_len) != 0) continue;
      if (fn[prefix_len] != '_') continue;
      /* Check suffix is .bats (not .bats.sha256) */
      if (fnlen < 5) continue;
      if (memcmp(fn + fnlen - 5, ".bats", 5) != 0) continue;
      if (fnlen > 7 && memcmp(fn + fnlen - 7, ".sha256", 7) == 0) continue;
      /* Extract version string */
      int vstart = prefix_len + 1;
      int vte = fnlen - 5; /* before .bats */
      int vlen = vte - vstart;
      if (vlen <= 0 || vlen >= 64) continue;
      char ver[64];
      memcpy(ver, fn + vstart, vlen);
      ver[vlen] = '\0';
      /* Skip dev versions */
      int is_dev = 0;
      for (int k = 0; k < vlen - 2; k++) {
        if (ver[k] == 'd' && ver[k+1] == 'e' && ver[k+2] == 'v') {
          is_dev = 1; break;
        }
      }
      if (is_dev) continue;
      /* Compare to current best */
      if (best_ver[0] == '\0' || _bpoc_version_cmp(ver, best_ver) > 0) {
        strcpy(best_ver, ver);
        snprintf(best_file, sizeof(best_file), "%s/%s", pkg_dir, fn);
      }
    }
    closedir(d);

    if (best_ver[0] == '\0') {
      fprintf(stderr, "error: no version found for '%s'\n", pkg);
      return -1;
    }

    /* Record resolved */
    strcpy(resolved[nresolved].name, pkg);
    strcpy(resolved[nresolved].version, best_ver);
    nresolved++;

    /* Extract to bats_modules/pkg/ if not already there */
    char check_path[4096];
    snprintf(check_path, sizeof(check_path), "bats_modules/%s/src/lib.bats", pkg);
    struct stat cst;
    if (stat(check_path, &cst) != 0) {
      /* Need to extract */
      char mkdir_cmd[4096];
      snprintf(mkdir_cmd, sizeof(mkdir_cmd), "mkdir -p bats_modules/%s", pkg);
      system(mkdir_cmd);
      char unzip_cmd[8192];
      snprintf(unzip_cmd, sizeof(unzip_cmd),
        "unzip -o -q '%s' -d 'bats_modules/%s'", best_file, pkg);
      if (system(unzip_cmd) != 0) {
        fprintf(stderr, "error: failed to extract '%s'\n", best_file);
        return -1;
      }
    }

    /* Scan transitive deps from extracted bats.toml */
    char dep_toml_path[4096];
    snprintf(dep_toml_path, sizeof(dep_toml_path),
      "bats_modules/%s/bats.toml", pkg);
    int dtfd = open(dep_toml_path, O_RDONLY);
    if (dtfd >= 0) {
      char dt[4096];
      int dtlen = (int)read(dtfd, dt, sizeof(dt) - 1);
      close(dtfd);
      if (dtlen > 0) {
        dt[dtlen] = '\0';
        int dt_in_deps = 0;
        int dsi = 0;
        while (dsi < dtlen) {
          int dls = dsi;
          while (dsi < dtlen && dt[dsi] != '\n') dsi++;
          int dle = dsi;
          if (dsi < dtlen) dsi++;
          int dll = dle - dls;
          if (dll == 14 && memcmp(dt + dls, "[dependencies]", 14) == 0) {
            dt_in_deps = 1; continue;
          }
          if (dll > 0 && dt[dls] == '[') { dt_in_deps = 0; continue; }
          if (!dt_in_deps || dll < 3 || dt[dls] != '"') continue;
          int dne = dls + 1;
          while (dne < dle && dt[dne] != '"') dne++;
          int dnlen = dne - dls - 1;
          if (dnlen <= 0 || dnlen >= 256) continue;
          char tdep[256];
          memcpy(tdep, dt + dls + 1, dnlen);
          tdep[dnlen] = '\0';
          /* Check not already queued or resolved */
          int dup = 0;
          for (int r = 0; r < nresolved; r++) {
            if (strcmp(resolved[r].name, tdep) == 0) { dup = 1; break; }
          }
          if (!dup) {
            for (int q = qh; q < qt; q++) {
              if (strcmp(queue[q], tdep) == 0) { dup = 1; break; }
            }
          }
          if (!dup && qt < 256) {
            strcpy(queue[qt++], tdep);
          }
        }
      }
    }

    /* Also scan src/lib.bats for #use directives (transitive deps) */
    char src_path[4096];
    snprintf(src_path, sizeof(src_path),
      "bats_modules/%s/src/lib.bats", pkg);
    int sfd = open(src_path, O_RDONLY);
    if (sfd >= 0) {
      char sbuf[65536];
      int slen = (int)read(sfd, sbuf, sizeof(sbuf) - 1);
      close(sfd);
      if (slen > 0) {
        sbuf[slen] = '\0';
        int si2 = 0;
        while (si2 < slen) {
          /* Look for "#use " at start of line */
          int lstart = si2;
          while (si2 < slen && sbuf[si2] != '\n') si2++;
          int lte = si2;
          if (si2 < slen) si2++;
          int llen = lte - lstart;
          if (llen < 10 || sbuf[lstart] != '#') continue;
          if (memcmp(sbuf + lstart, "#use ", 5) != 0) continue;
          /* Extract package name: #use <pkg> as <alias> */
          int ps = lstart + 5;
          /* Skip leading whitespace */
          while (ps < lte && sbuf[ps] == ' ') ps++;
          int pe = ps;
          while (pe < lte && sbuf[pe] != ' ') pe++;
          int plen = pe - ps;
          if (plen <= 0 || plen >= 256) continue;
          char use_pkg[256];
          memcpy(use_pkg, sbuf + ps, plen);
          use_pkg[plen] = '\0';
          /* Check not already queued or resolved */
          int dup2 = 0;
          for (int r = 0; r < nresolved; r++) {
            if (strcmp(resolved[r].name, use_pkg) == 0) { dup2 = 1; break; }
          }
          if (!dup2) {
            for (int q = qh; q < qt; q++) {
              if (strcmp(queue[q], use_pkg) == 0) { dup2 = 1; break; }
            }
          }
          if (!dup2 && qt < 256) {
            strcpy(queue[qt++], use_pkg);
          }
        }
      }
    }
  }

  /* Write bats.lock */
  char lock[65536];
  int li = 0;
  for (int r = 0; r < nresolved; r++) {
    int nlen = _bpoc_slen(resolved[r].name);
    int vlen = _bpoc_slen(resolved[r].version);
    if (li + nlen + 1 + vlen + 1 >= 65536) break;
    memcpy(lock + li, resolved[r].name, nlen); li += nlen;
    lock[li++] = ' ';
    memcpy(lock + li, resolved[r].version, vlen); li += vlen;
    lock[li++] = '\n';
  }
  _bpoc_write_file("bats.lock", lock, li);
  fprintf(stderr, "locked %d packages\n", nresolved);
  return 0;
}

static void _bpoc_print_completions_bash(void) {
    fputs(
        "_bats_poc() {\n"
        "    local cur prev\n"
        "    cur=\"${COMP_WORDS[COMP_CWORD]}\"\n"
        "    prev=\"${COMP_WORDS[COMP_CWORD-1]}\"\n"
        "\n"
        "    local commands=\"init lock add remove build run test check tree upload clean completions\"\n"
        "\n"
        "    local i cmd=\"\"\n"
        "    for ((i=1; i < COMP_CWORD; i++)); do\n"
        "        case \"${COMP_WORDS[i]}\" in\n"
        "            --run-in)\n"
        "                ((i++))\n"
        "                ;;\n"
        "            -*)\n"
        "                ;;\n"
        "            *)\n"
        "                cmd=\"${COMP_WORDS[i]}\"\n"
        "                break\n"
        "                ;;\n"
        "        esac\n"
        "    done\n"
        "\n"
        "    if [[ -z \"$cmd\" ]]; then\n"
        "        if [[ \"$cur\" == -* ]]; then\n"
        "            COMPREPLY=($(compgen -W \"--version -V --help -h --run-in --quiet -q\" -- \"$cur\"))\n"
        "        else\n"
        "            COMPREPLY=($(compgen -W \"$commands\" -- \"$cur\"))\n"
        "        fi\n"
        "        return\n"
        "    fi\n"
        "\n"
        "    case \"$prev\" in\n"
        "        --repository|--run-in)\n"
        "            COMPREPLY=($(compgen -d -- \"$cur\"))\n"
        "            return\n"
        "            ;;\n"
        "        --only)\n"
        "            COMPREPLY=($(compgen -W \"native wasm\" -- \"$cur\"))\n"
        "            return\n"
        "            ;;\n"
        "        --bin|--filter)\n"
        "            return\n"
        "            ;;\n"
        "    esac\n"
        "\n"
        "    case \"$cmd\" in\n"
        "        init)\n"
        "            if [[ \"$cur\" == -* ]]; then\n"
        "                COMPREPLY=($(compgen -W \"--help -h\" -- \"$cur\"))\n"
        "            else\n"
        "                COMPREPLY=($(compgen -W \"binary library\" -- \"$cur\"))\n"
        "            fi\n"
        "            ;;\n"
        "        lock)\n"
        "            COMPREPLY=($(compgen -W \"--repository --help -h\" -- \"$cur\"))\n"
        "            ;;\n"
        "        add)\n"
        "            COMPREPLY=($(compgen -W \"--repository --help -h\" -- \"$cur\"))\n"
        "            ;;\n"
        "        remove)\n"
        "            COMPREPLY=($(compgen -W \"--repository --help -h\" -- \"$cur\"))\n"
        "            ;;\n"
        "        build)\n"
        "            COMPREPLY=($(compgen -W \"--only --verbose -v --repository --help -h\" -- \"$cur\"))\n"
        "            ;;\n"
        "        run)\n"
        "            COMPREPLY=($(compgen -W \"--bin --verbose -v --repository --help -h\" -- \"$cur\"))\n"
        "            ;;\n"
        "        test)\n"
        "            COMPREPLY=($(compgen -W \"--filter --only --verbose -v --repository --help -h\" -- \"$cur\"))\n"
        "            ;;\n"
        "        check)\n"
        "            COMPREPLY=($(compgen -W \"--verbose -v --repository --help -h\" -- \"$cur\"))\n"
        "            ;;\n"
        "        tree)\n"
        "            COMPREPLY=($(compgen -W \"--repository --help -h\" -- \"$cur\"))\n"
        "            ;;\n"
        "        upload)\n"
        "            COMPREPLY=($(compgen -W \"--repository --help -h\" -- \"$cur\"))\n"
        "            ;;\n"
        "        clean)\n"
        "            COMPREPLY=($(compgen -W \"--help -h\" -- \"$cur\"))\n"
        "            ;;\n"
        "        completions)\n"
        "            COMPREPLY=($(compgen -W \"bash zsh fish\" -- \"$cur\"))\n"
        "            ;;\n"
        "    esac\n"
        "}\n"
        "complete -F _bats_poc bats-poc\n"
    , stdout);
}
static void _bpoc_print_completions_zsh(void) {
    fputs(
        "#compdef bats-poc\n"
        "\n"
        "_bats_poc() {\n"
        "    local -a commands\n"
        "    commands=(\n"
        "        'init:Create a new project'\n"
        "        'lock:Generate bats.lock'\n"
        "        'add:Add a dep" "en" "dency'\n"
        "        'remove:Remove a dep" "en" "dency'\n"
        "        'build:Build the project'\n"
        "        'run:Build and run a binary'\n"
        "        'test:Run tests'\n"
        "        'check:Type-check the project'\n"
        "        'tree:Show dep" "en" "dency tree'\n"
        "        'upload:Upload a library'\n"
        "        'clean:Remove artifacts'\n"
        "        'completions:Generate shell completions'\n"
        "    )\n"
        "\n"
        "    _arguments -C \\\n"
        "        '--version[Show version]' \\\n"
        "        '-V[Show version]' \\\n"
        "        '--help[Show help]' \\\n"
        "        '-h[Show help]' \\\n"
        "        '--run-in[Run in directory]:directory:_directories' \\\n"
        "        '--quiet[Suppress progress output]' \\\n"
        "        '-q[Suppress progress output]' \\\n"
        "        '1:command:->command' \\\n"
        "        '*::args:->args'\n"
        "\n"
        "    case $state in\n"
        "        command)\n"
        "            _describe 'command' commands\n"
        "            ;;\n"
        "        args)\n"
        "            case ${words[1]} in\n"
        "                init)\n"
        "                    _arguments \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]' \\\n"
        "                        '1:kind:(binary library)'\n"
        "                    ;;\n"
        "                lock)\n"
        "                    _arguments \\\n"
        "                        '--repository[Repository directory]:directory:_directories' \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]'\n"
        "                    ;;\n"
        "                add)\n"
        "                    _arguments \\\n"
        "                        '--repository[Repository directory]:directory:_directories' \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]' \\\n"
        "                        '1:package:' \\\n"
        "                        '2:constraint:'\n"
        "                    ;;\n"
        "                remove)\n"
        "                    _arguments \\\n"
        "                        '--repository[Repository directory]:directory:_directories' \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]' \\\n"
        "                        '1:package:'\n"
        "                    ;;\n"
        "                build)\n"
        "                    _arguments \\\n"
        "                        '--only[Target platform]:target:(native wasm)' \\\n"
        "                        '--verbose[Verbose output]' \\\n"
        "                        '-v[Verbose output]' \\\n"
        "                        '--repository[Repository directory]:directory:_directories' \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]'\n"
        "                    ;;\n"
        "                run)\n"
        "                    _arguments \\\n"
        "                        '--bin[Binary to run]:name:' \\\n"
        "                        '--verbose[Verbose output]' \\\n"
        "                        '-v[Verbose output]' \\\n"
        "                        '--repository[Repository directory]:directory:_directories' \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]'\n"
        "                    ;;\n"
        "                test)\n"
        "                    _arguments \\\n"
        "                        '--filter[Filter tests by name]:pattern:' \\\n"
        "                        '--only[Target platform]:target:(native wasm)' \\\n"
        "                        '--verbose[Verbose output]' \\\n"
        "                        '-v[Verbose output]' \\\n"
        "                        '--repository[Repository directory]:directory:_directories' \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]'\n"
        "                    ;;\n"
        "                check)\n"
        "                    _arguments \\\n"
        "                        '--verbose[Verbose output]' \\\n"
        "                        '-v[Verbose output]' \\\n"
        "                        '--repository[Repository directory]:directory:_directories' \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]'\n"
        "                    ;;\n"
        "                tree)\n"
        "                    _arguments \\\n"
        "                        '--repository[Repository directory]:directory:_directories' \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]'\n"
        "                    ;;\n"
        "                upload)\n"
        "                    _arguments \\\n"
        "                        '--repository[Repository directory]:directory:_directories' \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]'\n"
        "                    ;;\n"
        "                clean)\n"
        "                    _arguments \\\n"
        "                        '--help[Show help]' \\\n"
        "                        '-h[Show help]'\n"
        "                    ;;\n"
        "                completions)\n"
        "                    _arguments \\\n"
        "                        '1:shell:(bash zsh fish)'\n"
        "                    ;;\n"
        "            esac\n"
        "            ;;\n"
        "    esac\n"
        "}\n"
        "\n"
        "_bats_poc\n"
    , stdout);
}
static void _bpoc_print_completions_fish(void) {
    fputs(
        "complete -c bats-poc -f\n"
        "\n"
        "function __bats_poc_no_subcommand\n"
        "    set -l cmd (commandline -opc)\n"
        "    set -l skip_next 0\n"
        "    for c in $cmd[2..]\n"
        "        if test $skip_next -eq 1\n"
        "            set skip_next 0\n"
        "            continue\n"
        "        en" "d\n"
        "        switch $c\n"
        "            case --run-in\n"
        "                set skip_next 1\n"
        "            case '-*'\n"
        "                continue\n"
        "            case '*'\n"
        "                return 1\n"
        "        en" "d\n"
        "    en" "d\n"
        "    return 0\n"
        "en" "d\n"
        "\n"
        "function __bats_poc_using_subcommand\n"
        "    set -l cmd (commandline -opc)\n"
        "    set -l skip_next 0\n"
        "    for c in $cmd[2..]\n"
        "        if test $skip_next -eq 1\n"
        "            set skip_next 0\n"
        "            continue\n"
        "        en" "d\n"
        "        switch $c\n"
        "            case --run-in\n"
        "                set skip_next 1\n"
        "            case '-*'\n"
        "                continue\n"
        "            case '*'\n"
        "                test \"$c\" = \"$argv[1]\"\n"
        "                return $status\n"
        "        en" "d\n"
        "    en" "d\n"
        "    return 1\n"
        "en" "d\n"
        "\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -l version -s V -d 'Show version'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -l help -s h -d 'Show help'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -l run-in -rF -d 'Run in directory'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -l quiet -s q -d 'Suppress progress output'\n"
        "\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a init -d 'Create a new project'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a lock -d 'Generate bats.lock'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a add -d 'Add a dep" "en" "dency'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a remove -d 'Remove a dep" "en" "dency'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a build -d 'Build the project'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a run -d 'Build and run a binary'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a test -d 'Run tests'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a check -d 'Type-check the project'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a tree -d 'Show dep" "en" "dency tree'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a upload -d 'Upload a library'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a clean -d 'Remove artifacts'\n"
        "complete -c bats-poc -n __bats_poc_no_subcommand -a completions -d 'Shell completions'\n"
        "\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand init' -a 'binary library'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand lock' -l repository -rF -d 'Repository directory'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand add' -l repository -rF -d 'Repository directory'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand remove' -l repository -rF -d 'Repository directory'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand build' -l only -ra 'native wasm' -d 'Target platform'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand build' -l verbose -s v -d 'Verbose output'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand build' -l repository -rF -d 'Repository directory'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand run' -l bin -r -d 'Binary to run'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand run' -l verbose -s v -d 'Verbose output'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand run' -l repository -rF -d 'Repository directory'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand test' -l filter -r -d 'Filter tests by name'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand test' -l only -ra 'native wasm' -d 'Target platform'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand test' -l verbose -s v -d 'Verbose output'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand test' -l repository -rF -d 'Repository directory'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand check' -l verbose -s v -d 'Verbose output'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand check' -l repository -rF -d 'Repository directory'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand tree' -l repository -rF -d 'Repository directory'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand upload' -l repository -rF -d 'Repository directory'\n"
        "complete -c bats-poc -n '__bats_poc_using_subcommand completions' -a 'bash zsh fish'\n"
    , stdout);
}
%}

end

(* ============================================================
   Helpers
   ============================================================ *)

(* Copy a string literal into a builder *)
fun put_lit {fuel:nat} .<fuel>.
  (b: !$B.builder, p: ptr, i: int, len: int, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if i >= len then ()
  else let
    val c = $UNSAFE begin $extfcall(int, "_bpoc_byte_at", p, i) end
    val () = $B.put_byte(b, c)
  in put_lit(b, p, i + 1, len, fuel - 1) end

fn bput(b: !$B.builder, s: string): void = let
  val p = $UNSAFE begin $UNSAFE.castvwtp1{ptr}(s) end
  val len = $UNSAFE begin $extfcall(int, "_bpoc_slen", p) end
in put_lit(b, p, 0, len, $AR.checked_nat(len + 1)) end

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

fun print_borrow {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (buf: !$A.borrow(byte, l, n), i: int, len: int, max: int n,
   fuel: int fuel): void =
  if fuel <= 0 then ()
  else if i >= len then ()
  else let
    val b = src_byte(buf, i, max)
    val () = print_char(int2char0(b))
  in print_borrow(buf, i + 1, len, max, fuel - 1) end

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
   Build pipeline: helpers
   ============================================================ *)

(* Copy bytes from a frozen borrow into a builder *)
fun copy_to_builder {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (src: !$A.borrow(byte, l, n), start: int, len: int, max: int n,
   dst: !$B.builder, fuel: int fuel): void =
  if fuel <= 0 then ()
  else if start >= len then ()
  else let
    val b = src_byte(src, start, max)
    val () = $B.put_byte(dst, b)
  in copy_to_builder(src, start + 1, len, max, dst, fuel - 1) end

(* Find start of basename in a null-terminated path (after last '/') *)
fun find_basename_start {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (bv: !$A.borrow(byte, l, n), pos: int, max: int n,
   last: int, fuel: int fuel): int =
  if fuel <= 0 then last + 1
  else let
    val b = src_byte(bv, pos, max)
  in
    if $AR.eq_int_int(b, 0) then last + 1
    else if $AR.eq_int_int(b, 47) then
      find_basename_start(bv, pos + 1, max, pos, fuel - 1)
    else find_basename_start(bv, pos + 1, max, last, fuel - 1)
  end

(* Find null terminator in a borrow *)
fun find_null_bv {l:agz}{n:pos}{fuel:nat} .<fuel>.
  (bv: !$A.borrow(byte, l, n), pos: int, max: int n,
   fuel: int fuel): int =
  if fuel <= 0 then pos
  else let
    val b = src_byte(bv, pos, max)
  in
    if $AR.eq_int_int(b, 0) then pos
    else find_null_bv(bv, pos + 1, max, fuel - 1)
  end

(* Run a shell command. cmd_b is CONSUMED. Returns exit code.
   When remap_offset > 0, stderr is remapped: strip build/, .dats->.bats, adjust line=N *)
fn run_sh(cmd_b: $B.builder, remap_offset: int): int = let
  val @(cmd_arr, cmd_len) = $B.to_arr(cmd_b)
  val @(fz_cmd, bv_cmd) = $A.freeze<byte>(cmd_arr)
  val _verbose = $UNSAFE begin $extfcall(int, "_bpoc_is_verbose") end
  val () = (if _verbose > 0 then let
    val () = print! ("  + ")
    val () = print_borrow(bv_cmd, 0, cmd_len, 65536,
      $AR.checked_nat(cmd_len + 1))
  in print_newline() end else ())
  (* /bin/sh = 7 bytes *)
  val sh_path = $A.alloc<byte>(7)
  val () = $A.write_byte(sh_path, 0, 47)
  val () = $A.write_byte(sh_path, 1, 98)
  val () = $A.write_byte(sh_path, 2, 105)
  val () = $A.write_byte(sh_path, 3, 110)
  val () = $A.write_byte(sh_path, 4, 47)
  val () = $A.write_byte(sh_path, 5, 115)
  val () = $A.write_byte(sh_path, 6, 104)
  val @(fz_sh, bv_sh) = $A.freeze<byte>(sh_path)
  (* argv: "sh\0-c\0<cmd>\0" *)
  val argv_b = $B.create()
  val () = $B.put_byte(argv_b, 115)
  val () = $B.put_byte(argv_b, 104)
  val () = $B.put_byte(argv_b, 0)
  val () = $B.put_byte(argv_b, 45)
  val () = $B.put_byte(argv_b, 99)
  val () = $B.put_byte(argv_b, 0)
  val () = copy_to_builder(bv_cmd, 0, cmd_len, 65536, argv_b,
    $AR.checked_nat(cmd_len + 1))
  val () = $B.put_byte(argv_b, 0)
  val @(argv_arr, _) = $B.to_arr(argv_b)
  val @(fz_a, bv_a) = $A.freeze<byte>(argv_arr)
  (* envp: empty *)
  val envp = $A.alloc<byte>(1)
  val () = $A.write_byte(envp, 0, 0)
  val @(fz_e, bv_e) = $A.freeze<byte>(envp)
  val sr = $P.spawn(bv_sh, 7, bv_a, 3, bv_e, 0,
    $P.dev_null(), $P.dev_null(), $P.pipe_new())
  val () = $A.drop<byte>(fz_sh, bv_sh)
  val () = $A.free<byte>($A.thaw<byte>(fz_sh))
  val () = $A.drop<byte>(fz_a, bv_a)
  val () = $A.free<byte>($A.thaw<byte>(fz_a))
  val () = $A.drop<byte>(fz_e, bv_e)
  val () = $A.free<byte>($A.thaw<byte>(fz_e))
  val () = $A.drop<byte>(fz_cmd, bv_cmd)
  val () = $A.free<byte>($A.thaw<byte>(fz_cmd))
in
  case+ sr of
  | ~$R.ok(sp) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = sp
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(sout_p)
      val+ ~$P.pipe_fd(err_fd) = serr_p
      val eb = $A.alloc<byte>(4096)
      val err_r = $F.file_read(err_fd, eb, 4096)
      val elen = (case+ err_r of
        | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val ecr = $F.file_close(err_fd)
      val () = $R.discard<int><int>(ecr)
      val wr = $P.child_wait(child)
      val ec = (case+ wr of
        | ~$R.ok(n) => n | ~$R.err(_) => ~1): int
    in
      if ec <> 0 then let
        val () = $UNSAFE begin $extfcall(void, "_bpoc_handle_stderr",
          $UNSAFE.castvwtp1{ptr}(eb), elen, remap_offset) end
        val () = $A.free<byte>(eb)
      in ec end
      else let
        val () = $A.free<byte>(eb)
      in 0 end
    end
  | ~$R.err(_) => ~1
end

(* Write builder contents to file via C helper. builder is CONSUMED.
   Path borrow must contain a null-terminated path. *)
fn write_file_from_builder {lp:agz}{np:pos}
  (path_bv: !$A.borrow(byte, lp, np), path_len: int np,
   content_b: $B.builder): int = let
  val @(content_arr, content_len) = $B.to_arr(content_b)
  val @(fz_c, bv_c) = $A.freeze<byte>(content_arr)
  val p_path = $UNSAFE begin $UNSAFE.castvwtp1{ptr}(path_bv) end
  val p_data = $UNSAFE begin $UNSAFE.castvwtp1{ptr}(bv_c) end
  val rc = $UNSAFE begin $extfcall(int, "_bpoc_write_file",
    p_path, p_data, content_len) end
  val () = $A.drop<byte>(fz_c, bv_c)
  val () = $A.free<byte>($A.thaw<byte>(fz_c))
in rc end

(* Preprocess one .bats file: read -> lex -> emit -> write .sats + .dats
   All three path borrows must be null-terminated builder arrays (65536) *)
fn preprocess_one
  {l1:agz}{l2:agz}{l3:agz}
  (src_bv: !$A.borrow(byte, l1, 65536),
   sats_bv: !$A.borrow(byte, l2, 65536),
   dats_bv: !$A.borrow(byte, l3, 65536)): int = let
  (* Cache check: if .sats is newer than .bats source, skip preprocessing *)
  val fresh = $UNSAFE begin
    $extfcall(int, "_bpoc_is_newer",
      $UNSAFE.castvwtp1{ptr}(sats_bv),
      $UNSAFE.castvwtp1{ptr}(src_bv))
  end
in
  if fresh > 0 then 0
  else let
  val or = $F.file_open(src_bv, 65536, 0, 0)
in
  case+ or of
  | ~$R.ok(fd) => let
      val buf = $A.alloc<byte>(65536)
      val rr = $F.file_read(fd, buf, 65536)
      val nbytes = (case+ rr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val cr = $F.file_close(fd)
      val () = $R.discard<int><int>(cr)
      val @(fz_src, bv_src) = $A.freeze<byte>(buf)
      val @(span_arr, _span_len, span_count) = do_lex(bv_src, nbytes, 65536)
      val @(fz_sp, bv_sp) = $A.freeze<byte>(span_arr)
      val @(sats_arr, sats_len, dats_arr, dats_len, _pre) =
        do_emit(bv_src, nbytes, 65536, bv_sp, 65536, span_count)
      val () = $A.drop<byte>(fz_sp, bv_sp)
      val () = $A.free<byte>($A.thaw<byte>(fz_sp))
      val () = $A.drop<byte>(fz_src, bv_src)
      val () = $A.free<byte>($A.thaw<byte>(fz_src))
      (* Write .sats *)
      val sb = $B.create()
      val @(fz_s, bv_s) = $A.freeze<byte>(sats_arr)
      val () = copy_to_builder(bv_s, 0, sats_len, 65536, sb,
        $AR.checked_nat(sats_len + 1))
      val () = $A.drop<byte>(fz_s, bv_s)
      val () = $A.free<byte>($A.thaw<byte>(fz_s))
      val r1 = write_file_from_builder(sats_bv, 65536, sb)
      (* Write .dats - prepend self-staload *)
      val db = $B.create()
      val bn_start = find_basename_start(sats_bv, 0, 65536, ~1, 4096)
      val bn_end = find_null_bv(sats_bv, bn_start, 65536, 4096)
      val () = bput(db, "staload \"./")
      val () = copy_to_builder(sats_bv, bn_start, bn_end, 65536, db,
        $AR.checked_nat(bn_end - bn_start + 1))
      val () = bput(db, "\"\n")
      val @(fz_d, bv_d) = $A.freeze<byte>(dats_arr)
      val () = copy_to_builder(bv_d, 0, dats_len, 65536, db,
        $AR.checked_nat(dats_len + 1))
      val () = $A.drop<byte>(fz_d, bv_d)
      val () = $A.free<byte>($A.thaw<byte>(fz_d))
      val r2 = write_file_from_builder(dats_bv, 65536, db)
    in
      if r1 = 0 then (if r2 = 0 then 0 else ~1) else ~1
    end
  | ~$R.err(_) => ~1
end end

(* ============================================================
   Build pipeline: do_build
   ============================================================ *)

(* Build a null-terminated path array from string.
   Returns arr(byte, l, 65536) for some l. Caller must free. *)
fn str_to_path_arr(s: string): [l:agz] $A.arr(byte, l, 65536) = let
  val b = $B.create()
  val () = bput(b, s)
  val () = $B.put_byte(b, 0)
  val @(arr, _) = $B.to_arr(b)
in arr end

(* ============================================================
   clean: remove build/ and dist/ directories
   ============================================================ *)
fn do_clean(): void = let
  val cmd = $B.create()
  val () = bput(cmd, "rm -rf build dist docs")
  val rc = run_sh(cmd, 0)
in
  if rc <> 0 then println! ("error: clean failed")
  else println! ("cleaned build/, dist/, and docs/")
end

(* ============================================================
   lock: read bats.lock and verify it exists
   ============================================================ *)
fn do_lock(): void = let
  (* Check if --repository was specified *)
  val repo_buf = $A.alloc<byte>(4096)
  val rplen = $UNSAFE begin
    $extfcall(int, "_bpoc_get_repo",
      $UNSAFE.castvwtp1{ptr}(repo_buf), 4096)
  end
in
  if rplen > 0 then let
    (* Full lock resolution with repository *)
    val rc = $UNSAFE begin
      $extfcall(int, "_bpoc_resolve_lock",
        $UNSAFE.castvwtp1{ptr}(repo_buf))
    end
    val () = $A.free<byte>(repo_buf)
  in
    if rc <> 0 then println! ("error: lock resolution failed")
    else ()
  end
  else let
    (* No repository - just read existing lockfile *)
    val () = $A.free<byte>(repo_buf)
    val la = str_to_path_arr("bats.lock")
    val @(fz_la, bv_la) = $A.freeze<byte>(la)
    val lock_or = $F.file_open(bv_la, 65536, 0, 0)
    val () = $A.drop<byte>(fz_la, bv_la)
    val () = $A.free<byte>($A.thaw<byte>(fz_la))
  in
    case+ lock_or of
    | ~$R.ok(lfd) => let
        val lock_buf = $A.alloc<byte>(65536)
        val lr = $F.file_read(lfd, lock_buf, 65536)
        val lock_len = (case+ lr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
        val lcr = $F.file_close(lfd)
        val () = $R.discard<int><int>(lcr)
      in
        if lock_len > 0 then let
          val @(fz_lb, bv_lb) = $A.freeze<byte>(lock_buf)
          val () = println! ("bats.lock:")
          val () = print_borrow(bv_lb, 0, lock_len, 65536,
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

fn do_build(release: int): void = let
  (* Step 1: mkdir build directories *)
  val cmd = $B.create()
  val () = bput(cmd, "mkdir -p build/src/bin build/bats_modules dist/debug dist/release")
  val r0 = run_sh(cmd, 0)
  val () = (if r0 <> 0 then println! ("error: mkdir failed") else ())
in
  if r0 <> 0 then ()
  else let
    (* Step 2: Get PATSHOME *)
    val phbuf = $A.alloc<byte>(512)
    val ph_key = $A.alloc<byte>(8)
    val () = $A.write_byte(ph_key, 0, 80)   (* P *)
    val () = $A.write_byte(ph_key, 1, 65)   (* A *)
    val () = $A.write_byte(ph_key, 2, 84)   (* T *)
    val () = $A.write_byte(ph_key, 3, 83)   (* S *)
    val () = $A.write_byte(ph_key, 4, 72)   (* H *)
    val () = $A.write_byte(ph_key, 5, 79)   (* O *)
    val () = $A.write_byte(ph_key, 6, 77)   (* M *)
    val () = $A.write_byte(ph_key, 7, 69)   (* E *)
    val @(fz_ph, bv_ph) = $A.freeze<byte>(ph_key)
    val ph_r = $E.get(bv_ph, 8, phbuf, 512)
    val () = $A.drop<byte>(fz_ph, bv_ph)
    val () = $A.free<byte>($A.thaw<byte>(fz_ph))
    val phlen = (case+ ph_r of
      | ~$R.some(n) => n | ~$R.none() => 0): int
  in
    if phlen <= 0 then let
      val () = $A.free<byte>(phbuf)
    in println! ("error: PATSHOME not set") end
    else let
      val @(fz_patshome, bv_patshome) = $A.freeze<byte>(phbuf)

      (* Step 3: Scan bats_modules/ for deps and preprocess *)
      val bm_arr = str_to_path_arr("bats_modules")
      val @(fz_bm, bv_bm) = $A.freeze<byte>(bm_arr)
      val bmdir_r = $F.dir_open(bv_bm, 65536)
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
                    else let
                      val () = print! ("  preprocessed dep: ")
                      val () = print_borrow(bv_e, 0, elen, 256, $AR.checked_nat(elen + 1))
                    in print_newline() end)
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

      (* Step 4: Preprocess src/bin/*.bats *)
      val sb_arr = str_to_path_arr("src/bin")
      val @(fz_sb, bv_sb) = $A.freeze<byte>(sb_arr)
      val sbdir_r = $F.dir_open(bv_sb, 65536)
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
                    else let
                      val () = print! ("  preprocessed: src/bin/")
                      val () = print_borrow(bv_e, 0, elen, 256, $AR.checked_nat(elen + 1))
                    in print_newline() end)
                    (* Step 5: Generate synthetic entry *)
                    val entry = $B.create()
                    val () = bput(entry, "staload \"./src/bin/")
                    val () = copy_to_builder(bv_e, 0, stem_len, 256, entry,
                      $AR.checked_nat(stem_len + 1))
                    val () = bput(entry, ".sats\"\n")
                    (* dynload all dep modules *)
                    val bm2_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm2, bv_bm2) = $A.freeze<byte>(bm2_arr)
                    val bdir2 = $F.dir_open(bv_bm2, 65536)
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
                    val ew = write_file_from_builder(bv_ep, 65536, entry)
                    val () = $A.drop<byte>(fz_ep, bv_ep)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ep))
                    val () = (if ew <> 0 then
                      println! ("error: failed to write synthetic entry")
                      else println! ("  generated synthetic entry"))

                    (* Step 6: Run patsopt on all .dats files *)
                    (* patsopt for dep modules *)
                    val bm3_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm3, bv_bm3) = $A.freeze<byte>(bm3_arr)
                    val bdir3 = $F.dir_open(bv_bm3, 65536)
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
                                  val pc = $B.create()
                                  val () = bput(pc, "PATSHOME=")
                                  val () = copy_to_builder(ph, 0, phlen, 512, pc,
                                    $AR.checked_nat(phlen + 1))
                                  val () = $B.put_byte(pc, 32)
                                  val () = copy_to_builder(ph, 0, phlen, 512, pc,
                                    $AR.checked_nat(phlen + 1))
                                  val () = bput(pc, "/bin/patsopt -IATS build -IATS build/src -IATS build/bats_modules -o build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pc,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(pc, "/src/lib_dats.c -d build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, pc,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(pc, "/src/lib.dats")
                                  val rc = run_sh(pc, 1)
                                  val () = (if rc <> 0 then let
                                    val () = print! ("error: patsopt failed for dep ")
                                    val () = print_borrow(bv_de, 0, dlen, 256,
                                      $AR.checked_nat(dlen + 1))
                                  in print_newline() end
                                  else let
                                    val () = print! ("  patsopt: ")
                                    val () = print_borrow(bv_de, 0, dlen, 256,
                                      $AR.checked_nat(dlen + 1))
                                  in print_newline() end)
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

                    (* patsopt for the binary *)
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
                    val () = (if rbp <> 0 then
                      println! ("error: patsopt failed for binary")
                      else println! ("  patsopt: binary"))

                    (* patsopt for synthetic entry *)
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
                    val () = (if rep <> 0 then
                      println! ("error: patsopt failed for entry")
                      else println! ("  patsopt: entry"))

                    (* Step 7: clang compile all _dats.c *)
                    (* Compile deps *)
                    val bm4_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm4, bv_bm4) = $A.freeze<byte>(bm4_arr)
                    val bdir4 = $F.dir_open(bv_bm4, 65536)
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
                                  val cc = $B.create()
                                  val () = bput(cc, "PATH=/usr/bin:/usr/local/bin:/bin cc -c -o build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, cc,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(cc, "/src/lib_dats.o build/bats_modules/")
                                  val () = copy_to_builder(bv_de, 0, dlen, 256, cc,
                                    $AR.checked_nat(dlen + 1))
                                  val () = bput(cc, "/src/lib_dats.c ")
                                  val () = (if rr > 0 then bput(cc, "-O2 -I")
                                    else bput(cc, "-g -O0 -I"))
                                  val () = copy_to_builder(ph, 0, phlen, 512, cc,
                                    $AR.checked_nat(phlen + 1))
                                  val () = bput(cc, " -I")
                                  val () = copy_to_builder(ph, 0, phlen, 512, cc,
                                    $AR.checked_nat(phlen + 1))
                                  val () = bput(cc, "/ccomp/runtime")
                                  val rc = run_sh(cc, 0)
                                  val () = (if rc <> 0 then let
                                    val () = print! ("error: cc failed for dep ")
                                    val () = print_borrow(bv_de, 0, dlen, 256,
                                      $AR.checked_nat(dlen + 1))
                                  in print_newline() end else ())
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

                    (* Compile binary *)
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

                    (* Compile entry *)
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
                    val () = bput(link, "_dats.o")
                    (* Add all dep .o files *)
                    val bm5_arr = str_to_path_arr("bats_modules")
                    val @(fz_bm5, bv_bm5) = $A.freeze<byte>(bm5_arr)
                    val bdir5 = $F.dir_open(bv_bm5, 65536)
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
                    val () = (if rel > 0 then bput(link, " -O2")
                      else bput(link, " -g -O0"))
                    val rl = run_sh(link, 0)

                    val () = $A.drop<byte>(fz_sp, bv_sp)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sp))
                    val () = $A.drop<byte>(fz_ss, bv_ss)
                    val () = $A.free<byte>($A.thaw<byte>(fz_ss))
                    val () = $A.drop<byte>(fz_sd, bv_sd)
                    val () = $A.free<byte>($A.thaw<byte>(fz_sd))
                    val () = (if rl = 0 then let
                      val () = (if rel > 0 then print! ("  built: dist/release/")
                        else print! ("  built: dist/debug/"))
                      val () = print_borrow(bv_e, 0, stem_len, 256,
                        $AR.checked_nat(stem_len + 1))
                    in print_newline() end
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

      val () = $A.drop<byte>(fz_patshome, bv_patshome)
      val () = $A.free<byte>($A.thaw<byte>(fz_patshome))
    in end
  end
end

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

fn cmd_is_init {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 4 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 3 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
      in (* "init" = 105,110,105,116 *)
        $AR.eq_int_int(c0, 105) && $AR.eq_int_int(c1, 110) &&
        $AR.eq_int_int(c2, 105) && $AR.eq_int_int(c3, 116)
      end else false
    else false
  end

fn cmd_is_tree {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 4 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 3 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
      in (* "tree" = 116,114,101,101 *)
        $AR.eq_int_int(c0, 116) && $AR.eq_int_int(c1, 114) &&
        $AR.eq_int_int(c2, 101) && $AR.eq_int_int(c3, 101)
      end else false
    else false
  end

fn cmd_is_add {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 3 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 2 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
      in (* "add" = 97,100,100 *)
        $AR.eq_int_int(c0, 97) && $AR.eq_int_int(c1, 100) &&
        $AR.eq_int_int(c2, 100)
      end else false
    else false
  end

fn cmd_is_remove {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 6 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 5 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
        val c4 = byte2int0($A.get<byte>(buf, o0 + 4))
        val c5 = byte2int0($A.get<byte>(buf, o0 + 5))
      in (* "remove" = 114,101,109,111,118,101 *)
        $AR.eq_int_int(c0, 114) && $AR.eq_int_int(c1, 101) &&
        $AR.eq_int_int(c2, 109) && $AR.eq_int_int(c3, 111) &&
        $AR.eq_int_int(c4, 118) && $AR.eq_int_int(c5, 101)
      end else false
    else false
  end

fn cmd_is_version {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 9 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 8 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
      in (* "--version" = 45,45,118,101,114,115,105,111,110 *)
        $AR.eq_int_int(c0, 45) && $AR.eq_int_int(c1, 45) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 2)), 118) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 3)), 101) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 4)), 114) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 5)), 115) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 6)), 105) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 7)), 111) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 8)), 110)
      end else false
    else false
  end

fn cmd_is_completions {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 11 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 10 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
      in (* "completions" = 99,111,109,112,108,101,116,105,111,110,115 *)
        $AR.eq_int_int(c0, 99) && $AR.eq_int_int(c1, 111) &&
        $AR.eq_int_int(c2, 109) && $AR.eq_int_int(c3, 112) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 4)), 108) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 5)), 101) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 6)), 116) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 7)), 105) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 8)), 111) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 9)), 110) &&
        $AR.eq_int_int(byte2int0($A.get<byte>(buf, o0 + 10)), 115)
      end else false
    else false
  end

fn cmd_is_test {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 4 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 3 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
      in (* "test" = 116,101,115,116 *)
        $AR.eq_int_int(c0, 116) && $AR.eq_int_int(c1, 101) &&
        $AR.eq_int_int(c2, 115) && $AR.eq_int_int(c3, 116)
      end else false
    else false
  end

fn cmd_is_upload {l:agz}{n:pos}
  (buf: !$A.arr(byte, l, n), off: int, len: int, max: int n): bool =
  if len <> 6 then false
  else let val o0 = g1ofg0(off) in
    if o0 >= 0 then
      if o0 + 5 < max then let
        val c0 = byte2int0($A.get<byte>(buf, o0))
        val c1 = byte2int0($A.get<byte>(buf, o0 + 1))
        val c2 = byte2int0($A.get<byte>(buf, o0 + 2))
        val c3 = byte2int0($A.get<byte>(buf, o0 + 3))
        val c4 = byte2int0($A.get<byte>(buf, o0 + 4))
        val c5 = byte2int0($A.get<byte>(buf, o0 + 5))
      in (* "upload" = 117,112,108,111,97,100 *)
        $AR.eq_int_int(c0, 117) && $AR.eq_int_int(c1, 112) &&
        $AR.eq_int_int(c2, 108) && $AR.eq_int_int(c3, 111) &&
        $AR.eq_int_int(c4, 97) && $AR.eq_int_int(c5, 100)
      end else false
    else false
  end

(* ============================================================
   test: build and run tests
   ============================================================ *)
fn do_test(): void = let
  val () = do_build(0)
  (* Test infrastructure requires unittest block support in emitter.
     For now, report that the build succeeded. *)
  val () = println! ("no tests found")
in () end

(* ============================================================
   upload: package library for repository
   ============================================================ *)
fn do_upload(): void = let
  (* Read bats.toml for package name and verify kind = "lib" *)
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 65536, 0, 0)
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
          (* Get repository path before branching *)
          val repo = $A.alloc<byte>(4096)
          val rplen = $UNSAFE begin
            $extfcall(int, "_bpoc_get_repo",
              $UNSAFE.castvwtp1{ptr}(repo), 4096)
          end
        in
          case+ nr of
          | ~$R.some(nlen) =>
            if is_lib then
              if rplen > 0 then let
                val cmd = $B.create()
                val () = bput(cmd, "mkdir -p ")
                val @(fz_rp, bv_rp) = $A.freeze<byte>(repo)
                val () = copy_to_builder(bv_rp, 0, rplen, 4096, cmd,
                  $AR.checked_nat(rplen + 1))
                val () = bput(cmd, "/")
                val @(fz_nb, bv_nb) = $A.freeze<byte>(nbuf)
                val () = copy_to_builder(bv_nb, 0, nlen, 256, cmd,
                  $AR.checked_nat(nlen + 1))
                val () = bput(cmd, " && zip -r ")
                val () = copy_to_builder(bv_rp, 0, rplen, 4096, cmd,
                  $AR.checked_nat(rplen + 1))
                val () = bput(cmd, "/")
                val () = copy_to_builder(bv_nb, 0, nlen, 256, cmd,
                  $AR.checked_nat(nlen + 1))
                val () = bput(cmd, "/")
                val () = copy_to_builder(bv_nb, 0, nlen, 256, cmd,
                  $AR.checked_nat(nlen + 1))
                val () = bput(cmd, "_0.1.0.bats bats.toml src/")
                val () = $A.drop<byte>(fz_nb, bv_nb)
                val () = $A.free<byte>($A.thaw<byte>(fz_nb))
                val () = $A.drop<byte>(fz_rp, bv_rp)
                val () = $A.free<byte>($A.thaw<byte>(fz_rp))
                val rc = run_sh(cmd, 0)
              in
                if rc <> 0 then println! ("error: upload failed")
                else println! ("uploaded successfully")
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
fn do_completions(shell: int): void =
  if shell = 0 then
    $UNSAFE begin $extfcall(void, "_bpoc_print_completions_bash") end
  else if shell = 1 then
    $UNSAFE begin $extfcall(void, "_bpoc_print_completions_zsh") end
  else if shell = 2 then
    $UNSAFE begin $extfcall(void, "_bpoc_print_completions_fish") end
  else println! ("error: specify a shell (bash, zsh, fish)")

(* ============================================================
   init: create a new bats project
   ============================================================ *)
fn do_init(kind: int): void = let
  (* kind: 0=binary, 1=library *)
  (* Get current directory name via readlink /proc/self/cwd *)
  val cwd_buf = $A.alloc<byte>(4096)
  val cwd_len = $UNSAFE begin
    $extfcall(int, "readlink", "/proc/self/cwd",
      $UNSAFE.castvwtp1{ptr}(cwd_buf), 4095)
  end
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
  val () = (if kind = 0 then bput(cmd1, "mkdir -p src/bin")
    else bput(cmd1, "mkdir -p src"))
  val _ = run_sh(cmd1, 0)
  (* Write bats.toml *)
  val toml = $B.create()
  val () = bput(toml, "[package]\nname = \"")
  val () = copy_to_builder(bv_cwd, name_start, cwd_len, 4096, toml,
    $AR.checked_nat(name_len + 1))
  val () = (if kind = 0 then bput(toml, "\"\nkind = \"bin\"\n\n[dependencies]\n")
    else bput(toml, "\"\nkind = \"lib\"\n\n[dependencies]\n"))
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val rc = write_file_from_builder(bv_tp, 65536, toml)
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
  val rc2 = write_file_from_builder(bv_sp, 65536, src)
  val () = $A.drop<byte>(fz_sp, bv_sp)
  val () = $A.free<byte>($A.thaw<byte>(fz_sp))
  val () = $A.drop<byte>(fz_cwd, bv_cwd)
  val () = $A.free<byte>($A.thaw<byte>(fz_cwd))
  (* Write .gitignore *)
  val gi = $B.create()
  val () = bput(gi, "build/\ndist/\nbats_modules/\ndocs/\n")
  val gp = str_to_path_arr(".gitignore")
  val @(fz_gp, bv_gp) = $A.freeze<byte>(gp)
  val rc3 = write_file_from_builder(bv_gp, 65536, gi)
  val () = $A.drop<byte>(fz_gp, bv_gp)
  val () = $A.free<byte>($A.thaw<byte>(fz_gp))
in
  if rc = 0 then
    if rc2 = 0 then
      if rc3 = 0 then println! ("initialized bats project in current directory")
      else println! ("error: failed to write .gitignore")
    else println! ("error: failed to write source file")
  else println! ("error: failed to write bats.toml")
end

(* ============================================================
   tree: display dependency tree from bats.lock
   ============================================================ *)
fn do_tree(): void = let
  val la = str_to_path_arr("bats.lock")
  val @(fz_la, bv_la) = $A.freeze<byte>(la)
  val lock_or = $F.file_open(bv_la, 65536, 0, 0)
  val () = $A.drop<byte>(fz_la, bv_la)
  val () = $A.free<byte>($A.thaw<byte>(fz_la))
in
  case+ lock_or of
  | ~$R.ok(lfd) => let
      val lock_buf = $A.alloc<byte>(65536)
      val lr = $F.file_read(lfd, lock_buf, 65536)
      val lock_len = (case+ lr of | ~$R.ok(n) => n | ~$R.err(_) => 0): int
      val lcr = $F.file_close(lfd)
      val () = $R.discard<int><int>(lcr)
    in
      if lock_len > 0 then let
        (* Parse lock file: each line is "pkg version sha256" *)
        (* Just display as a flat tree for now *)
        val @(fz_lb, bv_lb) = $A.freeze<byte>(lock_buf)
        val () = println! (".")
        fun print_tree {l2:agz}{fuel2:nat} .<fuel2>.
          (bv: !$A.borrow(byte, l2, 65536), pos: int, len: int,
           fuel2: int fuel2): void =
          if fuel2 <= 0 then ()
          else if pos >= len then ()
          else let
            val b = src_byte(bv, pos, 65536)
          in
            if b = 10 then let (* newline *)
              val () = print_newline()
              val next = pos + 1
            in
              if next < len then let
                val nb = src_byte(bv, next, 65536)
              in
                if nb <> 10 then let
                  val () = print! ("|-- ")
                in print_tree(bv, next, len, fuel2 - 1) end
                else print_tree(bv, next, len, fuel2 - 1)
              end
              else ()
            end
            else let
              (* print chars until space (pkg name), skip rest of line *)
              val () = print_char(int2char0(b))
            in print_tree(bv, pos + 1, len, fuel2 - 1) end
          end
        val () = print! ("|-- ")
        val () = print_tree(bv_lb, 0, lock_len, $AR.checked_nat(lock_len + 1))
        val () = print_newline()
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
fn do_add {l:agz}{n:pos}
  (bv: !$A.borrow(byte, l, n), pkg_start: int, pkg_len: int,
   max: int n): void = let
  (* Read bats.toml *)
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 65536, 0, 0)
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
      val out = $A.alloc<byte>(8192)
      val nlen = $UNSAFE begin
        $extfcall(int, "_bpoc_inject_dep",
          $UNSAFE.castvwtp1{ptr}(tbuf), tlen,
          ptr_add<byte>($UNSAFE.castvwtp1{ptr}(bv), g1ofg0(pkg_start)), pkg_len,
          "", 0,
          $UNSAFE.castvwtp1{ptr}(out), 8192)
      end
      val () = $A.free<byte>(tbuf)
    in
      if nlen > 0 then let
        val rc = $UNSAFE begin $extfcall(int, "_bpoc_write_file",
          "bats.toml", $UNSAFE.castvwtp1{ptr}(out), nlen) end
        val () = $A.free<byte>(out)
      in
        if rc = 0 then let
            val () = print! ("added '")
            val () = print_borrow(bv, pkg_start, pkg_start + pkg_len, max,
              $AR.checked_nat(pkg_len + 1))
          in println! ("' to [dependencies]") end
        else println! ("error: cannot write bats.toml")
      end
      else let
        val () = $A.free<byte>(out)
      in println! ("error: failed to update bats.toml") end
    end
  | ~$R.err(_) => println! ("error: cannot open bats.toml")
end

(* ============================================================
   remove: remove a dependency from bats.toml
   ============================================================ *)
fn do_remove {l:agz}{n:pos}
  (bv: !$A.borrow(byte, l, n), pkg_start: int, pkg_len: int,
   max: int n): void = let
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 65536, 0, 0)
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
      val out = $A.alloc<byte>(8192)
      val nlen = $UNSAFE begin
        $extfcall(int, "_bpoc_strip_dep",
          $UNSAFE.castvwtp1{ptr}(tbuf), tlen,
          ptr_add<byte>($UNSAFE.castvwtp1{ptr}(bv), g1ofg0(pkg_start)), pkg_len,
          $UNSAFE.castvwtp1{ptr}(out), 8192)
      end
      val () = $A.free<byte>(tbuf)
    in
      if nlen > 0 then let
        val rc = $UNSAFE begin $extfcall(int, "_bpoc_write_file",
          "bats.toml", $UNSAFE.castvwtp1{ptr}(out), nlen) end
        val () = $A.free<byte>(out)
      in
        if rc = 0 then let
            val () = print! ("removed '")
            val () = print_borrow(bv, pkg_start, pkg_start + pkg_len, max,
              $AR.checked_nat(pkg_len + 1))
          in println! ("' from [dependencies]") end
        else println! ("error: cannot write bats.toml")
      end
      else let
        val () = $A.free<byte>(out)
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
   run: build then execute the binary
   ============================================================ *)
fn do_run(): void = let
  val () = do_build(0)
  val () = do_build(1)
  (* Read bats.toml to find the package name *)
  val tp = str_to_path_arr("bats.toml")
  val @(fz_tp, bv_tp) = $A.freeze<byte>(tp)
  val tor = $F.file_open(bv_tp, 65536, 0, 0)
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
              (* Check if --bin was specified *)
              val bin_name = $A.alloc<byte>(256)
              val bn_len = $UNSAFE begin
                $extfcall(int, "_bpoc_get_bin",
                  $UNSAFE.castvwtp1{ptr}(bin_name), 256)
              end
              val cmd = $B.create()
              val () = bput(cmd, "./dist/debug/")
            in
              if bn_len > 0 then let
                val @(fz_bn, bv_bn) = $A.freeze<byte>(bin_name)
                val () = copy_to_builder(bv_bn, 0, bn_len, 256, cmd,
                  $AR.checked_nat(bn_len + 1))
                val () = $A.drop<byte>(fz_bn, bv_bn)
                val () = $A.free<byte>($A.thaw<byte>(fz_bn))
                val () = $A.free<byte>(nbuf)
                val rc = run_sh(cmd, 0)
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
                val rc = run_sh(cmd, 0)
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
          (* Check for --run-in <dir> global flag before subcommand *)
          val first_start = tok0_end + 1
          val first_end = find_null(cl_buf, first_start, 4096, 4096)
          val first_len = first_end - first_start
          (* Use C helper to handle --run-in; returns offset to actual command *)
          val cmd_start = $UNSAFE begin
            $extfcall(int, "_bpoc_handle_run_in",
              $UNSAFE.castvwtp1{ptr}(cl_buf), cl_n,
              first_start, first_end, first_len)
          end
          val cmd_end = find_null(cl_buf, cmd_start, 4096, 4096)
          val cmd_len = cmd_end - cmd_start
          (* Parse global flags --verbose/-v and --quiet/-q *)
          val @(fz_flags, bv_flags) = $A.freeze<byte>(cl_buf)
          val has_verbose = $UNSAFE begin
            $extfcall(int, "_bpoc_has_flag",
              $UNSAFE.castvwtp1{ptr}(bv_flags), cl_n, cmd_end + 1, "--verbose")
          end
          val has_v = $UNSAFE begin
            $extfcall(int, "_bpoc_has_flag",
              $UNSAFE.castvwtp1{ptr}(bv_flags), cl_n, cmd_end + 1, "-v")
          end
          val has_quiet = $UNSAFE begin
            $extfcall(int, "_bpoc_has_flag",
              $UNSAFE.castvwtp1{ptr}(bv_flags), cl_n, cmd_end + 1, "--quiet")
          end
          val has_q = $UNSAFE begin
            $extfcall(int, "_bpoc_has_flag",
              $UNSAFE.castvwtp1{ptr}(bv_flags), cl_n, cmd_end + 1, "-q")
          end
          val () = $A.drop<byte>(fz_flags, bv_flags)
          val cl_buf = $A.thaw<byte>(fz_flags)
          val () = (if has_verbose > 0 orelse has_v > 0 then
            $UNSAFE begin $extfcall(void, "_bpoc_set_verbose", 1) end
            else ())
          val () = (if has_quiet > 0 orelse has_q > 0 then
            $UNSAFE begin $extfcall(void, "_bpoc_set_quiet", 1) end
            else ())
          (* Parse --repository flag *)
          val repo_buf = $A.alloc<byte>(4096)
          val rlen = $UNSAFE begin
            $extfcall(int, "_bpoc_get_flag_val",
              $UNSAFE.castvwtp1{ptr}(cl_buf), cl_n, cmd_end + 1,
              "--repository", $UNSAFE.castvwtp1{ptr}(repo_buf), 4096)
          end
          val () = (if rlen > 0 then
            $UNSAFE begin $extfcall(void, "_bpoc_set_repo",
              $UNSAFE.castvwtp1{ptr}(repo_buf), rlen) end
            else ())
          val () = $A.free<byte>(repo_buf)
        in
          if cmd_is_check(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_check() end
          else if cmd_is_build(cl_buf, cmd_start, cmd_len, 4096) then let
            val @(fz_cb, bv_cb) = $A.freeze<byte>(cl_buf)
            val only_val = $A.alloc<byte>(32)
            val olen = $UNSAFE begin
              $extfcall(int, "_bpoc_get_flag_val",
                $UNSAFE.castvwtp1{ptr}(bv_cb), cl_n, cmd_end + 1,
                "--only", $UNSAFE.castvwtp1{ptr}(only_val), 32)
            end
            val () = $A.drop<byte>(fz_cb, bv_cb)
            val () = $A.free<byte>($A.thaw<byte>(fz_cb))
            (* Check if --only debug|release|native|wasm *)
            val @(fz_ov, bv_ov) = $A.freeze<byte>(only_val)
            val only_debug = (if olen = 5 then let
              val b0 = byte2int0($A.read<byte>(bv_ov, 0))
              val b1 = byte2int0($A.read<byte>(bv_ov, 1))
            in $AR.eq_int_int(b0, 100) && $AR.eq_int_int(b1, 101) end
              else false): bool
            val only_release = (if olen = 7 then let
              val b0 = byte2int0($A.read<byte>(bv_ov, 0))
              val b1 = byte2int0($A.read<byte>(bv_ov, 1))
            in $AR.eq_int_int(b0, 114) && $AR.eq_int_int(b1, 101) end
              else false): bool
            (* "native" = 6 chars, n=110; "wasm" = 4 chars, w=119 *)
            val only_native = (if olen = 6 then let
              val b0 = byte2int0($A.read<byte>(bv_ov, 0))
            in $AR.eq_int_int(b0, 110) end
              else false): bool
            val only_wasm = (if olen = 4 then let
              val b0 = byte2int0($A.read<byte>(bv_ov, 0))
            in $AR.eq_int_int(b0, 119) end
              else false): bool
            val () = $A.drop<byte>(fz_ov, bv_ov)
            val () = $A.free<byte>($A.thaw<byte>(fz_ov))
          in
            if only_wasm then println! ("error: wasm target is not yet supported")
            else if only_debug then do_build(0)
            else if only_release then do_build(1)
            else let
              val () = do_build(0)
            in do_build(1) end
          end
          else if cmd_is_clean(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_clean() end
          else if cmd_is_lock(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_lock() end
          else if cmd_is_run(cl_buf, cmd_start, cmd_len, 4096) then let
            val bin_buf = $A.alloc<byte>(256)
            val blen = $UNSAFE begin
              $extfcall(int, "_bpoc_get_flag_val",
                $UNSAFE.castvwtp1{ptr}(cl_buf), cl_n, cmd_end + 1,
                "--bin", $UNSAFE.castvwtp1{ptr}(bin_buf), 256)
            end
            val () = (if blen > 0 then
              $UNSAFE begin $extfcall(void, "_bpoc_set_bin",
                $UNSAFE.castvwtp1{ptr}(bin_buf), blen) end
              else ())
            val () = $A.free<byte>(bin_buf)
            val () = $A.free<byte>(cl_buf)
          in do_run() end
          else if cmd_is_init(cl_buf, cmd_start, cmd_len, 4096) then let
            (* Parse init argument: "binary"|"bin" or "library"|"lib" *)
            val arg_start = cmd_end + 1
            val arg_end = find_null(cl_buf, arg_start, 4096, 4096)
            val arg_len = arg_end - arg_start
            (* Check for "binary"(6) or "bin"(3) → 0, "library"(7) or "lib"(3) → 1 *)
            val kind = (if arg_len = 6 orelse arg_len = 3 then let
                val a0 = g1ofg0(arg_start)
              in
                if a0 >= 0 then
                  if a0 < 4096 then let
                    val c0 = byte2int0($A.get<byte>(cl_buf, a0))
                  in
                    if $AR.eq_int_int(c0, 98) then 0  (* 'b' = binary/bin *)
                    else if $AR.eq_int_int(c0, 108) then 1  (* 'l' = library/lib *)
                    else ~1
                  end else ~1
                else ~1
              end
            else if arg_len = 7 then let
                val a0 = g1ofg0(arg_start)
              in
                if a0 >= 0 then
                  if a0 < 4096 then let
                    val c0 = byte2int0($A.get<byte>(cl_buf, a0))
                  in if $AR.eq_int_int(c0, 108) then 1 else ~1 end
                  else ~1
                else ~1
              end
            else ~1): int
            val () = $A.free<byte>(cl_buf)
          in
            if kind >= 0 then do_init(kind)
            else println! ("error: specify 'binary' or 'library'\nusage: bats-poc init binary|library")
          end
          else if cmd_is_test(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_test() end
          else if cmd_is_upload(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_upload() end
          else if cmd_is_tree(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in do_tree() end
          else if cmd_is_add(cl_buf, cmd_start, cmd_len, 4096) then let
            val pkg_start = cmd_end + 1
            val pkg_end = find_null(cl_buf, pkg_start, 4096, 4096)
            val pkg_len = pkg_end - pkg_start
            val @(fz_ab, bv_ab) = $A.freeze<byte>(cl_buf)
          in
            if pkg_len > 0 then let
              val () = do_add(bv_ab, pkg_start, pkg_len, 4096)
              val () = $A.drop<byte>(fz_ab, bv_ab)
              val () = $A.free<byte>($A.thaw<byte>(fz_ab))
            in end
            else let
              val () = $A.drop<byte>(fz_ab, bv_ab)
              val () = $A.free<byte>($A.thaw<byte>(fz_ab))
            in println! ("error: specify a package name\nusage: bats-poc add <package>") end
          end
          else if cmd_is_remove(cl_buf, cmd_start, cmd_len, 4096) then let
            val pkg_start = cmd_end + 1
            val pkg_end = find_null(cl_buf, pkg_start, 4096, 4096)
            val pkg_len = pkg_end - pkg_start
            val @(fz_rb, bv_rb) = $A.freeze<byte>(cl_buf)
          in
            if pkg_len > 0 then let
              val () = do_remove(bv_rb, pkg_start, pkg_len, 4096)
              val () = $A.drop<byte>(fz_rb, bv_rb)
              val () = $A.free<byte>($A.thaw<byte>(fz_rb))
            in end
            else let
              val () = $A.drop<byte>(fz_rb, bv_rb)
              val () = $A.free<byte>($A.thaw<byte>(fz_rb))
            in println! ("error: specify a package name\nusage: bats-poc remove <package>") end
          end
          else if cmd_is_completions(cl_buf, cmd_start, cmd_len, 4096) then let
            val arg_start = cmd_end + 1
            val arg_end = find_null(cl_buf, arg_start, 4096, 4096)
            val arg_len = arg_end - arg_start
            (* "bash"=4: b=98, "zsh"=3: z=122, "fish"=4: f=102 *)
            val shell = (if arg_len = 4 then let
                val a0 = g1ofg0(arg_start)
              in
                if a0 >= 0 then
                  if a0 < 4096 then let
                    val c0 = byte2int0($A.get<byte>(cl_buf, a0))
                  in
                    if $AR.eq_int_int(c0, 98) then 0  (* 'b' = bash *)
                    else if $AR.eq_int_int(c0, 102) then 2  (* 'f' = fish *)
                    else ~1
                  end else ~1
                else ~1
              end
            else if arg_len = 3 then let
                val a0 = g1ofg0(arg_start)
              in
                if a0 >= 0 then
                  if a0 < 4096 then let
                    val c0 = byte2int0($A.get<byte>(cl_buf, a0))
                  in if $AR.eq_int_int(c0, 122) then 1 else ~1 end
                  else ~1
                else ~1
              end
            else ~1): int
            val () = $A.free<byte>(cl_buf)
          in
            if shell >= 0 then do_completions(shell)
            else println! ("error: specify a shell (bash, zsh, fish)\nusage: bats-poc completions bash|zsh|fish")
          end
          else if cmd_is_version(cl_buf, cmd_start, cmd_len, 4096) then let
            val () = $A.free<byte>(cl_buf)
          in println! ("bats-poc 0.1.0") end
          else let
            val () = $A.free<byte>(cl_buf)
          in println! ("usage: bats-poc <init|lock|add|remove|build|run|test|check|tree|upload|clean|completions> [--only debug|release]") end
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
