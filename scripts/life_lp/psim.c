/* psim.c (R-31): sparse tiled bit-packed Life simulator (64 x 64 tiles, only tiles that are
   live or next to live tiles are computed).  Exact on the unbounded plane as long as no live cell
   comes within 2 tiles of the border of the tile array (then sim_run returns -1). */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
typedef struct { u64 a[64]; u64 b[64]; int tx, ty; int live; } Tile;
typedef struct {
  int NX, NY; long x0, y0;            /* tile (0,0) covers cells x0 .. x0+63, y0 .. y0+63 */
  int *grid;                           /* tile index or -1 */
  Tile *pool; int np, cap;
  int *act, nact; int *proc, nproc; int *mark; int stamp;
  int *freel, nfree;
} Sim;

static int get_tile(Sim *s, int tx, int ty) {
  int g = ty * s->NX + tx;
  if (s->grid[g] >= 0) return s->grid[g];
  int k;
  if (s->nfree) k = s->freel[--s->nfree];
  else {
    if (s->np == s->cap) { s->cap = s->cap ? 2 * s->cap : 1024; s->pool = realloc(s->pool, sizeof(Tile) * (size_t)s->cap);
      s->mark = realloc(s->mark, sizeof(int) * (size_t)s->cap); s->freel = realloc(s->freel, sizeof(int) * (size_t)s->cap); }
    k = s->np++;
  }
  memset(&s->pool[k], 0, sizeof(Tile)); s->pool[k].tx = tx; s->pool[k].ty = ty; s->mark[k] = 0;
  s->grid[g] = k; return k;
}
Sim *sim_new(int NX, int NY, long x0, long y0) {
  Sim *s = calloc(1, sizeof(Sim)); s->NX = NX; s->NY = NY; s->x0 = x0; s->y0 = y0;
  s->grid = malloc(sizeof(int) * (size_t)NX * NY); for (long i = 0; i < (long)NX * NY; i++) s->grid[i] = -1;
  s->act = malloc(sizeof(int) * (size_t)NX * NY); s->proc = malloc(sizeof(int) * (size_t)NX * NY);
  return s;
}
void sim_free(Sim *s) { free(s->grid); free(s->pool); free(s->act); free(s->proc); free(s->mark); free(s->freel); free(s); }
static void clear_all(Sim *s) {
  for (int k = 0; k < s->np; k++) { s->grid[s->pool[k].ty * s->NX + s->pool[k].tx] = -1; }
  s->np = 0; s->nfree = 0; s->nact = 0;
}
static void rebuild_active(Sim *s) {
  s->nact = 0;
  for (long g = 0; g < (long)s->NX * s->NY; g++) {
    int k = s->grid[g]; if (k < 0) continue;
    int live = 0; for (int r = 0; r < 64; r++) if (s->pool[k].a[r]) { live = 1; break; }
    if (live) s->act[s->nact++] = k; else { s->grid[g] = -1; s->freel[s->nfree++] = k; }
  }
}
int sim_set(Sim *s, int n, const long *xs, const long *ys) {
  clear_all(s);
  for (int i = 0; i < n; i++) {
    long x = xs[i] - s->x0, y = ys[i] - s->y0;
    if (x < 0 || y < 0 || x >= (long)s->NX * 64 || y >= (long)s->NY * 64) return -1;
    int k = get_tile(s, (int)(x >> 6), (int)(y >> 6));
    s->pool[k].a[y & 63] |= (u64)1 << (x & 63);
  }
  rebuild_active(s); return 0;
}
int sim_count(Sim *s) { int c = 0; for (int i = 0; i < s->nact; i++) for (int r = 0; r < 64; r++) c += __builtin_popcountll(s->pool[s->act[i]].a[r]); return c; }
/* cells; if box != NULL only cells outside box[0..3] (x0, y0, x1, y1 inclusive) */
int sim_get(Sim *s, long *xs, long *ys, const long *box, int maxn) {
  int c = 0;
  for (int i = 0; i < s->nact; i++) {
    Tile *t = &s->pool[s->act[i]];
    long bx = s->x0 + 64L * t->tx, by = s->y0 + 64L * t->ty;
    if (box && bx >= box[0] && bx + 63 <= box[2] && by >= box[1] && by + 63 <= box[3]) continue;
    for (int r = 0; r < 64; r++) { u64 w = t->a[r];
      while (w) { int j = __builtin_ctzll(w); w &= w - 1; long x = bx + j, y = by + r;
        if (box && x >= box[0] && x <= box[2] && y >= box[1] && y <= box[3]) continue;
        if (c < maxn) { xs[c] = x; ys[c] = y; } c++; } }
  }
  return c;
}
void sim_clear(Sim *s, int n, const long *xs, const long *ys) {
  for (int i = 0; i < n; i++) { long x = xs[i] - s->x0, y = ys[i] - s->y0;
    int g = (int)(y >> 6) * s->NX + (int)(x >> 6); int k = s->grid[g]; if (k < 0) continue;
    s->pool[k].a[y & 63] &= ~((u64)1 << (x & 63)); }
  rebuild_active(s);
}
static inline u64 rowof(Sim *s, int tx, int ty, int r) {
  /* row r (may be -1 or 64) of tile (tx, ty) */
  if (r < 0) { ty--; r = 63; } else if (r > 63) { ty++; r = 0; }
  int k = s->grid[ty * s->NX + tx]; return k < 0 ? 0 : s->pool[k].a[r];
}
int sim_run(Sim *s, long n) {
  for (long g = 0; g < n; g++) {
    if (!s->nact) return 0;
    s->stamp++;
    s->nproc = 0;
    int na = s->nact;
    for (int i = 0; i < na; i++) {
      Tile *t = &s->pool[s->act[i]];
      if (t->tx < 2 || t->ty < 2 || t->tx >= s->NX - 2 || t->ty >= s->NY - 2) return -1;
    }
    /* collect tiles to process (create neighbours as needed) */
    for (int i = 0; i < na; i++) {
      int tx = s->pool[s->act[i]].tx, ty = s->pool[s->act[i]].ty;
      for (int dy = -1; dy <= 1; dy++) for (int dx = -1; dx <= 1; dx++) {
        int k = get_tile(s, tx + dx, ty + dy);
        if (s->mark[k] != s->stamp) { s->mark[k] = s->stamp; s->proc[s->nproc++] = k; }
      }
    }
    for (int i = 0; i < s->nproc; i++) {
      Tile *t = &s->pool[s->proc[i]]; int tx = t->tx, ty = t->ty;
      u64 L[66], M[66], R[66];
      for (int r = -1; r <= 64; r++) {
        M[r + 1] = rowof(s, tx, ty, r); L[r + 1] = rowof(s, tx - 1, ty, r); R[r + 1] = rowof(s, tx + 1, ty, r);
      }
      int live = 0;
      for (int r = 0; r < 64; r++) {
        u64 al = (M[r] << 1) | (L[r] >> 63), am = M[r], ar = (M[r] >> 1) | (R[r] << 63);
        u64 bl = (M[r + 1] << 1) | (L[r + 1] >> 63), bm = M[r + 1], br = (M[r + 1] >> 1) | (R[r + 1] << 63);
        u64 cl = (M[r + 2] << 1) | (L[r + 2] >> 63), cm = M[r + 2], cr = (M[r + 2] >> 1) | (R[r + 2] << 63);
        u64 a0 = al ^ am ^ ar, a1 = (al & am) | (ar & (al ^ am));
        u64 c0 = cl ^ cm ^ cr, c1 = (cl & cm) | (cr & (cl ^ cm));
        u64 b0 = bl ^ br, b1 = bl & br;
        u64 s0 = a0 ^ b0 ^ c0, k1 = (a0 & b0) | (c0 & (a0 ^ b0));
        u64 par = a1 ^ b1 ^ c1 ^ k1;
        u64 two = (a1 & b1) | (c1 & k1) | ((a1 ^ b1) & (c1 ^ k1));
        u64 nx = par & ~two & (s0 | bm);
        t->b[r] = nx; live |= (nx != 0);
      }
      t->live = live;
    }
    s->nact = 0;
    for (int i = 0; i < s->nproc; i++) {
      int k = s->proc[i]; Tile *t = &s->pool[k];
      memcpy(t->a, t->b, sizeof(t->a));
      if (t->live) s->act[s->nact++] = k;
      else { s->grid[t->ty * s->NX + t->tx] = -1; s->freel[s->nfree++] = k; }
    }
  }
  return 0;
}
