/* gsim.c (R-29): bit-packed Life simulator on a finite grid that is checked never to be reached
   (a live cell within 66 cells of the border aborts), hence exact for the unbounded plane. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
typedef struct { int W, H; long x0, y0; u64 *a, *b; int rlo, rhi, wlo, whi; } Sim;

Sim *sim_new(int W, int H, long x0, long y0) {
  Sim *s = calloc(1, sizeof(Sim));
  s->W = W; s->H = H; s->x0 = x0; s->y0 = y0;
  s->a = calloc((size_t)W * H, 8); s->b = calloc((size_t)W * H, 8);
  s->rlo = H; s->rhi = -1; s->wlo = W; s->whi = -1;
  return s;
}
void sim_free(Sim *s) { free(s->a); free(s->b); free(s); }

static void bounds(Sim *s) {
  int W = s->W; s->rlo = s->H; s->rhi = -1; s->wlo = W; s->whi = -1;
  for (int r = 0; r < s->H; r++) for (int i = 0; i < W; i++) if (s->a[(size_t)r * W + i]) {
    if (r < s->rlo) s->rlo = r; if (r > s->rhi) s->rhi = r;
    if (i < s->wlo) s->wlo = i; if (i > s->whi) s->whi = i; }
}
/* returns 0, or -1 if a cell is outside the grid */
int sim_set(Sim *s, int n, const long *xs, const long *ys) {
  memset(s->a, 0, (size_t)s->W * s->H * 8);
  for (int k = 0; k < n; k++) {
    long x = xs[k] - s->x0, y = ys[k] - s->y0;
    if (x < 64 || y < 2 || x >= (long)s->W * 64 - 64 || y >= s->H - 2) return -1;
    s->a[(size_t)y * s->W + (x >> 6)] |= (u64)1 << (x & 63);
  }
  bounds(s); return 0;
}
int sim_count(Sim *s) {
  int c = 0; for (size_t k = 0; k < (size_t)s->W * s->H; k++) c += __builtin_popcountll(s->a[k]); return c;
}
int sim_get(Sim *s, long *xs, long *ys) {
  int c = 0;
  for (int r = 0; r < s->H; r++) for (int i = 0; i < s->W; i++) {
    u64 w = s->a[(size_t)r * s->W + i];
    while (w) { int j = __builtin_ctzll(w); w &= w - 1; xs[c] = (long)i * 64 + j + s->x0; ys[c] = r + s->y0; c++; }
  }
  return c;
}
/* bounding box (world cells, word precision in x) of the live cells */
void sim_box(Sim *s, long *out) {
  out[0] = (long)s->wlo * 64 + s->x0; out[1] = s->rlo + s->y0; out[2] = (long)s->whi * 64 + 63 + s->x0; out[3] = s->rhi + s->y0;
}
static inline u64 L(const u64 *r, int i) { return (r[i] << 1) | (r[i - 1] >> 63); }
static inline u64 R(const u64 *r, int i) { return (r[i] >> 1) | (r[i + 1] << 63); }
/* n generations; box (running bounding box, word precision) in box[4]; -1 if the border is reached */
int sim_run(Sim *s, long n, long *box) {
  int W = s->W;
  for (long g = 0; g < n; g++) {
    if (s->rhi < 0) return 0;
    if (s->rlo < 3 || s->rhi > s->H - 4 || s->wlo < 2 || s->whi > W - 3) return -1;
    int r0 = s->rlo - 1, r1 = s->rhi + 1, w0 = s->wlo - 1, w1 = s->whi + 1;
    int nrlo = s->H, nrhi = -1, nwlo = W, nwhi = -1;
    for (int r = r0; r <= r1; r++) {
      const u64 *up = s->a + (size_t)(r - 1) * W, *cu = s->a + (size_t)r * W, *dn = s->a + (size_t)(r + 1) * W;
      u64 *out = s->b + (size_t)r * W;
      for (int i = w0; i <= w1; i++) {
        u64 al = L(up, i), am = up[i], ar = R(up, i);
        u64 bl = L(cu, i), bm = cu[i], br = R(cu, i);
        u64 cl = L(dn, i), cm = dn[i], cr = R(dn, i);
        u64 a0 = al ^ am ^ ar, a1 = (al & am) | (ar & (al ^ am));
        u64 c0 = cl ^ cm ^ cr, c1 = (cl & cm) | (cr & (cl ^ cm));
        u64 b0 = bl ^ br, b1 = bl & br;
        u64 s0 = a0 ^ b0 ^ c0, k1 = (a0 & b0) | (c0 & (a0 ^ b0));
        u64 par = a1 ^ b1 ^ c1 ^ k1;
        u64 two = (a1 & b1) | (c1 & k1) | ((a1 ^ b1) & (c1 ^ k1));
        u64 nx = par & ~two & (s0 | bm);
        out[i] = nx;
        if (nx) { if (r < nrlo) nrlo = r; nrhi = r; if (i < nwlo) nwlo = i; if (i > nwhi) nwhi = i; }
      }
    }
    u64 *t = s->a; s->a = s->b; s->b = t;
    /* invariant: b is zero at the start of a step; the old a (now b) has cells only inside the region */
    for (int r = r0; r <= r1; r++) memset(s->b + (size_t)r * W + w0, 0, (size_t)(w1 - w0 + 1) * 8);
    s->rlo = nrlo; s->rhi = nrhi; s->wlo = nwlo; s->whi = nwhi;
    if (box && nrhi >= 0) {
      long bx0 = (long)nwlo * 64 + s->x0, by0 = nrlo + s->y0, bx1 = (long)nwhi * 64 + 63 + s->x0, by1 = nrhi + s->y0;
      if (bx0 < box[0]) box[0] = bx0; if (by0 < box[1]) box[1] = by0; if (bx1 > box[2]) box[2] = bx1; if (by1 > box[3]) box[3] = by1;
    }
  }
  return 0;
}
