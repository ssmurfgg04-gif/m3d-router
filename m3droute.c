/*
 * m3droute - router for the M3D (monolithic-3D) routing challenge.
 *
 * Method: negotiated-congestion (PathFinder) routing where each net's tree
 * is grown objective-aware: sinks attach one at a time, each attachment
 * minimizing (driver-to-attachment delay along the existing tree) + (cost of
 * the new branch), which targets the challenge score (sum over sinks of
 * driver->sink path delay) rather than generic tree weight. After a legal
 * solution exists, LNS rounds rip up batches of nets and re-route them
 * against hard capacity, keeping improvements only. Deterministic restarts
 * with different seeds; best legal result wins.
 *
 * usage: m3droute <case.json> <out.sol.json> [budget-secs] [seed]
 */
#define _GNU_SOURCE
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static void *xmalloc(size_t n) { void *p = malloc(n); if (!p) { fprintf(stderr, "oom\n"); exit(1); } return p; }
static void *xcalloc(size_t n, size_t s) { void *p = calloc(n, s); if (!p) { fprintf(stderr, "oom\n"); exit(1); } return p; }

/* ---------------------------------------------------------------- json dom */

typedef enum { J_NULL, J_BOOL, J_NUM, J_STR, J_ARR, J_OBJ } jtype;

typedef struct jv {
    jtype t;
    double num;
    char *str;
    struct jv **items;
    char **keys;
    int n;
} jv;

static char *jp;
static char *jpool;
static size_t jpool_used, jpool_cap;

static jv *jnew(jtype t)
{
    jv *v = xmalloc(sizeof *v);
    memset(v, 0, sizeof *v);
    v->t = t;
    return v;
}

static void pool_reserve(size_t n)
{
    if (jpool_used + n > jpool_cap) {
        jpool_cap = (jpool_used + n) * 2 + 4096;
        jpool = realloc(jpool, jpool_cap);
        if (!jpool) { fprintf(stderr, "oom\n"); exit(1); }
    }
}

static char *jstring(void)
{
    jp++;
    pool_reserve(strlen(jp) + 1);
    char *out = jpool + jpool_used;
    char *o = out;
    while (*jp && *jp != '"') {
        if (*jp == '\\' && jp[1]) {
            jp++;
            switch (*jp) {
            case 'n': *o++ = '\n'; break;
            case 't': *o++ = '\t'; break;
            case 'r': *o++ = '\r'; break;
            default:  *o++ = *jp;
            }
            jp++;
        } else {
            *o++ = *jp++;
        }
    }
    if (*jp == '"') jp++;
    *o = 0;
    jpool_used += (size_t)(o - out) + 1;
    return out;
}

static jv *jparse(void)
{
    while (*jp && isspace((unsigned char)*jp)) jp++;
    if (*jp == '{') {
        jp++;
        jv *v = jnew(J_OBJ);
        int cap = 8;
        v->keys = xmalloc((size_t)cap * sizeof(char *));
        v->items = xmalloc((size_t)cap * sizeof(jv *));
        for (;;) {
            while (*jp && isspace((unsigned char)*jp)) jp++;
            if (*jp == '}' || !*jp) { if (*jp == '}') jp++; break; }
            if (v->n == cap) {
                cap *= 2;
                v->keys = realloc(v->keys, (size_t)cap * sizeof(char *));
                v->items = realloc(v->items, (size_t)cap * sizeof(jv *));
            }
            v->keys[v->n] = jstring();
            while (*jp && isspace((unsigned char)*jp)) jp++;
            if (*jp == ':') jp++;
            v->items[v->n] = jparse();
            v->n++;
            while (*jp && isspace((unsigned char)*jp)) jp++;
            if (*jp == ',') jp++;
        }
        return v;
    }
    if (*jp == '[') {
        jp++;
        jv *v = jnew(J_ARR);
        int cap = 8;
        v->items = xmalloc((size_t)cap * sizeof(jv *));
        for (;;) {
            while (*jp && isspace((unsigned char)*jp)) jp++;
            if (*jp == ']' || !*jp) { if (*jp == ']') jp++; break; }
            if (v->n == cap) {
                cap *= 2;
                v->items = realloc(v->items, (size_t)cap * sizeof(jv *));
            }
            v->items[v->n] = jparse();
            v->n++;
            while (*jp && isspace((unsigned char)*jp)) jp++;
            if (*jp == ',') jp++;
        }
        return v;
    }
    if (*jp == '"') {
        jv *v = jnew(J_STR);
        v->str = jstring();
        return v;
    }
    if (!strncmp(jp, "true", 4)) { jp += 4; jv *v = jnew(J_BOOL); v->num = 1; return v; }
    if (!strncmp(jp, "false", 5)) { jp += 5; return jnew(J_BOOL); }
    if (!strncmp(jp, "null", 4)) { jp += 4; return jnew(J_NULL); }
    jv *v = jnew(J_NUM);
    v->num = strtod(jp, &jp);
    return v;
}

static jv *jget(jv *o, const char *k)
{
    if (!o || o->t != J_OBJ) return NULL;
    for (int i = 0; i < o->n; i++)
        if (!strcmp(o->keys[i], k)) return o->items[i];
    return NULL;
}

static int jint(jv *o, const char *k, int dflt)
{
    jv *v = jget(o, k);
    return v && v->t == J_NUM ? (int)v->num : dflt;
}

/* ---------------------------------------------------------------- instance */

static int W, H, L, NV, WH;
static int *layer_delay;
static int via_delay;
static int n_pins, n_nets;
static int *pin_vid;      /* pin id -> vid */
static int *pin_net;      /* pin id -> net id */
static int **net_pins;    /* net id -> pin ids, driver first */
static int *net_npins;
static char case_name[256];

static inline int cX(int v) { return v % W; }
static inline int cY(int v) { return (v / W) % H; }
static inline int cZ(int v) { return v / WH; }

static void load_instance(const char *path)
{
    FILE *f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "cannot open %s\n", path); exit(1); }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = xmalloc((size_t)sz + 1);
    if (fread(buf, 1, (size_t)sz, f) != (size_t)sz) { fprintf(stderr, "short read\n"); exit(1); }
    buf[sz] = 0;
    fclose(f);
    jp = buf;
    jv *root = jparse();

    jv *g = jget(root, "grid");
    W = jint(g, "width", 0);
    H = jint(g, "height", 0);
    L = jint(g, "layers", 0);
    WH = W * H;
    NV = W * H * L;

    jv *d = jget(root, "delay");
    jv *ld = jget(d, "layer_delay");
    layer_delay = xmalloc((size_t)L * sizeof(int));
    for (int z = 0; z < L; z++) layer_delay[z] = z < ld->n ? (int)ld->items[z]->num : 1;
    via_delay = jint(d, "via_delay", 1);

    jv *nm = jget(root, "name");
    snprintf(case_name, sizeof case_name, "%s", nm && nm->str ? nm->str : "case");

    jv *pins = jget(root, "pins");
    n_pins = pins ? pins->n : 0;
    pin_vid = xmalloc((size_t)n_pins * sizeof(int));
    pin_net = xmalloc((size_t)n_pins * sizeof(int));
    for (int i = 0; i < n_pins; i++) {
        jv *p = pins->items[i];
        int id = jint(p, "id", i);
        pin_vid[id] = (jint(p, "z", 0) * H + jint(p, "y", 0)) * W + jint(p, "x", 0);
        pin_net[id] = -1;
    }

    jv *nets = jget(root, "nets");
    n_nets = nets ? nets->n : 0;
    net_pins = xmalloc((size_t)n_nets * sizeof(int *));
    net_npins = xmalloc((size_t)n_nets * sizeof(int));
    for (int i = 0; i < n_nets; i++) {
        jv *n = nets->items[i];
        int id = jint(n, "id", i);
        jv *sinks = jget(n, "sinks");
        int drv = jint(n, "driver", 0);
        int ns = sinks ? sinks->n : 0;
        net_npins[id] = ns + 1;
        net_pins[id] = xmalloc((size_t)(ns + 1) * sizeof(int));
        net_pins[id][0] = drv;
        for (int s = 0; s < ns; s++) net_pins[id][s + 1] = (int)sinks->items[s]->num;
        pin_net[drv] = id;
        for (int s = 0; s < ns; s++) pin_net[net_pins[id][s + 1]] = id;
    }
}

/* edge key: type 0 = x step, 1 = y step, 2 = via; index = min endpoint */
static inline int eidx(int u, int v) { return u < v ? u : v; }
static inline int etype(int u, int v)
{
    int d = u < v ? v - u : u - v;
    return d == 1 ? 0 : d == W ? 1 : 2;
}

/* ---------------------------------------------------------------- rng */

static uint64_t rng_s = 88172645463325252ULL;
static inline uint64_t rnd(void)
{
    uint64_t x = rng_s;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    rng_s = x ? x : 1;
    return rng_s;
}
static inline double rnd01(void) { return (double)(rnd() >> 11) / 9007199254740992.0; }

/* ---------------------------------------------------------------- state */

#define VCONG 1.0
#define HIST_FAC 0.5
#define PRES0 0.5
#define PRES_MULT 1.7
#define MAX_ITERS 80

static int *occ_v;          /* #nets on vertex */
static int *occ_e[3];       /* #nets on edge */
static float *h_v;          /* congestion history */
static float *h_e[3];
static int *pin_wall;       /* vid -> owning net, or -1 */

static double *dist;
static int *stamp;
static int *prevv;
static int cur_stamp;

typedef struct {
    int *verts;  int nv, cap_v;
    int (*edges)[2]; int ne, cap_e;
    long long *vdist;      /* driver delay per tree vertex (during growth) */
    long long delay;       /* sum of sink delays */
} route_t;

static route_t *routes;
static int *net_routed;

/* tree membership: tree_member[v] == tree_gen -> in current tree */
static int *tree_member;
static int tree_gen;

typedef struct { double d; int v; } hitem;
static hitem *heap; static int heap_n, heap_cap;

static void heap_push(double d, int v)
{
    if (heap_n == heap_cap) {
        heap_cap = heap_cap ? heap_cap * 2 : 4096;
        heap = realloc(heap, (size_t)heap_cap * sizeof(hitem));
        if (!heap) { fprintf(stderr, "oom\n"); exit(1); }
    }
    int i = heap_n++;
    heap[i].d = d; heap[i].v = v;
    while (i > 0) {
        int p = (i - 1) / 2;
        if (heap[p].d <= heap[i].d) break;
        hitem t = heap[p]; heap[p] = heap[i]; heap[i] = t;
        i = p;
    }
}
static hitem heap_pop(void)
{
    hitem top = heap[0];
    heap[0] = heap[--heap_n];
    int i = 0;
    for (;;) {
        int l = 2 * i + 1, r = l + 1, m = i;
        if (l < heap_n && heap[l].d < heap[m].d) m = l;
        if (r < heap_n && heap[r].d < heap[m].d) m = r;
        if (m == i) break;
        hitem t = heap[m]; heap[m] = heap[i]; heap[i] = t;
        i = m;
    }
    return top;
}

static int *touched; static int touched_n, touched_cap;
static void touch(int v)
{
    if (touched_n == touched_cap) {
        touched_cap = touched_cap ? touched_cap * 2 : 4096;
        touched = realloc(touched, (size_t)touched_cap * sizeof(int));
        if (!touched) { fprintf(stderr, "oom\n"); exit(1); }
    }
    touched[touched_n++] = v;
}
static void scratch_reset(void)
{
    for (int i = 0; i < touched_n; i++) stamp[touched[i]] = 0;
    touched_n = 0;
}

static void route_occ(route_t *r, int sign)
{
    for (int i = 0; i < r->nv; i++) occ_v[r->verts[i]] += sign;
    for (int i = 0; i < r->ne; i++) {
        int u = r->edges[i][0], v = r->edges[i][1];
        occ_e[etype(u, v)][eidx(u, v)] += sign;
    }
}

static void route_free(route_t *r)
{
    free(r->verts); free(r->edges); free(r->vdist);
    memset(r, 0, sizeof *r);
}

static void route_append(route_t *r, int v, long long d)
{
    if (r->nv == r->cap_v) {
        r->cap_v = r->cap_v ? r->cap_v * 2 : 16;
        r->verts = realloc(r->verts, (size_t)r->cap_v * sizeof(int));
        r->vdist = realloc(r->vdist, (size_t)r->cap_v * sizeof(long long));
        if (!r->verts || !r->vdist) { fprintf(stderr, "oom\n"); exit(1); }
    }
    r->verts[r->nv] = v;
    r->vdist[r->nv] = d;
    r->nv++;
}

static void route_append_edge(route_t *r, int u, int v)
{
    if (r->ne == r->cap_e) {
        r->cap_e = r->cap_e ? r->cap_e * 2 : 16;
        r->edges = realloc(r->edges, (size_t)r->cap_e * sizeof *r->edges);
        if (!r->edges) { fprintf(stderr, "oom\n"); exit(1); }
    }
    r->edges[r->ne][0] = u;
    r->edges[r->ne][1] = v;
    r->ne++;
}

/* exact driver->sink delays via BFS over the tree edges */
static long long route_delay_bfs(route_t *r, int nid)
{
    if (r->nv <= 1) return 0;
    int np = net_npins[nid];
    /* adjacency via edge list (nets are small) */
    long long *dd = xmalloc((size_t)r->nv * sizeof(long long));
    int *bfs = xmalloc((size_t)r->nv * sizeof(int));
    int head = 0, tail = 0;
    int driver = pin_vid[net_pins[nid][0]];
    /* index map vid -> local */
    for (int i = 0; i < r->nv; i++) {
        dd[i] = -1;
        if (r->verts[i] == driver) { dd[i] = 0; bfs[tail++] = i; }
    }
    while (head < tail) {
        int i = bfs[head++];
        int u = r->verts[i];
        for (int e = 0; e < r->ne; e++) {
            int a = r->edges[e][0], b = r->edges[e][1];
            int other = -1;
            if (a == u) other = b;
            else if (b == u) other = a;
            if (other < 0) continue;
            int j = -1;
            for (int k = 0; k < r->nv; k++) if (r->verts[k] == other) { j = k; break; }
            if (j >= 0 && dd[j] < 0) {
                int t = etype(a, b);
                int dly = t == 2 ? via_delay : layer_delay[cZ(a)];
                dd[j] = dd[i] + dly;
                bfs[tail++] = j;
            }
        }
    }
    long long s = 0;
    for (int p = 1; p < np; p++) {
        int sink = pin_vid[net_pins[nid][p]];
        for (int k = 0; k < r->nv; k++)
            if (r->verts[k] == sink) { s += dd[k] >= 0 ? dd[k] : 0; break; }
    }
    free(dd); free(bfs);
    return s;
}

/* grow net nid's tree. soft: negotiated costs; hard: strict capacity.
 * returns 0 ok, -1 unroutable. route must be empty.
 * seed_alpha scales how strongly attachments chase small driver distance
 * (1.0 = pure objective-aware, 0.0 = nearest-attachment like the baseline).
 * permute_sinks: randomize the attachment order when set. */
static double seed_alpha = 1.0;
static int permute_sinks = 0;
static int route_net(int nid, double pres, int hard)
{
    route_t *r = &routes[nid];
    int np = net_npins[nid];
    int driver = pin_vid[net_pins[nid][0]];

    tree_gen++;
    route_append(r, driver, 0);
    tree_member[driver] = tree_gen;

    int *rem = xmalloc((size_t)np * sizeof(int));
    int nrem = 0;
    for (int i = 1; i < np; i++) rem[nrem++] = pin_vid[net_pins[nid][i]];
    if (permute_sinks && nrem > 1) {
        for (int i = nrem - 1; i > 0; i--) {
            int j = (int)(rnd() % (uint64_t)(i + 1));
            int t = rem[i]; rem[i] = rem[j]; rem[j] = t;
        }
    }

    int *path = xmalloc((size_t)NV * sizeof(int));

    while (nrem > 0) {
        cur_stamp++;
        heap_n = 0;
        for (int k = 0; k < r->nv; k++) {
            int v = r->verts[k];
            stamp[v] = cur_stamp;
            dist[v] = seed_alpha * (double)r->vdist[k];
            prevv[v] = -1;
            touch(v);
            heap_push(seed_alpha * (double)r->vdist[k], v);
        }
        int found = -1;
        while (heap_n > 0) {
            hitem it = heap_pop();
            int u = it.v;
            if (stamp[u] != cur_stamp || it.d > dist[u]) continue;
            int is_rem = 0;
            for (int q = 0; q < nrem; q++)
                if (rem[q] == u) { is_rem = 1; break; }
            if (is_rem) { found = u; break; }
            int x = cX(u), y = cY(u), z = cZ(u);
            static const int dx[6] = { 1, -1, 0, 0, 0, 0 };
            static const int dy[6] = { 0, 0, 1, -1, 0, 0 };
            static const int dz[6] = { 0, 0, 0, 0, 1, -1 };
            for (int m = 0; m < 6; m++) {
                int nx = x + dx[m], ny = y + dy[m], nz = z + dz[m];
                if (nx < 0 || nx >= W || ny < 0 || ny >= H || nz < 0 || nz >= L) continue;
                int v = (nz * H + ny) * W + nx;
                if (tree_member[v] == tree_gen) continue;
                if (pin_wall[v] != -1 && pin_wall[v] != nid) continue;
                int t = m < 4 ? (m < 2 ? 0 : 1) : 2;
                int e = eidx(u, v);
                int other_e = occ_e[t][e];
                int other_v = occ_v[v];
                if (hard && (other_e || other_v)) continue;
                int dly = t == 2 ? via_delay : layer_delay[z];
                double c = dly * (1.0 + h_e[t][e] + pres * other_e)
                         + VCONG * (h_v[v] + pres * other_v);
                double nd = dist[u] + c;
                if (stamp[v] != cur_stamp || nd < dist[v] - 1e-9) {
                    if (stamp[v] != cur_stamp) { stamp[v] = cur_stamp; touch(v); }
                    dist[v] = nd;
                    prevv[v] = u;
                    heap_push(nd, v);
                }
            }
        }
        if (found < 0) {
            scratch_reset();
            free(rem); free(path);
            return -1;
        }
        int plen = 0;
        int v = found;
        while (v != -1 && tree_member[v] != tree_gen) {
            path[plen++] = v;
            v = prevv[v];
        }
        int seed = v;    /* seed is a tree vertex (or found == driver, plen==0) */
        long long dseed = 0;
        for (int i = 0; i < r->nv; i++)
            if (r->verts[i] == seed) { dseed = r->vdist[i]; break; }
        int prev = seed;
        for (int i = plen - 1; i >= 0; i--) {
            int u = path[i];
            int t = etype(prev, u);
            int dly = t == 2 ? via_delay : layer_delay[cZ(prev)];
            route_append_edge(r, prev, u);
            route_append(r, u, dseed + dly);
            dseed += dly;
            tree_member[u] = tree_gen;
            prev = u;
        }
        /* sinks along the path are connected too */
        {
            int keep = 0;
            for (int q = 0; q < nrem; q++) {
                int onpath = rem[q] == found;
                for (int i = 0; !onpath && i < plen; i++)
                    if (path[i] == rem[q]) onpath = 1;
                if (!onpath) rem[keep++] = rem[q];
            }
            nrem = keep;
        }
        scratch_reset();
    }
    free(rem);
    free(path);
    r->delay = route_delay_bfs(r, nid);
    return 0;
}

static long long total_delay(void)
{
    long long s = 0;
    for (int n = 0; n < n_nets; n++)
        if (net_routed[n]) s += routes[n].delay;
    return s;
}

static int all_routed(void)
{
    for (int n = 0; n < n_nets; n++)
        if (!net_routed[n]) return 0;
    return 1;
}

static int overuse_scan(int bump)
{
    int over = 0;
    for (int v = 0; v < NV; v++)
        if (occ_v[v] > 1) { over += occ_v[v] - 1; if (bump) h_v[v] += HIST_FAC; }
    for (int t = 0; t < 3; t++)
        for (int e = 0; e < NV; e++)
            if (occ_e[t][e] > 1) { over += occ_e[t][e] - 1; if (bump) h_e[t][e] += HIST_FAC; }
    return over;
}

static int touching_overuse(int nid)
{
    route_t *r = &routes[nid];
    for (int i = 0; i < r->nv; i++)
        if (occ_v[r->verts[i]] > 1) return 1;
    for (int i = 0; i < r->ne; i++) {
        int u = r->edges[i][0], v = r->edges[i][1];
        if (occ_e[etype(u, v)][eidx(u, v)] > 1) return 1;
    }
    return 0;
}

static int *net_bbox;
static int *rip_list; static int rip_n;

/* full negotiated pass. 0 = legal complete routing found. */
static int negotiate(int seed)
{
    rng_s = seed ? (uint64_t)seed : 88172645463325252ULL;

    for (int n = 0; n < n_nets; n++) {
        if (net_routed[n]) route_occ(&routes[n], -1);
        net_routed[n] = 0;
        route_free(&routes[n]);
    }
    memset(h_v, 0, (size_t)NV * sizeof(float));
    for (int t = 0; t < 3; t++) memset(h_e[t], 0, (size_t)NV * sizeof(float));

    /* order: bbox desc, seeded jitter */
    int *order = xmalloc((size_t)n_nets * sizeof(int));
    for (int i = 0; i < n_nets; i++) {
        order[i] = i;
        int minx = 1 << 30, maxx = -1, miny = 1 << 30, maxy = -1, minz = 1 << 30, maxz = -1;
        for (int p = 0; p < net_npins[i]; p++) {
            int v = pin_vid[net_pins[i][p]];
            int x = cX(v), y = cY(v), z = cZ(v);
            if (x < minx) minx = x; if (x > maxx) maxx = x;
            if (y < miny) miny = y; if (y > maxy) maxy = y;
            if (z < minz) minz = z; if (z > maxz) maxz = z;
        }
        net_bbox[i] = (maxx - minx) + (maxy - miny) + (maxz - minz);
    }
    for (int i = 1; i < n_nets; i++) {
        int cur = order[i], j = i - 1;
        while (j >= 0 && net_bbox[order[j]] < net_bbox[cur]) {
            order[j + 1] = order[j];
            j--;
        }
        order[j + 1] = cur;
    }

    double pres = PRES0;
    int first = 1;
    for (int it = 0; it < MAX_ITERS; it++) {
        if (first) {
            for (int i = 0; i < n_nets; i++) {
                if (route_net(order[i], pres, 0) == 0) {
                    net_routed[order[i]] = 1;
                    route_occ(&routes[order[i]], +1);
                } else {
                    fprintf(stderr, "  net %d unroutable (soft)\n", order[i]);
                }
            }
            first = 0;
        } else {
            rip_n = 0;
            for (int n = 0; n < n_nets; n++)
                if (net_routed[n] && touching_overuse(n)) rip_list[rip_n++] = n;
            if (rip_n == 0 && all_routed()) { free(order); return 0; }
            for (int i = 0; i < rip_n; i++) {
                route_occ(&routes[rip_list[i]], -1);
                net_routed[rip_list[i]] = 0;
                route_free(&routes[rip_list[i]]);
            }
            for (int i = 0; i < rip_n; i++) {
                if (route_net(rip_list[i], pres, 0) == 0) {
                    net_routed[rip_list[i]] = 1;
                    route_occ(&routes[rip_list[i]], +1);
                }
            }
        }
        int over = overuse_scan(1);
        pres *= PRES_MULT;
        if (over == 0 && all_routed()) { free(order); return 0; }
        if (over == 0 && !all_routed()) { free(order); return -1; }
    }
    free(order);
    return -1;
}

/* one polish sweep: every net alone, rip + reroute hard + keep if better.
 * permute sinks so repeated sweeps explore different tree shapes. */
static long long polish_sweep(long long best)
{
    permute_sinks = 1;
    int improved = 0;
    /* worst-delay nets first: order by delay desc */
    int *order = xmalloc((size_t)n_nets * sizeof(int));
    for (int i = 0; i < n_nets; i++) order[i] = i;
    for (int i = 1; i < n_nets; i++) {
        int cur = order[i], j = i - 1;
        while (j >= 0 && routes[order[j]].delay < routes[cur].delay) {
            order[j + 1] = order[j];
            j--;
        }
        order[j + 1] = cur;
    }
    for (int k = 0; k < n_nets; k++) {
        int n = order[k];
        if (!net_routed[n]) continue;
        route_t saved = routes[n];
        long long saved_delay = routes[n].delay;
        route_occ(&routes[n], -1);
        net_routed[n] = 0;
        memset(&routes[n], 0, sizeof(route_t));
        if (route_net(n, 0.0, 1) == 0) {
            net_routed[n] = 1;
            route_occ(&routes[n], +1);
            if (routes[n].delay < saved_delay) {
                best += routes[n].delay - saved_delay;
                improved++;
                route_free(&saved);
            } else {
                route_occ(&routes[n], -1);
                net_routed[n] = 0;
                route_free(&routes[n]);
                routes[n] = saved;
                net_routed[n] = 1;
                route_occ(&routes[n], +1);
            }
        } else {
            route_free(&routes[n]);
            routes[n] = saved;
            net_routed[n] = 1;
            route_occ(&routes[n], +1);
        }
    }
    permute_sinks = 0;
    free(order);
    fprintf(stderr, "  polish: %d nets improved, delay %lld\n", improved, best);
    return best;
}

/* LNS: rip batches, reroute against hard capacity, keep improvements. */
static long long lns(long long best, double seconds, int seed)
{
    /* note: history clearing and rng seeding happen once in the refine
     * driver; subsequent calls continue from the current state. */
    if (seed) rng_s = (uint64_t)seed * 2654435761u + 7;
    permute_sinks = 1;
    struct timespec t0;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    int rounds = 0, accepted = 0;

    int *batch = xmalloc((size_t)n_nets * sizeof(int));
    route_t *saved = xmalloc((size_t)n_nets * sizeof(route_t));

    for (;;) {
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC, &now);
        double el = (double)(now.tv_sec - t0.tv_sec);
        if (el > seconds) break;
        rounds++;

        int want = 1 + (int)(n_nets * (0.10 + 0.15 * rnd01()));
        if (want > n_nets) want = n_nets;
        int nb = 0;
        for (int tries = 0; tries < want * 6 && nb < want; tries++) {
            int n = (int)(rnd() % (uint64_t)n_nets);
            if (!net_routed[n]) continue;
            int dup = 0;
            for (int i = 0; i < nb; i++) if (batch[i] == n) { dup = 1; break; }
            if (!dup) batch[nb++] = n;
        }
        if (nb == 0) continue;

        /* shuffle the batch FIRST so saved[] indices stay aligned */
        for (int i = nb - 1; i > 0; i--) {
            int j = (int)(rnd() % (uint64_t)(i + 1));
            int t = batch[i]; batch[i] = batch[j]; batch[j] = t;
        }

        for (int i = 0; i < nb; i++) {
            saved[i] = routes[batch[i]];
            route_occ(&routes[batch[i]], -1);
            net_routed[batch[i]] = 0;
            memset(&routes[batch[i]], 0, sizeof(route_t));
        }
        int ok = 1;
        for (int i = 0; i < nb && ok; i++) {
            if (route_net(batch[i], 0.0, 1) != 0) ok = 0;
            else { net_routed[batch[i]] = 1; route_occ(&routes[batch[i]], +1); }
        }
        if (ok) {
            long long cur = total_delay();
            if (cur < best) {
                best = cur;
                accepted++;
                for (int i = 0; i < nb; i++) route_free(&saved[i]);
            } else {
                ok = 0;  /* revert below */
            }
        }
        if (!ok) {
            for (int i = 0; i < nb; i++) {
                if (net_routed[batch[i]]) {
                    route_occ(&routes[batch[i]], -1);
                    net_routed[batch[i]] = 0;
                }
                route_free(&routes[batch[i]]);
                routes[batch[i]] = saved[i];
                net_routed[batch[i]] = 1;
                route_occ(&routes[batch[i]], +1);
            }
        }
    }

    fprintf(stderr, "  lns: %d rounds, %d accepted, delay %lld\n", rounds, accepted, best);
    permute_sinks = 0;
    free(batch);
    free(saved);
    return best;
}

static void write_sol(const char *path)
{
    FILE *f = fopen(path, "w");
    if (!f) { fprintf(stderr, "cannot write %s\n", path); exit(1); }
    fprintf(f, "{\n \"format\": \"m3d-submission\",\n \"version\": 1,\n"
               " \"instance\": \"%s\",\n \"routes\": [\n", case_name);
    for (int n = 0; n < n_nets; n++) {
        fprintf(f, "  {\"net\": %d, \"edges\": [", n);
        for (int i = 0; i < routes[n].ne; i++) {
            int u = routes[n].edges[i][0], v = routes[n].edges[i][1];
            fprintf(f, "%s[[%d,%d,%d],[%d,%d,%d]]", i ? "," : "",
                    cX(u), cY(u), cZ(u), cX(v), cY(v), cZ(v));
        }
        fprintf(f, "]}%s\n", n + 1 < n_nets ? "," : "");
    }
    fprintf(f, " ]\n}\n");
    fclose(f);
}

int main(int argc, char **argv)
{
    if (argc < 3) {
        fprintf(stderr, "usage: %s <case.json> <out.sol.json> [budget-secs] [seed] [alpha]\n", argv[0]);
        return 1;
    }
    double budget = argc > 3 ? atof(argv[3]) : 10.0;
    int seed = argc > 4 ? atoi(argv[4]) : 1;
    if (argc > 5) seed_alpha = atof(argv[5]);

    load_instance(argv[1]);

    occ_v = xcalloc((size_t)NV, sizeof(int));
    for (int t = 0; t < 3; t++) occ_e[t] = xcalloc((size_t)NV, sizeof(int));
    h_v = xcalloc((size_t)NV, sizeof(float));
    for (int t = 0; t < 3; t++) h_e[t] = xcalloc((size_t)NV, sizeof(float));
    dist = xmalloc((size_t)NV * sizeof(double));
    stamp = xcalloc((size_t)NV, sizeof(int));
    prevv = xmalloc((size_t)NV * sizeof(int));
    tree_member = xcalloc((size_t)NV, sizeof(int));
    pin_wall = xmalloc((size_t)NV * sizeof(int));
    for (int v = 0; v < NV; v++) pin_wall[v] = -1;
    for (int p = 0; p < n_pins; p++) pin_wall[pin_vid[p]] = pin_net[p];
    routes = xcalloc((size_t)n_nets, sizeof(route_t));
    net_routed = xcalloc((size_t)n_nets, sizeof(int));
    rip_list = xmalloc((size_t)n_nets * sizeof(int));
    net_bbox = xmalloc((size_t)n_nets * sizeof(int));

    struct timespec t0;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    long long best = -1;
    int best_seed = -1;
    int restarts = budget >= 100 ? 3 : (budget >= 40 ? 2 : 1);
    for (int r = 0; r < restarts; r++) {
        int s = seed + r * 977;
        if (negotiate(s) == 0) {
            long long d = total_delay();
            fprintf(stderr, "  restart %d (seed %d): legal, delay %lld\n", r, s, d);
            if (best < 0 || d < best) { best = d; best_seed = s; }
        } else {
            fprintf(stderr, "  restart %d (seed %d): no legal solution\n", r, s);
        }
    }
    if (best < 0) {
        fprintf(stderr, "FAILED to route %s\n", case_name);
        return 2;
    }
    if (best_seed != seed + (restarts - 1) * 977) {
        /* reproduce the champion deterministically */
        fprintf(stderr, "re-running best seed %d\n", best_seed);
        negotiate(best_seed);
    }

    struct timespec t1;
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double used = (double)(t1.tv_sec - t0.tv_sec);
    double left = budget - used;
    if (left > 1.0) {
        /* alternate polish sweeps and LNS batches until the budget ends */
        rng_s = (uint64_t)seed * 2654435761u + 7;
        memset(h_v, 0, (size_t)NV * sizeof(float));
        for (int t = 0; t < 3; t++) memset(h_e[t], 0, (size_t)NV * sizeof(float));
        struct timespec tr;
        clock_gettime(CLOCK_MONOTONIC, &tr);
        double slice = left / 8.0;
        if (slice < 2.0) slice = left;
        for (;;) {
            best = polish_sweep(best);
            if (slice >= left) { best = lns(best, left, seed); break; }
            best = lns(best, slice, seed);
            struct timespec tn;
            clock_gettime(CLOCK_MONOTONIC, &tn);
            double el = (double)(tn.tv_sec - tr.tv_sec);
            if (el >= left) break;
            if (left - el < 2.0) break;
        }
    }
    else best = total_delay();
    /* the refine loop never makes things illegal; re-verify bookkeeping */
    best = total_delay();

    write_sol(argv[2]);

    struct timespec t2;
    clock_gettime(CLOCK_MONOTONIC, &t2);
    double total = (double)(t2.tv_sec - t0.tv_sec);
    fprintf(stderr, "%s: nets=%d total_delay=%lld time=%.2fs\n",
            case_name, n_nets, best, total);
    printf("%s %lld %.3f\n", case_name, best, total);
    return 0;
}
