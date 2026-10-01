# Transliteration of the KP1Y object definitions (as read from the Lean sources) into Python,
# used only to cross-check against the independent JS engine y1/engine.js.
import json, sys, itertools, subprocess

def select(frame, value, n):
    # greatest ancestor p of c in frame with 0<value(p)<value(c)
    par = [None]*n
    for c in range(n):
        p = frame[c]
        best = None
        while p is not None:
            if 0 < value[p] < value[c]:
                best = p; break   # ancestors visited in decreasing order -> first hit is greatest
            p = frame[p]
        par[c] = best
    return par

def rows_of(base_vals, base_forest, n):
    rows = [(base_vals, base_forest)]
    while True:
        V, P = rows[-1]
        d = [ (V[c]-V[P[c]]) if P[c] is not None else 0 for c in range(n)]
        if all(x == 0 for x in d):
            rows.append((d, [None]*n)); break
        rows.append((d, select(P, d, n)))
    return rows

def mountain(base_vals, base_forest, n):
    R = rows_of(base_vals, base_forest, n)
    def val(r, c): return R[r][0][c] if r < len(R) else 0
    def par(r, c): return R[r][1][c] if r < len(R) else None
    height = []
    for c in range(n):
        h = 0
        while val(h+1, c) > 0: h += 1
        height.append(h)
    return {'n': n, 'val': val, 'par': par, 'height': height}

def ancestors(par, r, c):
    out = []; p = par(r, c)
    while p is not None: out.append(p); p = par(r, p)
    return out

def root_at(Mt, r, c):
    q = c
    while Mt['par'](r, q) is not None: q = Mt['par'](r, q)
    return q

def next_layer(Mt):
    n = Mt['n']; h = Mt['height']
    top = [Mt['val'](h[c], c) for c in range(n)]
    pseudo = [None]*n
    for c in range(n):
        if h[c] == 0: continue
        cands = [p for p in ancestors(Mt['par'], h[c]-1, c) if h[p] == h[c] or h[p]+1 == h[c]]
        pseudo[c] = max(cands) if cands else None
    return top, select(pseudo, top, n)

def layers(s):
    n = len(s)
    lin = [None] + list(range(n-1))
    base = (list(s), select(lin, s, n))
    out = []
    while True:
        Mt = mountain(base[0], base[1], n)
        out.append(Mt)
        if all(v == 1 for v in base[0]): break
        base = next_layer(Mt)
    return out

def expand(s, N):
    m = len(s)
    if m == 0: return []
    x = m-1
    if s[x] == 1: return s[:x]
    Ls = layers(s)
    bad = None
    for k, Mt in enumerate(Ls):
        for r in range(Mt['height'][x]):
            p = Mt['par'](r, x)
            if p is not None and Mt['val'](r, x) == Mt['val'](r, p) + 1:
                bad = (k, r, p)
    K, level, y = bad
    L = x - y
    B = max(s)        # horizon = predecessor of strict SequenceBound
    width = x + N*L
    def raw(c):        # RawDecoded: (y,x] sources
        if c <= y: return (y+1, 0)
        return (y+1 + (c-y-1) % L, (c-y-1)//L)
    def dec(c):        # OrdinaryCoordinates.Decoded: [y,x) sources
        if c < y: return (c, 0)
        return (y + (c-y) % L, (c-y)//L)
    def pc(b, p):      # ParentCopy
        return p if p < y else p + b*L
    tower = []
    for k in range(B):
        X = Ls[k] if k < len(Ls) else None
        if X is None:   # beyond computed layers: all ones, no parents
            tower.append(([0]*width, lambda r, c: None)); continue
        hX = X['height']; pX = X['par']
        if k < K:      # Lower
            floor = hX[y]; rise = hX[x] - floor
            def incone(c, X=X, floor=floor, hX=hX): return hX[c] >= floor and root_at(X, floor, c) == y
            H = []; 
            for c in range(width):
                if c <= x: H.append(hX[c])
                else:
                    s_, b = raw(c); H.append(hX[s_] + b*rise if incone(s_) else hX[s_])
            def P(r, c, pX=pX, floor=floor, rise=rise, incone=incone, H=H):
                if r >= H[c]: return None
                if c <= x: return pX(r, c)
                s_, b = raw(c)
                if incone(s_) and floor <= r:
                    off = b*rise
                    u = floor if r < floor + off else r - off
                    p = pX(u, s_); return None if p is None else p + b*L
                p = pX(r, s_); return None if p is None else pc(b, p)
            tower.append((H, P))
        elif k == K:   # Terminal
            H = [hX[dec(c)[0]] for c in range(width)]
            def P(r, c, pX=pX, H=H):
                if r >= H[c]: return None
                if c < x: return pX(r, c)
                s_, b = raw(c)
                if s_ == x and level <= r: return pX(r, y)
                p = pX(r, s_); return None if p is None else pc(b, p)
            tower.append((H, P))
        else:          # Ordinary
            H = [hX[dec(c)[0]] for c in range(width)]
            def P(r, c, pX=pX, H=H):
                if r >= H[c]: return None
                s_, b = dec(c); p = pX(r, s_); return None if p is None else pc(b, p)
            tower.append((H, P))
    # reconstruction: Run with top all-one at layer B, Rebuilds downward (GridColumn equations)
    top = [1]*width
    for k in reversed(range(B)):
        H, P = tower[k]
        F = {}
        for c in range(width):
            col = {}
            col[H[c]] = top[c]
            for r in reversed(range(H[c])):
                p = P(r, c)
                assert p is not None and p < c, (k, r, c, p)
                col[r] = col[r+1] + F[p].get(r, 0)
            F[c] = col
        top = [F[c][0] for c in range(width)]
    return top

def legal_seqs(maxlen, maxval):
    for L_ in range(0, maxlen+1):
        for t in itertools.product(range(1, maxval+1), repeat=L_):
            if L_ == 0 or t[0] == 1: yield list(t)

if __name__ == '__main__':
    tests = []
    for s in legal_seqs(int(sys.argv[1]), int(sys.argv[2])):
        for N in range(0, 4): tests.append((s, N))
    js = subprocess.run(['node', sys.argv[3]], input=json.dumps(tests), capture_output=True, text=True)
    ref = json.loads(js.stdout)
    bad = 0
    for (s, N), r in zip(tests, ref):
        mine = expand(s, N)
        if r is None: continue
        if mine != r:
            bad += 1
            if bad <= 10: print('MISMATCH', s, N, mine, r)
    print('cases', len(tests), 'mismatches', bad)
