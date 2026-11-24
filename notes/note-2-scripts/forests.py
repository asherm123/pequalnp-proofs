# Exhaustive check: every forest (no isolated vertices, up to isomorphism) on n<=6 vertices,
# B2 minimum size of f_G equals |E|+tau(G)-1.
import itertools, time
from b2sat import *
def canon(n,E):
    best=None
    for p in itertools.permutations(range(n)):
        k=tuple(sorted(tuple(sorted((p[u],p[v]))) for u,v in E))
        if best is None or k<best: best=k
    return best
def is_forest(n,E):
    par=list(range(n))
    def f(a):
        while par[a]!=a: a=par[a]
        return a
    for u,v in E:
        a,b=f(u),f(v)
        if a==b: return False
        par[a]=b
    return True
seen=set(); bad=0; cnt=0
for n in range(2,7):
    allE=list(itertools.combinations(range(n),2))
    for m in range(1,n):
        for E in itertools.combinations(allE,m):
            if not is_forest(n,E): continue
            if len({x for e in E for x in e})<n: continue
            c=canon(n,E)
            if c in seen: continue
            seen.add(c); cnt+=1
            f=edge_fn(n,E); pred=len(E)+tau(n,E)-1
            # lower bound check: no circuit of size pred-1; upper: circuit of size pred
            r1,_=circuit_exists(n,f,pred-1,900) if pred>=2 else (False,None)
            r2,_=circuit_exists(n,f,pred,900)
            ok = (r1 is False) and (r2 is True)
            if not ok: bad+=1
            print(n,E,"pred",pred,"no(pred-1):",r1 is False,"yes(pred):",r2,"OK" if ok else "MISMATCH",flush=True)
print("forests checked",cnt,"mismatches",bad,flush=True)
