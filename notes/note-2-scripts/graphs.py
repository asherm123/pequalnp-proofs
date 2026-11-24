import sys, time
from b2sat import *
def path(n): return n,[(i,i+1) for i in range(n-1)]
def cycle(n): return n,[(i,(i+1)%n) for i in range(n)]
def star(k): return k+1,[(0,i) for i in range(1,k+1)]
def spider(): return 7,[(0,1),(1,2),(0,3),(3,4),(0,5),(5,6)]
cases=[("P3",path(3)),("P4",path(4)),("P5",path(5)),("P6",path(6)),("S3",star(3)),("S4",star(4)),
       ("C4",cycle(4)),("C5",cycle(5)),("C6",cycle(6)),("P7",path(7)),("spider",spider())]
for name,(n,E) in cases:
    if len(sys.argv)>1 and name not in sys.argv[1:]: continue
    f=edge_fn(n,E); t=tau(n,E); pred=len(E)+t-1
    t0=time.time()
    # check pred-1 first (is B2 cheaper?) then pred
    lo=n-1
    s,last,c=min_size(n,f,lo=lo,hi=pred+1,timeout=900)
    print(name,"n=",n,"|E|+tau-1=",pred,"B2 min=",s if s else f"unknown (>= {last}? started at {lo})", "circ=",c, f"{time.time()-t0:.1f}s",flush=True)
