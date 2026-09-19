"""Independent standard-library-only exhaustive labeled residual-graph check.
Enumerates every triangle-free six-vertex B with at most six edges, then
all multisets of six maximal independent neighborhoods. No atlas/isomorphism
or SAT/coloring implementation is used. Outputs are classified by the
weighted five-cycle of false-twin classes, canonically under D5.
"""

if not __debug__:
    raise RuntimeError("Run without -O: verification assertions must remain enabled")

import itertools as it,json,pathlib,time,collections
from verify_dense17_independent import adj_of,indsets
R=pathlib.Path(__file__).resolve().parent

def cycle_type(a):
 groups={}
 for v in range(len(a)):groups.setdefault(a[v],[]).append(v)
 pp=list(groups.values());assert len(pp)==5
 qa=[sum(1<<j for j in range(5) if a[pp[i][0]]>>pp[j][0]&1) for i in range(5)];assert all(x.bit_count()==2 for x in qa)
 types=[]
 for first in range(5):
  for second in range(5):
   if not(qa[first]>>second&1):continue
   path=[first,second]
   while len(path)<5:
    nxt=[v for v in range(5) if v not in path and qa[path[-1]]>>v&1];assert len(nxt)==1;path.append(nxt[0])
   assert qa[path[-1]]>>first&1;types.append(tuple(len(pp[v]) for v in path))
 return min(types)
def run():
 t=time.time();counts=collections.Counter();types=collections.Counter();reps={};pairs=list(it.combinations(range(6),2))
 for eb in range(7):
  for be in it.combinations(pairs,eb):
   counts['B_labeled']+=1;ba=adj_of(6,be)
   if any(ba[u]&ba[v] for u,v in be):continue
   counts['B_triangle_free']+=1;ii=indsets(ba)
   if max(s.bit_count() for s in ii)>5:continue
   mis=[s for s in ii if all((s>>v&1) or (s&ba[v]) for v in range(6))];mis.sort(key=lambda s:(-s.bit_count(),s))
   chosen=[];deg=[0]*6;uncovered=[(u,v) for u,v in pairs if not(ba[u]>>v&1) and not(ba[u]&ba[v])]
   def rec(start,w):
    k=len(chosen);left=6-k
    if 5*k-w>6 or 6+w+5*left+eb<36:return
    if not left:
     counts['edge_degree_feasible']+=1
     if any(not any(s>>u&1 and s>>v&1 for s in chosen) for u,v in uncovered):return
     if any(s.bit_count()+sum(not(s&r) for r in chosen)>6 for s in ii):return
     counts['feasible']+=1
     fe=[(0,v) for v in range(1,7)]+[(u+7,v+7) for u,v in be]+[(i+1,v+7) for i,s in enumerate(chosen) for v in range(6) if s>>v&1];fa=adj_of(13,fe);typ=cycle_type(fa);types[typ]+=1;reps.setdefault(typ,fe);return
    for j in range(start,len(mis)):
     s=mis[j];vs=[v for v in range(6) if s>>v&1]
     if any(deg[v]+ba[v].bit_count()>=6 for v in vs):continue
     for v in vs:deg[v]+=1
     chosen.append(s);rec(j,w+s.bit_count());chosen.pop()
     for v in vs:deg[v]-=1
   rec(0,0)
 known=json.loads((R/'mtf13_results.json').read_text())['graphs'];known_types={cycle_type(adj_of(13,r['F_edges'])) for r in known};assert set(types)==known_types and len(types)==4
 out=dict(status='complete',seconds=time.time()-t,counts=dict(counts),all_outputs_match_original_enumeration=True,types=[dict(cyclic_twin_sizes=key,encodings=types[key],F_edges=reps[key]) for key in sorted(types)])
 (R/'mtf13_independent_verification.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='types'},flush=True)
if __name__=='__main__':run()
