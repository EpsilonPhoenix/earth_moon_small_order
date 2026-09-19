"""Independent complete enumeration, using only the Python standard library.
No graph catalogue, NetworkX, SAT solver, or isomorphism library is used.
B has order 9 and independence number 6, so it has a vertex cover of size 3.
Enumerate that 3-vertex graph (empty, edge, or P3) and the six independent
vertices' neighborhoods as multisets. Then enumerate the seven rows of A.
All outputs must have the explicit five-twin-class form. This is a complete
second generation of the relevant 17-vertex graphs, not only a spot check.
"""

if not __debug__:
    raise RuntimeError("Run without -O: verification assertions must remain enabled")

import itertools as it,json,pathlib,time,collections
R=pathlib.Path(__file__).resolve().parent

def adj_of(n,edges):
 a=[0]*n
 for u,v in edges:a[u]|=1<<v;a[v]|=1<<u
 return a

def indsets(a):
 n=len(a);good=[True]*(1<<n);out=[]
 for mask in range(1<<n):
  if mask:
   bit=mask&-mask;v=bit.bit_length()-1;good[mask]=good[mask^bit] and not(a[v]&(mask^bit))
  if good[mask]:out.append(mask)
 return out

def run():
 t=time.time();cnt=collections.Counter();outputs=[]
 for de in [[],[(0,1)],[(0,1),(1,2)]]:
  da=adj_of(3,de);patterns=indsets(da)
  for neighborhood_types in it.combinations_with_replacement(patterns,6):
   cnt['B_encodings']+=1
   be=de+[(d,3+c) for c,mask in enumerate(neighborhood_types) for d in range(3) if mask>>d&1]
   eb=len(be)
   if not 8<=eb<=13:continue
   ba=adj_of(9,be);ii=indsets(ba)
   if max(x.bit_count() for x in ii)>6:continue
   cnt['B_encodings_after_filters']+=1
   mis=[x for x in ii if all((x>>v&1) or (x&ba[v]) for v in range(9))]
   mis.sort(key=lambda x:(-x.bit_count(),x));deg=[0]*9;chosen=[]
   pairs=[(u,v) for u,v in it.combinations(range(9),2) if not(ba[u]>>v&1) and not(ba[u]&ba[v])]
   def visit(start,weight):
    k=len(chosen);left=7-k
    if 6*k-weight>5 or weight+left*6+eb<50:return
    if not left:
     if weight+eb<50:return
     cnt['degree_edge_feasible']+=1
     if any(not any((s>>u&1) and (s>>v&1) for s in chosen) for u,v in pairs):return
     if any(s.bit_count()+sum(not(s&x) for x in chosen)>7 for s in ii):return
     cnt['feasible_encodings']+=1
     fe=[(0,v) for v in range(1,8)]+[(u+8,v+8) for u,v in be]+[(i+1,j+8) for i,s in enumerate(chosen) for j in range(9) if s>>j&1]
     fa=adj_of(17,fe);groups={}
     for v in range(17):groups.setdefault(fa[v],[]).append(v)
     pp=list(groups.values());assert sorted(map(len,pp))==[3,3,3,4,4]
     quot=[(i,j) for i,j in it.combinations(range(5),2) if fa[pp[i][0]]>>pp[j][0]&1]
     qa=adj_of(5,quot);assert all(q.bit_count()==2 for q in qa)
     # The two size-four twin classes are adjacent in F.
     a,b=[i for i,p in enumerate(pp) if len(p)==4];assert qa[a]>>b&1
     # Give a literal non-biplanarity certificate for its cone complement.
     tri_free=[]
     for i,j in it.combinations(range(5),2):
      if not(qa[i]>>j&1):tri_free.extend((u,v) for u in pp[i] for v in pp[j])
     tri_free.extend((v,17) for v in pp[a]+pp[b]);ta=adj_of(18,tri_free)
     assert len(tri_free)==65 and all(not(ta[u]&ta[v]) for u,v in tri_free)
     outputs.append(dict(B_edges=be,row_masks=list(chosen),F_edges=fe,twin_classes=pp,obstruction_edges=tri_free))
     return
    for j in range(start,len(mis)):
     s=mis[j]
     if 6*(k+1)-weight-s.bit_count()>5:continue
     vs=[v for v in range(9) if s>>v&1]
     if any(deg[v]+ba[v].bit_count()>=7 for v in vs):continue
     for v in vs:deg[v]+=1
     chosen.append(s);visit(j,weight+s.bit_count());chosen.pop()
     for v in vs:deg[v]-=1
   visit(0,0)
 out=dict(status='complete',seconds=time.time()-t,counts=dict(cnt),all_feasible_have_five_cycle_twin_quotient=True,all_cones_have_triangle_free_65_edge_obstruction=True,encodings=outputs)
 (R/'dense17_independent_verification.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='encodings'},flush=True)
if __name__=='__main__':run()
