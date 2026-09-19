"""Rebuild the finite exclusions independently as binary MILPs for HiGHS.
No Z3 API, SMT parsing, or C++ graph/coloring code is used. Saved coloring
cuts are checked directly; induced-diamond cuts are reconstructed literally.
"""

if not __debug__:
    raise RuntimeError("Run without -O: verification assertions must remain enabled")

import itertools as it,json,pathlib,time,collections
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
R=pathlib.Path(__file__).resolve().parent
class Model:
 def __init__(self,n):self.n=n;self.rows=[];self.lb=[];self.ub=[]
 def var(self):i=self.n;self.n+=1;return i
 def add(self,terms,lo=-np.inf,hi=np.inf):
  d=collections.defaultdict(float)
  for j,a in terms:d[j]+=a
  self.rows.append(dict(d));self.lb.append(lo);self.ub.append(hi)
 def lex(self,a,b):
  self.add([(j,2**(len(a)-1-i)) for i,j in enumerate(a)]+[(j,-2**(len(b)-1-i)) for i,j in enumerate(b)],hi=0)
 def solve(self):
  ii=[];jj=[];dd=[]
  for i,row in enumerate(self.rows):
   for j,x in row.items():ii.append(i);jj.append(j);dd.append(x)
  A=coo_matrix((dd,(ii,jj)),shape=(len(self.rows),self.n)).tocsc()
  out=milp(np.zeros(self.n),integrality=np.ones(self.n),bounds=Bounds(np.zeros(self.n),np.ones(self.n)),constraints=LinearConstraint(A,np.array(self.lb),np.array(self.ub)),options={'time_limit':90,'mip_rel_gap':0.0})
  return dict(status=int(out.status),message=out.message,variables=self.n,constraints=len(self.rows))
def norm(es):return {tuple(sorted(e)) for e in es}
def critical13(r):
 be=norm(r['base_edges']);fixed=set(it.combinations(range(6),2))|{(u+6,v+6) for u,v in be};ve=[(u,v+6) for u in range(6) for v in range(7)];ix={e:i for i,e in enumerate(ve)};m=Model(42)
 bd=[sum(v in e for e in be) for v in range(7)];need=42-len(fixed);m.add([(j,1) for j in range(42)],need,need)
 for u in range(6):m.add([(ix[(u,v+6)],1) for v in range(7)],lo=1)
 for v in range(7):m.add([(ix[(u,v+6)],1) for u in range(6)],lo=6-bd[v])
 for size in range(1,7):
  for C in it.combinations(range(7),size):
   if any(e not in be for e in it.combinations(C,2)):continue
   for U in it.combinations(range(6),7-size):
    js=[ix[(u,v+6)] for u in U for v in C];m.add([(j,1) for j in js],hi=len(js)-1)
 if not any(all(e not in be for e in it.combinations(C,2)) for C in it.combinations(range(7),3)):
  ws=[]
  for u in range(6):
   for v,w in it.combinations(range(7),2):
    if (v,w) in be:continue
    t=m.var();ws.append(t)
    for j in [ix[(u,v+6)],ix[(u,w+6)]]:m.add([(t,1),(j,1)],hi=1)
  m.add([(j,1) for j in ws],lo=1)
 for u in range(5):m.lex([ix[(u,v+6)] for v in range(7)],[ix[(u+1,v+6)] for v in range(7)])
 bn=[{u for u in range(7) if tuple(sorted((u,v))) in be} for v in range(7)]
 for v,w in it.combinations(range(7),2):
  if bn[v]-{w}==bn[w]-{v}:m.lex([ix[(u,v+6)] for u in range(6)],[ix[(u,w+6)] for u in range(6)])
 high=[m.var() for v in range(13)]
 for v in range(13):
  fixeddeg=sum(v in e for e in fixed);incident=[j for j,e in enumerate(ve) if v in e]
  # delta>=6 is already imposed. These two inequalities make h equivalent to d>=7.
  m.add([(j,1) for j in incident]+[(high[v],-6)],hi=6-fixeddeg)
  m.add([(j,1) for j in incident]+[(high[v],-1)],lo=6-fixeddeg)
 for cut in r['diamond_cuts']:
  D=sorted(cut['vertices']);pat=norm(cut['edges']);assert len(D)==4 and len(pat)==5
  assert all(e in pat for e in it.combinations(D,2) if e in fixed)
  assert all(e in fixed or e in ix for e in pat)
  const=0;terms=[(high[v],1) for v in D]
  for e in it.combinations(D,2):
   if e not in ix:continue
   if e in pat:const+=1;terms.append((ix[e],-1))
   else:terms.append((ix[e],1))
  m.add(terms,lo=1-const)
 for c in r['coloring_cuts']:
  assert len(c)==13 and len(set(c))<=6 and all(c[u]!=c[v] for u,v in fixed)
  m.add([(j,1) for j,(u,v) in enumerate(ve) if c[u]==c[v]],lo=1)
 return m.solve()
def attachment(r):
 E=norm(r['base_edges']);m=Model(39);var=lambda i,v:13*i+v;deg=[sum(v in e for e in E) for v in range(13)]
 m.add([(j,1) for j in range(39)],hi=63-len(E))
 for i in range(3):m.add([(var(i,v),1) for v in range(13)],lo=7)
 for v in range(13):m.add([(var(i,v),1) for i in range(3)],lo=max(0,7-deg[v]))
 for C in it.combinations(range(13),6):
  if all(e in E for e in it.combinations(C,2)):
   for i in range(3):m.add([(var(i,v),1) for v in C],hi=5)
 for i in range(2):m.lex([var(i,v) for v in range(13)],[var(i+1,v) for v in range(13)])
 neighbors=[{u for u in range(13) if tuple(sorted((u,v))) in E} for v in range(13)]
 for group in r['twin_groups']:
  for u,v in zip(group,group[1:]):
   assert neighbors[u]-{v}==neighbors[v]-{u};m.lex([var(i,u) for i in range(3)],[var(i,v) for i in range(3)])
 for c in r['coloring_cuts']:
  assert len(c)==13 and len(set(c))==7 and all(c[u]!=c[v] for u,v in E)
  bs=[m.var() for i in range(3)];m.add([(b,1) for b in bs],lo=1)
  for i,b in enumerate(bs):
   for co in set(c):m.add([(var(i,v),1) for v in range(13) if c[v]==co]+[(b,-1)],lo=0)
 return m.solve()
def main():
 start=time.time();records=[]
 for name,fun in [('critical13_K6_results',critical13),('attachment_results',attachment)]:
  data=json.loads((R/(name+'.json')).read_text());assert data['complete']
  for r in data['results']:
   t=time.time();out=fun(r);out.update(family=name,base_index=r['base_index'],seconds=time.time()-t);records.append(out)
   print(name,r['base_index'],out['status'],round(out['seconds'],3),flush=True)
   (R/'independent_milp_verification.json').write_text(json.dumps(dict(status='complete' if len(records)==90 else 'running',all_infeasible=all(x['status']==2 for x in records),seconds=time.time()-start,results=records),indent=2))
   if out['status']!=2:raise RuntimeError(out)
 print('VERIFIED',len(records),'independent MILP exclusions',time.time()-start,flush=True)
if __name__=='__main__':main()
