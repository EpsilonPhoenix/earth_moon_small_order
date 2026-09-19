"""Independently generate all 7-vertex graphs with 1..6 edges from the
empty graph by edge augmentation; compare complements with the 80 bases
used in the SAT exclusions. This does not consult the graph atlas.
"""

if not __debug__:
    raise RuntimeError("Run without -O: verification assertions must remain enabled")

import networkx as nx,itertools as it,json,pathlib,collections,time
R=pathlib.Path(__file__).resolve().parent
def ky(G):return tuple(sorted(dict(G.degree()).values())),tuple(sorted(nx.triangles(G).values()))
def run():
 start=time.time();gs=[nx.empty_graph(7)];allgs=[];counts=[]
 for m in range(1,7):
  out=[];b=collections.defaultdict(list)
  for G in gs:
   for u,v in nx.non_edges(G):
    H=G.copy();H.add_edge(u,v);key=ky(H)
    if any(nx.is_isomorphic(H,J) for J in b[key]):continue
    b[key].append(H);out.append(H)
  gs=out;allgs+=out;counts.append(len(out))
 data=json.loads((R/'critical13_K6_results.json').read_text())['results'];assert len(allgs)==len(data)==80
 match=[]
 for g in allgs:
  H=nx.complement(g);found=[]
  for r in data:
   B=nx.empty_graph(7);B.add_edges_from(r['base_edges'])
   if nx.is_isomorphic(H,B):found.append(r['base_index'])
  assert len(found)==1;match.append(found[0])
 assert len(set(match))==80
 out=dict(status='complete',counts_by_complement_edges=counts,num_bases=80,all_SAT_bases_covered=True,seconds=time.time()-start)
 (R/'B7_independent_verification.json').write_text(json.dumps(out,indent=2));print(out)
if __name__=='__main__':run()
