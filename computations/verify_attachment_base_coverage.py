"""Independent generation of all ten attachment bases from the four
canonical complement cycle types. Also verifies the four bases' exact
chromatic number and criticality using matching, without a coloring solver.
"""

if not __debug__:
    raise RuntimeError("Run without -O: verification assertions must remain enabled")

import itertools as it,json,pathlib,time,networkx as nx
R=pathlib.Path(__file__).resolve().parent

def quotient(G):
 d={}
 for v in G:d.setdefault(tuple(sorted(set(G[v])|{v})),[]).append(v)
 pp=list(d.values());Q=nx.Graph();Q.add_nodes_from((i,dict(size=len(P))) for i,P in enumerate(pp));Q.add_edges_from((i,j) for i,j in it.combinations(range(len(pp)),2) if G.has_edge(pp[i][0],pp[j][0]));return Q

def run():
 start=time.time();types=[(1,1,1,5,5),(1,1,2,5,4),(1,1,3,5,3),(1,2,4,4,2)];records=[];bases=json.loads((R/'attachment_bases.json').read_text());targets=[];hits={r['id']:0 for r in bases}
 for r in bases:
  H=nx.empty_graph(13);H.add_edges_from(r['edges']);targets.append((r['id'],quotient(H)))
 for typ in types:
  parts=[i for i,w in enumerate(typ) for _ in range(w)];F=nx.empty_graph(13);F.add_edges_from((u,v) for u,v in it.combinations(range(13),2) if (parts[u]-parts[v])%5 in (1,4));H=nx.complement(F);assert H.number_of_edges() in [41,42]
  assert sum(nx.triangles(F).values())==0
  assert all(len(nx.max_weight_matching(F.subgraph([u for u in F if u!=v]),maxcardinality=True))==6 for v in F)
  edge_witnesses=[]
  for u,v in H.edges():
   good=[]
   for w in set(F[u])&set(F[v]):
    rest=[x for x in F if x not in [u,v,w]];M=nx.max_weight_matching(F.subgraph(rest),maxcardinality=True)
    if len(M)==5:good.append(dict(triple=[u,v,w],pairs=sorted(map(sorted,M))));break
   assert good;edge_witnesses.append(dict(deleted_edge=[u,v],color_classes=[good[0]['triple']]+good[0]['pairs']))
  for add in [None]+(list(nx.non_edges(H)) if H.number_of_edges()==41 else []):
   Q=H.copy()
   if add:Q.add_edge(*add)
   if any(all(Q.has_edge(u,v) for u,v in it.combinations(C,2)) for C in it.combinations(range(13),7)):continue
   S=quotient(Q);matches=[i for i,T in targets if nx.is_isomorphic(S,T,node_match=lambda a,b:a['size']==b['size'])];assert len(matches)==1;hits[matches[0]]+=1
  records.append(dict(complement_cycle_type=typ,num_edges=H.number_of_edges(),edge_deletion_colorings=edge_witnesses))
 assert len(hits)==10 and min(hits.values())>0
 out=dict(status='complete',all_four_bases_7_critical=True,all_allowed_zero_or_one_edge_augmentations_covered=True,base_multiplicities=hits,seconds=time.time()-start,criticality_certificates=records)
 (R/'attachment_base_independent_verification.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='criticality_certificates'})
if __name__=='__main__':run()
