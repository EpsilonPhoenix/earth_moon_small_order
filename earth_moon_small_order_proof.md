# Nine-colorability of biplanar graphs of order at most eighteen

## Theorem

**Every finite simple biplanar graph on at most eighteen vertices admits a proper coloring with at most nine colors.**

Here a graph is **biplanar** if its edges can be partitioned into two planar graphs on the same vertex set. A graph is **\(k\)-critical** if its chromatic number is \(k\) and every proper subgraph has smaller chromatic number. Criticality throughout means subgraph-criticality, not merely vertex-criticality.

The argument through seventeen vertices uses critical-graph structure and edge counting. At eighteen vertices it additionally uses two finite graph classifications and finite independent-set attachment exclusions. Their reproducible checks are included in `computations/`. The arithmetic, computational checks, and Lean development have separate roles; `README.md` records the precise formalization status.

## 1. Preliminaries

Write \(n(G)=|V(G)|\), \(e(G)=|E(G)|\), \(\alpha(G)\) for the independence number, and \(\omega(G)\) for the clique number. The join \(A\vee B\) adds every edge between two disjoint graphs \(A\) and \(B\).

We use the following classical results.

**Gallai's critical-edge bound.** If \(k+2\le n\le2k-1\), every \(k\)-critical graph on \(n\) vertices has at least
\[
f_k(n)=\binom n2-(n-k)^2-1
\tag{1}
\]
edges. Equality is attained. In the notation \(n=k+p\), the extremal graphs are exactly
\[
K_{k-p-1}\vee D,\qquad D\in\mathcal{DG}(p+1).
\tag{2}
\]

**Gallai's decomposition theorem.** A critical graph with connected complement and chromatic number \(q\) has at least \(2q-1\) vertices. The components of the complement therefore give a decomposition into critical join factors, whose chromatic numbers add.

**Brooks's theorem.** A connected graph of maximum degree \(d\) is \(d\)-colorable unless it is a complete graph or an odd cycle.

These statements, including the extremal characterization and the ordinary-coloring version of Brooks's theorem, are recorded in [1, Theorems 1.1, 1.2, 3.7, 4.1, 5.1, and 7.2].

We also use the non-biplanarity of \(K_9\), recorded in [2, p. 14:13]. Consequently every biplanar graph is \(K_9\)-free. For \(n\ge3\), the planar edge bounds give
\[
e(G)\le6n-12
\tag{3}
\]
for every biplanar graph, and
\[
e(G)\le4n-8
\tag{4}
\]
when the graph is also triangle-free. Equation (4) applies in particular to every bipartite subgraph of a biplanar graph.

A \(k\)-critical graph has minimum degree at least \(k-1\): a coloring of the graph with a low-degree vertex deleted would otherwise extend. There is no \(k\)-critical graph on \(k+1\) vertices. Indeed, the degree bound makes its complement a matching. Zero missing edges give chromatic number \(k+1\); two or more missing edges allow a \((k-1)\)-coloring; and exactly one missing edge leaves a proper \(K_k\) subgraph.

Finally, a graph that is not nine-colorable has a subgraph minimal with that property. Deleting a vertex from this subgraph gives a nine-coloring, so adding the vertex back with a tenth color proves that the subgraph is 10-critical. Biplanarity is inherited by subgraphs. It therefore suffices to exclude \(K_9\)-free, 10-critical biplanar graphs of the stated orders.

## 2. Orders at most fifteen

Let \(G\) be a putative critical counterexample of order \(n\). Orders below ten cannot have chromatic number ten. At order ten the graph would be \(K_{10}\), which contains \(K_9\). Order eleven is excluded by the preceding critical-graph observation. Equation (1) handles the remaining orders through fifteen:

| \(n\) | \(f_{10}(n)\) | Biplanar upper bound \(6n-12\) |
|---:|---:|---:|
| 12 | 61 | 60 |
| 13 | 68 | 66 |
| 14 | 74 | 72 |
| 15 | 79 | 78 |

Every row contradicts (3).

## 3. The independent-triple counting lemma

Suppose that a \(K_9\)-free, 10-critical graph \(G\) has an independent set \(I\) of size three. The graph \(G-I\) is 9-chromatic: criticality gives an upper bound of nine, while an eight-coloring could be extended by assigning one new color to all of \(I\). Its minimum degree is at least six.

Choose a 9-critical subgraph \(Q\subseteq G-I\), and put
\[
t=|V(Q)|,\qquad W=V(G-I)\setminus V(Q),\qquad s=|W|=n-3-t.
\]
The clique restriction and the absence of a 9-critical graph on ten vertices give \(11\le t\le n-3\). The subgraph \(Q\) need not be induced; the edges of the induced graph on \(V(Q)\) are at least those of \(Q\).

At least \(6s-\binom s2\) edges of \(G-I\) have an endpoint in \(W\). To see this, sum the degrees of the vertices of \(W\) inside \(G-I\) and subtract the internal edges of \(W\), whose number is at most \(\binom s2\). Meanwhile the vertices of \(I\) have total degree at least 27, with no double counting because \(I\) is independent. Thus
\[
e(G)\ge L(n,t):=27+f_9(t)+6(n-3-t)-\binom{n-3-t}{2}.
\tag{5}
\]
All uses below lie in Gallai's range.

| \(n\) | Possible \(t\) | Values of \(L(n,t)\), in order | Minimum |
|---:|:---|:---|---:|
| 16 | 11, 12, 13 | 88, 89, 88 | 88 |
| 17 | 11, 12, 13, 14 | 92, 94, 94, 92 | 92 |
| 18 | 11, 12, 13, 14, 15 | 95, 98, 99, 98, 95 | 95 |

The first two rows exclude an independent triple at orders sixteen and seventeen: their minima exceed 84 and 90, respectively. At order eighteen, where the edge budget is 96, only \(t=11\) and \(t=15\) remain.

## 4. Independence number at most two: orders sixteen and seventeen

Assume \(\alpha(G)\le2\), and write
\[
G=H_1\vee\cdots\vee H_r
\]
using the connected components \(F_i=\overline{H_i}\) of \(F=\overline G\). Write \(q_i=\chi(H_i)\), \(n_i=|V(H_i)|\), and \(w_i=\omega(H_i)\).

Gallai gives \(n_i\ge2q_i-1\). Conversely, deleting a vertex from the critical factor \(H_i\) leaves a \((q_i-1)\)-colorable graph, and every color class has at most two vertices. Hence \(n_i-1\le2(q_i-1)\), and therefore
\[
n_i=2q_i-1,\qquad r=20-n.
\tag{6}
\]
A factor with \(q_i=1\) is a singleton. A factor with \(q_i=2\) would be \(K_2\), whose complement is disconnected, contrary to the choice of factors. Thus each \(n_i\) is either one or an odd integer at least five.

Clique numbers add under joins, so \(\sum_iw_i\le8\). A singleton consumes one of these clique vertices and contributes no complement edges. For a non-singleton factor,
\[
w_i\le q_i-1=\frac{n_i-1}{2};
\]
otherwise it would contain a proper clique with its full chromatic number, contrary to criticality. Each \(F_i\) is triangle-free. A neighborhood in \(F_i\) is therefore an independent set in \(F_i\), equivalently a clique in \(H_i\). Consequently
\[
\Delta(F_i)\le w_i,\qquad e(F_i)\le\left\lfloor\frac{n_iw_i}{2}\right\rfloor.
\tag{7}
\]

Equations (6)–(7) leave the following complete table. The bounds maximize over all permitted clique allocations, not just a selected allocation.

| \(n\) | Component orders in \(\overline G\) | Upper bound on \(e(\overline G)\) |
|---:|:---|---:|
| 16 | 1, 1, 1, 13 | 32 |
| 16 | 1, 1, 5, 9 | 23 |
| 16 | 1, 1, 7, 7 | 20 |
| 16 | 1, 5, 5, 5 | 15 |
| 17 | 1, 1, 15 | 45 |
| 17 | 1, 5, 11 | 32 |
| 17 | 1, 7, 9 | 28 |
| 17 | 5, 5, 7 | 20 |

For example, three singleton factors at order sixteen leave at most five clique vertices for the thirteen-vertex factor, giving \(\lfloor13\cdot5/2\rfloor=32\). It follows that
\[
\begin{aligned}
n=16&:\quad e(G)\ge\binom{16}{2}-32=88>84,\\
n=17&:\quad e(G)\ge\binom{17}{2}-45=91>90.
\end{aligned}
\]
Together with Sections 2–3, this proves the theorem through seventeen vertices.

## 5. Order eighteen with independence number at most two

A minimal counterexample of order at most eighteen must now use all eighteen vertices. It is 10-critical, has minimum degree at least nine, is \(K_9\)-free, and has at most 96 edges.

Under \(\alpha(G)\le2\), equation (6) gives two complement components, of orders
\[
(1,17),\quad(5,13),\quad(7,11),\quad(9,9).
\]
A join between factors of orders \(a,b\) contains \(K_{a,b}\). The last three pairs have \(ab=65,77,81\), respectively, exceeding the triangle-free biplanar budget \(4\cdot18-8=64\). Thus
\[
G=K_1\vee H,
\tag{8}
\]
where \(H\) is 9-critical on seventeen vertices, \(\alpha(H)\le2\), and \(\omega(H)\le7\).

Set \(F=\overline H\). Then \(F\) is triangle-free, \(\alpha(F)\le7\), and \(\Delta(F)\le7\). Also
\[
e(H)\le96-17=79,\qquad
57\le e(F)=136-e(H)\le\left\lfloor\frac{17\cdot7}{2}\right\rfloor=59.
\tag{9}
\]

The graph \(F\) is maximal triangle-free. If \(uv\) is a nonedge of \(F\), then \(uv\in E(H)\), and \(H-uv\) has an eight-coloring. Seventeen vertices in eight color classes require an independent triple in \(H-uv\). Since \(H\) has no independent triple, that triple must be \(\{u,v,w\}\), where \(uw,vw\in E(F)\). Thus adding \(uv\) to \(F\) creates a triangle. Also \(F-v\) has a perfect matching for each \(v\), since an eight-coloring of \(H-v\) consists of eight pairs; this latter property is not needed for the enumeration.

### 5.1 Finite classification A

**Lemma A.** Up to isomorphism, there is exactly one maximal triangle-free graph \(F\) satisfying
\[
|V(F)|=17,\quad57\le e(F)\le59,\quad\Delta(F)\le7,\quad\alpha(F)\le7.
\]
It is the independent-set blow-up of a five-cycle with cyclic part sizes \((4,4,3,3,3)\), and it has 58 edges.

Here is the complete enumeration reduction. There is a degree-seven vertex \(v\). Let \(A=N(v)\), an independent set of size seven, and let \(B\) be the remaining nine vertices. An \(A\)-vertex's neighborhood in \(B\) is a maximal independent set of \(F[B]\): a missing \(A\)–\(B\) edge requires a common neighbor, necessarily in \(B\).

Every such row has size at most six. If their total size is \(w\), then
\[
w+e(F[B])\ge50,\qquad w+2e(F[B])\le63.
\]
Therefore \(w\ge37\), \(8\le e(F[B])\le13\), and \(\alpha(F[B])=6\). The last assertion follows because \(v\) excludes an independent seven-set in \(B\), while some row must have size six.

An independent six-set in \(B\) leaves a three-vertex cover. Its induced graph is empty, an edge, or a three-vertex path. Enumerate these three cover types, all multisets of neighborhoods of the six independent vertices in the cover, and then all multisets of seven maximal-independent rows from \(A\) to \(B\). This covers every eligible graph, allowing duplicates.

The remaining tests are exact. For every independent \(S\subseteq B\), require
\[
|S|+|\{a\in A:N(a)\cap S=\varnothing\}|\le7.
\]
For every nonedge in \(B\) without a common \(B\)-neighbor, require an \(A\)-row containing both endpoints. The row maximality tests handle missing \(A\)–\(B\) edges. All other nonedges already have a common neighbor.

`verify_dense17_independent.py` exhausts 2,388 residual encodings, finds three feasible complete encodings, and checks directly that each has precisely the stated five false-twin classes. It uses only the Python standard library.

### 5.2 A literal density obstruction

In \(H=\overline F\), retain only edges between distinct blow-up parts. They form a triangle-free graph with 57 edges: the quotient is the complement of a five-cycle, again a five-cycle. The two size-four parts are adjacent in \(F\)'s quotient, so their union is independent in this retained subgraph.

Add the eight edges from the cone vertex in (8) to those two parts. The resulting subgraph of \(G\) is triangle-free and has 65 edges on eighteen vertices, contradicting (4). This excludes the entire independence-number-two branch. Both the enumeration verifier and `arithmetic_check.py` construct and directly check the obstruction.

## 6. A degree-list lemma

**Lemma.** A \(k\)-critical graph cannot contain an induced diamond \(K_4-e\) whose four vertices all have degree \(k-1\) in the whole graph.

Delete the diamond and \((k-1)\)-color the rest. Each diamond vertex has at least its internal degree available in its color list. The adjacent centers therefore have lists of size at least three, and the nonadjacent tips have lists of size at least two. Truncate to these sizes.

If the tip lists intersect, give both tips a common color. Each center then has at least two remaining colors, so their edge can be colored. If the tip lists are disjoint, their union has four colors. One of those colors lies outside the first center's three-element list. Use it on the corresponding tip, and use any available color on the other tip. The first center retains at least two colors; the second retains at least one. Color the second center first, then the first.

Either way the coloring extends, contradicting criticality. Only vertex-criticality is needed for this lemma.

## 7. Order eighteen with an independent triple

Let \(I,Q,W,t\) be as in Section 3. Only \(t=11\) and \(t=15\) remain.

### 7.1 The case \(t=11\)

Now \(|W|=4\). Introduce nonnegative integers
\[
\begin{aligned}
a&=\sum_{i\in I}(d_G(i)-9),&
b&=\sum_{w\in W}(d_{G-I}(w)-6),\\
c&=e(G[V(Q)])-50,&
d&=6-e(G[W]).
\end{aligned}
\]
The exact edge count is
\[
e(G)=95+a+b+c+d.
\tag{10}
\]
Indeed, the edges incident with \(I\) contribute \(27+a\), the induced graph on \(V(Q)\) contributes \(50+c\), and the remaining edges of \(G-I\) contribute \((24+b)-(6-d)\).

Since \(e(G)\le96\), at most one unit of slack is available. At least two vertices of \(I\) have degree nine. At least three vertices of \(W\) have degree six in \(G-I\); each must be adjacent to all three vertices of \(I\), and hence has degree nine in \(G\). Also \(G[W]\) is \(K_4\) or \(K_4\) minus one edge, so two of those three vertices are adjacent.

Together with two degree-nine vertices of \(I\), that adjacent pair induces a diamond whose four vertices have degree nine. The preceding lemma excludes it. No classification of the eleven-vertex graph \(Q\) is needed.

### 7.2 The case \(t=15\)

Now \(Q\) spans \(G-I\), and \(e(Q)\) is 68 or 69. The graph \(G-I\) can contain at most one extra edge beyond \(Q\).

Decompose the 9-critical graph \(Q\) into critical join factors. Gallai's factor-size condition, the fact that nontrivial 3-critical factors are odd cycles, and the minimum-degree or Gallai edge bounds give the complete table below.

| Complement-component orders | Edge lower bound |
|:---|---:|
| 1, 1, 1, 1, 1, 1, 9 | 78 |
| 1, 1, 1, 1, 1, 10 | 75 |
| 1, 1, 1, 1, 11 | 72 |
| 1, 1, 1, 5, 7 | 86 |
| 1, 1, 1, 12 | 69 |
| 1, 1, 5, 8 | 84 |
| 1, 1, 13 | 68 |
| 1, 5, 9 | 83 |
| 1, 7, 7 | 85 |
| 5, 5, 5 | 90 |

The row \((1,1,1,12)\) could attain 69 only if its twelve-vertex, 6-critical factor had 30 edges. It would then be 5-regular, contrary to Brooks's theorem. Thus its actual bound is at least 70. Only
\[
Q=K_2\vee R
\tag{11}
\]
remains, where \(R\) is 7-critical on thirteen vertices with 41 or 42 edges. The table is generated independently by `arithmetic_check.py`.

Both vertices of the \(K_2\) must be adjacent to all three vertices of \(I\). Otherwise delete a vertex \(i\in I\) missing one of them, say \(z\), and nine-color the remainder. The color of \(z\) occurs nowhere else in \(G-I\), because \(z\) is universal there. It can therefore be assigned to \(i\): any other vertices carrying it lie in the independent set \(I\). This contradicts criticality.

Consequently
\[
G=K_2\vee J,
\tag{12}
\]
where \(J\) is 8-critical on sixteen vertices, is \(K_7\)-free, has minimum degree at least seven, and has at most 63 edges. The last bound subtracts the 33 edges incident with the two universal vertices from 96.

The graph \(J\) is obtained by attaching an independent triple to a thirteen-vertex graph \(H\). Either \(H=R\), or \(e(R)=41\) and \(H\) is obtained from \(R\) by adding one edge. It remains to exclude precisely these attachments.

## 8. The thirteen-vertex bases

**Lemma B.** Every \(K_7\)-free, 7-critical graph on thirteen vertices with at most 42 edges is the complement of an independent-set five-cycle blow-up with one of the cyclic part-size sequences
\[
(1,1,1,5,5),\quad(1,1,2,5,4),\quad(1,1,3,5,3),\quad(1,2,4,4,2).
\tag{13}
\]
The first three have 41 edges; the fourth has 42.

### 8.1 The 41-edge case

Gallai's extremal characterization (2) gives \(\mathcal{DG}(7)\). Explicitly, take a clique \(X\) of size five and a clique \(Y\) of size six, with no edges between them. Split \(Y=Y_1\cup Y_2\) into nonempty parts. Add nonadjacent vertices \(a,b\), with neighborhoods \(X\cup Y_1\) and \(X\cup Y_2\), respectively.

Up to swapping the split parts, the split sizes are \((1,5),(2,4),(3,3)\). These are the first three graphs in (13). Each has independence number two.

### 8.2 The 42-edge case with an independent triple

Suppose \(R\) has an independent triple. Removing it leaves a 6-chromatic graph of minimum degree at least three. Take a 6-critical subgraph \(C\). If \(C\ne K_6\), its order \(t\) is 8, 9, or 10, and the analogue of (5) gives
\[
e(R)\ge18+f_6(t)+3(10-t)-\binom{10-t}{2}=46,47,46,
\]
respectively. Thus \(R\) contains \(K_6\).

Fix such a clique and let \(B\) be the induced graph on the other seven vertices. If \(b=e(B)\) and \(s\) counts cross edges, then \(b+s=27\) and \(2b+s\ge42\), so \(b\ge15\). Also \(b\le20\) by \(K_7\)-freeness.

There are 80 unlabeled seven-vertex graphs with 15–20 edges. Their complements have one through six edges, with counts \(1,2,5,10,21,41\). `verify_B7_catalogue.py` generates this catalogue by successive edge addition and exact isomorphism testing, without consulting a graph atlas.

For each \(B\), use 42 Boolean variables for possible \(K_6\)–\(B\) edges. Require exactly 42 total edges, minimum degree six, no \(K_7\), and an independent triple. Colorings and diamonds give necessary cuts:

* For each supplied proper six-coloring of the fixed edges, at least one variable cross edge must join equal-colored vertices.
* An induced diamond cannot have all four degrees equal to six.

The second cut applies to the intended critical graph. It is also valid for every non-six-colorable graph satisfying the other constraints. Any 7-critical subgraph on fewer than thirteen vertices would force at least \(49,50,49,46\) total edges at orders \(9,10,11,12\), respectively, by the minimum-degree counting argument. Orders seven and eight are excluded by clique-freeness and the no-\(k+1\) observation. A spanning critical subgraph with 41 edges would be \(\mathcal{DG}(7)\), whose independence number two contradicts an independent triple in its supergraph. Thus any relevant non-six-colorable graph is itself critical.

All 80 finite instances are infeasible. The included verifier checks the 285 supplied coloring cuts directly, reconstructs the diamond cuts, and rebuilds each instance as a binary MILP for HiGHS.

### 8.3 The independence-number-two case

Let \(F=\overline R\). Criticality makes \(F\) maximal triangle-free by the same argument as in Section 5. It has thirteen vertices, 36 or 37 edges, maximum degree at most six, and independence number at most six.

Anchor a degree-six vertex \(v\), with independent neighborhood \(A\) of size six and remaining set \(B\) of size six. The six \(A\)–\(B\) rows are maximal independent sets of size at most five. Their total size is at least 24, so \(e(F[B])\le6\).

`verify_mtf13_independent.py` enumerates every labeled six-vertex graph with at most six edges: 9,949 edge sets, of which 5,014 are triangle-free. It then enumerates every admissible multiset of six maximal-independent rows, checking maximality, degrees, edge count, and independence number. The search permits a harmless superset of the edge range; every surviving output still has 36 or 37 edges.

There are 291 feasible encodings, all of the four types in (13). Classification uses their five false-twin classes and the weighted five-cycle quotient, rather than a heuristic graph hash. This completes Lemma B.

## 9. Excluding the independent-triple attachments

From the four bases in (13), retain each base and add every possible single edge to each 41-edge base. Discard graphs containing \(K_7\) and identify isomorphic results. Exactly ten bases remain: three with 41 edges and seven with 42 edges. `verify_attachment_base_coverage.py` regenerates this list and checks that every permitted augmentation is represented.

Fix such a base \(H\), and use variables \(x_{iv}\) for the edges from each new vertex \(i\in\{0,1,2\}\) to \(v\in V(H)\). The new vertices form an independent set. Necessary conditions from Section 7.2 are
\[
\begin{aligned}
\sum_{i,v}x_{iv}&\le63-e(H),\\
\sum_vx_{iv}&\ge7 &&\text{for every }i,\\
\sum_ix_{iv}&\ge\max\{0,7-d_H(v)\} &&\text{for every }v.
\end{aligned}
\tag{14}
\]
A new vertex must not be adjacent to all vertices of any six-clique in \(H\), since that would create a \(K_7\).

Let \(c\) be any proper seven-coloring of \(H\), with color classes \(C_1,\ldots,C_7\). If each new vertex misses at least one color class, assign it a missing color; the three assignments do not conflict because the new vertices are independent. Hence non-seven-colorability requires
\[
\bigvee_{i=0}^2\;\bigwedge_{j=1}^7\;\bigvee_{v\in C_j}x_{iv}.
\tag{15}
\]

For the ten bases, 70 supplied base colorings, together with (14), the clique constraints, and valid symmetry constraints, make every instance infeasible. Every coloring is checked directly. The MILP encoding of (15) uses a blocking indicator for each new vertex, requires at least one indicator, and makes an active indicator imply an incident edge into every color class. This is equisatisfiable with (15).

Both finite families use row ordering and ordering of columns within twin classes. These symmetry constraints preserve a representative: a lexicographically minimal row-major matrix in each row-permutation/twin-column-permutation orbit satisfies both orderings. No assumption of a planar embedding enters these attachment exclusions.

The independent MILP verifier confirms infeasibility for all ten attachments and all 80 classification instances. A further verifier, `verify_exact_smt.py`, translates those reconstructed integral constraints into pseudo-Boolean inequalities and reproduces all 90 exclusions using Z3 with exact arithmetic. Thus (12) is impossible, excluding \(t=15\). Section 7.1 excludes \(t=11\), and Section 5 excludes \(\alpha(G)\le2\). This completes the proof through eighteen vertices.

## 10. Consequence and verification dependencies

Any biplanar graph with chromatic number at least ten has at least nineteen vertices. A nineteen-vertex biplanar graph that is not nine-colorable is necessarily vertex-critical and exactly 10-chromatic: deleting a vertex leaves a nine-colorable graph, and adding the vertex back uses at most one extra color.

The numerical calculations are checked by `arithmetic_check.py`. The finite mathematical dependencies are Lemma A, the two computational branches of Lemma B, complete generation of the ten attachment bases, and infeasibility of the ten attachment instances. Their verifiers and input data are included, rather than only recorded solver statuses. A successful external solver run is computational evidence; it is not automatically a proof term in Lean. The Lean source exposes the currently unformalized dependencies as explicit hypotheses.

The accompanying Lean 4.34.0 development has been compiled successfully. Its main declaration, `EarthMoon.nine_colorable_through18_of_inputs`, is a kernel-checked conditional theorem: `GraphReductionInputs`, `FiniteCaseInputs`, and a concrete instantiation of `PlanarPredicate` remain to be supplied. The dependency audit contains no `sorryAx`; that fact does not discharge the explicit hypotheses. The build record and reproduction commands are in `README.md`.

## References

[1] Justus von Postel, Thomas Schweser, and Michael Stiebitz. *Point partition numbers: decomposable and indecomposable critical graphs*. arXiv:1912.12654v2, 12 December 2021. In particular Theorems 1.1, 1.2, 3.7, 4.1, 5.1, and 7.2, specialized to ordinary graph coloring.

[2] Markus Kirchweger, Manfred Scheucher, and Stefan Szeider. *SAT-Based Generation of Planar Graphs*. SAT 2023, LIPIcs 271, Article 14. DOI: 10.4230/LIPIcs.SAT.2023.14. Page 14:13 records the non-biplanarity of \(K_n\) for \(n\ge9\). The proof above does not use the paper's computational exclusion through thirteen vertices.
