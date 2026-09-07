# The Bollobás–Nikiforov Inequality in Lean

**Authors:** Gabriel Coutinho, Yinchen Liu, Thomás Jung Spier, Quanyu Tang, Shengtong Zhang

Ideation uses GPT 6 Astra, which also generated the manuscript [`docs/sol.tex`](docs/sol.tex).

Formalization completed by Grok 4.6 in the Cursor Editor, directed by
Shengtong Zhang (responsible maintainer); Palomar submission packaging by a
Claude Fable 5.1 agent. See `automation` in
[`formalization.yaml`](formalization.yaml) for the role breakdown.

This repository is a Lean 4 and Mathlib formalization of the Bollobás–Nikiforov
conjecture on the two largest adjacency eigenvalues of a graph, together with
the weighted spectral inequality and the completely-positive matrix theorem
that prove it, following the note [`docs/sol.tex`](docs/sol.tex).

## The theorems

Let $G$ be a finite simple graph on $n$ vertices with adjacency matrix $A_G$,
$m = |E(G)|$ edges and clique number $\omega(G)$, and write
$\lambda_1(G) \ge \cdots \ge \lambda_n(G)$ for the adjacency eigenvalues.

**The Bollobás–Nikiforov inequality.** Every noncomplete graph on at least two
vertices satisfies

$$
\lambda_1(G)^2 + \lambda_2(G)^2 \le 2\Bigl(1 - \frac{1}{\omega(G)}\Bigr) m .
$$

This was conjectured by Bollobás and Nikiforov in 2007. It follows from the
following weighted form. For a real symmetric matrix $B$ let $F(B)$ be the sum
of the squares of its two largest positive eigenvalues (missing terms replaced
by zero).

**Weighted spectral inequality.** If $B$ is symmetric, entrywise nonnegative,
has zero diagonal and $B_{ij} = 0$ whenever $\{i,j\} \notin E(G)$, then

$$
F(B) \le \Bigl(1 - \frac{1}{\omega(G)}\Bigr) \lVert B \rVert_F^2 .
$$

The coefficient is best possible for every graph with an edge. The proof rests
on a matrix theorem. For a positive semidefinite $X$ put

$$
\mathcal{M}(X) =  X \circ X + \sum_{i < j: X_{ij} < 0} X_{ij}^2 (e_i - e_j)(e_i - e_j)^T.
$$

**Planar Gram matrices.** If $X_{ij} = z_i^{\top} z_j$ with
$z_1, \dots, z_n \in \mathbb R^2$ lying in a closed half-plane through the
origin, then $\mathcal M(X)$ is completely positive.

A variational argument then removes the half-plane hypothesis from the scalar
inequality.

**Rank-two Gram inequality.** For every real positive semidefinite $X$ of rank
at most two,

$$
\sum_{i,j} (A_G)_{ij}\,(X_{ij})_+^2 \le \Bigl(1 - \frac{1}{\omega(G)}\Bigr) \lVert X \rVert_F^2 .
$$

**The rank-two conic parameter.** Consequently the parameter
$\chi''_{\mathrm{vec},3}(G)$ of Coutinho, Spier and Zhang equals $\omega(G)$
for every graph, which settles their Conjectures 2 and 3 without any lower
bound on the clique number.

## Comparison with prior work

Nikiforov [[Nik02]](https://doi.org/10.1017/S0963548301004928) proved
$\lambda_1(G)^2 \le 2(1 - 1/\omega(G))m$, and Bollobás and Nikiforov
[[BN07]](https://doi.org/10.1016/j.jctb.2006.12.002) conjectured that the same
right-hand side bounds $\lambda_1^2 + \lambda_2^2$ for noncomplete graphs. The
conjecture was known for graphs $G$ with $\chi(G) = \omega(G)$ by the
theorem of Ando and Lin [[AL15]](https://doi.org/10.1016/j.laa.2015.08.007), for
triangle-free graphs by Lin, Ning and Wu
[[LNW21]](https://doi.org/10.1017/S0963548320000462), for regular graphs
[[Zha24]](https://doi.org/10.1016/j.laa.2024.01.002), for graphs with $m$
edges and $O(m^{3/2-\varepsilon})$ triangles
[[KP25]](https://arxiv.org/abs/2407.19341) and for related classes
[[ZZ25]](https://doi.org/10.1016/j.laa.2025.01.037), and asymptotically almost surely for random graphs
[[LB25]](https://arxiv.org/abs/2501.07137). Complete multipartite graphs are
weakly perfect and hence covered by [AL15]; Giacomelli
[[Gia26]](https://arxiv.org/abs/2603.26379) gives a self-contained treatment of
that class, and the dense $K_4$-free result announced in its abstract is not
proven in its body. Coutinho, Spier and Zhang
[[CSZ24]](https://arxiv.org/abs/2411.08184) proved a version with weaker
constants for all graphs via conic programming and introduced the rank-two
program $\chi''_{\mathrm{vec},3}$, conjecturing that it equals $\omega(G)$ for
large clique number.

The results formalized here prove the conjecture for all graphs, in the
stronger weighted form, and prove $\chi''_{\mathrm{vec},3}(G) = \omega(G)$ for every graph.
The bound with up to $\omega(G)$ positive eigenvalues proposed by Elphick, Linz and Wocjan [[ELW24]](https://doi.org/10.1016/j.laa.2023.12.010) is not addressed.

### References

- [AL15] T. Ando, M. Lin, *Proof of a conjectured lower bound on the chromatic number of a graph*, Linear Algebra Appl. 485 (2015), 480–484. [doi:10.1016/j.laa.2015.08.007](https://doi.org/10.1016/j.laa.2015.08.007)
- [BN07] B. Bollobás, V. Nikiforov, *Cliques and the spectral radius*, J. Combin. Theory Ser. B 97 (2007), 859–865. [doi:10.1016/j.jctb.2006.12.002](https://doi.org/10.1016/j.jctb.2006.12.002)
- [CSZ24] G. Coutinho, T. J. Spier, S. Zhang, *Conic programming to understand sums of squares of eigenvalues of graphs*, arXiv:2411.08184 (2024). [arXiv](https://arxiv.org/abs/2411.08184)
- [Gia26] P. Giacomelli, *The Bollobás–Nikiforov conjecture for complete multipartite graphs and dense K₄-free graphs*, arXiv:2603.26379 (2026). [arXiv](https://arxiv.org/abs/2603.26379)
- [ELW24] C. Elphick, W. Linz, P. Wocjan, *Two conjectured strengthenings of Turán's theorem*, Linear Algebra Appl. 684 (2024), 23–36. [doi:10.1016/j.laa.2023.12.010](https://doi.org/10.1016/j.laa.2023.12.010)
- [KP25] H. Kumar, S. Pragada, *Bollobás–Nikiforov conjecture for graphs with not so many triangles*, Linear Algebra Appl. 727 (2025), 1–9. [arXiv](https://arxiv.org/abs/2407.19341)
- [LB25] C. Liu, C. Bu, *Bollobás–Nikiforov conjecture holds asymptotically almost surely*, arXiv:2501.07137 (2025). [arXiv](https://arxiv.org/abs/2501.07137)
- [LNW21] H. Lin, B. Ning, B. Wu, *Eigenvalues and triangles in graphs*, Combin. Probab. Comput. 30 (2021), 258–270. [doi:10.1017/S0963548320000462](https://doi.org/10.1017/S0963548320000462)
- [MS65] T. S. Motzkin, E. G. Straus, *Maxima for graphs and a new proof of a theorem of Turán*, Canad. J. Math. 17 (1965), 533–540. [doi:10.4153/CJM-1965-053-6](https://doi.org/10.4153/CJM-1965-053-6)
- [Nik02] V. Nikiforov, *Some inequalities for the largest eigenvalue of a graph*, Combin. Probab. Comput. 11 (2002), 179–189. [doi:10.1017/S0963548301004928](https://doi.org/10.1017/S0963548301004928)
- [Zha24] S. Zhang, *On the first two eigenvalues of regular graphs*, Linear Algebra Appl. 686 (2024), 102–110. [doi:10.1016/j.laa.2024.01.002](https://doi.org/10.1016/j.laa.2024.01.002)
- [ZZ25] J. Zeng, X.-D. Zhang, *A note on the Bollobás–Nikiforov conjecture*, Linear Algebra Appl. 710 (2025), 230–242. [doi:10.1016/j.laa.2025.01.037](https://doi.org/10.1016/j.laa.2025.01.037)

## Writeup

The note [`docs/sol.tex`](docs/sol.tex) is the source being formalized. It is
a preliminary research note; the manuscript was generated by GPT 6 Astra, with
the mathematics developed in collaboration with it by the authors.

## Lean

For a description of the Lean side of the project, including the Palomar
submission surface, see [`README_lean.md`](README_lean.md).
