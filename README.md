# Plantholt–Shan: the overfull conjecture for minimum degree (1 + ε) n (Lean 4)

M. J. Plantholt and S. Shan, *Edge coloring graphs with large minimum degree* (arXiv:2105.05286):
for every `ε > 0` and `n` large, a graph on `2n` vertices with minimum degree at least `(1 + ε) n`
has chromatic index `Δ` if and only if it has no `Δ`-overfull subgraph.

## Statements (`PlantholtShanChallenge.lean`)

* `PlantholtShan.theorem_1_2`: Theorem 1.2, with `PlantholtShan.HasOverfullSubgraph`, the definition of
  [plantholt-overfull-criterion](https://github.com/jtraverso/plantholt-overfull-criterion)
  restated so that the statements import only Mathlib (definitionally equal to
  `Plantholt.HasOverfullSubgraph`).
* `PlantholtShan.theorem_1_3b`, `PlantholtShan.theorem_1_3c`: Theorem 1.3, Conditions (b) and (c).
  Condition (a) (regular graphs) is
  [asymptotic-one-factorization](https://github.com/jtraverso/asymptotic-one-factorization).
* `PlantholtShan.lemma_2_11`: perfect matchings in bipartite graphs with few low-degree vertices.
* `PlantholtShan.hakimi` (Theorem 2.5), `PlantholtShan.hamiltonConnected_of_minDegree`
  (Theorem 2.6, `δ ≥ n/2 + 1`), `PlantholtShan.exists_spanning_paths` (Lemma 2.12).

## Proofs (`PSLib/`)

* `Engine/`: the scheme of Section 4 for a multigraph split into two halves (Vaughan's method):
  transfers and alternating paths making the old colour classes perfect matchings (`Step2`),
  Shannon colouring and McDiarmid equalization (`Equalize.lean`) of the uncoloured inner edges,
  completion of the new classes by Lemma 2.11 (`Step3*`), Kőnig's theorem on the rest (`Main`).
* `Engine/Split.lean`: balanced splits with prescribed pairs (Lemma 4.1);
  `Engine/Dummy.lean`: the dummy edges of Step 1.
* `Thm13b*.lean`, `Thm13c.lean`: Conditions (b), (c), with explicit (huge) thresholds.
* `Thm12*.lean`: Theorem 1.2 by induction on `Δ`; Case 2 removes pairs of perfect matchings along a
  Shannon colouring of the Hakimi multigraph of deficiencies (instead of linear forests); the
  edge additions and Lemmas 2.7, 2.10 are not needed.

Dependencies (lake, pinned; no code copied): asymptotic-one-factorization (PALOMAR-2026-11-12-000014),
shannon-edge-colouring (PALOMAR-2026-10-29-000023), vizing (PALOMAR-2026-10-15-000004),
plantholt-overfull-criterion (PALOMAR-2026-11-04-000016), menger-hamiltonian
(PALOMAR-2026-10-15-000020).

Build: Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3`, `lake build`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.

Apache 2.0. Author: Juan Pablo Traverso Gianini.
