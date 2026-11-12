# Plantholt–Shan: tools for the asymptotic overfull conjecture (Lean 4)

Auxiliary results of M. J. Plantholt and S. Shan, *Edge coloring graphs with large minimum degree*
(arXiv:2105.05286), Section 2. Later versions of this package will add their Theorems 1.2 and 1.3;
the regular case is [asymptotic-one-factorization](https://github.com/jtraverso/asymptotic-one-factorization).

## Statements (`PlantholtShanChallenge.lean`, Mathlib definitions only)

* `PlantholtShan.hakimi`: Hakimi's theorem on degree functions of loopless multigraphs (Thm 2.5).
* `PlantholtShan.hamiltonConnected_of_minDegree`: `n ≥ 5`, `n + 2 ≤ 2δ` ⇒ Hamilton-connected
  (Thm 2.6).
* `PlantholtShan.exists_spanning_paths`: spanning linear forests with prescribed pairs of ends
  (Lemma 2.12).

Proofs in `PSLib/`. Dirac's theorem comes from
[menger-hamiltonian](https://github.com/jtraverso/menger-hamiltonian) (PALOMAR-2026-10-15-000020,
pinned at `35c5f68`, required as a lake dependency; no code is copied).

Build: Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3`, `lake build`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.

Apache 2.0. Author: Juan Pablo Traverso Gianini.
