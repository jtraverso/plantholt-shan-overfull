/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Group.Nat.Even

/-!
# Plantholt–Shan: tools for the asymptotic overfull conjecture

The auxiliary results of M. J. Plantholt and S. Shan, *Edge coloring graphs with large minimum
degree* (arXiv:2105.05286), Section 2:

* `hakimi` (Theorem 2.5, Hakimi 1962): degree functions of loopless multigraphs.
* `hamiltonConnected_of_minDegree` (Theorem 2.6, Hamilton-connected part, in the form
  `δ ≥ n/2 + 1`).
* `exists_spanning_paths` (Lemma 2.12): spanning linear forests with prescribed pairs of ends.
-/

@[expose] public section

namespace PlantholtShan

universe u

/-- A loopless multigraph on `V`: symmetric edge multiplicities with zero diagonal. -/
structure IsMultigraph {V : Type*} (m : V → V → ℕ) : Prop where
  symm : ∀ u v, m u v = m v u
  loopless : ∀ v, m v v = 0

/-- **Hakimi's theorem** (1962; Plantholt–Shan, Theorem 2.5). A function `d : V → ℕ` is the degree
function of a loopless multigraph iff its sum is even and no value exceeds the sum of the others. -/
theorem hakimi {V : Type*} [Fintype V] [DecidableEq V] (d : V → ℕ) :
    (∃ m : V → V → ℕ, IsMultigraph m ∧ ∀ v, ∑ u, m v u = d v) ↔
      Even (∑ v, d v) ∧ ∀ v, 2 * d v ≤ ∑ u, d u := by
  sorry

/-- **Hamilton-connectedness** (Plantholt–Shan, Theorem 2.6, for `δ ≥ n/2 + 1`): a graph on `n ≥ 5`
vertices with `n + 2 ≤ 2δ` has a Hamiltonian path between any two distinct vertices. -/
theorem hamiltonConnected_of_minDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 5 ≤ Fintype.card V)
    (hdeg : Fintype.card V + 2 ≤ 2 * G.minDegree) (u v : V) (huv : u ≠ v) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  sorry

/-- **Spanning linear forests with prescribed ends** (Plantholt–Shan, Lemma 2.12). For pairs
`(aᵢ, bᵢ)`, `i ≤ t`, of distinct vertices (all `2(t + 1)` of them distinct) in a graph with
`n + 6(t + 1) + 2 ≤ 2δ` and `3(t + 1) + 5 ≤ n`, there are paths `Pᵢ` from `aᵢ` to `bᵢ`, pairwise
vertex-disjoint and together covering all vertices. -/
theorem exists_spanning_paths {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : ℕ} (a b : Fin (t + 1) → V) (hab : ∀ i j, a i ≠ b j)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hdeg : Fintype.card V + 6 * (t + 1) + 2 ≤ 2 * G.minDegree)
    (hn : 3 * (t + 1) + 5 ≤ Fintype.card V) :
    ∃ P : ∀ i, G.Walk (a i) (b i), (∀ i, (P i).IsPath) ∧
      (∀ i j, i ≠ j → ∀ v, v ∈ (P i).support → v ∉ (P j).support) ∧
      ∀ v, ∃ i, v ∈ (P i).support := by
  sorry

end PlantholtShan
