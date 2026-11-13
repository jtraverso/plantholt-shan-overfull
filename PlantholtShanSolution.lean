/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Plantholt.Main
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Data.Set.Card
public import PSLib.Thm12
public import PSLib.Thm13c
public import PSLib.Konig
public import PSLib.Hakimi
public import PSLib.LinForest

/-!
# Proofs of the statements in `PlantholtShanChallenge.lean` (library `PSLib/`)

The auxiliary results of M. J. Plantholt and S. Shan, *Edge coloring graphs with large minimum
degree* (arXiv:2105.05286), Section 2:

* `hakimi` (Theorem 2.5, Hakimi 1962): degree functions of loopless multigraphs.
* `hamiltonConnected_of_minDegree` (Theorem 2.6, Hamilton-connected part, in the form
  `δ ≥ n/2 + 1`).
* `exists_spanning_paths` (Lemma 2.12): spanning linear forests with prescribed pairs of ends.
* `lemma_2_11` (Lemma 2.11): perfect matchings in bipartite graphs with few low-degree vertices.

and the main results:

* `theorem_1_3b`, `theorem_1_3c` (Theorem 1.3, Conditions (b) and (c)).
* `theorem_1_2` (Theorem 1.2): for `δ(G) ≥ (1 + ε) n` and `n` large, `χ'(G) = Δ(G)` if and only if
  `G` has no `Δ(G)`-overfull subgraph.
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
      Even (∑ v, d v) ∧ ∀ v, 2 * d v ≤ ∑ u, d u :=
  ⟨fun ⟨m, hm, hd⟩ => by
    have hm' : PSLib.IsMultigraph m := ⟨hm.symm, hm.loopless⟩
    have hsum : ∑ v, d v = ∑ v, ∑ u, m v u := Finset.sum_congr rfl fun v _ => (hd v).symm
    refine ⟨hsum ▸ PSLib.even_sum_degrees hm', fun v => ?_⟩
    rw [hsum, ← hd v]
    exact PSLib.two_mul_degree_le hm' v,
  fun ⟨hev, hmax⟩ => by
    obtain ⟨m, hm, hd⟩ := PSLib.exists_multigraph _ d rfl hev hmax
    exact ⟨m, ⟨hm.symm, hm.loopless⟩, hd⟩⟩

/-- **Hamilton-connectedness** (Plantholt–Shan, Theorem 2.6, for `δ ≥ n/2 + 1`): a graph on `n ≥ 5`
vertices with `n + 2 ≤ 2δ` has a Hamiltonian path between any two distinct vertices. -/
theorem hamiltonConnected_of_minDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 5 ≤ Fintype.card V)
    (hdeg : Fintype.card V + 2 ≤ 2 * G.minDegree) (u v : V) (huv : u ≠ v) :
    ∃ p : G.Walk u v, p.IsHamiltonian :=
  PSLib.exists_hamiltonian_path G hn hdeg huv

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
      ∀ v, ∃ i, v ∈ (P i).support :=
  PSLib.exists_paths t G a b hab ha hb hdeg hn

open Finset

/-- **Plantholt–Shan, Lemma 2.11.** A bipartite graph with sides of size `n` in which every vertex
has degree at least `t` and at most `t` vertices have degree less than `n / 2` has a perfect
matching. -/
theorem lemma_2_11 {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (n t : ℕ) (hα : Fintype.card α = n)
    (hβ : Fintype.card β = n) (R : α → β → Prop) [∀ x y, Decidable (R x y)]
    (hdx : ∀ x, t ≤ #(univ.filter fun y => R x y)) (hdy : ∀ y, t ≤ #(univ.filter fun x => R x y))
    (hlow : #(univ.filter fun x => 2 * #(univ.filter fun y => R x y) < n) +
      #(univ.filter fun y => 2 * #(univ.filter fun x => R x y) < n) ≤ t) :
    ∃ σ : α → β, Function.Injective σ ∧ ∀ x, R x (σ x) := by
  exact PSLib.exists_perfect_matching_of_few_low n t hα hβ R hdx hdy hlow

/-- **Plantholt–Shan, Theorem 1.3 (b).** For `ε > 0` there is `N` such that a graph on `2n ≥ 2N`
vertices with two distinct vertices `x`, `y` with `d(x) = d(y) ≥ (1/2 + 3ε/2) n`, all other
vertices of degree `Δ(G) ≥ (1 + ε) n`, and `Δ(G) − δ(G) ≤ (1/2 − ε/2) n`, has chromatic index
`Δ(G)`. -/
theorem theorem_1_3b (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n : ℕ), N ≤ n → Fintype.card V = 2 * n →
      (∃ x y : V, x ≠ y ∧ G.degree x = G.degree y ∧ (1 / 2 + 3 * ε / 2) * n ≤ G.degree x ∧
        (∀ z, z ≠ x → z ≠ y → G.degree z = G.maxDegree) ∧ (1 + ε) * n ≤ G.maxDegree ∧
        (G.maxDegree : ℝ) - G.minDegree ≤ (1 / 2 - ε / 2) * n) →
      G.lineGraph.Colorable G.maxDegree := by
  exact PSLib.Eng.thm13b ε hε

/-- **Plantholt–Shan, Theorem 1.3 (c).** For `ε > 0` there is `N` such that a graph on `2n ≥ 2N`
vertices with `Δ(G) − δ(G) ≥ n^{6/7}`, at least `n^{6/7}` vertices of degree `δ(G)`, at least
`n + 1` vertices of degree `Δ(G)`, and `δ(G) ≥ (1 + ε) n`, has chromatic index `Δ(G)`. -/
theorem theorem_1_3c (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n : ℕ), N ≤ n → Fintype.card V = 2 * n →
      (n : ℝ) ^ ((6 : ℝ) / 7) ≤ (G.maxDegree : ℝ) - G.minDegree →
      (n : ℝ) ^ ((6 : ℝ) / 7) ≤ #(univ.filter fun v => G.degree v = G.minDegree) →
      n + 1 ≤ #(univ.filter fun v => G.degree v = G.maxDegree) →
      (1 + ε) * n ≤ G.minDegree →
      G.lineGraph.Colorable G.maxDegree := by
  exact PSLib.Eng.thm13c ε hε

/-- `G` has a `Δ(G)`-overfull subgraph: a subgraph on an odd number `≥ 3` of vertices with more
than `Δ(G) (|V(H)| - 1) / 2` edges (the definition `Plantholt.HasOverfullSubgraph` of the
registered entry `jtraverso/plantholt-overfull-criterion`, restated here so that the statements
only import Mathlib). -/
def HasOverfullSubgraph {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  ∃ H : G.Subgraph, Odd H.verts.ncard ∧ 3 ≤ H.verts.ncard ∧
    G.maxDegree * (H.verts.ncard - 1) < 2 * H.edgeSet.ncard

/-- **Plantholt–Shan, Theorem 1.2.** For `ε > 0` there is `N` such that a graph `G` on
`2n ≥ 2N` vertices with minimum degree at least `(1 + ε) n` has chromatic index `Δ(G)` if and only
if it contains no `Δ(G)`-overfull subgraph (`HasOverfullSubgraph`, as in the registered entry
`jtraverso/plantholt-overfull-criterion`). -/
theorem theorem_1_2 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n : ℕ), N ≤ n → Fintype.card V = 2 * n → (1 + ε) * n ≤ G.minDegree →
      (G.lineGraph.Colorable G.maxDegree ↔ ¬ HasOverfullSubgraph G) := by
  exact PSLib.Eng.thm12 ε hε

end PlantholtShan
