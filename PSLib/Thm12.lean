/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Thm12Main
public import Plantholt.Main

/-!
# Plantholt–Shan, Theorem 1.2

For `0 < ε` there is `N` such that a graph `G` on `2n ≥ 2N` vertices with minimum degree at least
`(1 + ε) n` has chromatic index `Δ(G)` if and only if it contains no `Δ(G)`-overfull subgraph.

The `Δ`-overfull subgraphs are those of the registered entry `jtraverso/plantholt-overfull-criterion`
(`Plantholt.HasOverfullSubgraph`). The forward direction is `Plantholt.two_mul_eIn_le_of_colorable`;
for the converse, the subgraphs `G − z` give `2Δ ≤ defi G Δ + 2 d(z)`, and `thm12_of_ge` applies.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset SimpleGraph Real

universe u

/-- **Plantholt–Shan, Theorem 1.2.** -/
theorem thm12 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n : ℕ), N ≤ n → Fintype.card V = 2 * n → (1 + ε) * n ≤ G.minDegree →
      (G.lineGraph.Colorable G.maxDegree ↔ ¬ Plantholt.HasOverfullSubgraph G) := by
  classical
  obtain ⟨q0, hq0⟩ := exists_nat_one_div_lt hε
  set q := q0 + 1
  have hq : 0 < q := Nat.succ_pos q0
  have hqε : 1 / (q : ℝ) < ε := by simpa [q] using hq0
  obtain ⟨N, hN⟩ := thm12_of_ge.{u} hq
  refine ⟨N, fun V _ _ G inst n hn hV hδ => ?_⟩
  obtain rfl : inst = fun a b => Classical.propDecidable (G.Adj a b) := Subsingleton.elim _ _
  rw [← Plantholt.noOverfull_iff]
  constructor
  · intro hcol S hS
    exact Plantholt.two_mul_eIn_le_of_colorable G hcol hS
  · intro hno
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    have hεq : 1 < ε * q := by rwa [div_lt_iff₀ hqpos] at hqε
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    apply hN V n hn hV G.maxDegree G
    · intro v
      refine ⟨?_, G.degree_le_maxDegree v⟩
      have h1 : ((q : ℝ) + 1) * n ≤ q * G.minDegree := by
        have := mul_le_mul_of_nonneg_left hδ hqpos.le
        nlinarith
      have h2 : (q + 1) * n ≤ q * G.minDegree := by exact_mod_cast h1
      exact le_trans h2 (Nat.mul_le_mul_left _ (G.minDegree_le_degree v))
    · intro z
      -- the odd set `V − z`
      have hodd : Odd #(univ.erase z) := by
        rw [card_erase_of_mem (mem_univ z), card_univ, hV]
        have : 0 < n := by
          by_contra h; push Not at h
          have : n = 0 := by omega
          subst this
          simp at hV
          exact (Fintype.card_eq_zero_iff.1 hV).elim z
        exact ⟨n - 1, by omega⟩
      have h1 := hno _ hodd
      have h2 := Plantholt.eIn_erase_add G z
      have h3 := G.sum_degrees_eq_twice_card_edges
      have h4 : defi G G.maxDegree + ∑ v, G.degree v = 2 * n * G.maxDegree := by
        unfold defi
        rw [← sum_add_distrib, sum_congr rfl fun v _ => Nat.sub_add_cancel (G.degree_le_maxDegree v),
          sum_const, card_univ, hV, smul_eq_mul]
      rw [card_erase_of_mem (mem_univ z), card_univ, hV] at h1
      have h5 : G.maxDegree * (2 * n - 1 - 1) + 2 * G.maxDegree = 2 * n * G.maxDegree := by
        have : 1 ≤ n := by
          by_contra h; push Not at h
          have : n = 0 := by omega
          subst this; simp at hV; exact (Fintype.card_eq_zero_iff.1 hV).elim z
        have e : 2 * n - 1 - 1 + 2 = 2 * n := by omega
        calc G.maxDegree * (2 * n - 1 - 1) + 2 * G.maxDegree
            = G.maxDegree * (2 * n - 1 - 1 + 2) := by ring
          _ = 2 * n * G.maxDegree := by rw [e]; ring
      have h6 := G.degree_le_maxDegree z
      nlinarith

end PSLib.Eng
