/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Thm12Tools

/-!
# Removing a matching

A partner map `τ` that is an involution on `V ∖ W` along edges of `G` gives a matching `pmGraph W τ`
covering exactly `V ∖ W`. `remove_pm`: the graph `G \ M` has degrees `d − 1` outside `W` and `d` on
`W`, and an edge colouring of `G \ M` with `a` colours extends to one of `G` with `a + 1` colours.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset SimpleGraph
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The matching of a partner map. -/
def pmGraph (W : Finset V) (τ : V → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => u ∉ W ∧ v = τ u

/-- **Removing a matching.** -/
theorem remove_pm (G : SimpleGraph V) (W : Finset V) (τ : V → V)
    (hτ : ∀ v, v ∉ W → τ v ∉ W ∧ τ (τ v) = v ∧ G.Adj v (τ v)) :
    (∀ v, (G \ pmGraph W τ).degree v + (if v ∈ W then 0 else 1) = G.degree v) ∧
      (∀ a, (G \ pmGraph W τ).lineGraph.Colorable a → G.lineGraph.Colorable (a + 1)) := by
  set M := pmGraph W τ
  have hadj : ∀ u v, M.Adj u v ↔ u ∉ W ∧ v = τ u := by
    intro u v
    simp only [M, pmGraph, fromRel_adj]
    constructor
    · rintro ⟨-, h | ⟨hv, rfl⟩⟩
      · exact h
      · exact ⟨(hτ v hv).1, (hτ v hv).2.1.symm⟩
    · rintro ⟨hu, rfl⟩
      exact ⟨(hτ u hu).2.2.ne, Or.inl ⟨hu, rfl⟩⟩
  have hle : M ≤ G := by
    intro u v h
    obtain ⟨hu, rfl⟩ := (hadj u v).1 h
    exact (hτ u hu).2.2
  have hnb : ∀ v, M.neighborFinset v = if v ∈ W then ∅ else {τ v} := by
    intro v
    ext u
    rw [mem_neighborFinset, hadj]
    split_ifs with hv
    · simp [hv]
    · simp [hv, eq_comm]
  have hdM : ∀ v, M.degree v = if v ∈ W then 0 else 1 := by
    intro v
    rw [← card_neighborFinset_eq_degree, hnb]
    split_ifs <;> simp
  refine ⟨fun v => ?_, fun a ha => ?_⟩
  · have h1 : (G \ M).neighborFinset v = G.neighborFinset v \ M.neighborFinset v := by
      ext u; simp [mem_neighborFinset]
    have h2 : M.neighborFinset v ⊆ G.neighborFinset v := by
      intro u hu
      rw [mem_neighborFinset] at hu ⊢
      exact hle hu
    have h3 : (G \ M).degree v = G.degree v - M.degree v := by
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
        ← card_neighborFinset_eq_degree, h1, card_sdiff_of_subset h2]
    have h4 : M.degree v ≤ G.degree v := by
      have := card_le_card h2
      rwa [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at this
    have h5 := hdM v
    rw [h3]
    split_ifs at h5 ⊢ <;> omega
  · refine colorable_of_le_sup (H₁ := G \ M) (H₂ := M) (fun u v h => ?_) ha
      (colorable_one_of_degree_le_one M fun v => by rw [hdM]; split_ifs <;> omega)
    by_cases hm : M.Adj u v
    · exact Or.inr hm
    · exact Or.inl ⟨h, hm⟩

end PSLib.Eng
