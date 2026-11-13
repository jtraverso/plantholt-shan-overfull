/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Thm12Pm

/-!
# Removing pairs of perfect matchings

`iter_pm`: for a family `W j` (`j ∈ s`) of small even vertex sets, we remove, for every `j ∈ s`, a
perfect matching of the current graph and a perfect matching of the current graph minus `W j`. A
vertex loses `2 |s|` minus the number of sets containing it, and colourings extend with `2 |s|` new
colours. (This replaces the spanning linear forests of Plantholt–Shan, Case 2 of Theorem 1.2: a
linear forest whose leaves are the pairs of a matching is the union of two such matchings.)
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset SimpleGraph Real
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Iterated removal of pairs of perfect matchings.** -/
theorem iter_pm {J : Type*} [DecidableEq J] {n p : ℕ} (hn : 0 < n)
    (hV : Fintype.card V = 2 * n) (hch : 4 * n * exp (-((p : ℝ) ^ 2 / (2 * n))) < 1) (s0 : ℕ)
    (h2s : 2 * s0 ≤ n) (W : J → Finset V) (hW : ∀ j, Even #(W j) ∧ #(W j) ≤ 2 * s0) :
    ∀ (s : Finset J) (G' : SimpleGraph V), (∀ v, n + p + 4 * s0 + 2 * #s ≤ G'.degree v) →
      ∃ G'' : SimpleGraph V, (∀ v, G''.degree v + 2 * #s =
          G'.degree v + #(s.filter fun j => v ∈ W j)) ∧
        ∀ a, G''.lineGraph.Colorable a → G'.lineGraph.Colorable (a + 2 * #s) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro G' _
    exact ⟨G', fun v => by simp, fun a h => by simpa using h⟩
  | insert j s hj ih =>
    intro G' hdeg
    -- a perfect matching of `G'`
    obtain ⟨τ₁, hτ₁⟩ := exists_pm_avoiding G' hn hV ∅ (by simp) ∅ (t0 := 0) hch
      (fun v _ _ => by have := hdeg v; rw [card_insert_of_notMem hj] at this; simp; omega)
      (fun v _ h => absurd h (notMem_empty v)) (by simp) (by simp)
    obtain ⟨hd₁, hc₁⟩ := remove_pm G' ∅ τ₁ hτ₁
    -- a perfect matching of `G₁ − W j`
    obtain ⟨τ₂, hτ₂⟩ := exists_pm_avoiding (G' \ pmGraph ∅ τ₁) hn hV (W j) (hW j).1 ∅ (t0 := 0) hch
      (fun v _ _ => by
        have h1 := hdeg v; have h2 := hd₁ v; have h3 := (hW j).2
        rw [card_insert_of_notMem hj] at h1; simp only [notMem_empty, if_false] at h2; omega)
      (fun v _ h => absurd h (notMem_empty v)) (by simp) (by have := (hW j).2; omega)
    obtain ⟨hd₂, hc₂⟩ := remove_pm (G' \ pmGraph ∅ τ₁) (W j) τ₂ hτ₂
    obtain ⟨G'', hd, hc⟩ := ih ((G' \ pmGraph ∅ τ₁) \ pmGraph (W j) τ₂) (fun v => by
        have h1 := hdeg v; have h2 := hd₁ v; have h3 := hd₂ v
        rw [card_insert_of_notMem hj] at h1; simp only [notMem_empty, if_false] at h2
        split_ifs at h3 <;> omega)
    refine ⟨G'', fun v => ?_, fun a ha => ?_⟩
    · have h1 := hd v; have h2 := hd₁ v; have h3 := hd₂ v
      simp only [notMem_empty, if_false] at h2
      rw [card_insert_of_notMem hj, filter_insert]
      by_cases hv : v ∈ W j
      · rw [if_pos hv, card_insert_of_notMem (fun h => hj (mem_filter.1 h).1)]
        rw [if_pos hv] at h3; omega
      · rw [if_neg hv]; rw [if_neg hv] at h3; omega
    · have := hc₁ _ (hc₂ _ (hc a ha))
      rw [card_insert_of_notMem hj]
      convert this using 1

end PSLib.Eng
