/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Split
public import PSLib.Engine.Step3Loop
public import PSLib.Konig
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Tools for Theorem 1.2

* `colorable_of_le_sup`: if every edge of `G` is an edge of `H₁` or of `H₂`, colourings of the line
  graphs of `H₁` and `H₂` with `a` and `b` colours give one of `G` with `a + b` colours.
* `colorable_one_of_degree_le_one`: a matching is edge-colourable with one colour.
* `exists_pairing_with`: a pairing of the vertices in which an even set `W` is a union of pairs.
* `exists_pm_avoiding`: in a graph of high minimum degree, `V ∖ W` has a perfect matching, for a
  small even set `W` (a balanced split along such a pairing and Lemma 2.11).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset Real AOF SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Union of edge colourings.** -/
theorem colorable_of_le_sup {G H₁ H₂ : SimpleGraph V} {a b : ℕ}
    (hle : ∀ u v, G.Adj u v → H₁.Adj u v ∨ H₂.Adj u v) (h₁ : H₁.lineGraph.Colorable a)
    (h₂ : H₂.lineGraph.Colorable b) : G.lineGraph.Colorable (a + b) := by
  classical
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  have hmem : ∀ e : G.edgeSet, e.1 ∉ H₁.edgeSet → e.1 ∈ H₂.edgeSet := by
    rintro ⟨e, he⟩ h
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeSet] at he ⊢
      rcases hle u v he with h' | h'
      · exact absurd ((mem_edgeSet _).2 h') h
      · exact h'
  refine ⟨Coloring.mk (fun e => if h : e.1 ∈ H₁.edgeSet then Fin.castAdd b (c₁ ⟨e.1, h⟩)
    else Fin.natAdd a (c₂ ⟨e.1, hmem e h⟩)) ?_⟩
  intro e f hef
  rw [lineGraph_adj_iff_exists] at hef
  obtain ⟨hne, v, hve, hvf⟩ := hef
  by_cases he : e.1 ∈ H₁.edgeSet <;> by_cases hf : f.1 ∈ H₁.edgeSet <;>
    simp only [dif_pos, dif_neg, he, hf, not_false_eq_true]
  · intro h
    have := Fin.castAdd_injective _ _ h
    exact c₁.valid (show H₁.lineGraph.Adj ⟨e.1, he⟩ ⟨f.1, hf⟩ by
      rw [lineGraph_adj_iff_exists]
      exact ⟨fun h' => hne (Subtype.ext (by simpa using congrArg Subtype.val h')), v, hve, hvf⟩)
      this
  · intro h
    have := congrArg Fin.val h
    simp at this; omega
  · intro h
    have := congrArg Fin.val h
    simp at this; omega
  · intro h
    have := Fin.natAdd_injective _ _ h
    exact c₂.valid (show H₂.lineGraph.Adj ⟨e.1, hmem e he⟩ ⟨f.1, hmem f hf⟩ by
      rw [lineGraph_adj_iff_exists]
      exact ⟨fun h' => hne (Subtype.ext (by simpa using congrArg Subtype.val h')), v, hve, hvf⟩)
      this

/-- **A matching needs one colour.** -/
theorem colorable_one_of_degree_le_one (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : ∀ v, M.degree v ≤ 1) : M.lineGraph.Colorable 1 := by
  refine ⟨Coloring.mk (fun _ => 0) ?_⟩
  intro e f hef
  rw [lineGraph_adj_iff_exists] at hef
  obtain ⟨hne, v, hve, hvf⟩ := hef
  exfalso
  obtain ⟨e, he⟩ := e
  obtain ⟨f, hf⟩ := f
  simp only at hve hvf
  obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.1 hve
  obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.1 hvf
  rw [mem_edgeSet] at he hf
  have hab : a ≠ b := by rintro rfl; exact hne rfl
  have : 2 ≤ M.degree v := by
    rw [← card_neighborFinset_eq_degree]
    have : ({a, b} : Finset V) ⊆ M.neighborFinset v := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simpa
    have := card_le_card this
    rwa [card_pair hab] at this
  have := hM v
  omega

end PSLib.Eng
