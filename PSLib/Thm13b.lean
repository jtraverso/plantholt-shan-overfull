/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Build
public import PSLib.Engine.Split
public import PSLib.Engine.ParamsB
public import AOF.Main

/-!
# Plantholt–Shan, Theorem 1.3 (b)

A graph on `2n` vertices with two vertices `x ≠ y` of equal degree `δ ≥ (1/2 + 3ε/2) n`, all other
vertices of degree `Δ ≥ (1 + ε) n`, and `Δ − δ ≤ (1/2 − ε/2) n`, has chromatic index `Δ` when `n` is
large.

Proof: split the vertices into halves `A`, `Aᶜ` with `x`, `y` on different sides and all degrees
balanced (Lemma 4.1, `exists_balanced_split`), colour the inner edges with
`k = Δ(G_A ∪ G_B) + 1` colours (Vizing) equalized on each side, and run the engine with the special
set `T = {x, y}`, `t = a / 100`, `l = 2t` (`a = n / q`).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset Real ShannonColouring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A pairing of the vertices with `x`, `y` as the pair `0`. -/
theorem exists_pairing {n : ℕ} (hn : 0 < n) (hV : Fintype.card V = 2 * n) {x y : V}
    (hxy : x ≠ y) : ∃ e : Fin n × Bool ≃ V, e (⟨0, hn⟩, false) = x ∧ e (⟨0, hn⟩, true) = y := by
  classical
  have hcard : Fintype.card (Fin n × Bool) = Fintype.card V := by simp [hV, mul_comm]
  let e0 := Fintype.equivOfCardEq hcard
  set i0 : Fin n := ⟨0, hn⟩
  let e1 := e0.trans (Equiv.swap (e0 (i0, false)) x)
  have h1 : e1 (i0, false) = x := by simp [e1]
  let e2 := e1.trans (Equiv.swap (e1 (i0, true)) y)
  have hne : x ≠ e1 (i0, true) := by
    rw [← h1]; intro h; have := e1.injective h; simp at this
  refine ⟨e2, ?_, by simp [e2]⟩
  show Equiv.swap (e1 (i0, true)) y (e1 (i0, false)) = x
  rw [h1, Equiv.swap_apply_of_ne_of_ne hne hxy]

theorem sum_dx_side {E : Type*} [Fintype E] [DecidableEq E] {ends : E → V × V} {A : Finset V}
    (S : Finset V) (hS : S = A ∨ S = Aᶜ) :
    ∑ v ∈ S, dx ends A v = #(univ.filter fun e => ¬ Inner ends A e) := by
  classical
  unfold dx
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  by_cases hi : Inner ends A e
  · simp [hi]
  · simp only [hi, not_false_eq_true, true_and, if_true]
    rw [← card_filter]
    unfold Inner at hi
    have hne : (ends e).1 ≠ (ends e).2 := fun h => hi (by rw [h])
    rw [card_filter_incident (e := e) (a := (ends e).1) (b := (ends e).2) (Or.inl rfl) (Or.inr rfl)
      hne]
    rcases hS with hS | hS <;> rw [hS]
    · by_cases h : (ends e).1 ∈ A
      · have : (ends e).2 ∉ A := fun h' => hi ⟨fun _ => h', fun _ => h⟩
        simp [h, this]
      · have : (ends e).2 ∈ A := by
          by_contra h'; exact hi ⟨fun h'' => absurd h'' h, fun h'' => absurd h'' h'⟩
        simp [h, this]
    · by_cases h : (ends e).1 ∈ A
      · have : (ends e).2 ∉ A := fun h' => hi ⟨fun _ => h', fun _ => h⟩
        simp [h, this]
      · have : (ends e).2 ∈ A := by
          by_contra h'; exact hi ⟨fun h'' => absurd h'' h, fun h'' => absurd h'' h'⟩
        simp [h, this]

/-- A proper colouring of the edge family gives a colouring of the line graph. -/
theorem lineGraph_colorable_of {G : SimpleGraph V} [DecidableRel G.Adj] {Δ : ℕ}
    (fc : GE G → Fin Δ) (hfc : IsProperEdgeColouring (gends G) fc) : G.lineGraph.Colorable Δ := by
  refine ⟨SimpleGraph.Coloring.mk (fun e => fc ⟨e.1, SimpleGraph.mem_edgeFinset.2 e.2⟩) ?_⟩
  intro e f hef
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hef
  obtain ⟨hne, v, hve, hvf⟩ := hef
  refine hfc _ _ (fun h => hne (Subtype.ext (by simpa using congrArg Subtype.val h))) ⟨v, ?_, ?_⟩
  · exact (gends_incident_iff _ v).2 hve
  · exact (gends_incident_iff _ v).2 hvf

end PSLib.Eng
