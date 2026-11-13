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

/-- A pairing of the vertices in which the even set `W` is the union of the first `m` pairs. -/
theorem exists_pairing_with {n m : ℕ} (hV : Fintype.card V = 2 * n) (W : Finset V)
    (hW : #W = 2 * m) : ∃ e : Fin n × Bool ≃ V, ∀ i b, (e (i, b) ∈ W ↔ i.val < m) := by
  classical
  have hm : m ≤ n := by have := card_le_univ W; omega
  have hα : Fintype.card (Fin m × Bool) = Fintype.card {x // x ∈ W} := by
    simp [hW, mul_comm]
  have hβ : Fintype.card (Fin (n - m) × Bool) = Fintype.card {x // x ∉ W} := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hW, hV]; simp; omega
  let eA := Fintype.equivOfCardEq hα
  let eB := Fintype.equivOfCardEq hβ
  let eF : Fin n ≃ Fin m ⊕ Fin (n - m) := (finCongr (by omega)).trans finSumFinEquiv.symm
  let e : Fin n × Bool ≃ V := (Equiv.prodCongr eF (Equiv.refl Bool)).trans
    ((Equiv.sumProdDistrib _ _ _).trans ((Equiv.sumCongr eA eB).trans
      (Equiv.sumCompl fun x => x ∈ W)))
  refine ⟨e, fun i b => ?_⟩
  rcases hi : eF i with j | j
  · have hij : i.val = j.val := by
      have h2 : (finCongr (by omega : n = m + (n - m)) i : Fin (m + (n - m))) =
          finSumFinEquiv (Sum.inl j) := by
        rw [← hi]; simp [eF]
      have := congrArg Fin.val h2
      simpa using this
    have : e (i, b) = (eA (j, b)).1 := by
      simp [e, hi]
    rw [this, hij]
    exact ⟨fun _ => j.2, fun _ => (eA (j, b)).2⟩
  · have hij : i.val = m + j.val := by
      have h2 : (finCongr (by omega : n = m + (n - m)) i : Fin (m + (n - m))) =
          finSumFinEquiv (Sum.inr j) := by
        rw [← hi]; simp [eF]
      have := congrArg Fin.val h2
      simpa using this
    have : e (i, b) = (eB (j, b)).1 := by
      simp [e, hi]
    rw [this, hij]
    exact ⟨fun h => absurd h (eB (j, b)).2, fun h => by omega⟩

/-- **Perfect matchings avoiding a small even set.** -/
theorem exists_pm_avoiding (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (hn : 0 < n)
    (hV : Fintype.card V = 2 * n) (W : Finset V) (hW : Even #W) (Low : Finset V) {s t0 : ℕ}
    (hch : 4 * n * exp (-((s : ℝ) ^ 2 / (2 * n))) < 1)
    (hgen : ∀ v, v ∉ W → v ∉ Low → n + s + 2 * #W ≤ G.degree v)
    (hlow : ∀ v, v ∉ W → v ∈ Low → s + 2 * #W + 2 * t0 ≤ G.degree v)
    (hLow : #Low ≤ t0) (htn : 2 * t0 + #W ≤ n) :
    ∃ τ : V → V, ∀ v, v ∉ W → τ v ∉ W ∧ τ (τ v) = v ∧ G.Adj v (τ v) := by
  classical
  obtain ⟨m, hm⟩ := hW
  obtain ⟨e, he⟩ := exists_pairing_with hV W (show #W = 2 * m by omega)
  obtain ⟨σ, hσ⟩ := exists_balanced_split G hn e (s := (s : ℝ)) (by positivity) hch
  set A := half e σ
  have hA : #A = n := card_half e σ
  have hB : #Aᶜ = n := by rw [card_compl, hV, hA]; omega
  -- the sizes of the two parts outside `W`
  have hAW : #(A ∩ W) = m := by
    have : A ∩ W = (univ.filter fun i : Fin n => i.val < m).image fun i => e (i, σ i) := by
      ext v
      simp only [A, half, mem_inter, mem_image, mem_univ, true_and, mem_filter]
      constructor
      · rintro ⟨⟨i, rfl⟩, hv⟩; exact ⟨i, (he i _).1 hv, rfl⟩
      · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, rfl⟩, (he i _).2 hi⟩
    rw [this, card_image_of_injective _ (fun i j h => by
      have := e.injective h; simpa using congrArg Prod.fst this)]
    rw [Fin.card_filter_val_lt]; omega
  have hWsplit : #(W ∩ A) + #(W \ A) = #W := card_inter_add_card_sdiff W A
  have hX : #(A \ W) = n - m := by
    have := card_sdiff_add_card_inter A W; rw [hA, hAW] at this; omega
  have hY : #(Aᶜ \ W) = n - m := by
    have h1 := card_sdiff_add_card_inter Aᶜ W
    have h2 : W \ A = Aᶜ ∩ W := by ext v; simp [and_comm]
    rw [inter_comm W A, hAW, h2] at hWsplit
    rw [hB] at h1; omega
  set X := A \ W
  set Y := Aᶜ \ W
  -- degrees across the split
  have hbal : ∀ v, degIn G A v < degIn G Aᶜ v + s ∧ degIn G Aᶜ v < degIn G A v + s := by
    intro v
    have hw := abs_lt.1 (hσ v)
    exact ⟨by exact_mod_cast (by linarith : (degIn G A v : ℝ) < degIn G Aᶜ v + s),
      by exact_mod_cast (by linarith : (degIn G Aᶜ v : ℝ) < degIn G A v + s)⟩
  have hdeg : ∀ v, degIn G A v + degIn G Aᶜ v = G.degree v := by
    intro v
    unfold degIn
    rw [← card_union_of_disjoint (disjoint_filter_filter disjoint_compl_right),
      ← card_neighborFinset_eq_degree]
    congr 1; ext u; simp [mem_neighborFinset]; tauto
  have hdegX : ∀ x ∈ X, degIn G Aᶜ x ≤ #(Y.filter fun y => G.Adj x y) + #W := by
    intro x _
    unfold degIn
    refine (card_le_card fun y hy => ?_).trans (card_union_le _ _)
    by_cases hyW : y ∈ W
    · exact mem_union_right _ hyW
    · exact mem_union_left _ (mem_filter.2 ⟨mem_sdiff.2 ⟨(mem_filter.1 hy).1, hyW⟩,
        (mem_filter.1 hy).2⟩)
  have hdegY : ∀ y ∈ Y, degIn G A y ≤ #(X.filter fun x => G.Adj x y) + #W := by
    intro y _
    unfold degIn
    refine (card_le_card fun x hx => ?_).trans (card_union_le _ _)
    by_cases hxW : x ∈ W
    · exact mem_union_right _ hxW
    · exact mem_union_left _ (mem_filter.2 ⟨mem_sdiff.2 ⟨(mem_filter.1 hx).1, hxW⟩,
        (mem_filter.1 hx).2.symm⟩)
  -- Lemma 2.11 on `X`, `Y`
  let α := {x // x ∈ X}
  let β := {y // y ∈ Y}
  have hα : Fintype.card α = n - m := by rw [Fintype.card_coe, hX]
  have hβ : Fintype.card β = n - m := by rw [Fintype.card_coe, hY]
  have hdx : ∀ x : α, t0 ≤ #(univ.filter fun y : β => G.Adj x.1 y.1) := by
    intro x
    rw [card_filter_subtype Y (fun y => G.Adj x.1 y)]
    have h1 := hdegX x.1 x.2; have h2 := hbal x.1; have h3 := hdeg x.1
    have hxW : x.1 ∉ W := (mem_sdiff.1 x.2).2
    by_cases hL : x.1 ∈ Low
    · have := hlow x.1 hxW hL; omega
    · have := hgen x.1 hxW hL; omega
  have hdy : ∀ y : β, t0 ≤ #(univ.filter fun x : α => G.Adj x.1 y.1) := by
    intro y
    rw [card_filter_subtype X (fun x => G.Adj x y.1)]
    have h1 := hdegY y.1 y.2; have h2 := hbal y.1; have h3 := hdeg y.1
    have hyW : y.1 ∉ W := (mem_sdiff.1 y.2).2
    by_cases hL : y.1 ∈ Low
    · have := hlow y.1 hyW hL; omega
    · have := hgen y.1 hyW hL; omega
  have hlow' : #(univ.filter fun x : α => 2 * #(univ.filter fun y : β => G.Adj x.1 y.1) < n - m) +
      #(univ.filter fun y : β => 2 * #(univ.filter fun x : α => G.Adj x.1 y.1) < n - m) ≤ t0 := by
    have h1 : #(univ.filter fun x : α => 2 * #(univ.filter fun y : β => G.Adj x.1 y.1) < n - m) ≤
        #(X ∩ Low) := by
      rw [card_filter_subtype X (fun x => 2 * #(univ.filter fun y : β => G.Adj x y.1) < n - m)]
      refine card_le_card fun x hx => ?_
      obtain ⟨hxX, hlt⟩ := mem_filter.1 hx
      refine mem_inter.2 ⟨hxX, ?_⟩
      by_contra hL
      rw [card_filter_subtype Y (fun y => G.Adj x y)] at hlt
      have h1 := hdegX x hxX; have h2 := hbal x; have h3 := hdeg x
      have := hgen x (mem_sdiff.1 hxX).2 hL; omega
    have h2 : #(univ.filter fun y : β => 2 * #(univ.filter fun x : α => G.Adj x.1 y.1) < n - m) ≤
        #(Y ∩ Low) := by
      rw [card_filter_subtype Y (fun y => 2 * #(univ.filter fun x : α => G.Adj x.1 y) < n - m)]
      refine card_le_card fun y hy => ?_
      obtain ⟨hyY, hlt⟩ := mem_filter.1 hy
      refine mem_inter.2 ⟨hyY, ?_⟩
      by_contra hL
      rw [card_filter_subtype X (fun x => G.Adj x y)] at hlt
      have h1 := hdegY y hyY; have h2 := hbal y; have h3 := hdeg y
      have := hgen y (mem_sdiff.1 hyY).2 hL; omega
    have h3 : #(X ∩ Low) + #(Y ∩ Low) ≤ #Low := by
      rw [← card_union_of_disjoint]
      · exact card_le_card (union_subset inter_subset_right inter_subset_right)
      · rw [Finset.disjoint_left]; intro v h1 h2
        exact mem_compl.1 (mem_sdiff.1 (mem_inter.1 h2).1).1 (mem_sdiff.1 (mem_inter.1 h1).1).1
    omega
  obtain ⟨σ', hinj, hadj⟩ := exists_perfect_matching_of_few_low (n - m) t0 hα hβ
    (fun x y => G.Adj x.1 y.1) hdx hdy hlow'
  have hbij : Function.Bijective σ' := by
    rw [Fintype.bijective_iff_injective_and_card]; exact ⟨hinj, hα.trans hβ.symm⟩
  set inv := (Equiv.ofBijective σ' hbij).symm
  have hXY : ∀ v, v ∈ X → v ∉ Y := fun v hX hY =>
    mem_compl.1 (mem_sdiff.1 hY).1 (mem_sdiff.1 hX).1
  -- the partner map
  let τ : V → V := fun v =>
    if h : v ∈ X then (σ' ⟨v, h⟩).1 else if h' : v ∈ Y then (inv ⟨v, h'⟩).1 else v
  have hτX : ∀ (v : V) (h : v ∈ X), τ v = (σ' ⟨v, h⟩).1 := fun v h => dif_pos h
  have hτY : ∀ (v : V) (h : v ∈ Y), τ v = (inv ⟨v, h⟩).1 := fun v h => by
    simp only [τ]; rw [dif_neg (fun h' => hXY v h' h), dif_pos h]
  have hσinv : ∀ y : β, σ' (inv y) = y := fun y => (Equiv.ofBijective σ' hbij).apply_symm_apply y
  have hinvσ : ∀ x : α, inv (σ' x) = x := fun x => (Equiv.ofBijective σ' hbij).symm_apply_apply x
  refine ⟨τ, fun v hv => ?_⟩
  have hvXY : v ∈ X ∨ v ∈ Y := by
    by_cases hvA : v ∈ A
    · exact Or.inl (mem_sdiff.2 ⟨hvA, hv⟩)
    · exact Or.inr (mem_sdiff.2 ⟨mem_compl.2 hvA, hv⟩)
  rcases hvXY with hvX | hvY
  · rw [hτX v hvX]
    have hy := (σ' ⟨v, hvX⟩).2
    refine ⟨(mem_sdiff.1 hy).2, ?_, hadj ⟨v, hvX⟩⟩
    rw [hτY _ hy]
    have := hinvσ ⟨v, hvX⟩
    exact congrArg Subtype.val this
  · rw [hτY v hvY]
    have hx := (inv ⟨v, hvY⟩).2
    refine ⟨(mem_sdiff.1 hx).2, ?_, ?_⟩
    · rw [hτX _ hx]
      exact congrArg Subtype.val (hσinv ⟨v, hvY⟩)
    · have := hadj (inv ⟨v, hvY⟩)
      rw [hσinv] at this
      exact this.symm

end PSLib.Eng
