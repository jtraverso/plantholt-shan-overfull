/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Kőnig's edge-colouring theorem for bipartite graphs, via regular multigraphs

For sets `X`, `Y` of the same size and a relation `R` between them in which every vertex has at
most `D` partners, there are `D` bijections `σⱼ : X → Y` such that every `R`-pair `(x, y)` is
`(x, σⱼ x)` for some `j`; colouring the pair by such a `j` gives a proper edge colouring of the
bipartite graph `R` with `D` colours (`exists_konig`).

Proof: complete `R` to a `D`-regular bipartite multigraph by adding edges between deficient vertices
(`exists_transport`), then peel off perfect matchings by Hall's theorem
(`exists_bij_of_regular_mult`).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib

open Finset

section Transport

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Transportation**: nonnegative integer row sums `f` and column sums `g` with the same total
are realized by a matrix. -/
theorem exists_transport : ∀ (S : ℕ) (f : α → ℕ) (g : β → ℕ), ∑ x, f x = S → ∑ y, g y = S →
    ∃ m : α → β → ℕ, (∀ x, ∑ y, m x y = f x) ∧ ∀ y, ∑ x, m x y = g y := by
  intro S
  induction S with
  | zero =>
    intro f g hf hg
    refine ⟨fun _ _ => 0, fun x => ?_, fun y => ?_⟩
    · simp [(sum_eq_zero_iff.1 hf) x (mem_univ x)]
    · simp [(sum_eq_zero_iff.1 hg) y (mem_univ y)]
  | succ S ih =>
    intro f g hf hg
    obtain ⟨x0, hx0⟩ : ∃ x, 0 < f x := by
      by_contra h; push Not at h
      have : ∑ x, f x = 0 := sum_eq_zero fun x _ => Nat.le_zero.1 (h x)
      omega
    obtain ⟨y0, hy0⟩ : ∃ y, 0 < g y := by
      by_contra h; push Not at h
      have : ∑ y, g y = 0 := sum_eq_zero fun y _ => Nat.le_zero.1 (h y)
      omega
    set f' : α → ℕ := Function.update f x0 (f x0 - 1)
    set g' : β → ℕ := Function.update g y0 (g y0 - 1)
    have hf' : ∑ x, f' x = S := by
      have h1 := Finset.sum_update_of_mem (mem_univ x0) f (f x0 - 1)
      have h2 := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (mem_univ x0) f
      simp only [f']; omega
    have hg' : ∑ y, g' y = S := by
      have h1 := Finset.sum_update_of_mem (mem_univ y0) g (g y0 - 1)
      have h2 := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (mem_univ y0) g
      simp only [g']; omega
    obtain ⟨m, hm1, hm2⟩ := ih f' g' hf' hg'
    refine ⟨fun x y => m x y + if x = x0 ∧ y = y0 then 1 else 0, fun x => ?_, fun y => ?_⟩
    · rw [sum_add_distrib, hm1]
      by_cases hx : x = x0
      · subst hx
        simp only [f', Function.update_self, true_and, sum_ite_eq', mem_univ, ite_true]
        omega
      · simp [f', hx]
    · rw [sum_add_distrib, hm2]
      by_cases hy : y = y0
      · subst hy
        simp only [g', Function.update_self, and_true, sum_ite_eq', mem_univ, ite_true]
        omega
      · simp [g', hy]

end Transport

section Hall

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Regular bipartite multigraphs have perfect matchings** (Hall). -/
theorem exists_bij_of_regular_mult (w : α → β → ℕ) (D : ℕ) (hD : 0 < D)
    (hr : ∀ x, ∑ y, w x y = D) (hc : ∀ y, ∑ x, w x y = D) :
    ∃ σ : α → β, Function.Injective σ ∧ ∀ x, 0 < w x (σ x) := by
  classical
  let t : α → Finset β := fun x => univ.filter fun y => 0 < w x y
  have hall : ∀ S : Finset α, #S ≤ #(S.biUnion t) := by
    intro S
    have h1 : ∑ x ∈ S, ∑ y ∈ S.biUnion t, w x y = #S * D := by
      rw [← Finset.sum_const_nat (s := S) (f := fun _ => D) fun _ _ => rfl]
      refine sum_congr rfl fun x hx => ?_
      rw [← hr x]
      refine sum_subset (subset_univ _) fun y _ hy => ?_
      by_contra hpos
      exact hy (mem_biUnion.2 ⟨x, hx, mem_filter.2 ⟨mem_univ _, Nat.pos_of_ne_zero hpos⟩⟩)
    have h2 : ∑ x ∈ S, ∑ y ∈ S.biUnion t, w x y ≤ #(S.biUnion t) * D := by
      rw [sum_comm, ← Finset.sum_const_nat (s := S.biUnion t) (f := fun _ => D) fun _ _ => rfl]
      refine sum_le_sum fun y _ => ?_
      rw [← hc y]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
    exact Nat.le_of_mul_le_mul_right (h1 ▸ h2) hD
  obtain ⟨σ, hinj, hσ⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  exact ⟨σ, hinj, fun x => (mem_filter.1 (hσ x)).2⟩

/-- **Decomposition into perfect matchings.** A `D`-regular bipartite multigraph is a sum of `D`
injective maps. -/
theorem exists_decomposition (hcard : Fintype.card α = Fintype.card β) :
    ∀ (D : ℕ) (w : α → β → ℕ), (∀ x, ∑ y, w x y = D) → (∀ y, ∑ x, w x y = D) →
      ∃ σ : Fin D → α → β, (∀ j, Function.Injective (σ j)) ∧
        ∀ x y, #(univ.filter fun j => σ j x = y) = w x y := by
  classical
  intro D
  induction D with
  | zero =>
    intro w hr _
    refine ⟨fun j => j.elim0, fun j => j.elim0, fun x y => ?_⟩
    have := (sum_eq_zero_iff.1 (hr x)) y (mem_univ y)
    simp [this]
  | succ D ih =>
    intro w hr hc
    obtain ⟨τ, hτinj, hτ⟩ := exists_bij_of_regular_mult w (D + 1) (Nat.succ_pos D) hr hc
    have hτbij : Function.Bijective τ := by
      rw [Fintype.bijective_iff_injective_and_card]; exact ⟨hτinj, hcard⟩
    set w' : α → β → ℕ := fun x y => w x y - if τ x = y then 1 else 0
    have hw' : ∀ x y, w' x y + (if τ x = y then 1 else 0) = w x y := by
      intro x y
      simp only [w']
      split_ifs with h
      · subst h; have := hτ x; omega
      · omega
    have hr' : ∀ x, ∑ y, w' x y = D := by
      intro x
      have := hr x
      rw [← sum_congr rfl fun y _ => hw' x y, sum_add_distrib, sum_ite_eq, if_pos (mem_univ _)]
        at this
      omega
    have hc' : ∀ y, ∑ x, w' x y = D := by
      intro y
      obtain ⟨x0, hx0⟩ := hτbij.2 y
      have := hc y
      rw [← sum_congr rfl fun x _ => hw' x y, sum_add_distrib] at this
      have hone : ∑ x, (if τ x = y then 1 else 0) = 1 := by
        rw [sum_boole]
        have : (univ.filter fun x => τ x = y) = {x0} := by
          ext x; simp only [mem_filter, mem_univ, true_and, mem_singleton]
          constructor
          · intro h; exact hτinj (h.trans hx0.symm)
          · rintro rfl; exact hx0
        rw [this, card_singleton]; rfl
      omega
    obtain ⟨σ, hσinj, hσ⟩ := ih w' hr' hc'
    refine ⟨Fin.snoc σ τ, fun j => ?_, fun x y => ?_⟩
    · induction j using Fin.lastCases with
      | last => simpa using hτinj
      | cast j => simpa using hσinj j
    · rw [← hw' x y, ← hσ x y, card_filter, card_filter, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]

end Hall

section Konig

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Kőnig's edge-colouring theorem** (bipartite graphs with sides of equal size): if every vertex
has at most `D` partners under `R`, there are `D` bijections `σⱼ : α → β` covering every `R`-pair. -/
theorem exists_konig (hcard : Fintype.card α = Fintype.card β) (R : α → β → Prop)
    [∀ x y, Decidable (R x y)] (D : ℕ)
    (hx : ∀ x, #(univ.filter fun y => R x y) ≤ D) (hy : ∀ y, #(univ.filter fun x => R x y) ≤ D) :
    ∃ σ : Fin D → α → β, (∀ j, Function.Injective (σ j)) ∧
      ∀ x y, R x y → ∃ j, σ j x = y := by
  classical
  let r : α → β → ℕ := fun x y => if R x y then 1 else 0
  have hrow : ∀ x, ∑ y, r x y = #(univ.filter fun y => R x y) := fun x => by
    simp only [r, sum_boole, Nat.cast_id]
  have hcol : ∀ y, ∑ x, r x y = #(univ.filter fun x => R x y) := fun y => by
    simp only [r, sum_boole, Nat.cast_id]
  let f : α → ℕ := fun x => D - #(univ.filter fun y => R x y)
  let g : β → ℕ := fun y => D - #(univ.filter fun x => R x y)
  have htot : ∑ x, ∑ y, r x y = ∑ y, ∑ x, r x y := sum_comm
  have hf : ∑ x, f x = Fintype.card α * D - ∑ x, ∑ y, r x y := by
    have : ∀ x, f x + ∑ y, r x y = D := fun x => by rw [hrow]; have := hx x; simp only [f]; omega
    have h := sum_congr rfl fun x (_ : x ∈ univ) => this x
    rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul] at h
    omega
  have hg : ∑ y, g y = Fintype.card β * D - ∑ y, ∑ x, r x y := by
    have : ∀ y, g y + ∑ x, r x y = D := fun y => by rw [hcol]; have := hy y; simp only [g]; omega
    have h := sum_congr rfl fun y (_ : y ∈ univ) => this y
    rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul] at h
    omega
  obtain ⟨m, hm1, hm2⟩ := exists_transport (∑ x, f x) f g rfl (by rw [hf, hg, hcard, htot])
  let w : α → β → ℕ := fun x y => r x y + m x y
  have hwr : ∀ x, ∑ y, w x y = D := fun x => by
    simp only [w]; rw [sum_add_distrib, hm1, hrow]; have := hx x; simp only [f]; omega
  have hwc : ∀ y, ∑ x, w x y = D := fun y => by
    simp only [w]; rw [sum_add_distrib, hm2, hcol]; have := hy y; simp only [g]; omega
  obtain ⟨σ, hσinj, hσ⟩ := exists_decomposition hcard D w hwr hwc
  refine ⟨σ, hσinj, fun x y hxy => ?_⟩
  have hpos : 0 < #(univ.filter fun j => σ j x = y) := by
    rw [hσ x y]; simp only [w, r, if_pos hxy]; omega
  obtain ⟨j, hj⟩ := card_pos.1 hpos
  exact ⟨j, (mem_filter.1 hj).2⟩

end Konig

section FewLow

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Plantholt–Shan, Lemma 2.11.** A bipartite graph with sides of size `n`, minimum degree at
least `t`, and at most `t` vertices of degree less than `n / 2` has a perfect matching. -/
theorem exists_perfect_matching_of_few_low (n t : ℕ) (hα : Fintype.card α = n)
    (hβ : Fintype.card β = n) (R : α → β → Prop) [∀ x y, Decidable (R x y)]
    (hdx : ∀ x, t ≤ #(univ.filter fun y => R x y)) (hdy : ∀ y, t ≤ #(univ.filter fun x => R x y))
    (hlow : #(univ.filter fun x => 2 * #(univ.filter fun y => R x y) < n) +
      #(univ.filter fun y => 2 * #(univ.filter fun x => R x y) < n) ≤ t) :
    ∃ σ : α → β, Function.Injective σ ∧ ∀ x, R x (σ x) := by
  classical
  let nb : α → Finset β := fun x => univ.filter fun y => R x y
  suffices hall : ∀ S : Finset α, #S ≤ #(S.biUnion nb) by
    obtain ⟨σ, hinj, hσ⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective nb).1 hall
    exact ⟨σ, hinj, fun x => (mem_filter.1 (hσ x)).2⟩
  intro S
  by_contra hS
  push Not at hS
  set N := S.biUnion nb with hN
  have hsub : ∀ x ∈ S, nb x ⊆ N := fun x hx => subset_biUnion_of_mem nb hx
  obtain ⟨x0, hx0⟩ : S.Nonempty := by
    rw [← card_pos]; omega
  have ht1 : t + 1 ≤ #S := by
    have := card_le_card (hsub x0 hx0); have : t ≤ #(nb x0) := hdx x0; omega
  -- some vertex of `S` has high degree
  obtain ⟨x1, hx1, hx1hi⟩ : ∃ x ∈ S, n ≤ 2 * #(nb x) := by
    by_contra h
    push Not at h
    have : S ⊆ univ.filter fun x => 2 * #(univ.filter fun y => R x y) < n :=
      fun x hx => mem_filter.2 ⟨mem_univ _, h x hx⟩
    have := card_le_card this
    omega
  have hNhi : n ≤ 2 * #N := by have := card_le_card (hsub x1 hx1); omega
  have hSn : #S ≤ n := hα ▸ card_le_univ S
  -- vertices of `Y \ N` have all their neighbours outside `S`
  have hYlow : ∀ y ∈ univ \ N, #(univ.filter fun x => R x y) ≤ n - #S := by
    intro y hy
    have : (univ.filter fun x => R x y) ⊆ univ \ S := by
      intro x hx
      refine mem_sdiff.2 ⟨mem_univ _, fun hxS => ?_⟩
      exact (mem_sdiff.1 hy).2 (hsub x hxS (mem_filter.2 ⟨mem_univ _, (mem_filter.1 hx).2⟩))
    have := card_le_card this
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hα] at this
    exact this
  have hYcard : #(univ \ N) = n - #N := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hβ]
  have hNn : #N ≤ n := hβ ▸ card_le_univ N
  obtain ⟨y0, hy0⟩ : (univ \ N).Nonempty := by rw [← card_pos]; omega
  have hty : t ≤ n - #S := (hdy y0).trans (hYlow y0 hy0)
  have : univ \ N ⊆ univ.filter fun y => 2 * #(univ.filter fun x => R x y) < n := by
    intro y hy
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    have := hYlow y hy
    omega
  have := card_le_card this
  omega

end FewLow

end PSLib
