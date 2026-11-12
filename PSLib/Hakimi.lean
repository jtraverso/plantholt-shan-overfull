/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max

/-!
# Hakimi's theorem on degree sequences of multigraphs

A function `d : V → ℕ` on a finite set is the degree function of a loopless multigraph (symmetric
multiplicities `m : V → V → ℕ` with `m v v = 0`) iff `∑ d` is even and `2 d v ≤ ∑ d` for every
`v`, i.e. no degree exceeds the sum of the others (S. L. Hakimi, 1962).
-/

@[expose] public section

namespace PSLib

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `m` is a loopless multigraph: symmetric multiplicities with zero diagonal. -/
structure IsMultigraph (m : V → V → ℕ) : Prop where
  symm : ∀ u v, m u v = m v u
  loopless : ∀ v, m v v = 0

/-- The degree sum of a loopless multigraph is even. -/
theorem even_sum_degrees {m : V → V → ℕ} (hm : IsMultigraph m) :
    Even (∑ v, ∑ u, m v u) := by
  classical
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  set T := ∑ v, ∑ u, if v < u then m v u else 0
  have hsplit : ∀ v u, m v u = (if v < u then m v u else 0) + (if u < v then m v u else 0) := by
    intro v u
    rcases lt_trichotomy v u with h | rfl | h
    · simp [h, not_lt.2 h.le]
    · simp [hm.loopless]
    · simp [h, not_lt.2 h.le]
  have h2 : ∑ v, ∑ u, (if u < v then m v u else 0) = T := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun v _ => sum_congr rfl fun u _ => ?_
    rw [hm.symm]
  have : ∑ v, ∑ u, m v u = T + T := by
    calc ∑ v, ∑ u, m v u
        = ∑ v, ∑ u, ((if v < u then m v u else 0) + (if u < v then m v u else 0)) :=
          sum_congr rfl fun v _ => sum_congr rfl fun u _ => hsplit v u
      _ = T + ∑ v, ∑ u, (if u < v then m v u else 0) := by
          simp only [sum_add_distrib, T]
      _ = T + T := by rw [h2]
  rw [this]
  exact ⟨T, rfl⟩

/-- In a loopless multigraph no degree exceeds the sum of the others. -/
theorem two_mul_degree_le {m : V → V → ℕ} (hm : IsMultigraph m) (v : V) :
    2 * ∑ u, m v u ≤ ∑ w, ∑ u, m w u := by
  classical
  have h1 : ∑ u ∈ univ.erase v, m v u = ∑ u, m v u := sum_erase _ (hm.loopless v)
  have h2 : ∑ u ∈ univ.erase v, m v u ≤ ∑ w ∈ univ.erase v, ∑ u, m w u :=
    sum_le_sum fun w _ => by
      rw [hm.symm]
      exact single_le_sum (f := fun x => m w x) (fun _ _ => Nat.zero_le _) (mem_univ v)
  have h3 := add_sum_erase univ (fun w => ∑ u, m w u) (mem_univ v)
  omega

/-- **Hakimi's theorem**, the construction. -/
theorem exists_multigraph :
    ∀ (S : ℕ) (d : V → ℕ), ∑ v, d v = S → Even S → (∀ v, 2 * d v ≤ S) →
      ∃ m : V → V → ℕ, IsMultigraph m ∧ ∀ v, ∑ u, m v u = d v := by
  classical
  intro S
  induction S using Nat.strong_induction_on with
  | _ S ih =>
  intro d hS hev hmax
  rcases Nat.eq_zero_or_pos S with rfl | hSpos
  · refine ⟨fun _ _ => 0, ⟨fun _ _ => rfl, fun _ => rfl⟩, fun v => ?_⟩
    have := (sum_eq_zero_iff.1 hS) v (mem_univ v)
    simp [this]
  -- a vertex `v` of maximum degree
  have hne : (univ : Finset V).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hS
    omega
  obtain ⟨v, -, hvmax⟩ := exists_max_image univ d hne
  have hvpos : 0 < d v := by
    by_contra h
    push Not at h
    have : ∀ w, d w = 0 := fun w => by have := hvmax w (mem_univ w); omega
    simp [this] at hS
    omega
  have hrest : ∑ w ∈ univ.erase v, d w + d v = S := by rw [sum_erase_add _ _ (mem_univ v), hS]
  -- a vertex `u ≠ v` of positive degree, preferring one with `2 d u = S`
  obtain ⟨u, huv, hupos, hupref⟩ : ∃ u, u ≠ v ∧ 0 < d u ∧
      ((∃ w, w ≠ v ∧ 2 * d w = S) → 2 * d u = S) := by
    by_cases hbig : ∃ w, w ≠ v ∧ 2 * d w = S
    · obtain ⟨w, hwv, hw⟩ := hbig
      exact ⟨w, hwv, by omega, fun _ => hw⟩
    · have hpos : 0 < ∑ w ∈ univ.erase v, d w := by have := hmax v; omega
      obtain ⟨w, hw, hwpos⟩ : ∃ w ∈ univ.erase v, 0 < d w := by
        by_contra h
        push Not at h
        have : ∑ w ∈ univ.erase v, d w = 0 :=
          sum_eq_zero fun w hw => Nat.le_zero.1 (h w hw)
        omega
      exact ⟨w, ne_of_mem_erase hw, hwpos, fun h => absurd h hbig⟩
  -- the reduced degree function
  set d' : V → ℕ := fun x => d x - (if x = u then 1 else 0) - (if x = v then 1 else 0) with hd'
  have hd'u : d' u + 1 = d u := by simp [hd', huv]; omega
  have hd'v : d' v + 1 = d v := by simp [hd', Ne.symm huv]; omega
  have hd'o : ∀ x, x ≠ u → x ≠ v → d' x = d x := by intro x h1 h2; simp [hd', h1, h2]
  have hsum' : ∑ x, d' x + 2 = S := by
    have e1 : ∑ x, d x = ∑ x, (d' x + ((if x = u then 1 else 0) + (if x = v then 1 else 0))) := by
      refine sum_congr rfl fun x _ => ?_
      by_cases h1 : x = u
      · subst h1; simp [huv]; omega
      · by_cases h2 : x = v
        · subst h2; simp [h1]; omega
        · simp [h1, h2, hd'o x h1 h2]
    rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq', if_pos (mem_univ _),
      if_pos (mem_univ _)] at e1
    omega
  have hmax' : ∀ x, 2 * d' x ≤ S - 2 := by
    intro x
    by_cases h1 : x = u
    · subst h1; have := hmax x; omega
    by_cases h2 : x = v
    · subst h2; have := hmax x; omega
    rw [hd'o x h1 h2]
    by_contra hlt
    push Not at hlt
    -- then `2 d x = S` (parity), so `u` was chosen with `2 d u = S`, impossible
    obtain ⟨r, hr⟩ := hev
    have hx : 2 * d x = S := by have := hmax x; omega
    have hu2 := hupref ⟨x, h2, hx⟩
    have hthree : d x + d u + d v ≤ S := by
      have hsub : ({x, u, v} : Finset V) ⊆ univ := subset_univ _
      have := sum_le_sum_of_subset_of_nonneg hsub (f := d) fun _ _ _ => Nat.zero_le _
      rw [sum_insert (by simp [h1, h2]), sum_insert (by simpa using huv), sum_singleton,
        hS] at this
      omega
    have := hvmax x (mem_univ x)
    omega
  obtain ⟨m', hm', hdeg'⟩ := ih (S - 2) (by omega) d' (by omega)
    (by obtain ⟨r, hr⟩ := hev; exact ⟨r - 1, by omega⟩) hmax'
  refine ⟨fun x y => m' x y + (if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then 1 else 0),
    ⟨fun x y => ?_, fun x => ?_⟩, fun x => ?_⟩
  · rw [hm'.symm x y]
    have : ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) ↔ ((y = u ∧ x = v) ∨ (y = v ∧ x = u)) := by tauto
    simp only [this]
  · have : ¬ ((x = u ∧ x = v) ∨ (x = v ∧ x = u)) := by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact huv (h1.symm.trans h2)
      · exact huv (h2.symm.trans h1)
    simp [hm'.loopless x, this]
  · rw [sum_add_distrib, hdeg' x]
    by_cases h1 : x = u
    · subst h1
      rw [Finset.sum_eq_single v (fun y _ hy => by simp [hy, huv])
        (fun h => absurd (mem_univ v) h)]
      simp only [true_and, and_true, true_or, if_true]
      exact hd'u
    by_cases h2 : x = v
    · subst h2
      rw [Finset.sum_eq_single u (fun y _ hy => by simp [hy, Ne.symm huv])
        (fun h => absurd (mem_univ u) h)]
      simp only [true_and, and_true, or_true, if_true]
      exact hd'v
    · have hiff : ∀ y, ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) := fun y => by
        rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact h1 h
        · exact h2 h
      simp only [hiff, if_false, sum_const_zero, add_zero]
      exact hd'o x h1 h2

end PSLib
