/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Main

/-!
# The initial state of Step 2

Colour every inner edge by a proper colouring `c1` with `k` colours whose classes are equalized on
each side, and leave the crossing edges uncoloured. This state satisfies `Inv2` with
`K = 3 μ₀ + 2 μ_T₀`, `X = 3 (μ₀ / k + 4)`, `K_A = μ_A`, `K_B = μ_B` (`init_inv`); moreover
`miss v + din v = k` for every vertex, and `μ_S = ∑_{v ∈ S} miss v`.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → V × V} {A : Finset V} {k : ℕ}

variable (ends A) in
/-- The inner edges with first end in `S`. -/
def innerSide (S : Finset V) : Finset E := univ.filter fun e => Inner ends A e ∧ (ends e).1 ∈ S

variable (ends A) in
/-- The initial colouring: inner edges by `c1`, crossing edges uncoloured. -/
def col0 (c1 : E → Fin k) (e : E) : Option (Fin k) := if Inner ends A e then some (c1 e) else none

theorem mu_eq_sum_miss (col : E → Option (Fin k)) (S : Finset V) :
    mu ends col S = ∑ v ∈ S, miss ends col v := by
  unfold mu missed miss
  simp only [card_filter]
  rw [sum_comm]

theorem sum_din_side (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (S : Finset V) (hS : S = A ∨ S = Aᶜ) :
    ∑ v ∈ S, din ends A v = 2 * #(innerSide ends A S) := by
  classical
  unfold din innerSide
  simp only [card_filter]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  by_cases hi : Inner ends A e
  · have hsame : ((ends e).1 ∈ S ↔ (ends e).2 ∈ S) := by
      unfold Inner at hi
      rcases hS with rfl | rfl
      · exact hi
      · simp only [mem_compl]; tauto
    by_cases h1 : (ends e).1 ∈ S
    · simp only [hi, h1, and_self, if_true, mul_one, true_and]
      rw [← card_filter, card_filter_incident (e := e) (a := (ends e).1) (b := (ends e).2)
        (Or.inl rfl) (Or.inr rfl) (hloop e), if_pos h1, if_pos (hsame.1 h1)]
    · simp only [hi, h1, and_false, if_false, mul_zero, true_and]
      rw [← card_filter, card_eq_zero, filter_eq_empty_iff]
      intro v hv hev
      rcases hev with rfl | rfl
      · exact h1 hv
      · exact h1 (hsame.2 hv)
  · simp [hi]

theorem cls_eq_innerSide (c1 : E → Fin k) (S : Finset V) (a : Fin k) :
    cls (innerSide ends A S) c1 a = #((innerSide ends A S).filter fun e => c1 e = a) := rfl

/-- **The initial state.** -/
theorem init_inv (hloop : ∀ e, (ends e).1 ≠ (ends e).2) {n : ℕ} (hA : #A = n) (hB : #Aᶜ = n)
    (hk : 0 < k) (c1 : E → Fin k)
    (hprop : ProperOn ends (univ.filter fun e => Inner ends A e) c1)
    (heqA : ∀ a b, cls (innerSide ends A A) c1 a ≤ cls (innerSide ends A A) c1 b + 1)
    (heqB : ∀ a b, cls (innerSide ends A Aᶜ) c1 a ≤ cls (innerSide ends A Aᶜ) c1 b + 1)
    (T : Finset V) (t : ℕ) :
    Inv2 ends A T t (3 * mu ends (col0 ends A c1) univ + 2 * mu ends (col0 ends A c1) T)
      (3 * (mu ends (col0 ends A c1) univ / k + 4)) (mu ends (col0 ends A c1) A)
      (mu ends (col0 ends A c1) Aᶜ) (col0 ends A c1) ∧
    ∀ v, miss ends (col0 ends A c1) v + din ends A v = k := by
  classical
  set col := col0 ends A c1
  have hprop' : Proper ends col := by
    intro e f hef he heq v hev hfv
    simp only [col, col0] at he heq
    by_cases hi : Inner ends A e
    · rw [if_pos hi] at heq
      by_cases hf : Inner ends A f
      · rw [if_pos hf] at heq
        exact hprop e (mem_filter.2 ⟨mem_univ _, hi⟩) f (mem_filter.2 ⟨mem_univ _, hf⟩) hef
          ⟨v, hev, hfv⟩ (Option.some_injective _ heq)
      · rw [if_neg hf] at heq; exact Option.some_ne_none _ heq
    · rw [if_neg hi] at he; exact he rfl
  have hrdeg : ∀ v, rdeg ends A col v = 0 := by
    intro v; unfold rdeg; rw [card_eq_zero, filter_eq_empty_iff]
    rintro e - ⟨hi, hc, -⟩; simp [col, col0, hi] at hc
  have hccol : ∀ v, ccol ends A col v = 0 := by
    intro v; unfold ccol; rw [card_eq_zero, filter_eq_empty_iff]
    rintro e - ⟨hi, hc, -⟩; simp [col, col0, hi] at hc
  have hmiss : ∀ v, miss ends col v + din ends A v = k := by
    intro v; have := miss_add_din_add_ccol (A := A) hprop' v; rw [hrdeg, hccol] at this; omega
  have hrsize : ∀ S, rsize ends A col S = 0 := by
    intro S; unfold rsize; rw [card_eq_zero, filter_eq_empty_iff]
    rintro e - ⟨hi, hc, -⟩; simp [col, col0, hi] at hc
  have hxcnt : ∀ c, xcnt ends A col c = 0 := by
    intro c; unfold xcnt; rw [card_eq_zero, filter_eq_empty_iff]
    rintro e - ⟨hi, hc⟩; simp [col, col0, hi] at hc
  -- the missed counts on one side
  have hside : ∀ (S : Finset V), (S = A ∨ S = Aᶜ) → #S = n →
      (∀ a b, cls (innerSide ends A S) c1 a ≤ cls (innerSide ends A S) c1 b + 1) →
      ∀ c, missed ends col c S ≤ mu ends col S / k + 2 := by
    intro S hS hSn heq c
    set C := (innerSide ends A S).filter fun e => c1 e = c
    have hends : ∀ e ∈ C, ∀ v, Incident ends e v → v ∈ S := by
      intro e he v hv
      have h1 := (mem_filter.1 (mem_filter.1 he).1).2
      have := side_of_inner h1.1 (Or.inl rfl) hv
      rcases hS with rfl | rfl
      · exact this.1 h1.2
      · rw [mem_compl] at h1 ⊢; exact fun h => h1.2 (this.2 h)
    have hcov : S.filter (fun v => Covers ends col c v) =
        C.biUnion fun e => univ.filter fun v => Incident ends e v := by
      ext v
      simp only [mem_filter, mem_biUnion, mem_univ, true_and, Covers, C, innerSide, col, col0]
      constructor
      · rintro ⟨hv, e, he, hev⟩
        have hi : Inner ends A e := by by_contra hi; rw [if_neg hi] at he; simp at he
        rw [if_pos hi] at he
        refine ⟨e, ⟨⟨hi, ?_⟩, Option.some_injective _ he⟩, hev⟩
        have := side_of_inner hi (Or.inl rfl) hev
        rcases hS with rfl | rfl
        · exact this.2 hv
        · rw [mem_compl] at hv ⊢; exact fun h => hv (this.1 h)
      · rintro ⟨e, ⟨⟨hi, h1⟩, hc⟩, hev⟩
        refine ⟨hends e (mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hi, h1⟩, hc⟩) v hev, e, ?_, hev⟩
        rw [if_pos hi, hc]
    have hdisj : (C : Set E).PairwiseDisjoint fun e => univ.filter fun v => Incident ends e v := by
      intro e he f hf hef
      rw [Function.onFun, disjoint_left]
      intro v hv hv'
      have he' := mem_filter.1 he
      have hf' := mem_filter.1 hf
      exact hprop e (mem_filter.2 ⟨mem_univ _, (mem_filter.1 he'.1).2.1⟩) f
        (mem_filter.2 ⟨mem_univ _, (mem_filter.1 hf'.1).2.1⟩) hef
        ⟨v, (mem_filter.1 hv).2, (mem_filter.1 hv').2⟩ (he'.2.trans hf'.2.symm)
    have hcovc : #(S.filter fun v => Covers ends col c v) = 2 * cls (innerSide ends A S) c1 c := by
      rw [hcov, card_biUnion hdisj]
      unfold cls
      rw [mul_comm, ← smul_eq_mul, ← sum_const]
      refine sum_congr rfl fun e _ => ?_
      rw [card_filter_incident (e := e) (a := (ends e).1) (b := (ends e).2) (Or.inl rfl)
        (Or.inr rfl) (hloop e)]
      simp
    have hmissed : missed ends col c S + 2 * cls (innerSide ends A S) c1 c = n := by
      unfold missed
      rw [← hcovc, ← hSn]
      have := card_filter_add_card_filter_not (s := S) (fun v => Covers ends col c v)
      omega
    -- `μ_S = k n − 2 #(inner edges of S)`
    have hmu : mu ends col S + 2 * #(innerSide ends A S) = k * n := by
      rw [mu_eq_sum_miss, ← sum_din_side hloop S hS, ← sum_add_distrib]
      rw [sum_congr rfl fun v _ => hmiss v, sum_const, smul_eq_mul, hSn, mul_comm]
    have hsum : ∑ b, cls (innerSide ends A S) c1 b = #(innerSide ends A S) := sum_cls _ c1
    have hle : #(innerSide ends A S) ≤ k * (cls (innerSide ends A S) c1 c + 1) := by
      rw [← hsum]
      calc ∑ b, cls (innerSide ends A S) c1 b ≤ ∑ _b : Fin k, (cls (innerSide ends A S) c1 c + 1) :=
            sum_le_sum fun b _ => heq b c
        _ = k * (cls (innerSide ends A S) c1 c + 1) := by simp
    have : k * missed ends col c S ≤ mu ends col S + 2 * k := by nlinarith
    have h2 : missed ends col c S ≤ (mu ends col S + 2 * k) / k :=
      (Nat.le_div_iff_mul_le hk).2 (by linarith)
    rwa [Nat.add_mul_div_right _ _ hk] at h2
  refine ⟨⟨⟨hprop', ?_, fun v => by rw [hrdeg]; exact Nat.zero_le _⟩, ?_, ?_, ?_⟩, hmiss⟩
  · intro e hi hc; simp [col, col0, hi] at hc
  · rw [hrsize, hrsize]; omega
  · intro c
    rw [hxcnt]
    have h1 := hside A (Or.inl rfl) hA heqA c
    have h2 := hside Aᶜ (Or.inr rfl) hB heqB c
    have hU : missed ends col c univ = missed ends col c A + missed ends col c Aᶜ := by
      unfold missed
      rw [← card_union_of_disjoint (disjoint_filter_filter disjoint_compl_right)]
      congr 1; ext v; simp [mem_filter]; tauto
    have hT : missed ends col c T ≤ missed ends col c univ :=
      card_le_card (filter_subset_filter _ (subset_univ T))
    have hmuU : mu ends col univ = mu ends col A + mu ends col Aᶜ := by
      rw [mu_eq_sum_miss, mu_eq_sum_miss, mu_eq_sum_miss, ← sum_add_sum_compl A]
    have hdiv : mu ends col A / k + mu ends col Aᶜ / k ≤ mu ends col univ / k := by
      rw [hmuU]; exact Nat.add_div_le_add_div _ _ _
    omega
  · rw [hrsize, hrsize]; omega

end PSLib.Eng
