/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Step2Ops

/-!
# Step 2: extending the colour classes to perfect matchings

`Inv2` adds three counting invariants to `Pre`:

* `pot`: `2 R + 3 μ + 2 μ_T ≤ K`, where `R` is the number of uncoloured inner edges, `μ` the number
  of (vertex, missing colour) pairs and `μ_T` those at special vertices;
* `xc`: for every colour `c`, `xcnt c + 2 missed c + missed_T c ≤ X`;
* `phi`: `2 R_B + μ_A + K_B = 2 R_A + μ_B + K_A` (balance between the sides).

`step2`: under numerical conditions on the degrees, every state satisfying `Inv2` can be modified
into one where every colour is present at every vertex. The loop: a missing colour at a special
vertex is moved away by a transfer; otherwise two non-special vertices miss a common colour (parity),
and a 5-path (opposite sides) or a transfer followed by a 5-path (same side) repairs both.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → V × V} {A : Finset V} {k : ℕ}

variable (ends) in
/-- The number of (vertex of `S`, missing colour) pairs. -/
def mu (col : E → Option (Fin k)) (S : Finset V) : ℕ := ∑ c, missed ends col c S

variable (ends A) in
/-- The invariant of Step 2. -/
structure Inv2 (T : Finset V) (t K X KA KB : ℕ) (col : E → Option (Fin k)) : Prop
    extends Pre ends A T t col where
  pot : 2 * (rsize ends A col A + rsize ends A col Aᶜ) + 3 * mu ends col univ + 2 * mu ends col T ≤ K
  xc : ∀ c, xcnt ends A col c + 2 * missed ends col c univ + missed ends col c T ≤ X
  phi : 2 * rsize ends A col Aᶜ + mu ends col A + KB = 2 * rsize ends A col A + mu ends col Aᶜ + KA

variable {T : Finset V} {t : ℕ} {col col' : E → Option (Fin k)} {c : Fin k}

theorem sum_ite_and_eq (P : Prop) [Decidable P] :
    ∑ d : Fin k, (if d = c ∧ P then 1 else 0) = if P then 1 else 0 := by
  simp_rw [ite_and]
  rw [sum_ite_eq' univ c]
  simp

theorem mu_transfer {v u : V}
    (h : ∀ d S, missed ends col' d S + (if d = c ∧ v ∈ S then 1 else 0) =
      missed ends col d S + (if d = c ∧ u ∈ S then 1 else 0)) (S : Finset V) :
    mu ends col' S + (if v ∈ S then 1 else 0) = mu ends col S + (if u ∈ S then 1 else 0) := by
  unfold mu
  rw [← sum_ite_and_eq (c := c), ← sum_ite_and_eq (c := c), ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun d _ => h d S

theorem mu_five {a b : V}
    (h : ∀ d S, missed ends col' d S + (if d = c then (if a ∈ S then 1 else 0) +
      (if b ∈ S then 1 else 0) else 0) = missed ends col d S) (S : Finset V) :
    mu ends col' S + ((if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0)) = mu ends col S := by
  unfold mu
  have : ∑ d : Fin k, (if d = c then (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) else 0) =
      (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) := by
    rw [sum_ite_eq' univ c]; simp
  rw [← this, ← sum_add_distrib]
  exact sum_congr rfl fun d _ => h d S

/-- The number of vertices missed by a colour has the parity of the number of vertices. -/
theorem missed_add_two_mul (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (h : Proper ends col) (c : Fin k) :
    missed ends col c univ + 2 * #(univ.filter fun e => col e = some c) = Fintype.card V := by
  classical
  set C := univ.filter fun e => col e = some c
  have hcov : (univ.filter fun v => Covers ends col c v) =
      C.biUnion fun e => univ.filter fun v => Incident ends e v := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, C]
    rfl
  have hdisj : (C : Set E).PairwiseDisjoint fun e => univ.filter fun v => Incident ends e v := by
    intro e he f hf hef
    rw [Function.onFun, disjoint_left]
    intro v hv hv'
    exact hef (h.eq_of_incident (mem_filter.1 he).2 (mem_filter.1 hf).2 (mem_filter.1 hv).2
      (mem_filter.1 hv').2)
  have h2 : #(univ.filter fun v => Covers ends col c v) = 2 * #C := by
    rw [hcov, card_biUnion hdisj, mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun e _ => ?_
    rw [card_filter_incident (e := e) (a := (ends e).1) (b := (ends e).2) (Or.inl rfl) (Or.inr rfl)
      (hloop e)]
    simp
  have := card_filter_add_card_filter_not (s := (univ : Finset V)) (fun v => Covers ends col c v)
  unfold missed
  rw [card_univ] at this
  omega

/-- The numerical estimate for good neighbours, in a state with given bounds. -/
theorem NN_big (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hs : XSimple ends A)
    (hP : Pre ends A T t col) {τT mb xb rb : ℕ} (ht : 0 < t) (hTA : #(T ∩ A) ≤ τT)
    (hTB : #(T ∩ Aᶜ) ≤ τT) (hm : missed ends col c univ ≤ mb) (hx : xcnt ends A col c ≤ xb)
    (hr : rsize ends A col A + rsize ends A col Aᶜ ≤ rb) (w : V) :
    dx ends A w + din ends A w ≤ #(NN ends A col c T t w) + k + rdeg ends A col w + mb + xb +
      2 * τT + 2 * (2 * rb / t) := by
  classical
  have h1 := card_NN_ge (c := c) (T := T) (t := t) hloop hs hP.proper w
  have h2 := miss_add_din_add_ccol (A := A) hP.proper w
  have h3 : missed ends col c (side' A w) ≤ missed ends col c univ :=
    card_le_card (filter_subset_filter _ (subset_univ _))
  have h4 : #(T ∩ side' A w) ≤ τT := by unfold side'; split_ifs <;> assumption
  have h5 : #((side' A w).filter fun x => t ≤ rdeg ends A col x) ≤ 2 * rb / t := by
    rw [Nat.le_div_iff_mul_le ht]
    have := card_high_mul (A := A) (t := t) hloop col (side' A w)
    omega
  omega

set_option maxHeartbeats 2000000 in
open Classical in
/-- **Step 2.** -/
theorem step2 {n τT K X KA KB : ℕ} (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hs : XSimple ends A)
    (hA : #A = n) (hB : #Aᶜ = n) (ht : 0 < t) (hTA : #(T ∩ A) ≤ τT) (hTB : #(T ∩ Aᶜ) ≤ τT)
    (HG : ∀ w, w ∉ T → n + 2 * (k + t + X / 2 + (X + 1) + 2 * τT + 2 * (2 * (K / 2 + 1) / t)) <
      2 * (dx ends A w + din ends A w))
    (HT : ∀ w, w ∈ T → k + X / 2 + (X + 1) + 2 * τT + 2 * (2 * (K / 2 + 1) / t) <
      dx ends A w + din ends A w) :
    ∀ (W : ℕ) (col : E → Option (Fin k)), 3 * mu ends col univ + 2 * mu ends col T = W →
      Inv2 ends A T t K X KA KB col →
      ∃ col' : E → Option (Fin k), Inv2 ends A T t K X KA KB col' ∧
        ∀ c v, Covers ends col' c v := by
  intro W
  induction W using Nat.strong_induction_on with
  | _ W ih =>
  intro col hW hI
  by_cases hall : ∀ c v, Covers ends col c v
  · exact ⟨col, hI, hall⟩
  push Not at hall
  -- generic bounds valid in `col` and after one transfer
  have hNbig : ∀ (col₁ : E → Option (Fin k)) (c : Fin k), Pre ends A T t col₁ →
      missed ends col₁ c univ ≤ X / 2 → xcnt ends A col₁ c ≤ X + 1 →
      rsize ends A col₁ A + rsize ends A col₁ Aᶜ ≤ K / 2 + 1 →
      (∀ w, w ∉ T → n < 2 * #(NN ends A col₁ c T t w)) ∧
        (∀ w, w ∈ T → 0 < #(NN ends A col₁ c T t w)) := by
    intro col₁ c hP hm hx hr
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · have := NN_big (c := c) hloop hs hP ht hTA hTB hm hx hr w
      have := hP.rdeg_le w
      have := HG w hw
      omega
    · have := NN_big (c := c) hloop hs hP ht hTA hTB hm hx hr w
      have := hP.rdeg_eq_zero hw
      have := HT w hw
      omega
  have hbase : ∀ c, missed ends col c univ ≤ X / 2 ∧ xcnt ends A col c ≤ X + 1 ∧
      rsize ends A col A + rsize ends A col Aᶜ ≤ K / 2 + 1 := by
    intro c
    have h1 := hI.xc c
    have h2 := hI.pot
    refine ⟨by omega, by omega, by omega⟩
  by_cases hTc : ∃ c, ∃ v ∈ T, ¬ Covers ends col c v
  · -- a transfer from a special vertex
    obtain ⟨c, v, hvT, hv⟩ := hTc
    obtain ⟨hb1, hb2, hb3⟩ := hbase c
    have hNv := (hNbig col c hI.toPre hb1 hb2 hb3).2 v hvT
    obtain ⟨e, f, w, u, hT, hwT, huT, hwr, hur, hws⟩ := exists_transfer hI.toPre hv hNv
    obtain ⟨hP', hm', hx', hr', -, -⟩ := transfer_pre hI.toPre hT hwT huT hwr hur
    have hwu := side_of_inner hT.fi hT.fb₁ hT.fb₂
    have hmu := mu_transfer hm'
    have hmU := hmu univ
    have hmT := hmu T
    have hmA := hmu A
    have hmB := hmu Aᶜ
    have hrA := hr' A hwu
    have hrB := hr' Aᶜ (by simp only [mem_compl]; tauto)
    simp only [mem_univ, if_true, hvT, huT, if_false, mem_compl] at hmU hmT hmB hrB
    have hW' : 3 * mu ends (transfer col c e f) univ + 2 * mu ends (transfer col c e f) T + 2 = W := by
      omega
    refine ih _ (by omega) (transfer col c e f) rfl ⟨hP', ?_, ?_, ?_⟩
    · have := hI.pot
      split_ifs at hrA hrB <;> omega
    · intro d
      have h1 := hm' d univ
      have h2 := hm' d T
      have h3 := hx' d
      have h4 := hI.xc d
      by_cases hd : d = c
      · subst hd; simp only [true_and, mem_univ, if_true, hvT, huT, if_false] at h1 h2 h3; omega
      · simp only [hd, false_and, if_false] at h1 h2 h3; omega
    · have := hI.phi
      have hws' := mem_side'.1 hws
      by_cases hvA : v ∈ A
      · have hwA : w ∉ A := by tauto
        have huA : u ∉ A := fun h => hwA (hwu.2 h)
        simp only [hvA, huA, hwA, if_true, if_false, not_true_eq_false, not_false_eq_true]
          at hmA hmB hrA hrB
        omega
      · have hwA : w ∈ A := by tauto
        have huA : u ∈ A := hwu.1 hwA
        simp only [hvA, huA, hwA, if_true, if_false, not_true_eq_false, not_false_eq_true]
          at hmA hmB hrA hrB
        omega
  push Not at hTc
  obtain ⟨c, v, hv⟩ := hall
  have hvT : v ∉ T := fun h => hv (hTc c v h)
  obtain ⟨hb1, hb2, hb3⟩ := hbase c
  obtain ⟨hNc, -⟩ := hNbig col c hI.toPre hb1 hb2 hb3
  -- a second vertex missing `c`
  obtain ⟨u, hu, huv⟩ : ∃ u, ¬ Covers ends col c u ∧ u ≠ v := by
    have hpar := missed_add_two_mul hloop hI.proper c
    have hcardV : Fintype.card V = 2 * n := by
      have := card_add_card_compl A
      rw [hA, hB] at this; omega
    have hpos : 0 < missed ends col c univ := by
      unfold missed; rw [card_pos]; exact ⟨v, mem_filter.2 ⟨mem_univ _, hv⟩⟩
    have h2 : 1 < missed ends col c univ := by omega
    unfold missed at h2
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 h2
    by_cases hxv : x = v
    · subst hxv; exact ⟨y, (mem_filter.1 hy).2, fun h => hxy h.symm⟩
    · exact ⟨x, (mem_filter.1 hx).2, hxv⟩
  have huT : u ∉ T := fun h => hu (hTc c u h)
  -- the effect of a 5-path on the invariant
  have hfive : ∀ (col₁ col₂ : E → Option (Fin k)) (a b : V), a ∈ A → b ∉ A → a ∉ T → b ∉ T →
      FiveRel ends A col₁ col₂ c a b →
      (mu ends col₂ univ + 2 = mu ends col₁ univ ∧ mu ends col₂ T = mu ends col₁ T ∧
        mu ends col₂ A + 1 = mu ends col₁ A ∧ mu ends col₂ Aᶜ + 1 = mu ends col₁ Aᶜ ∧
        (∀ d, missed ends col₂ d univ + (if d = c then 2 else 0) = missed ends col₁ d univ) ∧
        ∀ d, missed ends col₂ d T = missed ends col₁ d T) := by
    intro col₁ col₂ a b ha hb haT hbT hR
    have hm := mu_five hR.1
    have h1 := hm univ
    have h2 := hm T
    have h3 := hm A
    have h4 := hm Aᶜ
    simp only [mem_univ, if_true, haT, hbT, if_false, ha, hb, mem_compl, not_true_eq_false,
      not_false_eq_true] at h1 h2 h3 h4
    refine ⟨by omega, by omega, by omega, by omega, fun d => ?_, fun d => ?_⟩
    · have := hR.1 d univ
      simp only [mem_univ, if_true] at this
      split_ifs at this ⊢ <;> omega
    · have := hR.1 d T
      simp only [haT, hbT, if_false, add_zero, ite_self] at this
      exact this
  by_cases hside : (v ∈ A ↔ u ∈ A)
  · -- same side: a transfer from `v`, then a 5-path
    have hNv : 0 < #(NN ends A col c T t v) := by have := hNc v hvT; omega
    obtain ⟨e, f, w, u', hT, hwT, hu'T, hwr, hu'r, hws⟩ := exists_transfer hI.toPre hv hNv
    obtain ⟨hP1, hm1, hx1, hr1, -, hcov1⟩ := transfer_pre hI.toPre hT hwT hu'T hwr hu'r
    set col₁ := transfer col c e f
    have hwu' := side_of_inner hT.fi hT.fb₁ hT.fb₂
    have hws' := mem_side'.1 hws
    have hu'u : u' ≠ u := by rintro rfl; exact hu ⟨f, hT.fcol, hT.fb₂⟩
    have hfu1 : ¬ Covers ends col₁ c u := by
      rw [hcov1]; rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact hu h
      · exact huv h
    have hfu'1 : ¬ Covers ends col₁ c u' := by
      rw [hcov1]; rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact h ⟨rfl, rfl⟩
      · exact hT.a_ne_b₂ h.symm
    have hb1' : missed ends col₁ c univ ≤ X / 2 := by
      have := hm1 c univ; simp only [true_and, mem_univ, if_true] at this; omega
    have hb2' : xcnt ends A col₁ c ≤ X + 1 := by
      have := hx1 c; have := hI.xc c; simp only [if_true] at *; omega
    have hb3' : rsize ends A col₁ A + rsize ends A col₁ Aᶜ ≤ K / 2 + 1 := by
      have h1 := hr1 A hwu'
      have h2 := hr1 Aᶜ (by simp only [mem_compl]; tauto)
      have := hI.pot
      split_ifs at h1 h2 <;> simp_all <;> omega
    obtain ⟨hNc1, -⟩ := hNbig col₁ c hP1 hb1' hb2' hb3'
    -- the 5-path between `u` and `u'`
    have hfiveX : ∃ col₂, Pre ends A T t col₂ ∧
        ((u ∈ A ∧ FiveRel ends A col₁ col₂ c u u') ∨ (u ∉ A ∧ FiveRel ends A col₁ col₂ c u' u)) := by
      by_cases huA : u ∈ A
      · have hu'A : u' ∉ A := by tauto
        obtain ⟨col₂, h1, h2⟩ := exists_five hA hB hP1 huA hu'A huT hu'T hfu1 hfu'1 hNc1
        exact ⟨col₂, h1, Or.inl ⟨huA, h2⟩⟩
      · have hu'A : u' ∈ A := by tauto
        obtain ⟨col₂, h1, h2⟩ := exists_five hA hB hP1 hu'A huA hu'T huT hfu'1 hfu1 hNc1
        exact ⟨col₂, h1, Or.inr ⟨huA, h2⟩⟩
    obtain ⟨col₂, hP2, hR⟩ := hfiveX
    have hmu1 := mu_transfer hm1
    have h1U := hmu1 univ
    have h1T := hmu1 T
    have h1A := hmu1 A
    have h1B := hmu1 Aᶜ
    simp only [mem_univ, if_true, hvT, hu'T, if_false, mem_compl, not_true_eq_false,
      not_false_eq_true] at h1U h1T h1B
    have hrA := hr1 A hwu'
    have hrB := hr1 Aᶜ (by simp only [mem_compl]; tauto)
    simp only [mem_compl] at hrB
    rcases hR with ⟨huA, hR⟩ | ⟨huA, hR⟩
    · have hu'A : u' ∉ A := by tauto
      have hvA : v ∈ A := hside.2 huA
      have hwA : w ∉ A := by tauto
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hfive col₁ col₂ u u' huA hu'A huT hu'T hR
      simp only [hvA, hu'A, hwA, if_true, if_false, not_true_eq_false, not_false_eq_true]
        at h1A h1B hrA hrB
      have hW' : 3 * mu ends col₂ univ + 2 * mu ends col₂ T + 6 = W := by omega
      refine ih _ (by omega) col₂ rfl ⟨hP2, ?_, ?_, ?_⟩
      · have := hI.pot; have := hR.2.2.1; have := hR.2.2.2; omega
      · intro d
        have a1 := hm1 d univ
        have a2 := hm1 d T
        have a3 := hx1 d
        have a4 := hI.xc d
        have a5 := g5 d
        have a6 := g6 d
        have a7 := hR.2.1 d
        by_cases hd : d = c
        · subst hd
          simp only [true_and, mem_univ, if_true, hvT, hu'T, if_false] at a1 a2 a3 a5 a7
          omega
        · simp only [hd, false_and, if_false, add_zero] at a1 a2 a3 a5 a7; omega
      · have := hI.phi; have := hR.2.2.1; have := hR.2.2.2; omega
    · have hu'A : u' ∈ A := by tauto
      have hvA : v ∉ A := fun h => huA (hside.1 h)
      have hwA : w ∈ A := by tauto
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hfive col₁ col₂ u' u hu'A huA hu'T huT hR
      simp only [hvA, hu'A, hwA, if_true, if_false, not_true_eq_false, not_false_eq_true]
        at h1A h1B hrA hrB
      have hW' : 3 * mu ends col₂ univ + 2 * mu ends col₂ T + 6 = W := by omega
      refine ih _ (by omega) col₂ rfl ⟨hP2, ?_, ?_, ?_⟩
      · have := hI.pot; have := hR.2.2.1; have := hR.2.2.2; omega
      · intro d
        have a1 := hm1 d univ
        have a2 := hm1 d T
        have a3 := hx1 d
        have a4 := hI.xc d
        have a5 := g5 d
        have a6 := g6 d
        have a7 := hR.2.1 d
        by_cases hd : d = c
        · subst hd
          simp only [true_and, mem_univ, if_true, hvT, hu'T, if_false] at a1 a2 a3 a5 a7
          omega
        · simp only [hd, false_and, if_false, add_zero] at a1 a2 a3 a5 a7; omega
      · have := hI.phi; have := hR.2.2.1; have := hR.2.2.2; omega
  · -- opposite sides: a 5-path
    have hfiveX : ∃ col₂ a b, Pre ends A T t col₂ ∧ a ∈ A ∧ b ∉ A ∧ a ∉ T ∧ b ∉ T ∧
        FiveRel ends A col col₂ c a b := by
      by_cases hvA : v ∈ A
      · have huA : u ∉ A := by tauto
        obtain ⟨col₂, h1, h2⟩ := exists_five hA hB hI.toPre hvA huA hvT huT hv hu hNc
        exact ⟨col₂, v, u, h1, hvA, huA, hvT, huT, h2⟩
      · have huA : u ∈ A := by tauto
        obtain ⟨col₂, h1, h2⟩ := exists_five hA hB hI.toPre huA hvA huT hvT hu hv hNc
        exact ⟨col₂, u, v, h1, huA, hvA, huT, hvT, h2⟩
    obtain ⟨col₂, a, b, hP2, ha, hb, haT, hbT, hR⟩ := hfiveX
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hfive col col₂ a b ha hb haT hbT hR
    have hW' : 3 * mu ends col₂ univ + 2 * mu ends col₂ T + 6 = W := by omega
    refine ih _ (by omega) col₂ rfl ⟨hP2, ?_, ?_, ?_⟩
    · have := hI.pot; have := hR.2.2.1; have := hR.2.2.2; omega
    · intro d
      have a4 := hI.xc d
      have a5 := g5 d
      have a6 := g6 d
      have a7 := hR.2.1 d
      by_cases hd : d = c
      · subst hd; simp only [if_true] at a5 a7; omega
      · simp only [hd, if_false, add_zero] at a5 a7; omega
    · have := hI.phi; have := hR.2.2.1; have := hR.2.2.2; omega

end PSLib.Eng
