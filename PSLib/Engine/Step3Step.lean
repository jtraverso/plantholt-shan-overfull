/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Step3Loop

/-!
# Step 3: one new colour

`J_step`: the invariant `J` extends from a set `P` of processed new colours to `insert j P`, by a
perfect matching (Lemma 2.11) between the uncovered vertices of the two sides.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → V × V} {A : Finset V} {k l : ℕ}
  {col : E → Option (Fin k)} {c3 : E → Fin l}

theorem miss_eq_zero (hcov : ∀ c v, Covers ends col c v) (v : V) : miss ends col v = 0 := by
  unfold miss; rw [card_eq_zero, filter_eq_empty_iff]; exact fun c _ h => h (hcov c v)

/-- The degree estimate in the bipartite graph of available crossing edges. -/
theorem avail_ge (hs : XSimple ends A) {T : Finset V} {t : ℕ} (hP : Pre ends A T t col)
    (hcov : ∀ c v, Covers ends col c v) (cx : E → Option (Fin l)) {Y : Finset V} {cm : ℕ}
    (v : V) (_hY : Y ⊆ side' A v) (hYc : #(side' A v \ Y) ≤ cm) :
    dx ends A v + din ends A v ≤ #(Y.filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = none ∧
      cx e = none ∧ Incident ends e v ∧ Incident ends e w) + cm + k + rdeg ends A col v +
      ccx ends A cx v := by
  classical
  have h1 := card_avail (col := col) hs cx v
  have h2 := miss_add_din_add_ccol (A := A) hP.proper v
  rw [miss_eq_zero hcov] at h2
  have h3 : #((side' A v).filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = none ∧ cx e = none ∧
      Incident ends e v ∧ Incident ends e w) ≤ #(Y.filter fun w => ∃ e, ¬ Inner ends A e ∧
      col e = none ∧ cx e = none ∧ Incident ends e v ∧ Incident ends e w) +
      #(side' A v \ Y) := by
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro w hw
    by_cases hwY : w ∈ Y
    · exact mem_union_left _ (mem_filter.2 ⟨hwY, (mem_filter.1 hw).2⟩)
    · exact mem_union_right _ (mem_sdiff.2 ⟨(mem_filter.1 hw).1, hwY⟩)
  omega

open Classical in
/-- **One new colour.** -/
theorem J_step (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hs : XSimple ends A)
    {n τT t cmax : ℕ} {T L : Finset V} (hA : #A = n) (hB : #Aᶜ = n)
    (hP : Pre ends A T t col) (hcov : ∀ c v, Covers ends col c v)
    (hc3 : ProperOn ends (Rset ends A col) c3)
    (hcA : ∀ j, cls (Rside ends A col A) c3 j ≤ cmax)
    (hcB : ∀ j, cls (Rside ends A col Aᶜ) c3 j ≤ cmax)
    (hcase : (∀ j, cls (Rside ends A col A) c3 j = cls (Rside ends A col Aᶜ) c3 j) ∨
      (4 * cmax ≤ #(L ∩ A) ∧ 4 * cmax ≤ #(L ∩ Aᶜ)))
    (hTA : #(T ∩ A) ≤ τT) (hTB : #(T ∩ Aᶜ) ≤ τT)
    (HG3 : ∀ w, w ∉ T → n + 2 * (k + t + l + 2 * cmax) < 2 * (dx ends A w + din ends A w))
    (HT3 : ∀ w, w ∈ T → k + l + 2 * cmax + 2 * τT ≤ dx ends A w + din ends A w)
    (h4 : 4 * τT ≤ n)
    {P : Finset (Fin l)} {cx : E → Option (Fin l)} {F : Fin l → Finset V}
    (hJ : J ends A col c3 L P cx F) {j : Fin l} (hj : j ∉ P) :
    ∃ cx' F', J ends A col c3 L (insert j P) cx' F' := by
  -- the vertices covered by `R`-edges of colour `j`
  set AJ := covR ends A col c3 j A
  set BJ := covR ends A col c3 j Aᶜ
  have hAJs : AJ ⊆ A := filter_subset _ _
  have hBJs : BJ ⊆ Aᶜ := filter_subset _ _
  have hAJc : #AJ = 2 * cls (Rside ends A col A) c3 j := card_covR hloop hc3 j A (Or.inl rfl)
  have hBJc : #BJ = 2 * cls (Rside ends A col Aᶜ) c3 j := card_covR hloop hc3 j Aᶜ (Or.inr rfl)
  have hcase' : #AJ = #BJ ∨ (4 * cmax ≤ #(L ∩ A) ∧ 4 * cmax ≤ #(L ∩ Aᶜ)) := by
    rcases hcase with h | h
    · left; rw [hAJc, hBJc, h j]
    · right; exact h
  obtain ⟨Fj, hFL, hXY, hXc, hYc⟩ := exists_fillers hA hB hAJs hBJs
    (by have := hcA j; omega) (by have := hcB j; omega) hcase'
  set X := A \ (AJ ∪ Fj)
  set Y := Aᶜ \ (BJ ∪ Fj)
  have hXA : X ⊆ A := sdiff_subset
  have hYB : Y ⊆ Aᶜ := sdiff_subset
  have hXc' : #(A \ X) ≤ 2 * cmax := by
    rw [sdiff_sdiff_right_self, inf_eq_inter]; exact hXc
  have hYc' : #(Aᶜ \ Y) ≤ 2 * cmax := by
    rw [sdiff_sdiff_right_self, inf_eq_inter]; exact hYc
  have hsideX : ∀ x ∈ X, side' A x = Aᶜ := fun x hx => by unfold side'; rw [if_pos (hXA hx)]
  have hsideY : ∀ y ∈ Y, side' A y = A := fun y hy => by
    unfold side'; rw [if_neg (mem_compl.1 (hYB hy))]
  set H : V → V → Prop := fun v w => ∃ e, ¬ Inner ends A e ∧ col e = none ∧ cx e = none ∧
    Incident ends e v ∧ Incident ends e w
  have hHsymm : ∀ v w, H v w → H w v := by
    rintro v w ⟨e, h1, h2, h3, h4, h5⟩; exact ⟨e, h1, h2, h3, h5, h4⟩
  have hccx : ∀ v, ccx ends A cx v ≤ l := by
    intro v; have := hJ.j6 v
    have : #P ≤ l := by
      have := card_le_univ P; rw [Fintype.card_fin] at this; exact this
    omega
  -- degrees
  have hdegX : ∀ x ∈ X, dx ends A x + din ends A x ≤ #(Y.filter fun w => H x w) + 2 * cmax + k +
      rdeg ends A col x + l := by
    intro x hx
    have h0 := avail_ge (col := col) hs hP hcov cx (Y := Y) (cm := 2 * cmax) x
      (by rw [hsideX x hx]; exact hYB) (by rw [hsideX x hx]; exact hYc')
    change dx ends A x + din ends A x ≤ #(Y.filter fun w => H x w) + 2 * cmax + k +
      rdeg ends A col x + ccx ends A cx x at h0
    have := hccx x
    omega
  have hdegY : ∀ y ∈ Y, dx ends A y + din ends A y ≤ #(X.filter fun w => H w y) + 2 * cmax + k +
      rdeg ends A col y + l := by
    intro y hy
    have h0 := avail_ge (col := col) hs hP hcov cx (Y := X) (cm := 2 * cmax) y
      (by rw [hsideY y hy]; exact hXA) (by rw [hsideY y hy]; exact hXc')
    change dx ends A y + din ends A y ≤ #(X.filter fun w => H y w) + 2 * cmax + k +
      rdeg ends A col y + ccx ends A cx y at h0
    have := hccx y
    have heq : (X.filter fun w => H y w) = X.filter fun w => H w y :=
      filter_congr fun w _ => ⟨hHsymm y w, hHsymm w y⟩
    rw [heq] at h0
    omega
  have hXcard : #X ≤ n := hA ▸ card_le_card hXA
  -- Lemma 2.11 on the subtypes
  let α := {x // x ∈ X}
  let β := {y // y ∈ Y}
  have hα : Fintype.card α = #X := Fintype.card_coe X
  have hβ : Fintype.card β = #X := by rw [Fintype.card_coe, ← hXY]
  have hdx : ∀ x : α, 2 * τT ≤ #(univ.filter fun y : β => H x.1 y.1) := by
    intro x
    rw [card_filter_subtype Y (fun y => H x.1 y)]
    have := hdegX x.1 x.2
    by_cases hxT : x.1 ∈ T
    · have := HT3 x.1 hxT; have := hP.rdeg_eq_zero hxT; omega
    · have := HG3 x.1 hxT; have := hP.rdeg_le x.1; omega
  have hdy : ∀ y : β, 2 * τT ≤ #(univ.filter fun x : α => H x.1 y.1) := by
    intro y
    rw [card_filter_subtype X (fun x => H x y.1)]
    have := hdegY y.1 y.2
    by_cases hyT : y.1 ∈ T
    · have := HT3 y.1 hyT; have := hP.rdeg_eq_zero hyT; omega
    · have := HG3 y.1 hyT; have := hP.rdeg_le y.1; omega
  have hlow : #(univ.filter fun x : α => 2 * #(univ.filter fun y : β => H x.1 y.1) < #X) +
      #(univ.filter fun y : β => 2 * #(univ.filter fun x : α => H x.1 y.1) < #X) ≤ 2 * τT := by
    have h1 : #(univ.filter fun x : α => 2 * #(univ.filter fun y : β => H x.1 y.1) < #X) ≤ τT := by
      refine le_trans ?_ hTA
      rw [card_filter_subtype X (fun x => 2 * #(univ.filter fun y : β => H x y.1) < #X)]
      refine card_le_card fun x hx => ?_
      obtain ⟨hxX, hlt⟩ := mem_filter.1 hx
      refine mem_inter.2 ⟨?_, hXA hxX⟩
      by_contra hxT
      rw [card_filter_subtype Y (fun y => H x y)] at hlt
      have := hdegX x hxX; have := HG3 x hxT; have := hP.rdeg_le x; omega
    have h2 : #(univ.filter fun y : β => 2 * #(univ.filter fun x : α => H x.1 y.1) < #X) ≤ τT := by
      refine le_trans ?_ hTB
      rw [card_filter_subtype Y (fun y => 2 * #(univ.filter fun x : α => H x.1 y) < #X)]
      refine card_le_card fun y hy => ?_
      obtain ⟨hyY, hlt⟩ := mem_filter.1 hy
      refine mem_inter.2 ⟨?_, hYB hyY⟩
      by_contra hyT
      rw [card_filter_subtype X (fun x => H x y)] at hlt
      have := hdegY y hyY; have := HG3 y hyT; have := hP.rdeg_le y; omega
    omega
  obtain ⟨σ, hσinj, hσ⟩ := exists_perfect_matching_of_few_low (#X) (2 * τT) hα hβ
    (fun x y => H x.1 y.1) hdx hdy hlow
  have hσbij : Function.Bijective σ := by
    rw [Fintype.bijective_iff_injective_and_card]; exact ⟨hσinj, hα.trans hβ.symm⟩
  -- the matching edges
  let ex : α → E := fun x => (hσ x).choose
  have hex : ∀ x, ¬ Inner ends A (ex x) ∧ col (ex x) = none ∧ cx (ex x) = none ∧
      Incident ends (ex x) x.1 ∧ Incident ends (ex x) (σ x).1 := fun x => (hσ x).choose_spec
  have hxA : ∀ x : α, x.1 ∈ A := fun x => hXA x.2
  have hyB : ∀ y : β, y.1 ∉ A := fun y => mem_compl.1 (hYB y.2)
  have hxy : ∀ x : α, x.1 ≠ (σ x).1 := fun x h => hyB (σ x) (h ▸ hxA x)
  have hinc : ∀ x v, Incident ends (ex x) v ↔ v = x.1 ∨ v = (σ x).1 := fun x v =>
    incident_iff (hex x).2.2.2.1 (hex x).2.2.2.2 (hxy x) v
  have huniq : ∀ x x' v, Incident ends (ex x) v → Incident ends (ex x') v → x = x' := by
    intro x x' v h h'
    have h1 := (hinc x v).1 h
    have h2 := (hinc x' v).1 h'
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Subtype.ext (h1.symm.trans h2)
    · exact absurd (show (σ x').1 ∈ A by rw [← h2, h1]; exact hxA x) (hyB (σ x'))
    · exact absurd (show (σ x).1 ∈ A by rw [← h1, h2]; exact hxA x') (hyB (σ x))
    · exact hσinj (Subtype.ext (h1.symm.trans h2))
  set M := univ.image ex
  have hmemM : ∀ e, e ∈ M ↔ ∃ x, ex x = e := by intro e; simp [M]
  let cx' : E → Option (Fin l) := fun e => if e ∈ M then some j else cx e
  have hlcM : ∀ e ∈ M, lc ends A col c3 cx' e = some j := by
    intro e he
    obtain ⟨x, rfl⟩ := (hmemM e).1 he
    simp only [lc, cx', if_pos he]
    rw [if_neg (fun h => (hex x).1 h.1)]
  have hlcnM : ∀ e ∉ M, lc ends A col c3 cx' e = lc ends A col c3 cx e := by
    intro e he; simp only [lc, cx', if_neg he]
  have hlcM0 : ∀ e ∈ M, lc ends A col c3 cx e = none := by
    intro e he
    obtain ⟨x, rfl⟩ := (hmemM e).1 he
    simp only [lc]; rw [if_neg (fun h => (hex x).1 h.1)]; exact (hex x).2.2.1
  -- an `R`-edge of colour `j` or an old edge of colour `j` cannot meet `X ∪ Y`
  have hnoj : ∀ x : α, ∀ f v, Incident ends (ex x) v → Incident ends f v →
      lc ends A col c3 cx f ≠ some j := by
    intro x f v hev hfv hf
    unfold lc at hf
    by_cases hR : Inner ends A f ∧ col f = none
    · rw [if_pos hR] at hf
      have hfj : c3 f = j := Option.some_injective _ hf
      rcases (hinc x v).1 hev with rfl | rfl
      · have hfA : (ends f).1 ∈ A := (side_of_inner hR.1 (Or.inl rfl) hfv).2 (hxA x)
        have : x.1 ∈ AJ := mem_filter.2 ⟨hxA x, f, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hR⟩,
          hfA⟩, hfj, hfv⟩
        exact (mem_sdiff.1 x.2).2 (mem_union_left _ this)
      · have hfA : (ends f).1 ∈ Aᶜ := by
          rw [mem_compl]; intro h
          exact hyB (σ x) ((side_of_inner hR.1 (Or.inl rfl) hfv).1 h)
        have : (σ x).1 ∈ BJ := mem_filter.2 ⟨hYB (σ x).2, f, mem_filter.2
          ⟨mem_filter.2 ⟨mem_univ _, hR⟩, hfA⟩, hfj, hfv⟩
        exact (mem_sdiff.1 (σ x).2).2 (mem_union_left _ this)
    · rw [if_neg hR] at hf
      exact hj (hJ.j2 f j hf)
  refine ⟨cx', Function.update F j Fj, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- j1
    intro e he
    by_cases heM : e ∈ M
    · obtain ⟨x, rfl⟩ := (hmemM e).1 heM; exact ⟨(hex x).1, (hex x).2.1⟩
    · simp only [cx', if_neg heM] at he; exact hJ.j1 e he
  · -- j2
    intro e j' he
    by_cases heM : e ∈ M
    · simp only [cx', if_pos heM, Option.some_inj] at he; rw [← he]; exact mem_insert_self _ _
    · simp only [cx', if_neg heM] at he; exact mem_insert_of_mem (hJ.j2 e j' he)
  · -- j3
    intro e f hef v hev hfv hne heq
    by_cases heM : e ∈ M
    · rw [hlcM e heM] at heq
      by_cases hfM : f ∈ M
      · obtain ⟨x, rfl⟩ := (hmemM e).1 heM
        obtain ⟨x', rfl⟩ := (hmemM f).1 hfM
        exact hef (by rw [huniq x x' v hev hfv])
      · rw [hlcnM f hfM] at heq
        obtain ⟨x, rfl⟩ := (hmemM e).1 heM
        exact hnoj x f v hev hfv heq.symm
    · rw [hlcnM e heM] at heq hne
      by_cases hfM : f ∈ M
      · rw [hlcM f hfM] at heq
        obtain ⟨x, rfl⟩ := (hmemM f).1 hfM
        exact hnoj x e v hfv hev heq
      · rw [hlcnM f hfM] at heq
        exact hJ.j3 e f hef v hev hfv hne heq
  · -- j4
    intro j' hj' v hv
    by_cases hjj : j' = j
    · subst hjj
      rw [Function.update_self] at hv
      by_cases hvA : v ∈ A
      · by_cases hvAJ : v ∈ AJ
        · obtain ⟨e, heR, hej, hev⟩ := (mem_filter.1 hvAJ).2
          have hR := (mem_filter.1 (mem_filter.1 heR).1).2
          refine ⟨e, hev, ?_⟩
          simp only [lc, if_pos hR, hej]
        · have hvX : v ∈ X := mem_sdiff.2 ⟨hvA, by simp [hvAJ, hv]⟩
          exact ⟨ex ⟨v, hvX⟩, (hex _).2.2.2.1, hlcM _ (mem_image_of_mem _ (mem_univ _))⟩
      · by_cases hvBJ : v ∈ BJ
        · obtain ⟨e, heR, hej, hev⟩ := (mem_filter.1 hvBJ).2
          have hR := (mem_filter.1 (mem_filter.1 heR).1).2
          refine ⟨e, hev, ?_⟩
          simp only [lc, if_pos hR, hej]
        · have hvY : v ∈ Y := mem_sdiff.2 ⟨mem_compl.2 hvA, by simp [hvBJ, hv]⟩
          obtain ⟨x, hx⟩ := hσbij.2 ⟨v, hvY⟩
          refine ⟨ex x, ?_, hlcM _ (mem_image_of_mem _ (mem_univ _))⟩
          have := (hex x).2.2.2.2; rw [hx] at this; exact this
    · rw [Function.update_of_ne hjj] at hv
      obtain ⟨e, hev, he⟩ := hJ.j4 j' (by
        rcases mem_insert.1 hj' with h | h
        · exact absurd h hjj
        · exact h) v hv
      have heM : e ∉ M := fun h => by rw [hlcM0 e h] at he; exact absurd he (by simp)
      exact ⟨e, hev, by rw [hlcnM e heM]; exact he⟩
  · -- j5
    intro j'
    by_cases hjj : j' = j
    · subst hjj; rw [Function.update_self]; exact hFL
    · rw [Function.update_of_ne hjj]; exact hJ.j5 j'
  · -- j6
    intro v
    rw [card_insert_of_notMem hj]
    have h1 := hJ.j6 v
    have h2 : #(M.filter fun e => Incident ends e v) ≤ 1 := by
      refine card_le_one.2 fun e he f hf => ?_
      obtain ⟨heM, hev⟩ := mem_filter.1 he
      obtain ⟨hfM, hfv⟩ := mem_filter.1 hf
      obtain ⟨x, rfl⟩ := (hmemM e).1 heM
      obtain ⟨x', rfl⟩ := (hmemM f).1 hfM
      rw [huniq x x' v hev hfv]
    have h3 : (univ.filter fun e => ¬ Inner ends A e ∧ cx' e ≠ none ∧ Incident ends e v) ⊆
        (univ.filter fun e => ¬ Inner ends A e ∧ cx e ≠ none ∧ Incident ends e v) ∪
          M.filter fun e => Incident ends e v := by
      intro e he
      obtain ⟨hx, hc, hev⟩ := (mem_filter.1 he).2
      by_cases heM : e ∈ M
      · exact mem_union_right _ (mem_filter.2 ⟨heM, hev⟩)
      · simp only [cx', if_neg heM] at hc
        exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hx, hc, hev⟩)
    have := (card_le_card h3).trans (card_union_le _ _)
    unfold ccx at h1 ⊢
    omega

end PSLib.Eng
