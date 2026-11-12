/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Paths

/-!
# The composite moves of Step 2

* a transfer from a vertex `v` (used for special vertices and as the first half of a 7-path);
* a 5-path `a b₁ b₂ a₂ a₁ b` for `a ∈ A`, `b ∉ A` both missing `c` (transfer, transfer, close).

`Pre` collects the qualitative invariants (proper, uncoloured inner edges avoid `T`, `rdeg ≤ t`);
the moves preserve `Pre` and change the counts in a prescribed way.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → V × V} {A : Finset V} {k : ℕ}

variable (ends A) in
/-- Qualitative invariants of Step 2. -/
structure Pre (T : Finset V) (t : ℕ) (col : E → Option (Fin k)) : Prop where
  proper : Proper ends col
  good : ∀ e, Inner ends A e → col e = none → ∀ v, Incident ends e v → v ∉ T
  rdeg_le : ∀ v, rdeg ends A col v ≤ t

variable {T : Finset V} {t : ℕ} {col : E → Option (Fin k)} {c : Fin k}

theorem Pre.rdeg_eq_zero (h : Pre ends A T t col) {v : V} (hv : v ∈ T) :
    rdeg ends A col v = 0 := by
  unfold rdeg
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro e - ⟨hi, hc, hev⟩
  exact h.good e hi hc v hev hv

theorem fst_mem_of {f : E} {w u : V} (hw : Incident ends f w) (hu : Incident ends f u) (hwu : w ≠ u)
    {S : Finset V} (hwS : w ∈ S) (huS : u ∈ S) : (ends f).1 ∈ S := by
  rcases (incident_iff hw hu hwu (ends f).1).1 (Or.inl rfl) with h | h <;> rw [h] <;> assumption

theorem fst_not_mem_of {f : E} {w u : V} (hw : Incident ends f w) (hu : Incident ends f u)
    (hwu : w ≠ u) {S : Finset V} (hwS : w ∉ S) (huS : u ∉ S) : (ends f).1 ∉ S := by
  rcases (incident_iff hw hu hwu (ends f).1).1 (Or.inl rfl) with h | h <;> rw [h] <;> assumption

/-- The effect of a transfer from `v` to `u` through `w`. -/
theorem transfer_pre {e f : E} {v w u : V} (hP : Pre ends A T t col)
    (h : IsTransfer ends A col c e f v w u) (hwT : w ∉ T) (huT : u ∉ T)
    (hw : rdeg ends A col w < t) (hu : rdeg ends A col u < t) :
    Pre ends A T t (transfer col c e f) ∧
      (∀ d S, missed ends (transfer col c e f) d S + (if d = c ∧ v ∈ S then 1 else 0) =
        missed ends col d S + (if d = c ∧ u ∈ S then 1 else 0)) ∧
      (∀ d, xcnt ends A (transfer col c e f) d = xcnt ends A col d + if d = c then 1 else 0) ∧
      (∀ S : Finset V, (w ∈ S ↔ u ∈ S) →
        rsize ends A (transfer col c e f) S = rsize ends A col S + if w ∈ S then 1 else 0) ∧
      (∀ x, rdeg ends A (transfer col c e f) x =
        rdeg ends A col x + ((if x = w then 1 else 0) + if x = u then 1 else 0)) ∧
      (∀ d x, Covers ends (transfer col c e f) d x ↔
        (Covers ends col d x ∧ ¬ (d = c ∧ x = u)) ∨ (d = c ∧ x = v)) := by
  refine ⟨⟨h.proper hP.proper, ?_, ?_⟩, ?_, h.xcnt_eq, ?_, h.rdeg_eq, h.covers hP.proper⟩
  · intro g hgi hg x hx
    rcases (h.uncol_iff g).1 hg with ⟨hg', -⟩ | rfl
    · exact hP.good g hgi hg' x hx
    · rcases (incident_iff h.fb₁ h.fb₂ h.bb x).1 hx with rfl | rfl
      · exact hwT
      · exact huT
  · intro x
    rw [h.rdeg_eq]
    have := hP.rdeg_le x
    by_cases hxw : x = w
    · subst hxw; simp [h.bb]; omega
    · by_cases hxu : x = u
      · subst hxu; simp [hxw]; omega
      · simp [hxw, hxu]; omega
  · intro d S
    have := h.missed_eq hP.proper d S
    by_cases hd : d = c
    · subst hd; simpa using this
    · simpa [hd] using this
  · intro S hS
    rw [h.rsize_eq]
    congr 1
    by_cases hwS : w ∈ S
    · rw [if_pos (fst_mem_of h.fb₁ h.fb₂ h.bb hwS (hS.1 hwS)), if_pos hwS]
    · rw [if_neg (fst_not_mem_of h.fb₁ h.fb₂ h.bb hwS (fun h' => hwS (hS.2 h'))), if_neg hwS]

open Classical in
/-- A transfer from `v` exists as soon as `v` has a good uncoloured crossing neighbour. -/
theorem exists_transfer (_hP : Pre ends A T t col) {v : V} (hv : ¬ Covers ends col c v)
    (hN : 0 < #(NN ends A col c T t v)) :
    ∃ e f w u, IsTransfer ends A col c e f v w u ∧ w ∉ T ∧ u ∉ T ∧
      rdeg ends A col w < t ∧ rdeg ends A col u < t ∧ w ∈ side' A v := by
  obtain ⟨w, hw⟩ := card_pos.1 hN
  have hwUX := (mem_filter.1 hw).1
  obtain ⟨e, hex, hec, hev, hew, hvw⟩ := (mem_filter.1 hwUX).2
  obtain ⟨hwT, hwr, u, ⟨f, hfi, hfc, hfw, hfu, hwu⟩, huT, hur⟩ := (mem_filter.1 hw).2
  exact ⟨e, f, w, u, ⟨hev, hew, hvw, hex, hec, hfw, hfu, hwu, hfi, hfc, hv⟩, hwT, huT, hwr, hur,
    UX_sub v hwUX⟩

/-- The relations satisfied after a 5-path for the pair `a`, `b`. -/
def FiveRel (ends : E → V × V) (A : Finset V) (col col' : E → Option (Fin k)) (c : Fin k)
    (a b : V) : Prop :=
  (∀ d S, missed ends col' d S + (if d = c then (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0)
      else 0) = missed ends col d S) ∧
    (∀ d, xcnt ends A col' d = xcnt ends A col d + if d = c then 3 else 0) ∧
    rsize ends A col' A = rsize ends A col A + 1 ∧ rsize ends A col' Aᶜ = rsize ends A col Aᶜ + 1

open Classical in
/-- **Existence of a 5-path.** -/
theorem exists_five {n : ℕ} (hA : #A = n) (hB : #Aᶜ = n) (hP : Pre ends A T t col) {a b : V}
    (ha : a ∈ A) (hb : b ∉ A) (haT : a ∉ T) (hbT : b ∉ T) (hfa : ¬ Covers ends col c a)
    (hfb : ¬ Covers ends col c b) (hN : ∀ w, w ∉ T → n < 2 * #(NN ends A col c T t w)) :
    ∃ col', Pre ends A T t col' ∧ FiveRel ends A col col' c a b := by
  -- choose `a₁ ∈ NN b` and its partner `a₂`
  obtain ⟨a₁, ha₁⟩ := card_pos.1 (show 0 < #(NN ends A col c T t b) by have := hN b hbT; omega)
  have ha₁UX := (mem_filter.1 ha₁).1
  obtain ⟨e₃, hx₃, hc₃, he₃b, he₃a₁, hba₁⟩ := (mem_filter.1 ha₁UX).2
  obtain ⟨ha₁T, ha₁r, a₂, ⟨f₂, hf₂i, hf₂c, hf₂a₁, hf₂a₂, ha₁a₂⟩, ha₂T, ha₂r⟩ := (mem_filter.1 ha₁).2
  have ha₁A : a₁ ∈ A := by
    have := mem_side'.1 (UX_sub b ha₁UX); tauto
  have ha₂A : a₂ ∈ A := (side_of_inner hf₂i hf₂a₁ hf₂a₂).1 ha₁A
  -- choose `b₂ ∈ NN a₂ ∩ MM a`
  have h1 := hN a₂ ha₂T
  have h2 := hN a haT
  have h3 := card_NN_le_MM (A := A) (c := c) (T := T) (t := t) hP.proper a
  have hsub1 : NN ends A col c T t a₂ ⊆ Aᶜ := by
    intro w hw; have := mem_side'.1 (UX_sub a₂ (mem_filter.1 hw).1); rw [mem_compl]; tauto
  have hsub2 : MM ends A col c T t a ⊆ Aᶜ := by
    intro w hw; have := mem_side'.1 (MM_sub a hw); rw [mem_compl]; tauto
  obtain ⟨b₂, hb₂⟩ : (NN ends A col c T t a₂ ∩ MM ends A col c T t a).Nonempty := by
    rw [← card_pos]
    have := card_union_add_card_inter (NN ends A col c T t a₂) (MM ends A col c T t a)
    have := card_le_card (union_subset hsub1 hsub2)
    omega
  obtain ⟨hb₂N, hb₂M⟩ := mem_inter.1 hb₂
  have hb₂UX := (mem_filter.1 hb₂N).1
  obtain ⟨e₂, hx₂, hc₂, he₂a₂, he₂b₂, ha₂b₂⟩ := (mem_filter.1 hb₂UX).2
  obtain ⟨hb₂T, hb₂r, -⟩ := (mem_filter.1 hb₂N).2
  obtain ⟨b₁, hb₁N, f₁, hf₁i, hf₁c, hf₁b₁, hf₁b₂, hb₁b₂⟩ := (mem_filter.1 hb₂M).2
  have hb₁UX := (mem_filter.1 hb₁N).1
  obtain ⟨e₁, hx₁, hc₁, he₁a, he₁b₁, hab₁⟩ := (mem_filter.1 hb₁UX).2
  obtain ⟨hb₁T, hb₁r, -⟩ := (mem_filter.1 hb₁N).2
  have hb₂A : b₂ ∉ A := by rw [← mem_compl]; exact hsub2 hb₂M
  have hb₁A : b₁ ∉ A := fun h => hb₂A ((side_of_inner hf₁i hf₁b₁ hf₁b₂).1 h)
  -- coverage facts in `col`
  have hcb₁ : Covers ends col c b₁ := ⟨f₁, hf₁c, hf₁b₁⟩
  have hcb₂ : Covers ends col c b₂ := ⟨f₁, hf₁c, hf₁b₂⟩
  have hca₁ : Covers ends col c a₁ := ⟨f₂, hf₂c, hf₂a₁⟩
  have hca₂ : Covers ends col c a₂ := ⟨f₂, hf₂c, hf₂a₂⟩
  have hne_ab₂ : a ≠ b₂ := fun h => hb₂A (h ▸ ha)
  have hne_a₂a : a₂ ≠ a := fun h => hfa (h ▸ hca₂)
  have hne_a₁a : a₁ ≠ a := fun h => hfa (h ▸ hca₁)
  have hne_bb₂ : b ≠ b₂ := fun h => hfb (h ▸ hcb₂)
  have hne_bb₁ : b ≠ b₁ := fun h => hfb (h ▸ hcb₁)
  have hne_ba : b ≠ a := fun h => hb (h ▸ ha)
  -- first transfer
  have hT1 : IsTransfer ends A col c e₁ f₁ a b₁ b₂ :=
    ⟨he₁a, he₁b₁, hab₁, hx₁, hc₁, hf₁b₁, hf₁b₂, hb₁b₂, hf₁i, hf₁c, hfa⟩
  obtain ⟨hP1, hm1, hx1, hr1, hd1, hcov1⟩ := transfer_pre hP hT1 hb₁T hb₂T hb₁r hb₂r
  set col₁ := transfer col c e₁ f₁
  -- second transfer
  have he₂e₁ : e₂ ≠ e₁ := by
    rintro rfl
    rcases (incident_iff he₁a he₁b₁ hab₁ a₂).1 he₂a₂ with h | h
    · exact hne_a₂a h
    · exact hb₁A (h ▸ ha₂A)
  have hf₂e₁ : f₂ ≠ e₁ := by rintro rfl; exact hx₁ hf₂i
  have hf₂f₁ : f₂ ≠ f₁ := by
    rintro rfl
    rcases (incident_iff hf₂a₁ hf₂a₂ ha₁a₂ b₁).1 hf₁b₁ with h | h
    · exact hb₁A (h ▸ ha₁A)
    · exact hb₁A (h ▸ ha₂A)
  have hc₂' : col₁ e₂ = none := by
    rw [hT1.uncol_iff]; exact Or.inl ⟨hc₂, he₂e₁⟩
  have hf₂c' : col₁ f₂ = some c := by
    simp only [col₁, transfer]
    rw [Function.update_of_ne hf₂e₁, Function.update_of_ne hf₂f₁]; exact hf₂c
  have hfb₂' : ¬ Covers ends col₁ c b₂ := by
    rw [hcov1]; rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact h ⟨rfl, rfl⟩
    · exact hne_ab₂ h.symm
  have hT2 : IsTransfer ends A col₁ c e₂ f₂ b₂ a₂ a₁ :=
    ⟨he₂b₂, he₂a₂, fun h => ha₂b₂ h.symm, hx₂, hc₂', hf₂a₂, hf₂a₁, fun h => ha₁a₂ h.symm, hf₂i,
      hf₂c', hfb₂'⟩
  have hra₂ : rdeg ends A col₁ a₂ < t := by
    rw [hd1]; have : a₂ ≠ b₁ := fun h => hb₁A (h ▸ ha₂A)
    have : a₂ ≠ b₂ := fun h => hb₂A (h ▸ ha₂A)
    simp [*]
  have hra₁ : rdeg ends A col₁ a₁ < t := by
    rw [hd1]; have : a₁ ≠ b₁ := fun h => hb₁A (h ▸ ha₁A)
    have : a₁ ≠ b₂ := fun h => hb₂A (h ▸ ha₁A)
    simp [*]
  obtain ⟨hP2, hm2, hx2, hr2, -, hcov2⟩ := transfer_pre hP1 hT2 ha₂T ha₁T hra₂ hra₁
  set col₂ := transfer col₁ c e₂ f₂
  -- closing
  have he₃e₁ : e₃ ≠ e₁ := by
    rintro rfl
    rcases (incident_iff he₁a he₁b₁ hab₁ b).1 he₃b with h | h
    · exact hne_ba h
    · exact hne_bb₁ h
  have he₃e₂ : e₃ ≠ e₂ := by
    rintro rfl
    rcases (incident_iff he₂a₂ he₂b₂ ha₂b₂ b).1 he₃b with h | h
    · exact hb (h ▸ ha₂A)
    · exact hne_bb₂ h
  have he₃f₁ : e₃ ≠ f₁ := by rintro rfl; exact hx₃ hf₁i
  have he₃f₂ : e₃ ≠ f₂ := by rintro rfl; exact hx₃ hf₂i
  have hc₃' : col₂ e₃ = none := by
    rw [hT2.uncol_iff, hT1.uncol_iff]
    exact Or.inl ⟨Or.inl ⟨hc₃, he₃e₁⟩, he₃e₂⟩
  have hfa₁' : ¬ Covers ends col₂ c a₁ := by
    rw [hcov2]; rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact h ⟨rfl, rfl⟩
    · exact hb₂A (h ▸ ha₁A)
  have hfb' : ¬ Covers ends col₂ c b := by
    rw [hcov2, hcov1]
    rintro (⟨(⟨h, -⟩ | ⟨-, h⟩), -⟩ | ⟨-, h⟩)
    · exact hfb h
    · exact hne_ba h
    · exact hne_bb₂ h
  have hC : IsClose ends A col₂ c e₃ a₁ b :=
    ⟨he₃a₁, he₃b, fun h => hba₁ h.symm, hx₃, hc₃', hfa₁', hfb'⟩
  refine ⟨close col₂ c e₃, ⟨hC.proper hP2.proper, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro g hgi hg x hx
    exact hP2.good g hgi ((hC.uncol_iff g).1 hg).1 x hx
  · intro x; rw [hC.rdeg_eq]; exact hP2.rdeg_le x
  · intro d S
    have e1 := hm1 d S
    have e2 := hm2 d S
    have e3 := hC.missed_eq d S
    by_cases hd : d = c
    · subst hd
      simp only [true_and, if_true] at e1 e2 e3 ⊢
      split_ifs at e1 e2 e3 ⊢ <;> omega
    · simp only [hd, false_and, if_false, add_zero] at e1 e2 e3 ⊢
      omega
  · intro d
    rw [hC.xcnt_eq, hx2, hx1]
    split_ifs <;> omega
  · rw [hC.rsize_eq, hr2 A (by tauto), hr1 A (by tauto), if_pos ha₂A, if_neg hb₁A]
  · rw [hC.rsize_eq, hr2 Aᶜ (by simp only [mem_compl]; tauto),
      hr1 Aᶜ (by simp only [mem_compl]; tauto)]
    simp [ha₂A, hb₁A]

end PSLib.Eng
