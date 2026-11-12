/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Step2
public import ShannonColouring.Shannon
public import AOF.Classes

/-!
# Step 3, first half: colouring the uncoloured inner edges

`R` is the multigraph of uncoloured inner edges; it has maximum degree at most `t`. Shannon's
theorem colours it with `⌊3t/2⌋ ≤ l` colours, McDiarmid's equalization balances the classes on each
side, and when both sides have the same number of edges the classes of the second side are permuted
so that every colour has as many edges on both sides (`exists_R_colouring`).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → V × V} {A : Finset V} {k : ℕ}

variable (ends A) in
/-- The uncoloured inner edges. -/
def Rset (col : E → Option (Fin k)) : Finset E := univ.filter fun e => Inner ends A e ∧ col e = none

variable (ends A) in
/-- The uncoloured inner edges inside `S`. -/
def Rside (col : E → Option (Fin k)) (S : Finset V) : Finset E :=
  (Rset ends A col).filter fun e => (ends e).1 ∈ S

theorem card_Rside (col : E → Option (Fin k)) (S : Finset V) :
    #(Rside ends A col S) = rsize ends A col S := by
  unfold Rside Rset rsize
  rw [filter_filter]
  congr 1; ext e; simp [and_assoc]

/-- Equalized class sizes are at most the average plus one. -/
theorem le_div_add_one {l : ℕ} (hl : 0 < l) (f : Fin l → ℕ) (hf : ∀ a b, f a ≤ f b + 1) (N : ℕ)
    (hN : ∑ b, f b = N) (a : Fin l) : f a ≤ N / l + 1 := by
  have : l * (f a - 1) ≤ N := by
    rw [← hN]
    calc l * (f a - 1) = ∑ _b : Fin l, (f a - 1) := by simp
      _ ≤ ∑ b, f b := sum_le_sum fun b _ => by have := hf a b; omega
  have h2 : f a - 1 ≤ N / l := by
    rw [Nat.le_div_iff_mul_le hl]; rw [mul_comm]; exact this
  omega

theorem sum_cls (s : Finset E) {l : ℕ} (c : E → Fin l) : ∑ j, cls s c j = #s := by
  unfold cls
  rw [card_eq_sum_card_fiberwise (f := c) (t := univ) (fun _ _ => mem_univ _)]

variable {T : Finset V} {t : ℕ} {col : E → Option (Fin k)}

/-- Two inner edges sharing a vertex lie on the same side. -/
theorem same_side_of_share {e f : E} {v : V} (he : Inner ends A e) (hf : Inner ends A f)
    (hev : Incident ends e v) (hfv : Incident ends f v) :
    ((ends e).1 ∈ A ↔ (ends f).1 ∈ A) := by
  have h1 : ((ends e).1 ∈ A ↔ v ∈ A) := side_of_inner he (Or.inl rfl) hev
  have h2 : ((ends f).1 ∈ A ↔ v ∈ A) := side_of_inner hf (Or.inl rfl) hfv
  tauto

/-- **Colouring `R`.** -/
theorem exists_R_colouring (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hP : Pre ends A T t col)
    {l : ℕ} (hl : 3 * t / 2 ≤ l) (hl0 : 0 < l) :
    ∃ c3 : E → Fin l, ProperOn ends (Rset ends A col) c3 ∧
      (∀ j, cls (Rside ends A col A) c3 j ≤ rsize ends A col A / l + 1) ∧
      (∀ j, cls (Rside ends A col Aᶜ) c3 j ≤ rsize ends A col Aᶜ / l + 1) ∧
      (rsize ends A col A = rsize ends A col Aᶜ →
        ∀ j, cls (Rside ends A col A) c3 j = cls (Rside ends A col Aᶜ) c3 j) := by
  classical
  set R := Rset ends A col
  -- Shannon's theorem on the subtype of `R`
  let ι := {e // e ∈ R}
  let ends' : ι → V × V := fun i => ends i.1
  have hdeg : ∀ v, ShannonColouring.degree ends' v ≤ t := by
    intro v
    refine le_trans ?_ (hP.rdeg_le v)
    unfold ShannonColouring.degree rdeg
    rw [← card_map (Function.Embedding.subtype _)]
    refine card_le_card fun e he => ?_
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype] at he
    obtain ⟨i, hi, rfl⟩ := he
    have := (mem_filter.1 i.2).2
    exact mem_filter.2 ⟨mem_univ _, this.1, this.2, hi⟩
  obtain ⟨c', hc'⟩ := ShannonColouring.shannon ends' (fun i => hloop i.1) t hdeg
  let c0 : E → Fin l := fun e => if h : e ∈ R then Fin.castLE hl (c' ⟨e, h⟩) else ⟨0, hl0⟩
  have hc0 : ProperOn ends R c0 := by
    intro e he f hf hef hv
    simp only [c0, dif_pos he, dif_pos hf]
    intro heq
    exact hc' ⟨e, he⟩ ⟨f, hf⟩ (fun h => hef (congrArg Subtype.val h)) hv
      (Fin.castLE_injective hl heq)
  -- equalize each side
  set RA := Rside ends A col A
  set RB := Rside ends A col Aᶜ
  have hRA : RA ⊆ R := filter_subset _ _
  have hRB : RB ⊆ R := filter_subset _ _
  obtain ⟨cA, hcA, heA⟩ := exists_equalized hloop RA (energy RA c0) c0 rfl (hc0.mono hRA)
  obtain ⟨cB, hcB, heB⟩ := exists_equalized hloop RB (energy RB c0) c0 rfl (hc0.mono hRB)
  have hsumA := sum_cls RA cA
  have hsumB := sum_cls RB cB
  rw [card_Rside] at hsumA hsumB
  -- the permutation in the balanced case
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin l), rsize ends A col A = rsize ends A col Aᶜ →
      ∀ j, cls RB cB (π j) = cls RA cA j := by
    by_cases hbal : rsize ends A col A = rsize ends A col Aᶜ
    · obtain ⟨π, hπ⟩ := AOF.exists_perm_of_equitable (fun j => cls RA cA j) (fun j => cls RB cB j)
        heA heB (by rw [hsumA, hsumB, hbal])
      exact ⟨π, fun _ => hπ⟩
    · exact ⟨Equiv.refl _, fun h => absurd h hbal⟩
  let c3 : E → Fin l := fun e => if (ends e).1 ∈ A then cA e else π.symm (cB e)
  have hclsA : ∀ j, cls RA c3 j = cls RA cA j := by
    intro j; unfold cls; congr 1
    refine filter_congr fun e he => ?_
    have : (ends e).1 ∈ A := (mem_filter.1 he).2
    simp [c3, this]
  have hclsB : ∀ j, cls RB c3 j = cls RB cB (π j) := by
    intro j; unfold cls; congr 1
    refine filter_congr fun e he => ?_
    have : (ends e).1 ∉ A := by have := (mem_filter.1 he).2; rwa [mem_compl] at this
    simp only [c3, if_neg this]
    constructor
    · rintro rfl; simp
    · intro h; rw [h]; simp
  refine ⟨c3, ?_, fun j => ?_, fun j => ?_, fun hbal j => ?_⟩
  · intro e he f hf hef ⟨v, hev, hfv⟩
    have hei := (mem_filter.1 he).2.1
    have hfi := (mem_filter.1 hf).2.1
    have hside := same_side_of_share hei hfi hev hfv
    by_cases heA : (ends e).1 ∈ A
    · have hfA := hside.1 heA
      simp only [c3, if_pos heA, if_pos hfA]
      exact hcA e (mem_filter.2 ⟨he, heA⟩) f (mem_filter.2 ⟨hf, hfA⟩) hef ⟨v, hev, hfv⟩
    · have hfA : (ends f).1 ∉ A := fun h => heA (hside.2 h)
      simp only [c3, if_neg heA, if_neg hfA]
      intro h
      exact hcB e (mem_filter.2 ⟨he, mem_compl.2 heA⟩) f (mem_filter.2 ⟨hf, mem_compl.2 hfA⟩) hef
        ⟨v, hev, hfv⟩ (π.symm.injective h)
  · rw [hclsA]; exact le_div_add_one hl0 _ heA _ hsumA j
  · rw [hclsB]; exact le_div_add_one hl0 _ heB _ hsumB (π j)
  · rw [hclsA, hclsB, hπ hbal]

end PSLib.Eng
