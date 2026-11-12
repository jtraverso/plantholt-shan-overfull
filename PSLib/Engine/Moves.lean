/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Defs

/-!
# Elementary moves on partial colourings

Two elementary moves: uncolouring an edge `f` (`update col f none`) and colouring an uncoloured
edge `e` with a colour `c` missing at both its ends (`update col e (some c)`). We record how
`Covers`, `rdeg`, `ccol`, the crossing-edge counts `xcnt` and the inner-edge counts `rsize` change.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → V × V} {A : Finset V} {k : ℕ}

variable (ends A) in
/-- The number of coloured crossing edges of colour `c`. -/
def xcnt (col : E → Option (Fin k)) (c : Fin k) : ℕ :=
  #(univ.filter fun e => ¬ Inner ends A e ∧ col e = some c)

variable (ends A) in
/-- The number of uncoloured inner edges with first end in `S` (for `S = A` or `Aᶜ`: the size of
`R_A` or `R_B`). -/
def rsize (col : E → Option (Fin k)) (S : Finset V) : ℕ :=
  #(univ.filter fun e => Inner ends A e ∧ col e = none ∧ (ends e).1 ∈ S)

variable (ends) in
/-- The number of vertices of `S` missed by the colour `c`. -/
def missed (col : E → Option (Fin k)) (c : Fin k) (S : Finset V) : ℕ :=
  #(S.filter fun v => ¬ Covers ends col c v)

section Uncolour

variable {col : E → Option (Fin k)} {f : E} {c : Fin k}

theorem proper_uncolour (h : Proper ends col) (f : E) :
    Proper ends (Function.update col f none) := by
  intro e g hne he heg v hev hgv
  by_cases hef : e = f
  · subst hef; simp at he
  by_cases hgf : g = f
  · subst hgf
    rw [Function.update_of_ne hef] at he heg
    simp only [Function.update_self] at heg
    exact he heg
  rw [Function.update_of_ne hef] at he heg
  rw [Function.update_of_ne hgf] at heg
  exact h e g hne he heg v hev hgv

theorem covers_uncolour (h : Proper ends col) (hf : col f = some c) (d : Fin k) (v : V) :
    Covers ends (Function.update col f none) d v ↔
      Covers ends col d v ∧ ¬ (d = c ∧ Incident ends f v) := by
  constructor
  · rintro ⟨e, he, hev⟩
    have hef : e ≠ f := by rintro rfl; simp at he
    rw [Function.update_of_ne hef] at he
    refine ⟨⟨e, he, hev⟩, ?_⟩
    rintro ⟨rfl, hfv⟩
    exact hef (h.eq_of_incident he hf hev hfv)
  · rintro ⟨⟨e, he, hev⟩, hn⟩
    have hef : e ≠ f := by
      rintro rfl
      rw [hf] at he
      exact hn ⟨(Option.some_injective _ he).symm, hev⟩
    exact ⟨e, by rw [Function.update_of_ne hef]; exact he, hev⟩

theorem rdeg_uncolour (hf : col f = some c) (hfi : Inner ends A f) (v : V) :
    rdeg ends A (Function.update col f none) v =
      rdeg ends A col v + if Incident ends f v then 1 else 0 := by
  unfold rdeg
  split_ifs with hv
  · rw [← card_insert_of_notMem
      (s := univ.filter fun e => Inner ends A e ∧ col e = none ∧ Incident ends e v)
      (a := f) (by simp [hf])]
    congr 1; ext e
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hef : e = f
    · subst hef; simp [hfi, hv]
    · rw [Function.update_of_ne hef]; simp [hef]
  · congr 1; ext e
    simp only [mem_filter, mem_univ, true_and]
    by_cases hef : e = f
    · subst hef; simp [hf, hv]
    · rw [Function.update_of_ne hef]

theorem ccol_uncolour (hfi : Inner ends A f) (v : V) :
    ccol ends A (Function.update col f none) v = ccol ends A col v := by
  unfold ccol
  congr 1; ext e
  simp only [mem_filter, mem_univ, true_and]
  by_cases hef : e = f
  · subst hef; simp [hfi]
  · rw [Function.update_of_ne hef]

theorem xcnt_uncolour (hfi : Inner ends A f) (d : Fin k) :
    xcnt ends A (Function.update col f none) d = xcnt ends A col d := by
  unfold xcnt
  congr 1; ext e
  simp only [mem_filter, mem_univ, true_and]
  by_cases hef : e = f
  · subst hef; simp [hfi]
  · rw [Function.update_of_ne hef]

theorem rsize_uncolour (hf : col f = some c) (hfi : Inner ends A f) (S : Finset V) :
    rsize ends A (Function.update col f none) S =
      rsize ends A col S + if (ends f).1 ∈ S then 1 else 0 := by
  unfold rsize
  split_ifs with hv
  · rw [← card_insert_of_notMem
      (s := univ.filter fun e => Inner ends A e ∧ col e = none ∧ (ends e).1 ∈ S)
      (a := f) (by simp [hf])]
    congr 1; ext e
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hef : e = f
    · subst hef; simp [hfi, hv]
    · rw [Function.update_of_ne hef]; simp [hef]
  · congr 1; ext e
    simp only [mem_filter, mem_univ, true_and]
    by_cases hef : e = f
    · subst hef; simp [hf, hv]
    · rw [Function.update_of_ne hef]

end Uncolour

section Colour

variable {col : E → Option (Fin k)} {e : E} {c : Fin k}

theorem proper_colour (h : Proper ends col)
    (hfree : ∀ v, Incident ends e v → ¬ Covers ends col c v) :
    Proper ends (Function.update col e (some c)) := by
  intro e1 e2 hne h1 h12 v hv1 hv2
  by_cases he1 : e1 = e
  · subst he1
    have he2 : e2 ≠ e1 := fun h => hne h.symm
    rw [Function.update_self, Function.update_of_ne he2] at h12
    exact hfree v hv1 ⟨e2, h12.symm, hv2⟩
  by_cases he2 : e2 = e
  · subst he2
    rw [Function.update_self, Function.update_of_ne he1] at h12
    exact hfree v hv2 ⟨e1, h12, hv1⟩
  rw [Function.update_of_ne he1, Function.update_of_ne he2] at h12
  rw [Function.update_of_ne he1] at h1
  exact h e1 e2 hne h1 h12 v hv1 hv2

theorem covers_colour (he : col e = none) (d : Fin k) (v : V) :
    Covers ends (Function.update col e (some c)) d v ↔
      Covers ends col d v ∨ (d = c ∧ Incident ends e v) := by
  constructor
  · rintro ⟨g, hg, hgv⟩
    by_cases hge : g = e
    · subst hge
      rw [Function.update_self] at hg
      exact Or.inr ⟨(Option.some_injective _ hg).symm, hgv⟩
    · rw [Function.update_of_ne hge] at hg
      exact Or.inl ⟨g, hg, hgv⟩
  · rintro (⟨g, hg, hgv⟩ | ⟨rfl, hev⟩)
    · have hge : g ≠ e := by rintro rfl; rw [he] at hg; simp at hg
      exact ⟨g, by rw [Function.update_of_ne hge]; exact hg, hgv⟩
    · exact ⟨e, Function.update_self .., hev⟩

theorem rdeg_colour (hex : ¬ Inner ends A e) (v : V) :
    rdeg ends A (Function.update col e (some c)) v = rdeg ends A col v := by
  unfold rdeg
  congr 1; ext g
  simp only [mem_filter, mem_univ, true_and]
  by_cases hge : g = e
  · subst hge; simp [hex]
  · rw [Function.update_of_ne hge]

theorem ccol_colour (he : col e = none) (hex : ¬ Inner ends A e) (v : V) :
    ccol ends A (Function.update col e (some c)) v =
      ccol ends A col v + if Incident ends e v then 1 else 0 := by
  unfold ccol
  split_ifs with hv
  · rw [← card_insert_of_notMem
      (s := univ.filter fun g => ¬ Inner ends A g ∧ col g ≠ none ∧ Incident ends g v)
      (a := e) (by simp [he])]
    congr 1; ext g
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hge : g = e
    · subst hge; simp [hex, hv]
    · rw [Function.update_of_ne hge]; simp [hge]
  · congr 1; ext g
    simp only [mem_filter, mem_univ, true_and]
    by_cases hge : g = e
    · subst hge; simp [hv]
    · rw [Function.update_of_ne hge]

theorem xcnt_colour (he : col e = none) (hex : ¬ Inner ends A e) (d : Fin k) :
    xcnt ends A (Function.update col e (some c)) d =
      xcnt ends A col d + if d = c then 1 else 0 := by
  unfold xcnt
  split_ifs with hd
  · subst hd
    rw [← card_insert_of_notMem (s := univ.filter fun g => ¬ Inner ends A g ∧ col g = some d)
      (a := e) (by simp [he])]
    congr 1; ext g
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hge : g = e
    · subst hge; simp [hex]
    · rw [Function.update_of_ne hge]; simp [hge]
  · congr 1; ext g
    simp only [mem_filter, mem_univ, true_and]
    by_cases hge : g = e
    · subst hge; simp [he, Ne.symm hd]
    · rw [Function.update_of_ne hge]

theorem rsize_colour (hex : ¬ Inner ends A e) (S : Finset V) :
    rsize ends A (Function.update col e (some c)) S = rsize ends A col S := by
  unfold rsize
  congr 1; ext g
  simp only [mem_filter, mem_univ, true_and]
  by_cases hge : g = e
  · subst hge; simp [hex]
  · rw [Function.update_of_ne hge]

end Colour

end PSLib.Eng
