/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Moves

/-!
# Transfers and closings

* `close col c e`: an uncoloured crossing edge `e = ab` whose ends both miss `c` gets colour `c`.
* `transfer col c e f`: `a` misses `c`, `e = ab₁` is an uncoloured crossing edge and `f = b₁b₂` an
  inner edge of colour `c`; then `e` gets colour `c` and `f` is uncoloured. Afterwards `a` sees `c`
  and `b₂` misses it.

We give the complete effect of both moves on the counting functions.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → V × V} {A : Finset V} {k : ℕ}

theorem incident_iff {e : E} {a b : V} (ha : Incident ends e a) (hb : Incident ends e b)
    (hab : a ≠ b) (v : V) : Incident ends e v ↔ v = a ∨ v = b := by
  unfold Incident at *
  constructor
  · rintro (h | h) <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      first | exact Or.inl (h.symm.trans ha) | exact Or.inr (h.symm.trans hb) |
        exact absurd (ha.symm.trans hb) hab
  · rintro (rfl | rfl)
    · exact ha
    · exact hb

theorem card_filter_incident {e : E} {a b : V} (ha : Incident ends e a) (hb : Incident ends e b)
    (hab : a ≠ b) (S : Finset V) :
    #(S.filter fun v => Incident ends e v) = (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) := by
  have : S.filter (fun v => Incident ends e v) = S.filter (fun v => v = a ∨ v = b) := by
    ext v; simp only [mem_filter, incident_iff ha hb hab]
  rw [this, filter_or, card_union_of_disjoint]
  · rw [filter_eq', filter_eq']
    split_ifs <;> simp
  · rw [disjoint_filter]; rintro v _ rfl rfl; exact hab rfl

section Missed

variable {col : E → Option (Fin k)}

theorem missed_uncolour (h : Proper ends col) {f : E} {c : Fin k} (hf : col f = some c) (d : Fin k)
    (S : Finset V) :
    missed ends (Function.update col f none) d S =
      missed ends col d S + if d = c then #(S.filter fun v => Incident ends f v) else 0 := by
  unfold missed
  split_ifs with hd
  · subst hd
    rw [← card_union_of_disjoint]
    · congr 1; ext v
      simp only [mem_filter, mem_union, covers_uncolour h hf, not_and, not_not, true_and]
      constructor
      · rintro ⟨hv, h1⟩
        by_cases hc : Covers ends col d v
        · exact Or.inr ⟨hv, h1 hc⟩
        · exact Or.inl ⟨hv, hc⟩
      · rintro (⟨hv, hc⟩ | ⟨hv, hi⟩)
        · exact ⟨hv, fun h' => absurd h' hc⟩
        · exact ⟨hv, fun _ => hi⟩
    · rw [disjoint_filter]; intro v _ hc hi; exact hc ⟨f, hf, hi⟩
  · simp only [add_zero]
    congr 1; ext v
    simp only [mem_filter, covers_uncolour h hf, hd, false_and, not_false_eq_true, and_true]

theorem missed_colour {e : E} {c : Fin k} (he : col e = none)
    (hfree : ∀ v, Incident ends e v → ¬ Covers ends col c v) (d : Fin k) (S : Finset V) :
    missed ends (Function.update col e (some c)) d S +
      (if d = c then #(S.filter fun v => Incident ends e v) else 0) = missed ends col d S := by
  unfold missed
  split_ifs with hd
  · subst hd
    rw [← card_union_of_disjoint]
    · congr 1; ext v
      rw [mem_union, mem_filter, mem_filter, mem_filter, covers_colour he]
      constructor
      · rintro (⟨hv, hc⟩ | ⟨hv, hi⟩)
        · exact ⟨hv, fun h' => hc (Or.inl h')⟩
        · exact ⟨hv, hfree v hi⟩
      · rintro ⟨hv, hc⟩
        by_cases hi : Incident ends e v
        · exact Or.inr ⟨hv, hi⟩
        · exact Or.inl ⟨hv, fun h' => h'.elim hc (fun h'' => hi h''.2)⟩
    · rw [disjoint_filter]; intro v _ h1 hi; exact h1 ((covers_colour he _ _).2 (Or.inr ⟨rfl, hi⟩))
  · simp only [add_zero]
    congr 1; ext v
    simp only [mem_filter, covers_colour he, hd, false_and, or_false]

end Missed

/-- Colour the crossing edge `e` with `c`. -/
def close (col : E → Option (Fin k)) (c : Fin k) (e : E) : E → Option (Fin k) :=
  Function.update col e (some c)

/-- Colour `e` with `c` and uncolour `f`. -/
def transfer (col : E → Option (Fin k)) (c : Fin k) (e f : E) : E → Option (Fin k) :=
  Function.update (Function.update col f none) e (some c)

/-- The data of a transfer from `a` along `e = ab₁` and `f = b₁b₂` for the colour `c`. -/
structure IsTransfer (ends : E → V × V) (A : Finset V) (col : E → Option (Fin k)) (c : Fin k)
    (e f : E) (a b₁ b₂ : V) : Prop where
  ea : Incident ends e a
  eb : Incident ends e b₁
  ab : a ≠ b₁
  ex : ¬ Inner ends A e
  ecol : col e = none
  fb₁ : Incident ends f b₁
  fb₂ : Incident ends f b₂
  bb : b₁ ≠ b₂
  fi : Inner ends A f
  fcol : col f = some c
  amiss : ¬ Covers ends col c a

/-- The data of a closing along `e = ab` for the colour `c`. -/
structure IsClose (ends : E → V × V) (A : Finset V) (col : E → Option (Fin k)) (c : Fin k)
    (e : E) (a b : V) : Prop where
  ea : Incident ends e a
  eb : Incident ends e b
  ab : a ≠ b
  ex : ¬ Inner ends A e
  ecol : col e = none
  amiss : ¬ Covers ends col c a
  bmiss : ¬ Covers ends col c b

namespace IsClose

variable {col : E → Option (Fin k)} {c : Fin k} {e : E} {a b : V}
  (h : IsClose ends A col c e a b)
include h

theorem free : ∀ v, Incident ends e v → ¬ Covers ends col c v := by
  intro v hv
  rcases (incident_iff h.ea h.eb h.ab v).1 hv with rfl | rfl
  · exact h.amiss
  · exact h.bmiss

theorem proper (hp : Proper ends col) : Proper ends (close col c e) := proper_colour hp h.free

theorem covers (d : Fin k) (v : V) :
    Covers ends (close col c e) d v ↔ Covers ends col d v ∨ (d = c ∧ (v = a ∨ v = b)) := by
  rw [close, covers_colour h.ecol, incident_iff h.ea h.eb h.ab]

theorem rdeg_eq (v : V) : rdeg ends A (close col c e) v = rdeg ends A col v := rdeg_colour h.ex v

theorem ccol_eq (v : V) : ccol ends A (close col c e) v =
    ccol ends A col v + ((if v = a then 1 else 0) + if v = b then 1 else 0) := by
  rw [close, ccol_colour h.ecol h.ex]
  congr 1
  by_cases hva : v = a
  · subst hva; simp [h.ea, h.ab]
  · by_cases hvb : v = b
    · subst hvb; simp [h.eb, hva]
    · simp [incident_iff h.ea h.eb h.ab, hva, hvb]

theorem xcnt_eq (d : Fin k) : xcnt ends A (close col c e) d =
    xcnt ends A col d + if d = c then 1 else 0 := xcnt_colour h.ecol h.ex d

theorem rsize_eq (S : Finset V) : rsize ends A (close col c e) S = rsize ends A col S :=
  rsize_colour h.ex S

theorem missed_eq (d : Fin k) (S : Finset V) :
    missed ends (close col c e) d S +
      (if d = c then (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) else 0) =
      missed ends col d S := by
  rw [← card_filter_incident h.ea h.eb h.ab]
  exact missed_colour h.ecol h.free d S

theorem uncol_iff (g : E) : close col c e g = none ↔ col g = none ∧ g ≠ e := by
  unfold close
  by_cases hg : g = e
  · subst hg; simp
  · rw [Function.update_of_ne hg]; simp [hg]

end IsClose

namespace IsTransfer

variable {col : E → Option (Fin k)} {c : Fin k} {e f : E} {a b₁ b₂ : V}
  (h : IsTransfer ends A col c e f a b₁ b₂)
include h

theorem ne : e ≠ f := by
  rintro rfl; exact h.ex h.fi

theorem a_ne_b₂ : a ≠ b₂ := by
  rintro rfl; exact h.amiss ⟨f, h.fcol, h.fb₂⟩

/-- After uncolouring `f`, the edge `e` can be coloured. -/
theorem free (hp : Proper ends col) :
    ∀ v, Incident ends e v → ¬ Covers ends (Function.update col f none) c v := by
  intro v hv
  rw [covers_uncolour hp h.fcol]
  rcases (incident_iff h.ea h.eb h.ab v).1 hv with rfl | rfl
  · exact fun hc => h.amiss hc.1
  · exact fun hc => hc.2 ⟨rfl, h.fb₁⟩

theorem ecol' : Function.update col f none e = none := by
  rw [Function.update_of_ne h.ne]; exact h.ecol

theorem proper (hp : Proper ends col) : Proper ends (transfer col c e f) :=
  proper_colour (proper_uncolour hp f) (h.free hp)

theorem covers (hp : Proper ends col) (d : Fin k) (v : V) :
    Covers ends (transfer col c e f) d v ↔
      (Covers ends col d v ∧ ¬ (d = c ∧ v = b₂)) ∨ (d = c ∧ v = a) := by
  rw [transfer, covers_colour h.ecol', covers_uncolour hp h.fcol,
    incident_iff h.ea h.eb h.ab, incident_iff h.fb₁ h.fb₂ h.bb]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨rfl, rfl | rfl⟩)
    · exact Or.inl ⟨h1, fun ⟨h3, h4⟩ => h2 ⟨h3, Or.inr h4⟩⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨⟨f, h.fcol, h.fb₁⟩, fun ⟨_, h4⟩ => h.bb h4⟩
  · rintro (⟨h1, h2⟩ | ⟨rfl, rfl⟩)
    · by_cases hd : d = c ∧ v = b₁
      · obtain ⟨rfl, rfl⟩ := hd; exact Or.inr ⟨rfl, Or.inr rfl⟩
      · refine Or.inl ⟨h1, ?_⟩
        rintro ⟨rfl, rfl | rfl⟩
        · exact hd ⟨rfl, rfl⟩
        · exact h2 ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, Or.inl rfl⟩

theorem rdeg_eq (v : V) : rdeg ends A (transfer col c e f) v =
    rdeg ends A col v + ((if v = b₁ then 1 else 0) + if v = b₂ then 1 else 0) := by
  rw [transfer, rdeg_colour h.ex, rdeg_uncolour h.fcol h.fi]
  congr 1
  by_cases hv1 : v = b₁
  · subst hv1; simp [h.fb₁, h.bb]
  · by_cases hv2 : v = b₂
    · subst hv2; simp [h.fb₂, hv1]
    · simp [incident_iff h.fb₁ h.fb₂ h.bb, hv1, hv2]

theorem ccol_eq (v : V) : ccol ends A (transfer col c e f) v =
    ccol ends A col v + ((if v = a then 1 else 0) + if v = b₁ then 1 else 0) := by
  rw [transfer, ccol_colour h.ecol' h.ex, ccol_uncolour h.fi]
  congr 1
  by_cases hva : v = a
  · subst hva; simp [h.ea, h.ab]
  · by_cases hvb : v = b₁
    · subst hvb; simp [h.eb, hva]
    · simp [incident_iff h.ea h.eb h.ab, hva, hvb]

theorem xcnt_eq (d : Fin k) : xcnt ends A (transfer col c e f) d =
    xcnt ends A col d + if d = c then 1 else 0 := by
  rw [transfer, xcnt_colour h.ecol' h.ex, xcnt_uncolour h.fi]

theorem rsize_eq (S : Finset V) : rsize ends A (transfer col c e f) S =
    rsize ends A col S + if (ends f).1 ∈ S then 1 else 0 := by
  rw [transfer, rsize_colour h.ex, rsize_uncolour h.fcol h.fi]

theorem missed_eq (hp : Proper ends col) (d : Fin k) (S : Finset V) :
    missed ends (transfer col c e f) d S + (if d = c then (if a ∈ S then 1 else 0) else 0) =
      missed ends col d S + (if d = c then (if b₂ ∈ S then 1 else 0) else 0) := by
  have h1 := missed_colour (S := S) (d := d) h.ecol' (h.free hp)
  have h2 := missed_uncolour hp h.fcol d S
  rw [card_filter_incident h.ea h.eb h.ab] at h1
  rw [card_filter_incident h.fb₁ h.fb₂ h.bb] at h2
  rw [transfer]
  have hb₁ : missed ends (Function.update col f none) d S = missed ends col d S +
      (if d = c then (if b₁ ∈ S then 1 else 0) + (if b₂ ∈ S then 1 else 0) else 0) := h2
  split_ifs at h1 hb₁ ⊢ <;> simp_all

theorem uncol_iff (g : E) : transfer col c e f g = none ↔ (col g = none ∧ g ≠ e) ∨ g = f := by
  unfold transfer
  by_cases hge : g = e
  · subst hge; simp [h.ne]
  · rw [Function.update_of_ne hge]
    by_cases hgf : g = f
    · subst hgf; simp
    · rw [Function.update_of_ne hgf]; simp [hge, hgf]

end IsTransfer

end PSLib.Eng
