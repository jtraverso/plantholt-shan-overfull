/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Equalize

/-!
# Partial edge colourings of a bipartitioned multigraph

The multigraph is an edge family `ends : E → V × V`; a set `A` of vertices splits the edges into
*inner* edges (both ends on the same side of `A`, `Aᶜ`) and *crossing* edges. A partial colouring
is `col : E → Option (Fin k)`. For a vertex `v`:

* `din v`, `dx v`: the numbers of inner and crossing edges at `v`;
* `rdeg col v`: the number of uncoloured inner edges at `v`;
* `ccol col v`: the number of coloured crossing edges at `v`;
* `miss col v`: the number of colours missing at `v`.

For a proper partial colouring, `miss + din + ccol = k + rdeg` (`miss_add_din_add_ccol`).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (ends : E → V × V) (A : Finset V) {k : ℕ}

/-- Both ends of `e` lie on the same side. -/
def Inner (e : E) : Prop := ((ends e).1 ∈ A ↔ (ends e).2 ∈ A)

instance (e : E) : Decidable (Inner ends A e) :=
  inferInstanceAs (Decidable (((ends e).1 ∈ A ↔ (ends e).2 ∈ A)))

/-- A proper partial colouring: two distinct coloured edges with the same colour share no end. -/
def Proper (col : E → Option (Fin k)) : Prop :=
  ∀ e f, e ≠ f → col e ≠ none → col e = col f → ∀ v, Incident ends e v → ¬ Incident ends f v

/-- The colour `c` is present at `v`. -/
def Covers (col : E → Option (Fin k)) (c : Fin k) (v : V) : Prop :=
  ∃ e, col e = some c ∧ Incident ends e v

instance (col : E → Option (Fin k)) (c : Fin k) (v : V) : Decidable (Covers ends col c v) :=
  inferInstanceAs (Decidable (∃ e, col e = some c ∧ Incident ends e v))

/-- The number of colours missing at `v`. -/
def miss (col : E → Option (Fin k)) (v : V) : ℕ :=
  #(univ.filter fun c => ¬ Covers ends col c v)

/-- The number of inner edges at `v`. -/
def din (v : V) : ℕ := #(univ.filter fun e => Inner ends A e ∧ Incident ends e v)

/-- The number of crossing edges at `v`. -/
def dx (v : V) : ℕ := #(univ.filter fun e => ¬ Inner ends A e ∧ Incident ends e v)

/-- The number of uncoloured inner edges at `v`. -/
def rdeg (col : E → Option (Fin k)) (v : V) : ℕ :=
  #(univ.filter fun e => Inner ends A e ∧ col e = none ∧ Incident ends e v)

/-- The number of coloured crossing edges at `v`. -/
def ccol (col : E → Option (Fin k)) (v : V) : ℕ :=
  #(univ.filter fun e => ¬ Inner ends A e ∧ col e ≠ none ∧ Incident ends e v)

variable {ends A}

theorem Proper.eq_of_incident {col : E → Option (Fin k)} (h : Proper ends col) {e f : E} {c : Fin k}
    {v : V} (he : col e = some c) (hf : col f = some c) (hev : Incident ends e v)
    (hfv : Incident ends f v) : e = f := by
  by_contra hne
  exact h e f hne (by simp [he]) (he.trans hf.symm) v hev hfv

/-- The number of coloured edges at `v` equals the number of colours present at `v`. -/
theorem card_coloured_eq {col : E → Option (Fin k)} (h : Proper ends col) (v : V) :
    #(univ.filter fun e => col e ≠ none ∧ Incident ends e v) =
      #(univ.filter fun c => Covers ends col c v) := by
  classical
  set C := univ.filter fun e => col e ≠ none ∧ Incident ends e v
  have hinj : Set.InjOn col C := by
    intro e he f hf hef
    simp only [C, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at he hf
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 he.1
    exact h.eq_of_incident hc (hef ▸ hc) he.2 hf.2
  have himg : C.image col = (univ.filter fun c => Covers ends col c v).map
      ⟨some, Option.some_injective _⟩ := by
    ext x
    rw [mem_image, mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      simp only [C, mem_filter, mem_univ, true_and] at he
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 he.1
      exact ⟨c, mem_filter.2 ⟨mem_univ _, e, hc, he.2⟩, hc.symm⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨e, hce, hev⟩ := (mem_filter.1 hc).2
      exact ⟨e, mem_filter.2 ⟨mem_univ _, by simp [hce], hev⟩, hce⟩
  rw [← card_image_of_injOn hinj, himg, card_map]

/-- **The basic identity.** -/
theorem miss_add_din_add_ccol {col : E → Option (Fin k)} (h : Proper ends col) (v : V) :
    miss ends col v + din ends A v + ccol ends A col v = k + rdeg ends A col v := by
  classical
  have h1 := card_coloured_eq h v
  have h2 : #(univ.filter fun c => Covers ends col c v) + miss ends col v = k := by
    unfold miss
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  have h3 : #(univ.filter fun e => col e ≠ none ∧ Incident ends e v) =
      (#(univ.filter fun e => Inner ends A e ∧ Incident ends e v) -
        rdeg ends A col v) + ccol ends A col v := by
    have hsplit : (univ.filter fun e => col e ≠ none ∧ Incident ends e v) =
        (univ.filter fun e => Inner ends A e ∧ col e ≠ none ∧ Incident ends e v) ∪
          (univ.filter fun e => ¬ Inner ends A e ∧ col e ≠ none ∧ Incident ends e v) := by
      ext e; simp only [mem_filter, mem_univ, true_and, mem_union]; tauto
    have hdisj : Disjoint (univ.filter fun e => Inner ends A e ∧ col e ≠ none ∧ Incident ends e v)
        (univ.filter fun e => ¬ Inner ends A e ∧ col e ≠ none ∧ Incident ends e v) := by
      rw [disjoint_filter]; intro e _ h1 h2; exact h2.1 h1.1
    have hin : #(univ.filter fun e => Inner ends A e ∧ col e ≠ none ∧ Incident ends e v) +
        rdeg ends A col v = #(univ.filter fun e => Inner ends A e ∧ Incident ends e v) := by
      unfold rdeg
      rw [← card_union_of_disjoint]
      · congr 1; ext e; simp only [mem_filter, mem_univ, true_and, mem_union]
        by_cases hc : col e = none <;> simp [hc]
      · rw [disjoint_filter]; intro e _ h1 h2; exact h1.2.1 h2.2.1
    rw [hsplit, card_union_of_disjoint hdisj]
    unfold ccol
    omega
  have hle : rdeg ends A col v ≤ din ends A v := by
    unfold rdeg din
    exact card_le_card fun e he => by
      simp only [mem_filter, mem_univ, true_and] at he ⊢; exact ⟨he.1, he.2.2⟩
  unfold din at hle ⊢
  omega

end PSLib.Eng
