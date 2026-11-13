/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Hakimi
public import ShannonColouring.Shannon
public import PSLib.Equalize

/-!
# Grouping the deficiencies (Case 2 of Theorem 1.2)

For `d : V → ℕ` with even sum and `2 d(v) ≤ ∑ d`, Hakimi's theorem gives a loopless multigraph `H`
with degrees `d`; Shannon's theorem splits its edges into `⌊3g/2⌋` matchings (`g ≥ max d`), and
cutting every matching by the rank of its first ends into pieces of at most `s₀` edges gives a list
of even vertex sets of size at most `2 s₀`, containing every vertex `v` exactly `d(v)` times
(`exists_groups`).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The copies of the edges of a multigraph `m` with multiplicities below `B`, oriented by a rank. -/
def mEdges (rk : V → ℕ) (m : V → V → ℕ) (B : ℕ) : Type _ :=
  {x : V × V × Fin B // rk x.1 < rk x.2.1 ∧ x.2.2.val < m x.1 x.2.1}

noncomputable instance (rk : V → ℕ) (m : V → V → ℕ) (B : ℕ) : Fintype (mEdges rk m B) :=
  Subtype.fintype _

noncomputable instance (rk : V → ℕ) (m : V → V → ℕ) (B : ℕ) : DecidableEq (mEdges rk m B) :=
  Classical.decEq _

/-- The ends of an edge copy. -/
def mEnds (rk : V → ℕ) (m : V → V → ℕ) (B : ℕ) (x : mEdges rk m B) : V × V := (x.1.1, x.1.2.1)

/-- The copies between `v` and `u` (with `rk v < rk u`) correspond to the indices below `m v u`. -/
theorem card_copies {rk : V → ℕ} {m : V → V → ℕ} {B : ℕ} (hB : ∀ u v, m u v ≤ B) {v u : V}
    (h : rk v < rk u) :
    #(univ.filter fun x : mEdges rk m B => x.1.1 = v ∧ x.1.2.1 = u) = m v u := by
  have : #(univ.filter fun x : mEdges rk m B => x.1.1 = v ∧ x.1.2.1 = u) =
      #(univ.filter fun i : Fin B => i.val < m v u) := by
    refine card_bij (fun x _ => x.1.2.2) ?_ ?_ ?_
    · intro x hx
      obtain ⟨h1, h2⟩ := (mem_filter.1 hx).2
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      have := x.2.2; rw [h1, h2] at this; exact this
    · intro x hx y hy hxy
      obtain ⟨h1, h2⟩ := (mem_filter.1 hx).2
      obtain ⟨h3, h4⟩ := (mem_filter.1 hy).2
      apply Subtype.ext
      ext <;> simp_all
    · intro i hi
      exact ⟨⟨(v, u, i), h, (mem_filter.1 hi).2⟩, mem_filter.2 ⟨mem_univ _, rfl, rfl⟩, rfl⟩
  rw [this, Fin.card_filter_val_lt]
  exact min_eq_right (hB v u)

/-- The degree of the family of edge copies is the multigraph degree. -/
theorem degree_mEnds {rk : V → ℕ} (hrk : Function.Injective rk) {m : V → V → ℕ}
    (hm : IsMultigraph m) {B : ℕ} (hB : ∀ u v, m u v ≤ B) (v : V) :
    ShannonColouring.degree (mEnds rk m B) v = ∑ u, m v u := by
  unfold ShannonColouring.degree
  have hsplit : (univ.filter fun x : mEdges rk m B => (mEnds rk m B x).1 = v ∨
      (mEnds rk m B x).2 = v) = univ.biUnion fun u => (univ.filter fun x : mEdges rk m B =>
        x.1.1 = v ∧ x.1.2.1 = u) ∪ (univ.filter fun x : mEdges rk m B =>
          x.1.1 = u ∧ x.1.2.1 = v) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_union]
    simp only [mEnds]
    constructor
    · rintro (h | h)
      · exact ⟨x.1.2.1, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨x.1.1, Or.inr ⟨rfl, h⟩⟩
    · rintro ⟨u, (⟨h, -⟩ | ⟨-, h⟩)⟩
      · exact Or.inl h
      · exact Or.inr h
  rw [hsplit, card_biUnion]
  · refine sum_congr rfl fun u _ => ?_
    rw [card_union_of_disjoint]
    · rcases lt_trichotomy (rk v) (rk u) with h | h | h
      · rw [card_copies hB h]
        have : (univ.filter fun x : mEdges rk m B => x.1.1 = u ∧ x.1.2.1 = v) = ∅ := by
          rw [filter_eq_empty_iff]; rintro x - ⟨h1, h2⟩
          have := x.2.1; rw [h1, h2] at this; omega
        rw [this, card_empty, add_zero]
      · have huv : u = v := hrk h.symm
        subst huv
        rw [hm.loopless]
        have : (univ.filter fun x : mEdges rk m B => x.1.1 = u ∧ x.1.2.1 = u) = ∅ := by
          rw [filter_eq_empty_iff]; rintro x - ⟨h1, h2⟩
          have := x.2.1; rw [h1, h2] at this; omega
        rw [this, card_empty]
      · rw [card_copies hB h, hm.symm u v]
        have : (univ.filter fun x : mEdges rk m B => x.1.1 = v ∧ x.1.2.1 = u) = ∅ := by
          rw [filter_eq_empty_iff]; rintro x - ⟨h1, h2⟩
          have := x.2.1; rw [h1, h2] at this; omega
        rw [this, card_empty, zero_add]
    · rw [disjoint_filter]; rintro x - ⟨h1, -⟩ ⟨-, h4⟩
      have := x.2.1; rw [h1, h4] at this; omega
  · intro u _ w _ huw
    rw [Function.onFun, Finset.disjoint_left]
    intro x h1 h2
    simp only [mem_union, mem_filter, mem_univ, true_and] at h1 h2
    apply huw
    rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact a2.symm.trans b2
    · exact (a2.symm.trans b2).trans (a1.symm.trans b1)
    · exact (a1.symm.trans b1).trans (a2.symm.trans b2)
    · exact a1.symm.trans b1

/-- **The groups.** -/
theorem exists_groups {n s0 g : ℕ} (hV : Fintype.card V = 2 * n) (hs0 : 0 < s0) (d : V → ℕ)
    (hd : ∀ v, d v ≤ g) (heven : Even (∑ v, d v)) (hhak : ∀ v, 2 * d v ≤ ∑ u, d u) :
    ∃ W : Fin (3 * g / 2) × Fin (2 * n / s0 + 1) → Finset V,
      (∀ j, Even #(W j) ∧ #(W j) ≤ 2 * s0) ∧ ∀ v, #(univ.filter fun j => v ∈ W j) = d v := by
  obtain ⟨m, hm, hmd⟩ := exists_multigraph (∑ v, d v) d rfl heven hhak
  let rk : V → ℕ := fun v => (Fintype.equivFin V v).val
  have hrk : Function.Injective rk := fun u v h =>
    (Fintype.equivFin V).injective (Fin.ext h)
  have hrk2 : ∀ v, rk v < 2 * n := fun v => lt_of_lt_of_eq (Fintype.equivFin V v).2 hV
  have hB : ∀ u v, m u v ≤ g + 1 := fun u v => by
    have : m u v ≤ ∑ w, m u w := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ v)
    have := hd u; rw [hmd] at *; omega
  set ι := mEdges rk m (g + 1)
  set ends := mEnds rk m (g + 1)
  have hloop : ∀ x : ι, (ends x).1 ≠ (ends x).2 := fun x h => by
    have := x.2.1; simp only [ends, mEnds] at h; rw [h] at this; omega
  have hdeg : ∀ v, ShannonColouring.degree ends v = d v := fun v => by
    rw [degree_mEnds hrk hm (fun u v => le_trans (hB u v) (by omega)) v, hmd]
  obtain ⟨c, hc⟩ := ShannonColouring.shannon ends hloop g (fun v => by rw [hdeg]; exact hd v)
  let grp : ι → Fin (3 * g / 2) × Fin (2 * n / s0 + 1) := fun x =>
    (c x, ⟨rk x.1.1 / s0, Nat.lt_succ_of_le (Nat.div_le_div_right (hrk2 _).le)⟩)
  let E : Fin (3 * g / 2) × Fin (2 * n / s0 + 1) → Finset ι := fun j => univ.filter fun x => grp x = j
  let W : Fin (3 * g / 2) × Fin (2 * n / s0 + 1) → Finset V := fun j =>
    (E j).biUnion fun x => {(ends x).1, (ends x).2}
  -- edges of a group share no vertex
  have hdisj : ∀ j, ∀ x ∈ E j, ∀ y ∈ E j, x ≠ y → ∀ v, Incident ends x v → ¬ Incident ends y v := by
    intro j x hx y hy hxy v hxv hyv
    have hcx : c x = c y := by
      have h1 := (mem_filter.1 hx).2; have h2 := (mem_filter.1 hy).2
      exact congrArg Prod.fst (h1.trans h2.symm)
    exact hc x y hxy ⟨v, hxv, hyv⟩ hcx
  have hpair : ∀ x : ι, ({(ends x).1, (ends x).2} : Finset V) =
      univ.filter fun v => Incident ends x v := by
    intro x; ext v; simp [Incident, eq_comm]
  have hW : ∀ j, #(W j) = 2 * #(E j) := by
    intro j
    rw [card_biUnion]
    · rw [mul_comm, ← smul_eq_mul, ← sum_const]
      exact sum_congr rfl fun x _ => card_pair (hloop x)
    · intro x hx y hy hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro v hv hv'
      rw [hpair, mem_filter] at hv hv'
      exact hdisj j x hx y hy hxy v hv.2 hv'.2
  have hE : ∀ j, #(E j) ≤ s0 := by
    intro j
    have hinj : Set.InjOn (fun x : ι => rk x.1.1) (E j) := by
      intro x hx y hy h
      by_contra hxy
      have : x.1.1 = y.1.1 := hrk h
      exact hdisj j x hx y hy hxy x.1.1 (Or.inl rfl) (Or.inl this.symm)
    have hmaps : ∀ x ∈ E j, rk x.1.1 ∈ Ico (j.2.val * s0) (j.2.val * s0 + s0) := by
      intro x hx
      have h := congrArg (fun j => j.2.val) (mem_filter.1 hx).2
      simp only [grp] at h
      rw [mem_Ico, ← h]
      constructor
      · exact Nat.div_mul_le_self _ _
      · have := Nat.lt_div_mul_add (a := rk x.1.1) hs0; linarith
    have := card_le_card_of_injOn _ hmaps hinj
    simpa using this
  refine ⟨W, fun j => ⟨⟨#(E j), by rw [hW]; ring⟩, by rw [hW]; have := hE j; omega⟩, fun v => ?_⟩
  -- groups containing `v` correspond to edges at `v`
  rw [← hdeg v]
  unfold ShannonColouring.degree
  symm
  refine card_bij (fun x _ => grp x) ?_ ?_ ?_
  · intro x hx
    rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, mem_biUnion.2 ⟨x, mem_filter.2 ⟨mem_univ _, rfl⟩, ?_⟩⟩
    rw [hpair, mem_filter]; exact ⟨mem_univ _, hx.2⟩
  · intro x hx y hy hxy
    by_contra hne
    exact hdisj (grp x) x (mem_filter.2 ⟨mem_univ _, rfl⟩) y (mem_filter.2 ⟨mem_univ _, hxy.symm⟩)
      hne v (mem_filter.1 hx).2 (mem_filter.1 hy).2
  · intro j hj
    obtain ⟨x, hx, hvx⟩ := mem_biUnion.1 (mem_filter.1 hj).2
    rw [hpair, mem_filter] at hvx
    exact ⟨x, mem_filter.2 ⟨mem_univ _, hvx.2⟩, (mem_filter.1 hx).2⟩

end PSLib.Eng
