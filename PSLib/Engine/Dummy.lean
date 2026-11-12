/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Build

/-!
# Dummy edges (Plantholt–Shan, Step 1)

Given a proper colouring `c` of the inner edges of `G` with `k` colours and a set `S` of vertices,
we repeatedly join two vertices of `S` on the same side that miss a common colour `j` by a new
*dummy* edge of colour `j`. A dummy edge is a triple `(j, u, w)`.

`exists_dummies`: at the end, two distinct vertices of `S` on the same side never miss a common
colour; the colouring of real and dummy inner edges stays proper.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {k : ℕ}

variable (G A) in
/-- The colour `j` is present at `v` on a real inner edge. -/
def rcov (c : GE G → Fin k) (j : Fin k) (v : V) : Prop :=
  ∃ e : GE G, Inner (gends G) A e ∧ c e = j ∧ Incident (gends G) e v

/-- The colour `j` is present at `v` on a dummy edge. -/
def dcov (D : Finset (Fin k × V × V)) (j : Fin k) (v : V) : Prop :=
  ∃ d ∈ D, d.1 = j ∧ (d.2.1 = v ∨ d.2.2 = v)

variable (G A) in
/-- The data of a valid dummy set. -/
structure DValid (c : GE G → Fin k) (S : Finset V) (D : Finset (Fin k × V × V)) : Prop where
  ne : ∀ d ∈ D, d.2.1 ≠ d.2.2
  memS : ∀ d ∈ D, d.2.1 ∈ S ∧ d.2.2 ∈ S
  side : ∀ d ∈ D, (d.2.1 ∈ A ↔ d.2.2 ∈ A)
  realfree : ∀ d ∈ D, ∀ v, (d.2.1 = v ∨ d.2.2 = v) → ¬ rcov G A c d.1 v
  dfree : ∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → d.1 = d'.1 → ∀ v, (d.2.1 = v ∨ d.2.2 = v) →
    ¬ (d'.2.1 = v ∨ d'.2.2 = v)

open Classical in
/-- The number of (vertex of `S`, missing colour) pairs. -/
noncomputable def dmiss (c : GE G → Fin k) (S : Finset V) (D : Finset (Fin k × V × V)) : ℕ :=
  ∑ v ∈ S, #(univ.filter fun j => ¬ (rcov G A c j v ∨ dcov D j v))

open Classical in
/-- **The dummy edges.** -/
theorem exists_dummies (c : GE G → Fin k) (S : Finset V) :
    ∃ D, DValid G A c S D ∧ ∀ u w, u ≠ w → u ∈ S → w ∈ S → (u ∈ A ↔ w ∈ A) →
      ∀ j, (rcov G A c j u ∨ dcov D j u) ∨ (rcov G A c j w ∨ dcov D j w) := by
  suffices key : ∀ (m : ℕ) (D : Finset (Fin k × V × V)), dmiss (G := G) (A := A) c S D = m →
      DValid G A c S D → ∃ D, DValid G A c S D ∧ ∀ u w, u ≠ w → u ∈ S → w ∈ S →
        (u ∈ A ↔ w ∈ A) → ∀ j, (rcov G A c j u ∨ dcov D j u) ∨ (rcov G A c j w ∨ dcov D j w) by
    exact key _ ∅ rfl ⟨by simp, by simp, by simp, by simp, by simp⟩
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro D hm hD
  by_cases hdone : ∀ u w, u ≠ w → u ∈ S → w ∈ S → (u ∈ A ↔ w ∈ A) →
      ∀ j, (rcov G A c j u ∨ dcov D j u) ∨ (rcov G A c j w ∨ dcov D j w)
  · exact ⟨D, hD, hdone⟩
  push Not at hdone
  obtain ⟨u, w, huw, huS, hwS, hside, j, ⟨hRu, hDu⟩, ⟨hRw, hDw⟩⟩ := hdone
  set d0 : Fin k × V × V := (j, u, w)
  have hd0 : d0 ∉ D := fun h => hDu ⟨d0, h, rfl, Or.inl rfl⟩
  have hcov : ∀ j' v, dcov (insert d0 D) j' v ↔ dcov D j' v ∨ (j' = j ∧ (u = v ∨ w = v)) := by
    intro j' v
    constructor
    · rintro ⟨d, hd, hdj, hdv⟩
      rcases mem_insert.1 hd with rfl | hd
      · exact Or.inr ⟨hdj.symm, hdv⟩
      · exact Or.inl ⟨d, hd, hdj, hdv⟩
    · rintro (⟨d, hd, hdj, hdv⟩ | ⟨rfl, hv⟩)
      · exact ⟨d, mem_insert_of_mem hd, hdj, hdv⟩
      · exact ⟨d0, mem_insert_self _ _, rfl, hv⟩
  have hD' : DValid G A c S (insert d0 D) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d hd; rcases mem_insert.1 hd with rfl | hd
      · exact huw
      · exact hD.ne d hd
    · intro d hd; rcases mem_insert.1 hd with rfl | hd
      · exact ⟨huS, hwS⟩
      · exact hD.memS d hd
    · intro d hd; rcases mem_insert.1 hd with rfl | hd
      · exact hside
      · exact hD.side d hd
    · intro d hd v hv; rcases mem_insert.1 hd with rfl | hd
      · rcases hv with rfl | rfl
        · exact hRu
        · exact hRw
      · exact hD.realfree d hd v hv
    · intro d hd d' hd' hne hj v hv hv'
      rcases mem_insert.1 hd with rfl | hd <;> rcases mem_insert.1 hd' with rfl | hd'
      · exact hne rfl
      · rcases hv with rfl | rfl
        · exact hDu ⟨d', hd', hj.symm, hv'⟩
        · exact hDw ⟨d', hd', hj.symm, hv'⟩
      · rcases hv' with rfl | rfl
        · exact hDu ⟨d, hd, hj, hv⟩
        · exact hDw ⟨d, hd, hj, hv⟩
      · exact hD.dfree d hd d' hd' hne hj v hv hv'
  -- the measure decreases
  have hlt : dmiss (G := G) (A := A) c S (insert d0 D) < m := by
    rw [← hm]
    unfold dmiss
    apply sum_lt_sum
    · intro v _
      refine card_le_card fun j' hj' => ?_
      simp only [mem_filter, mem_univ, true_and, hcov] at hj' ⊢
      tauto
    · refine ⟨u, huS, card_lt_card ⟨fun j' hj' => ?_, fun h => ?_⟩⟩
      · simp only [mem_filter, mem_univ, true_and, hcov] at hj' ⊢
        tauto
      · have := h (show j ∈ univ.filter fun j' => ¬ (rcov G A c j' u ∨ dcov D j' u) by
          simp [hRu, hDu])
        simp only [mem_filter, mem_univ, true_and, hcov] at this
        exact this (by simp)
  exact ih _ hlt (insert d0 D) rfl hD'

section Family

variable (G) in
/-- The edges of `G` together with the dummy edges `D`. -/
abbrev DE (D : Finset (Fin k × V × V)) := GE G ⊕ {d // d ∈ D}

variable (G) in
/-- The ends of real and dummy edges. -/
noncomputable def dends (D : Finset (Fin k × V × V)) : DE G D → V × V :=
  Sum.elim (gends G) fun d => d.1.2

/-- The colouring of real and dummy edges. -/
def dcol (c : GE G → Fin k) (D : Finset (Fin k × V × V)) : DE G D → Fin k :=
  Sum.elim c fun d => d.1.1

variable {c : GE G → Fin k} {S : Finset V} {D : Finset (Fin k × V × V)}

theorem dends_loop (hD : DValid G A c S D) (x : DE G D) : (dends G D x).1 ≠ (dends G D x).2 := by
  rcases x with e | d
  · exact gends_loop e
  · exact hD.ne d.1 d.2

theorem dends_inner_inr (hD : DValid G A c S D) (d : {d // d ∈ D}) :
    Inner (dends G D) A (Sum.inr d) := hD.side d.1 d.2

theorem dends_inner_inl (e : GE G) : Inner (dends G D) A (Sum.inl e) ↔ Inner (gends G) A e := Iff.rfl

theorem dends_incident_inl (e : GE G) (v : V) :
    Incident (dends G D) (Sum.inl e) v ↔ Incident (gends G) e v := Iff.rfl

theorem dends_xsimple (hD : DValid G A c S D) : XSimple (dends G D) A := by
  intro x y hx hy u w huw hxu hxw hyu hyw
  rcases x with e | d
  · rcases y with f | d'
    · exact congrArg Sum.inl (gends_xsimple (A := A) e f hx hy u w huw hxu hxw hyu hyw)
    · exact absurd (dends_inner_inr hD d') hy
  · exact absurd (dends_inner_inr hD d) hx

theorem dcol_proper (hc : ProperOn (gends G) (univ.filter fun e => Inner (gends G) A e) c)
    (hD : DValid G A c S D) :
    ProperOn (dends G D) (univ.filter fun x => Inner (dends G D) A x) (dcol c D) := by
  intro x hx y hy hxy ⟨v, hxv, hyv⟩ heq
  rcases x with e | d <;> rcases y with f | d'
  · exact hc e (mem_filter.2 ⟨mem_univ _, (mem_filter.1 hx).2⟩) f
      (mem_filter.2 ⟨mem_univ _, (mem_filter.1 hy).2⟩) (fun h => hxy (congrArg Sum.inl h))
      ⟨v, hxv, hyv⟩ heq
  · exact hD.realfree d'.1 d'.2 v hyv ⟨e, (mem_filter.1 hx).2, heq, hxv⟩
  · exact hD.realfree d.1 d.2 v hxv ⟨f, (mem_filter.1 hy).2, heq.symm, hyv⟩
  · exact hD.dfree d.1 d.2 d'.1 d'.2 (fun h => hxy (congrArg Sum.inr (Subtype.ext h))) heq v hxv hyv

theorem card_filter_sum {α β : Type*} [Fintype α] [Fintype β] (p : α ⊕ β → Prop)
    [DecidablePred p] :
    #(univ.filter p) = #(univ.filter fun a => p (Sum.inl a)) + #(univ.filter fun b => p (Sum.inr b)) := by
  simp only [card_filter]
  exact Fintype.sum_sum_type _

theorem din_dends (hD : DValid G A c S D) (v : V) :
    din (dends G D) A v = din (gends G) A v + #(D.filter fun d => d.2.1 = v ∨ d.2.2 = v) := by
  classical
  unfold din
  rw [card_filter_sum]
  congr 1
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1; ext d
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨d', ⟨-, h⟩, rfl⟩; exact ⟨d'.2, h⟩
  · rintro ⟨hd, h⟩; exact ⟨⟨d, hd⟩, ⟨dends_inner_inr hD ⟨d, hd⟩, h⟩, rfl⟩

theorem dx_dends (hD : DValid G A c S D) (v : V) : dx (dends G D) A v = dx (gends G) A v := by
  classical
  unfold dx
  rw [card_filter_sum]
  have : #(univ.filter fun d : {d // d ∈ D} => ¬ Inner (dends G D) A (Sum.inr d) ∧
      Incident (dends G D) (Sum.inr d) v) = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]; exact fun d _ h => h.1 (dends_inner_inr hD d)
  rw [this, add_zero]
  rfl

open Classical in
/-- **The key bound** on the colours missing at the vertices of `S` on one side. -/
theorem sum_missing_S (hc : ProperOn (gends G) (univ.filter fun e => Inner (gends G) A e) c)
    (hD : DValid G A c S D)
    (hfin : ∀ u w, u ≠ w → u ∈ S → w ∈ S → (u ∈ A ↔ w ∈ A) →
      ∀ j, (rcov G A c j u ∨ dcov D j u) ∨ (rcov G A c j w ∨ dcov D j w))
    (P : Finset V) (hP : P = S ∩ A ∨ P = S ∩ Aᶜ) :
    ∑ v ∈ P, (k - din (dends G D) A v) ≤ k := by
  set col := col0 (dends G D) A (dcol c D)
  have hprop : Proper (dends G D) col := by
    intro x y hxy hx heq v hxv hyv
    simp only [col, col0] at hx heq
    by_cases hi : Inner (dends G D) A x
    · rw [if_pos hi] at heq
      by_cases hj : Inner (dends G D) A y
      · rw [if_pos hj] at heq
        exact dcol_proper hc hD x (mem_filter.2 ⟨mem_univ _, hi⟩) y (mem_filter.2 ⟨mem_univ _, hj⟩)
          hxy ⟨v, hxv, hyv⟩ (Option.some_injective _ heq)
      · rw [if_neg hj] at heq; exact Option.some_ne_none _ heq
    · rw [if_neg hi] at hx; exact hx rfl
  have hcov : ∀ j v, Covers (dends G D) col j v ↔ rcov G A c j v ∨ dcov D j v := by
    intro j v
    constructor
    · rintro ⟨x, hx, hxv⟩
      simp only [col, col0] at hx
      split_ifs at hx with hi
      rcases x with e | d
      · exact Or.inl ⟨e, hi, Option.some_injective _ hx, hxv⟩
      · exact Or.inr ⟨d.1, d.2, Option.some_injective _ hx, hxv⟩
    · rintro (⟨e, hi, hej, hev⟩ | ⟨d, hd, hdj, hdv⟩)
      · refine ⟨Sum.inl e, ?_, hev⟩
        simp only [col, col0]; rw [if_pos ((dends_inner_inl e).2 hi)]; simp [dcol, hej]
      · refine ⟨Sum.inr ⟨d, hd⟩, ?_, hdv⟩
        simp only [col, col0]; rw [if_pos (dends_inner_inr hD ⟨d, hd⟩)]; simp [dcol, hdj]
  have hmiss : ∀ v, miss (dends G D) col v + din (dends G D) A v = k := by
    intro v
    have h := miss_add_din_add_ccol (A := A) hprop v
    have h1 : rdeg (dends G D) A col v = 0 := by
      unfold rdeg; rw [card_eq_zero, filter_eq_empty_iff]
      rintro x - ⟨hi, hx, -⟩; simp [col, col0, hi] at hx
    have h2 : ccol (dends G D) A col v = 0 := by
      unfold ccol; rw [card_eq_zero, filter_eq_empty_iff]
      rintro x - ⟨hi, hx, -⟩; simp [col, col0, hi] at hx
    omega
  have hPS : ∀ v ∈ P, v ∈ S := by
    intro v hv; rcases hP with rfl | rfl <;> exact (mem_inter.1 hv).1
  have hPside : ∀ u ∈ P, ∀ w ∈ P, (u ∈ A ↔ w ∈ A) := by
    intro u hu w hw
    rcases hP with rfl | rfl
    · simp only [mem_inter] at hu hw; tauto
    · simp only [mem_inter, mem_compl] at hu hw; tauto
  calc ∑ v ∈ P, (k - din (dends G D) A v)
      = ∑ v ∈ P, #(univ.filter fun j => ¬ Covers (dends G D) col j v) := by
        refine sum_congr rfl fun v _ => ?_
        have := hmiss v; unfold miss at this; omega
    _ = #(P.biUnion fun v => univ.filter fun j => ¬ Covers (dends G D) col j v) := by
        rw [card_biUnion]
        intro u hu w hw huw
        rw [Function.onFun, disjoint_left]
        intro j hju hjw
        rcases hfin u w huw (hPS u hu) (hPS w hw) (hPside u hu w hw) j with h | h
        · exact (mem_filter.1 hju).2 ((hcov j u).2 h)
        · exact (mem_filter.1 hjw).2 ((hcov j w).2 h)
    _ ≤ k := by
        have := card_le_univ (P.biUnion fun v => univ.filter fun j => ¬ Covers (dends G D) col j v)
        rwa [Fintype.card_fin] at this

end Family

end PSLib.Eng
