/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Ops

/-!
# Candidates for alternating paths

For a colour `c`, a set `T` of special vertices and a threshold `t`:

* `UX col v`: the vertices joined to `v` by an uncoloured crossing edge;
* `Partner col c w u`: `wu` is an inner edge of colour `c`;
* `Good col c T t w`: `w ∉ T`, `rdeg w < t`, and the `c`-partner `u` of `w` exists, `u ∉ T`,
  `rdeg u < t`;
* `NN v = UX v ∩ Good`, `MM v` = the partners of `NN v`.

The main estimate: `#NN v ≥ #UX v − (missed + xcnt + 2|T| + 2 #{rdeg ≥ t})` on the other side.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → V × V} {A : Finset V} {k : ℕ}

section Defs

variable (ends A)

open Classical in
/-- The vertices joined to `v` by an uncoloured crossing edge. -/
noncomputable def UX (col : E → Option (Fin k)) (v : V) : Finset V :=
  univ.filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = none ∧ Incident ends e v ∧
    Incident ends e w ∧ v ≠ w

/-- `wu` is an inner edge of colour `c`. -/
def Partner (col : E → Option (Fin k)) (c : Fin k) (w u : V) : Prop :=
  ∃ f, Inner ends A f ∧ col f = some c ∧ Incident ends f w ∧ Incident ends f u ∧ w ≠ u

/-- A good vertex for colour `c`. -/
def Good (col : E → Option (Fin k)) (c : Fin k) (T : Finset V) (t : ℕ) (w : V) : Prop :=
  w ∉ T ∧ rdeg ends A col w < t ∧ ∃ u, Partner ends A col c w u ∧ u ∉ T ∧ rdeg ends A col u < t

open Classical in
/-- Good uncoloured crossing neighbours. -/
noncomputable def NN (col : E → Option (Fin k)) (c : Fin k) (T : Finset V) (t : ℕ) (v : V) :
    Finset V :=
  (UX ends A col v).filter (Good ends A col c T t)

open Classical in
/-- Their partners. -/
noncomputable def MM (col : E → Option (Fin k)) (c : Fin k) (T : Finset V) (t : ℕ) (v : V) :
    Finset V :=
  univ.filter fun u => ∃ w ∈ NN ends A col c T t v, Partner ends A col c w u

/-- The other side. -/
def side' (v : V) : Finset V := if v ∈ A then Aᶜ else A

end Defs

/-- Crossing edges are simple. -/
def XSimple (ends : E → V × V) (A : Finset V) : Prop :=
  ∀ e f, ¬ Inner ends A e → ¬ Inner ends A f → ∀ u w, u ≠ w → Incident ends e u →
    Incident ends e w → Incident ends f u → Incident ends f w → e = f

theorem side_of_crossing {e : E} {v w : V} (hx : ¬ Inner ends A e) (hv : Incident ends e v)
    (hw : Incident ends e w) (hvw : v ≠ w) : (v ∈ A ↔ w ∉ A) := by
  unfold Inner at hx
  unfold Incident at hv hw
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  · exact absurd rfl hvw
  · tauto
  · tauto
  · exact absurd rfl hvw

theorem ne_of_crossing {e : E} {v w : V} (hx : ¬ Inner ends A e) (hv : (ends e).1 = v)
    (hw : (ends e).2 = w) : v ≠ w := by
  rintro rfl; unfold Inner at hx; rw [hv, hw] at hx; exact hx Iff.rfl

theorem side_of_inner {f : E} {w u : V} (hi : Inner ends A f) (hw : Incident ends f w)
    (hu : Incident ends f u) : (w ∈ A ↔ u ∈ A) := by
  unfold Inner at hi
  unfold Incident at hw hu
  rcases hw with rfl | rfl <;> rcases hu with rfl | rfl <;> tauto

theorem mem_side' {v w : V} : w ∈ side' A v ↔ (v ∈ A ↔ w ∉ A) := by
  unfold side'
  split_ifs with hv <;> simp [hv]

theorem card_side' {n : ℕ} (hA : #A = n) (hB : #Aᶜ = n) (v : V) : #(side' A v) = n := by
  unfold side'; split_ifs <;> assumption

variable {col : E → Option (Fin k)} {c : Fin k} {T : Finset V} {t : ℕ}

theorem UX_sub (v : V) : UX ends A col v ⊆ side' A v := by
  intro w hw
  obtain ⟨e, hx, -, hv, hw', hvw⟩ := (mem_filter.1 hw).2
  exact mem_side'.2 (side_of_crossing hx hv hw' hvw)

/-- `#UX v ≥ dx v − ccol v`. -/
theorem card_UX (hs : XSimple ends A) (v : V) :
    dx ends A v ≤ #(UX ends A col v) + ccol ends A col v := by
  classical
  set X := univ.filter fun e => ¬ Inner ends A e ∧ col e = none ∧ Incident ends e v
  have hsplit : dx ends A v = #X + ccol ends A col v := by
    unfold dx ccol
    rw [← card_union_of_disjoint]
    · congr 1; ext e
      simp only [X, mem_filter, mem_univ, true_and, mem_union]
      by_cases hc : col e = none <;> simp [hc]
    · rw [disjoint_filter]; intro e _ h1 h2; exact h2.2.1 h1.2.1
  let oth : E → V := fun e => if (ends e).1 = v then (ends e).2 else (ends e).1
  have hoth : ∀ e ∈ X, oth e ∈ UX ends A col v ∧ Incident ends e (oth e) := by
    intro e he
    obtain ⟨hx, hc, hv⟩ := (mem_filter.1 he).2
    have hinc : Incident ends e (oth e) ∧ v ≠ oth e := by
      simp only [oth]
      split_ifs with h1
      · exact ⟨Or.inr rfl, fun h => ne_of_crossing hx h1 h.symm rfl⟩
      · refine ⟨Or.inl rfl, fun h => h1 h.symm⟩
    exact ⟨mem_filter.2 ⟨mem_univ _, e, hx, hc, hv, hinc.1, hinc.2⟩, hinc.1⟩
  have hinj : Set.InjOn oth X := by
    intro e he f hf hef
    obtain ⟨hxe, -, hve⟩ := (mem_filter.1 he).2
    obtain ⟨hxf, -, hvf⟩ := (mem_filter.1 hf).2
    have h1 := (hoth e he).2
    have h2 := (hoth f hf).2
    have hne : v ≠ oth e := by
      intro h
      obtain ⟨-, e', hx', -, hv', hw', hne'⟩ := mem_filter.1 (hoth e he).1
      have := side_of_crossing hxe hve h1
      rw [← h] at this; tauto
    exact hs e f hxe hxf v (oth e) hne hve h1 hvf (hef ▸ h2)
  have := card_le_card_of_injOn oth (fun e he => (hoth e he).1) hinj
  omega

open Classical in
/-- Vertices of the other side that are not good for `c`. -/
theorem card_not_good (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (h : Proper ends col) (S : Finset V)
    (hS : ∀ f w u, Inner ends A f → Incident ends f w → Incident ends f u → (w ∈ S ↔ u ∈ S))
    (hSx : ∀ e w u, ¬ Inner ends A e → Incident ends e w → Incident ends e u → w ∈ S → u ∈ S →
      w = u) :
    #(S.filter fun w => ¬ Good ends A col c T t w) ≤
      missed ends col c S + xcnt ends A col c + 2 * #(T ∩ S) +
        2 * #(S.filter fun w => t ≤ rdeg ends A col w) := by
  classical
  set H := S.filter fun w => t ≤ rdeg ends A col w
  -- the partner of a vertex is unique, and partners stay on the side
  have hpu : ∀ w w' u, Partner ends A col c w u → Partner ends A col c w' u → w = w' := by
    rintro w w' u ⟨f, -, hf, hfw, hfu, hwu⟩ ⟨f', -, hf', hfw', hfu', hwu'⟩
    have : f = f' := h.eq_of_incident hf hf' hfu hfu'
    subst this
    rcases (incident_iff hfw hfu hwu w').1 hfw' with h1 | h1
    · exact h1.symm
    · exact absurd h1 hwu'
  have hcard_partner : ∀ X : Finset V,
      #(S.filter fun w => ∃ u ∈ X, Partner ends A col c w u) ≤ #(X ∩ S) := by
    intro X
    have hsub : (S.filter fun w => ∃ u ∈ X, Partner ends A col c w u) ⊆
        (X ∩ S).biUnion fun u => S.filter fun w => Partner ends A col c w u := by
      intro w hw
      obtain ⟨hwS, u, huX, hp⟩ := mem_filter.1 hw
      obtain ⟨f, hfi, -, hfw, hfu, -⟩ := id hp
      exact mem_biUnion.2 ⟨u, mem_inter.2 ⟨huX, (hS f w u hfi hfw hfu).1 hwS⟩,
        mem_filter.2 ⟨hwS, hp⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ u ∈ X ∩ S, #(S.filter fun w => Partner ends A col c w u)
        ≤ ∑ u ∈ X ∩ S, 1 := sum_le_sum fun u _ => card_le_one.2 fun w hw w' hw' =>
          hpu w w' u (mem_filter.1 hw).2 (mem_filter.1 hw').2
      _ = #(X ∩ S) := by simp
  have hx : #(S.filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = some c ∧ Incident ends e w) ≤
      xcnt ends A col c := by
    have hsub : (S.filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = some c ∧ Incident ends e w) ⊆
        (univ.filter fun e => ¬ Inner ends A e ∧ col e = some c).biUnion
          fun e => S.filter fun w => Incident ends e w := by
      intro w hw
      obtain ⟨hwS, e, hex, hec, hew⟩ := mem_filter.1 hw
      exact mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, hex, hec⟩, mem_filter.2 ⟨hwS, hew⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    unfold xcnt
    calc ∑ e ∈ univ.filter (fun e => ¬ Inner ends A e ∧ col e = some c),
          #(S.filter fun w => Incident ends e w)
        ≤ ∑ e ∈ univ.filter (fun e => ¬ Inner ends A e ∧ col e = some c), 1 :=
          sum_le_sum fun e he => card_le_one.2 fun w hw w' hw' =>
            hSx e w w' (mem_filter.1 he).2.1 (mem_filter.1 hw).2 (mem_filter.1 hw').2
              (mem_filter.1 hw).1 (mem_filter.1 hw').1
      _ = _ := by simp
  have hsub : (S.filter fun w => ¬ Good ends A col c T t w) ⊆
      (S.filter fun w => ¬ Covers ends col c w) ∪
      (S.filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = some c ∧ Incident ends e w) ∪
      (T ∩ S) ∪ (S.filter fun w => ∃ u ∈ T, Partner ends A col c w u) ∪ H ∪
      (S.filter fun w => ∃ u ∈ H, Partner ends A col c w u) := by
    intro w hw
    obtain ⟨hwS, hng⟩ := mem_filter.1 hw
    simp only [mem_union, mem_filter, mem_inter, H]
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hcon
    obtain ⟨g, hg, hgw⟩ := h1 hwS
    have hgi : Inner ends A g := by
      by_contra hgi; exact h2 hwS g hgi hg hgw
    -- the other end of `g`
    obtain ⟨u, hgu, hwu⟩ : ∃ u, Incident ends g u ∧ w ≠ u := by
      unfold Incident at hgw
      rcases hgw with h | h
      · exact ⟨(ends g).2, Or.inr rfl, fun h' => hloop g (h.trans h')⟩
      · exact ⟨(ends g).1, Or.inl rfl, fun h' => hloop g (h'.symm.trans h.symm)⟩
    have hp : Partner ends A col c w u := ⟨g, hgi, hg, hgw, hgu, hwu⟩
    have huS : u ∈ S := (hS g w u hgi hgw hgu).1 hwS
    refine hng ⟨fun hwT => h3 hwT hwS, h5 hwS, u, hp, fun huT => h4 hwS u huT hp,
      Nat.lt_of_not_le fun hu => h6 hwS u ⟨huS, hu⟩ hp⟩
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  have := hcard_partner H
  have h2 := hcard_partner T
  have hHS : H ∩ S = H := inter_eq_left.2 (filter_subset _ _)
  rw [hHS] at this
  have := card_union_le (((S.filter fun w => ¬ Covers ends col c w) ∪
      (S.filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = some c ∧ Incident ends e w) ∪
      (T ∩ S) ∪ (S.filter fun w => ∃ u ∈ T, Partner ends A col c w u))) H
  have := card_union_le (((S.filter fun w => ¬ Covers ends col c w) ∪
      (S.filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = some c ∧ Incident ends e w) ∪
      (T ∩ S))) (S.filter fun w => ∃ u ∈ T, Partner ends A col c w u)
  have := card_union_le (((S.filter fun w => ¬ Covers ends col c w) ∪
      (S.filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = some c ∧ Incident ends e w)))
      (T ∩ S)
  have := card_union_le (S.filter fun w => ¬ Covers ends col c w)
      (S.filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = some c ∧ Incident ends e w)
  unfold missed
  omega

theorem rsize_add (col : E → Option (Fin k)) :
    rsize ends A col A + rsize ends A col Aᶜ =
      #(univ.filter fun e => Inner ends A e ∧ col e = none) := by
  unfold rsize
  rw [← card_union_of_disjoint]
  · congr 1; ext e
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_compl]
    tauto
  · rw [disjoint_filter]; intro e _ h1 h2; exact (mem_compl.1 h2.2.2) h1.2.2

theorem sum_rdeg (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (col : E → Option (Fin k)) :
    ∑ w, rdeg ends A col w = 2 * #(univ.filter fun e => Inner ends A e ∧ col e = none) := by
  classical
  unfold rdeg
  simp only [card_filter]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  by_cases hP : Inner ends A e ∧ col e = none
  · simp only [hP, true_and, if_true, mul_one]
    rw [← card_filter, card_filter_incident (e := e) (a := (ends e).1) (b := (ends e).2)
      (Or.inl rfl) (Or.inr rfl) (hloop e)]
    simp
  · simp only [mul_ite, mul_one, mul_zero]
    rw [if_neg hP]
    refine sum_eq_zero fun w _ => ?_
    rw [if_neg]; tauto

theorem card_high_mul (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (col : E → Option (Fin k))
    (S : Finset V) :
    #(S.filter fun w => t ≤ rdeg ends A col w) * t ≤
      2 * (rsize ends A col A + rsize ends A col Aᶜ) := by
  classical
  rw [rsize_add, ← sum_rdeg hloop]
  calc #(S.filter fun w => t ≤ rdeg ends A col w) * t
      = ∑ w ∈ S.filter (fun w => t ≤ rdeg ends A col w), t := by rw [sum_const, smul_eq_mul]
    _ ≤ ∑ w ∈ S.filter (fun w => t ≤ rdeg ends A col w), rdeg ends A col w :=
        sum_le_sum fun w hw => (mem_filter.1 hw).2
    _ ≤ ∑ w, rdeg ends A col w :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _

theorem side'_inner {f : E} {w u : V} (v : V) (hi : Inner ends A f) (hw : Incident ends f w)
    (hu : Incident ends f u) : (w ∈ side' A v ↔ u ∈ side' A v) := by
  rw [mem_side', mem_side']
  have := side_of_inner hi hw hu
  tauto

theorem side'_crossing {e : E} {w u : V} (v : V) (hx : ¬ Inner ends A e) (hw : Incident ends e w)
    (hu : Incident ends e u) (hws : w ∈ side' A v) (hus : u ∈ side' A v) : w = u := by
  by_contra hwu
  have := side_of_crossing hx hw hu hwu
  rw [mem_side'] at hws hus
  tauto

open Classical in
/-- **The main estimate** for good uncoloured crossing neighbours. -/
theorem card_NN_ge (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hs : XSimple ends A)
    (h : Proper ends col) (v : V) :
    dx ends A v ≤ #(NN ends A col c T t v) + ccol ends A col v + missed ends col c (side' A v) +
      xcnt ends A col c + 2 * #(T ∩ side' A v) +
        2 * #((side' A v).filter fun w => t ≤ rdeg ends A col w) := by
  have h1 := card_UX (col := col) hs v
  have h2 := card_not_good (c := c) (T := T) (t := t) hloop h (side' A v)
    (fun f w u hi hw hu => side'_inner v hi hw hu)
    (fun e w u hx hw hu hws hus => side'_crossing v hx hw hu hws hus)
  have h3 : #(UX ends A col v) ≤ #(NN ends A col c T t v) +
      #((side' A v).filter fun w => ¬ Good ends A col c T t w) := by
    unfold NN
    rw [← card_union_of_disjoint]
    · refine card_le_card fun w hw => ?_
      by_cases hg : Good ends A col c T t w
      · exact mem_union_left _ (mem_filter.2 ⟨hw, hg⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨UX_sub v hw, hg⟩)
    · rw [disjoint_left]; intro w h1 h2; exact (mem_filter.1 h2).2 (mem_filter.1 h1).2
  omega

open Classical in
theorem card_NN_le_MM (h : Proper ends col) (v : V) :
    #(NN ends A col c T t v) ≤ #(MM ends A col c T t v) := by
  have hpu : ∀ w w' u, Partner ends A col c w u → Partner ends A col c w' u → w = w' := by
    rintro w w' u ⟨f, -, hf, hfw, hfu, hwu⟩ ⟨f', -, hf', hfw', hfu', hwu'⟩
    have : f = f' := h.eq_of_incident hf hf' hfu hfu'
    subst this
    rcases (incident_iff hfw hfu hwu w').1 hfw' with h1 | h1
    · exact h1.symm
    · exact absurd h1 hwu'
  have hsub : NN ends A col c T t v ⊆ (MM ends A col c T t v).biUnion
      fun u => (NN ends A col c T t v).filter fun w => Partner ends A col c w u := by
    intro w hw
    obtain ⟨_, _, u, hp, _, _⟩ := (mem_filter.1 hw).2
    exact mem_biUnion.2 ⟨u, mem_filter.2 ⟨mem_univ _, w, hw, hp⟩, mem_filter.2 ⟨hw, hp⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ u ∈ MM ends A col c T t v, #((NN ends A col c T t v).filter
        fun w => Partner ends A col c w u)
      ≤ ∑ u ∈ MM ends A col c T t v, 1 := sum_le_sum fun u _ => card_le_one.2 fun w hw w' hw' =>
        hpu w w' u (mem_filter.1 hw).2 (mem_filter.1 hw').2
    _ = _ := by simp

open Classical in
theorem MM_sub (v : V) : MM ends A col c T t v ⊆ side' A v := by
  intro u hu
  obtain ⟨w, hw, f, hfi, -, hfw, hfu, -⟩ := (mem_filter.1 hu).2
  have hws : w ∈ side' A v := UX_sub v (mem_filter.1 hw).1
  exact (side'_inner v hfi hfw hfu).1 hws

end PSLib.Eng
