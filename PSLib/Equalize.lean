/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ShannonColouring.Kempe
public import ShannonColouring.PathEnds

/-!
# Equalized edge colourings of multigraphs (McDiarmid 1972)

For a loopless multigraph given as an edge family `ends : ι → V × V`, an edge set `s` and a proper
colouring of `s` with `k` colours, there is a proper colouring of `s` with `k` colours whose colour
classes differ in size by at most one (`exists_equalized`).

Proof: if the class of `a` exceeds that of `b` by at least two, the signed count
`δ(x) = #(a-edges at x) − #(b-edges at x)` sums to `2(|a| − |b|) > 0`, so some component `T` of the
`a`/`b` Kempe graph has `∑_T δ > 0`; a component has at most two vertices with `δ ≠ 0` (they have
degree one in a graph of maximum degree two), so the Kempe change on `T` moves exactly one edge from
`a` to `b` and the sum of the squared class sizes decreases. The Kempe machinery is that of the
registered Shannon entry (`ShannonColouring.kempeSwap`, `not_three_ends_in_component`).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib

open Finset ShannonColouring

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  {ends : ι → V × V} {k : ℕ}

instance (i : ι) (x : V) : Decidable (Incident ends i x) :=
  inferInstanceAs (Decidable ((ends i).1 = x ∨ (ends i).2 = x))

/-- The size of the colour class `a` within `s`. -/
def cls (s : Finset ι) (c : ι → Fin k) (a : Fin k) : ℕ := #(s.filter fun i => c i = a)

/-- The number of edges of `s` of colour `a` at `x`. -/
def degc (ends : ι → V × V) (s : Finset ι) (c : ι → Fin k) (a : Fin k) (x : V) : ℕ :=
  #(s.filter fun i => c i = a ∧ Incident ends i x)

/-- Double counting over a vertex set closed for the colours `a`, `b`. -/
theorem sum_degc_eq (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (s : Finset ι) (c : ι → Fin k)
    (a : Fin k) (T : Finset V) (hT : ∀ i ∈ s, c i = a → ((ends i).1 ∈ T ↔ (ends i).2 ∈ T)) :
    ∑ x ∈ T, degc ends s c a x = 2 * #(s.filter fun i => c i = a ∧ (ends i).1 ∈ T) := by
  classical
  simp only [degc, card_filter]
  rw [sum_comm]
  rw [show (2 * ∑ i ∈ s, if c i = a ∧ (ends i).1 ∈ T then 1 else 0) =
      ∑ i ∈ s, 2 * (if c i = a ∧ (ends i).1 ∈ T then 1 else 0) by rw [mul_sum]]
  refine sum_congr rfl fun i hi => ?_
  by_cases hc : c i = a
  · have h1 := hloop i
    have hTi := hT i hi hc
    simp only [hc, true_and, Incident]
    rw [← card_filter]
    by_cases h : (ends i).1 ∈ T
    · have : T.filter (fun x => (ends i).1 = x ∨ (ends i).2 = x) = {(ends i).1, (ends i).2} := by
        ext x; simp only [mem_filter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨-, h | h⟩ <;> [left; right] <;> exact h.symm
        · rintro (rfl | rfl)
          · exact ⟨h, Or.inl rfl⟩
          · exact ⟨hTi.1 h, Or.inr rfl⟩
      rw [this, card_pair h1, if_pos h]
    · have : T.filter (fun x => (ends i).1 = x ∨ (ends i).2 = x) = ∅ := by
        ext x; simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
        rintro hx (rfl | rfl)
        · exact h hx
        · exact h (hTi.2 hx)
      rw [this, card_empty, if_neg h]
  · simp [hc]

/-- The squared-size energy of a colouring. -/
def energy (s : Finset ι) (c : ι → Fin k) : ℕ := ∑ a, cls s c a ^ 2

theorem degc_le_one {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) (a : Fin k) (x : V) :
    degc ends s c a x ≤ 1 := by
  rw [degc, card_le_one]
  intro i hi j hj
  by_contra hne
  rw [mem_filter] at hi hj
  exact h i hi.1 j hj.1 hne ⟨x, hi.2.2, hj.2.2⟩ (hi.2.1.trans hj.2.1.symm)

/-- The Kempe change on a component with one more `a`-edge than `b`-edges. -/
theorem cls_kempeSwap {s : Finset ι} {c : ι → Fin k} {a b : Fin k} (hab : a ≠ b) (T : Finset V)
    (hT : KempeClosed ends s c a b (T : Set V)) (d : Fin k) :
    cls s (kempeSwap ends c a b (T : Set V)) d =
      if d = a then cls s c a - #(s.filter fun i => c i = a ∧ (ends i).1 ∈ T) +
          #(s.filter fun i => c i = b ∧ (ends i).1 ∈ T)
      else if d = b then cls s c b - #(s.filter fun i => c i = b ∧ (ends i).1 ∈ T) +
          #(s.filter fun i => c i = a ∧ (ends i).1 ∈ T)
      else cls s c d := by
  classical
  have key : ∀ i, kempeSwap ends c a b (T : Set V) i =
      if (ends i).1 ∈ T ∧ (c i = a ∨ c i = b) then Equiv.swap a b (c i) else c i := by
    intro i; simp [kempeSwap]
  split_ifs with hda hdb
  · subst hda
    have hba := Ne.symm hab
    have hsplit : s.filter (fun i => kempeSwap ends c d b (T : Set V) i = d) =
        (s.filter fun i => c i = d ∧ (ends i).1 ∉ T) ∪ (s.filter fun i => c i = b ∧ (ends i).1 ∈ T) := by
      ext i
      simp only [mem_filter, mem_union, key]
      by_cases h1 : (ends i).1 ∈ T <;> by_cases h2 : c i = d <;> by_cases h3 : c i = b <;>
        simp_all [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hdisj : Disjoint (s.filter fun i => c i = d ∧ (ends i).1 ∉ T)
        (s.filter fun i => c i = b ∧ (ends i).1 ∈ T) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      rw [mem_filter] at h1 h2; exact h1.2.2 h2.2.2
    have hA : cls s c d = #(s.filter fun i => c i = d ∧ (ends i).1 ∉ T) +
        #(s.filter fun i => c i = d ∧ (ends i).1 ∈ T) := by
      rw [cls, ← card_union_of_disjoint]
      · congr 1; ext i; simp only [mem_filter, mem_union]; tauto
      · rw [Finset.disjoint_left]; intro i h1 h2
        rw [mem_filter] at h1 h2; exact h1.2.2 h2.2.2
    rw [cls, hsplit, card_union_of_disjoint hdisj, hA]
    omega
  · subst hdb
    have hba := Ne.symm hab
    have hsplit : s.filter (fun i => kempeSwap ends c a d (T : Set V) i = d) =
        (s.filter fun i => c i = d ∧ (ends i).1 ∉ T) ∪ (s.filter fun i => c i = a ∧ (ends i).1 ∈ T) := by
      ext i
      simp only [mem_filter, mem_union, key]
      by_cases h1 : (ends i).1 ∈ T <;> by_cases h2 : c i = a <;> by_cases h3 : c i = d <;>
        simp_all [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hdisj : Disjoint (s.filter fun i => c i = d ∧ (ends i).1 ∉ T)
        (s.filter fun i => c i = a ∧ (ends i).1 ∈ T) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      rw [mem_filter] at h1 h2; exact h1.2.2 h2.2.2
    have hB : cls s c d = #(s.filter fun i => c i = d ∧ (ends i).1 ∉ T) +
        #(s.filter fun i => c i = d ∧ (ends i).1 ∈ T) := by
      rw [cls, ← card_union_of_disjoint]
      · congr 1; ext i; simp only [mem_filter, mem_union]; tauto
      · rw [Finset.disjoint_left]; intro i h1 h2
        rw [mem_filter] at h1 h2; exact h1.2.2 h2.2.2
    rw [cls, hsplit, card_union_of_disjoint hdisj, hB]
    omega
  · unfold cls
    congr 1
    ext i
    simp only [mem_filter, key]
    constructor
    · rintro ⟨hi, h⟩
      refine ⟨hi, ?_⟩
      split_ifs at h with h'
      · rcases h'.2 with h2 | h2
        · rw [h2, Equiv.swap_apply_left] at h; exact absurd h.symm hdb
        · rw [h2, Equiv.swap_apply_right] at h; exact absurd h.symm hda
      · exact h
    · rintro ⟨hi, h⟩
      refine ⟨hi, ?_⟩
      rw [if_neg]
      · exact h
      · rintro ⟨-, h2 | h2⟩
        · exact hda (h.symm.trans h2)
        · exact hdb (h.symm.trans h2)

section Components

variable {s : Finset ι} {c : ι → Fin k} {a b : Fin k}

/-- The signed count `#(a-edges at x) − #(b-edges at x)`. -/
def sdeg (ends : ι → V × V) (s : Finset ι) (c : ι → Fin k) (a b : Fin k) (x : V) : ℤ :=
  (degc ends s c a x : ℤ) - degc ends s c b x

theorem sum_sdeg (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (T : Finset V)
    (hT : KempeClosed ends s c a b (T : Set V)) :
    ∑ x ∈ T, sdeg ends s c a b x =
      2 * ((#(s.filter fun i => c i = a ∧ (ends i).1 ∈ T) : ℤ) -
        #(s.filter fun i => c i = b ∧ (ends i).1 ∈ T)) := by
  have ha := sum_degc_eq hloop s c a T fun i hi hc => hT i hi (Or.inl hc)
  have hb := sum_degc_eq hloop s c b T fun i hi hc => hT i hi (Or.inr hc)
  simp only [sdeg, sum_sub_distrib]
  rw [← Nat.cast_sum, ← Nat.cast_sum, ha, hb]
  push_cast
  ring

theorem kempe_degree_le (h : ProperOn ends s c) [DecidableRel (kempeGraph ends s c a b).Adj]
    (x : V) : (kempeGraph ends s c a b).degree x ≤ 2 :=
  (kempeGraph_degree_le h x {a, b} fun i _ _ hc => by
    rcases hc with hc | hc <;> simp [hc]).trans card_le_two

theorem kempe_degree_le_one (h : ProperOn ends s c)
    [DecidableRel (kempeGraph ends s c a b).Adj] {x : V} (hx : sdeg ends s c a b x ≠ 0) :
    (kempeGraph ends s c a b).degree x ≤ 1 := by
  have h1 := degc_le_one h a x
  have h2 := degc_le_one h b x
  have hz : degc ends s c a x = 0 ∨ degc ends s c b x = 0 := by
    by_contra hh
    push Not at hh
    apply hx
    simp only [sdeg]
    omega
  rcases hz with hz | hz
  · refine (kempeGraph_degree_le h x {b} fun i hi hix hc => ?_).trans (by simp)
    rcases hc with hc | hc
    · exfalso
      rw [degc, card_eq_zero, filter_eq_empty_iff] at hz
      exact hz hi ⟨hc, hix⟩
    · simp [hc]
  · refine (kempeGraph_degree_le h x {a} fun i hi hix hc => ?_).trans (by simp)
    rcases hc with hc | hc
    · simp [hc]
    · exfalso
      rw [degc, card_eq_zero, filter_eq_empty_iff] at hz
      exact hz hi ⟨hc, hix⟩

theorem sdeg_le_one (h : ProperOn ends s c) (x : V) : sdeg ends s c a b x ≤ 1 := by
  have := degc_le_one h a x
  simp only [sdeg]
  omega

open Classical in
/-- A Kempe component has signed sum at most `2`. -/
theorem sum_sdeg_component_le (h : ProperOn ends s c) (z : V) :
    ∑ x ∈ univ.filter (fun x => (kempeGraph ends s c a b).Reachable z x),
      sdeg ends s c a b x ≤ 2 := by
  classical
  set K := kempeGraph ends s c a b
  set T := univ.filter fun x => K.Reachable z x
  set E := T.filter fun x => sdeg ends s c a b x ≠ 0
  have hE : #E ≤ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ := two_lt_card.1 hlt
    simp only [E, T, mem_filter, mem_univ, true_and] at hu hv hw
    exact not_three_ends_in_component K (kempe_degree_le h) huv huw hvw
      (hu.1.symm.trans hv.1) (hu.1.symm.trans hw.1) (kempe_degree_le_one h hu.2)
      (kempe_degree_le_one h hv.2) (kempe_degree_le_one h hw.2)
  calc ∑ x ∈ T, sdeg ends s c a b x = ∑ x ∈ E, sdeg ends s c a b x := by
        rw [sum_filter_ne_zero]
    _ ≤ ∑ _x ∈ E, (1 : ℤ) := sum_le_sum fun x _ => sdeg_le_one h x
    _ = #E := by simp
    _ ≤ 2 := by exact_mod_cast hE

end Components

/-- **McDiarmid's equalization** (1972): a proper `k`-colouring of a multigraph can be replaced by
one whose colour classes differ in size by at most one. -/
theorem exists_equalized (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (s : Finset ι) :
    ∀ (m : ℕ) (c : ι → Fin k), energy s c = m → ProperOn ends s c →
      ∃ c' : ι → Fin k, ProperOn ends s c' ∧ ∀ a b, cls s c' a ≤ cls s c' b + 1 := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c hm h
  by_cases heq : ∀ a b, cls s c a ≤ cls s c b + 1
  · exact ⟨c, h, heq⟩
  push Not at heq
  obtain ⟨a, b, hab⟩ := heq
  have hne : a ≠ b := by rintro rfl; omega
  set K := kempeGraph ends s c a b
  -- the total signed sum
  have htot : ∑ x, sdeg ends s c a b x = 2 * ((cls s c a : ℤ) - cls s c b) := by
    have := sum_sdeg (s := s) (c := c) (a := a) (b := b) hloop univ (fun i _ _ => by simp)
    simpa [cls] using this
  -- a component with positive signed sum
  obtain ⟨z, hz⟩ : ∃ z, 0 < ∑ x ∈ univ.filter (fun x => K.Reachable z x), sdeg ends s c a b x := by
    by_contra hall
    push Not at hall
    have hfib := Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ.image K.connectedComponentMk)
      (g := K.connectedComponentMk) (fun x _ => mem_image_of_mem _ (mem_univ x))
      (fun x => sdeg ends s c a b x)
    have hle : ∑ C ∈ univ.image K.connectedComponentMk,
        ∑ x ∈ univ.filter (fun x => K.connectedComponentMk x = C), sdeg ends s c a b x ≤ 0 := by
      refine sum_nonpos fun C hC => ?_
      obtain ⟨z, -, rfl⟩ := mem_image.1 hC
      have := hall z
      convert this using 2
      ext x
      simp only [mem_filter, mem_univ, true_and, SimpleGraph.ConnectedComponent.eq]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [hfib, htot] at hle
    have : (cls s c b : ℤ) + 2 ≤ cls s c a := by exact_mod_cast hab
    omega
  set T := univ.filter fun x => K.Reachable z x
  have hT : KempeClosed ends s c a b (T : Set V) := by
    have := kempeClosed_reachable (s := s) (c := c) (α := a) (γ := b) hloop z
    convert this using 1
    ext x; simp [T, K]
  have hsum := sum_sdeg (s := s) (c := c) (a := a) (b := b) hloop T hT
  have hle2 := sum_sdeg_component_le (s := s) (c := c) (a := a) (b := b) h z
  set aT := #(s.filter fun i => c i = a ∧ (ends i).1 ∈ T)
  set bT := #(s.filter fun i => c i = b ∧ (ends i).1 ∈ T)
  have haT : aT = bT + 1 := by
    have h1 : ∑ x ∈ T, sdeg ends s c a b x = 2 * ((aT : ℤ) - bT) := hsum
    have h2 : 0 < 2 * ((aT : ℤ) - bT) := h1 ▸ hz
    have h3 : 2 * ((aT : ℤ) - bT) ≤ 2 := h1 ▸ hle2
    omega
  have haTle : aT ≤ cls s c a := card_le_card fun i hi => by
    rw [mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.1⟩
  have hbTle : bT ≤ cls s c b := card_le_card fun i hi => by
    rw [mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.1⟩
  set c' := kempeSwap ends c a b (T : Set V)
  have hcls := cls_kempeSwap (s := s) (c := c) hne T hT
  have hca : cls s c' a + 1 = cls s c a := by
    have := hcls a; rw [if_pos rfl] at this; rw [this]; omega
  have hcb : cls s c' b = cls s c b + 1 := by
    have := hcls b; rw [if_neg (Ne.symm hne), if_pos rfl] at this; rw [this]; omega
  have hcd : ∀ d, d ≠ a → d ≠ b → cls s c' d = cls s c d := by
    intro d h1 h2; have := hcls d; rw [if_neg h1, if_neg h2] at this; exact this
  -- the energy decreases
  have henergy : energy s c' < energy s c := by
    unfold energy
    rw [← add_sum_erase _ _ (mem_univ a), ← add_sum_erase _ _ (mem_univ a),
      ← add_sum_erase _ _ (mem_erase.2 ⟨Ne.symm hne, mem_univ b⟩),
      ← add_sum_erase _ _ (mem_erase.2 ⟨Ne.symm hne, mem_univ b⟩)]
    have hrest : ∑ d ∈ (univ.erase a).erase b, cls s c' d ^ 2 =
        ∑ d ∈ (univ.erase a).erase b, cls s c d ^ 2 :=
      sum_congr rfl fun d hd => by
        rw [mem_erase, mem_erase] at hd
        rw [hcd d hd.2.1 hd.1]
    rw [hrest]
    have hA : cls s c a = cls s c' a + 1 := hca.symm
    rw [hA, hcb]
    have : cls s c b + 2 ≤ cls s c' a + 1 := by omega
    nlinarith
  exact ih _ (hm ▸ henergy) c' rfl (h.kempeSwap hT)

end PSLib
