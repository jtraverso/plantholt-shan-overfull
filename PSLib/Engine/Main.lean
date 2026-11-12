/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Step3Step

/-!
# The engine: Steps 2–4

`engine`: from an initial partial colouring with `k` colours satisfying `Inv2`, and numerical
conditions on the degrees, the whole multigraph has a proper edge colouring with `Δ` colours.

* Step 2 (`step2`) makes every old colour present everywhere;
* Step 3 (`exists_R_colouring`, `J_step`) colours the remaining inner edges with `l` new colours and
  completes every new colour class to all vertices outside the filler sets `F j ⊆ L`;
* Step 4: the remaining crossing edges form a bipartite graph of maximum degree at most
  `Δ − k − l`, coloured by Kőnig's theorem (`exists_konig`).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → V × V} {A : Finset V} {k l : ℕ}
  {col : E → Option (Fin k)} {c3 : E → Fin l}

theorem J_all (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hs : XSimple ends A)
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
    (h4 : 4 * τT ≤ n) :
    ∀ (m : ℕ) (P : Finset (Fin l)) (cx : E → Option (Fin l)) (F : Fin l → Finset V),
      #(univ \ P) = m → J ends A col c3 L P cx F →
      ∃ cx F, J ends A col c3 L univ cx F := by
  intro m
  induction m with
  | zero =>
    intro P cx F hm hJ
    have : P = univ := by
      rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hm; exact eq_univ_of_forall fun j => hm (mem_univ j)
    exact ⟨cx, F, this ▸ hJ⟩
  | succ m ih =>
    intro P cx F hm hJ
    obtain ⟨j, hj⟩ : (univ \ P).Nonempty := by rw [← card_pos]; omega
    have hjP : j ∉ P := (mem_sdiff.1 hj).2
    obtain ⟨cx', F', hJ'⟩ := J_step hloop hs hA hB hP hcov hc3 hcA hcB hcase hTA hTB HG3 HT3 h4 hJ
      hjP
    refine ih (insert j P) cx' F' ?_ hJ'
    have : univ \ insert j P = (univ \ P).erase j := by
      ext x; simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_erase]; tauto
    rw [this, card_erase_of_mem hj, hm]; rfl

/-- The degree count for Step 4. -/
theorem step4_count (hprop : Proper ends col)
    (hcov : ∀ c v, Covers ends col c v) {L : Finset V} {cx : E → Option (Fin l)}
    {F : Fin l → Finset V} (hJ : J ends A col c3 L univ cx F) (v : V) :
    #(univ.filter fun e => ¬ Inner ends A e ∧ col e = none ∧ cx e = none ∧ Incident ends e v) +
      k + l ≤ dx ends A v + din ends A v + #(univ.filter fun j => v ∈ F j) := by
  classical
  set U := univ.filter fun e => ¬ Inner ends A e ∧ col e = none ∧ cx e = none ∧ Incident ends e v
  have h1 := miss_add_din_add_ccol (A := A) hprop v
  rw [miss_eq_zero hcov] at h1
  -- `dx = ccol + ccx + U`
  have h2 : dx ends A v = ccol ends A col v + ccx ends A cx v + #U := by
    unfold dx ccol ccx
    rw [← card_union_of_disjoint, ← card_union_of_disjoint]
    · congr 1; ext e
      simp only [U, mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨hx, hv⟩
        by_cases hc : col e = none
        · by_cases hc' : cx e = none
          · exact Or.inr ⟨hx, hc, hc', hv⟩
          · exact Or.inl (Or.inr ⟨hx, hc', hv⟩)
        · exact Or.inl (Or.inl ⟨hx, hc, hv⟩)
      · rintro ((⟨hx, -, hv⟩ | ⟨hx, -, hv⟩) | ⟨hx, -, -, hv⟩) <;> exact ⟨hx, hv⟩
    · rw [disjoint_union_left]
      constructor
      · rw [disjoint_filter]; intro e _ h h'; exact h.2.1 h'.2.1
      · rw [disjoint_filter]; intro e _ h h'; exact h.2.1 h'.2.2.1
    · rw [disjoint_filter]; intro e _ h h'
      exact h.2.1 (hJ.j1 e h'.2.1).2
  -- the new colours present at `v`
  set C := univ.filter fun e => lc ends A col c3 cx e ≠ none ∧ Incident ends e v
  have h3 : #C ≤ rdeg ends A col v + ccx ends A cx v := by
    unfold rdeg ccx
    refine (card_le_card fun e he => ?_).trans (card_union_le _ _)
    obtain ⟨hne, hev⟩ := (mem_filter.1 he).2
    unfold lc at hne
    by_cases hR : Inner ends A e ∧ col e = none
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hR.1, hR.2, hev⟩)
    · rw [if_neg hR] at hne
      exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, (hJ.j1 e hne).1, hne, hev⟩)
  have h4 : #(univ.filter fun j => v ∉ F j) ≤ #C := by
    have hsurj : (univ.filter fun j => v ∉ F j).map ⟨some, Option.some_injective _⟩ ⊆
        C.image (lc ends A col c3 cx) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hx
      obtain ⟨e, hev, he⟩ := hJ.j4 j (mem_univ _) v (mem_filter.1 hj).2
      exact mem_image.2 ⟨e, mem_filter.2 ⟨mem_univ _, by rw [he]; simp, hev⟩, he⟩
    have := (card_le_card hsurj).trans card_image_le
    rwa [card_map] at this
  have h5 := card_filter_add_card_filter_not (s := (univ : Finset (Fin l))) (fun j => v ∈ F j)
  rw [card_univ, Fintype.card_fin] at h5
  omega

variable (A) in
/-- The end of a crossing edge in `A`. -/
def aE (ends : E → V × V) (e : E) : V := if (ends e).1 ∈ A then (ends e).1 else (ends e).2

variable (A) in
/-- The end of a crossing edge outside `A`. -/
def bE (ends : E → V × V) (e : E) : V := if (ends e).1 ∈ A then (ends e).2 else (ends e).1

theorem crossing_ends {e : E} (hx : ¬ Inner ends A e) :
    Incident ends e (aE A ends e) ∧ Incident ends e (bE A ends e) ∧ aE A ends e ∈ A ∧
      bE A ends e ∉ A ∧ ∀ v, Incident ends e v → (v ∈ A → v = aE A ends e) ∧
        (v ∉ A → v = bE A ends e) := by
  unfold Inner at hx
  unfold aE bE Incident
  by_cases h : (ends e).1 ∈ A
  · have h2 : (ends e).2 ∉ A := fun h' => hx ⟨fun _ => h', fun _ => h⟩
    simp only [if_pos h]
    refine ⟨by simp, by simp, h, h2, fun v hv => ?_⟩
    rcases hv with rfl | rfl
    · exact ⟨fun _ => rfl, fun h' => absurd h h'⟩
    · exact ⟨fun h' => absurd h' h2, fun _ => rfl⟩
  · have h2 : (ends e).2 ∈ A := by
      by_contra h'; exact hx ⟨fun h'' => absurd h'' h, fun h'' => absurd h'' h'⟩
    simp only [if_neg h]
    refine ⟨by simp, by simp, h2, h, fun v hv => ?_⟩
    rcases hv with rfl | rfl
    · exact ⟨fun h' => absurd h' h, fun _ => rfl⟩
    · exact ⟨fun _ => rfl, fun h' => absurd h2 h'⟩

theorem oth_eq {e : E} {v w : V} (hv : Incident ends e v) (hw : Incident ends e w) (hvw : v ≠ w) :
    (if (ends e).1 = v then (ends e).2 else (ends e).1) = w := by
  unfold Incident at hv hw
  by_cases h : (ends e).1 = v
  · rw [if_pos h]
    rcases hw with hw | hw
    · exact absurd (h.symm.trans hw) hvw
    · exact hw
  · rw [if_neg h]
    rcases hv with hv | hv
    · exact absurd hv h
    · rcases hw with hw | hw
      · exact hw
      · exact absurd (hv.symm.trans hw) hvw

open Classical in
/-- **Step 4 and assembly.** -/
theorem step4 (hs : XSimple ends A) {n Δ : ℕ} {L : Finset V} (hA : #A = n) (hB : #Aᶜ = n)
    (hprop : Proper ends col) (hcov : ∀ c v, Covers ends col c v) {cx : E → Option (Fin l)}
    {F : Fin l → Finset V} (hJ : J ends A col c3 L univ cx F) (hl0 : 0 < l) (hkl : k + l ≤ Δ)
    (hΔ : ∀ v, dx ends A v + din ends A v ≤ Δ)
    (hL : ∀ v ∈ L, dx ends A v + din ends A v + l ≤ Δ) :
    ∃ fc : E → Fin Δ, IsProperEdgeColouring ends fc := by
  set D := Δ - k - l
  set U : V → Finset E := fun v =>
    univ.filter fun e => ¬ Inner ends A e ∧ col e = none ∧ cx e = none ∧ Incident ends e v
  have hU : ∀ v, #(U v) ≤ D := by
    intro v
    have h1 : #(U v) + k + l ≤ dx ends A v + din ends A v + #(univ.filter fun j => v ∈ F j) :=
      step4_count hprop hcov hJ v
    by_cases hvL : v ∈ L
    · have : #(univ.filter fun j => v ∈ F j) ≤ l := by
        have := card_le_univ (univ.filter fun j => v ∈ F j); rwa [Fintype.card_fin] at this
      have := hL v hvL; omega
    · have : #(univ.filter fun j => v ∈ F j) = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]; exact fun j _ h => hvL (hJ.j5 j h)
      have := hΔ v; omega
  let α := {a // a ∈ A}
  let β := {b // b ∈ Aᶜ}
  have hcard : Fintype.card α = Fintype.card β := by
    rw [Fintype.card_coe, Fintype.card_coe, hA, hB]
  let Rel : α → β → Prop := fun a b => ∃ e, ¬ Inner ends A e ∧ col e = none ∧ cx e = none ∧
    Incident ends e a.1 ∧ Incident ends e b.1
  let oth : V → E → V := fun v e => if (ends e).1 = v then (ends e).2 else (ends e).1
  have hxdeg : ∀ a : α, #(univ.filter fun b : β => Rel a b) ≤ D := by
    intro a
    rw [card_filter_subtype Aᶜ (fun b => ∃ e, ¬ Inner ends A e ∧ col e = none ∧ cx e = none ∧
      Incident ends e a.1 ∧ Incident ends e b)]
    refine le_trans ?_ (hU a.1)
    refine le_trans (card_le_card (t := (U a.1).image (oth a.1)) ?_) card_image_le
    intro b hb
    obtain ⟨hbB, e, hx, hc, hc', hea, heb⟩ := mem_filter.1 hb
    have hab : a.1 ≠ b := fun h => mem_compl.1 hbB (h ▸ a.2)
    exact mem_image.2 ⟨e, mem_filter.2 ⟨mem_univ _, hx, hc, hc', hea⟩, oth_eq hea heb hab⟩
  have hydeg : ∀ b : β, #(univ.filter fun a : α => Rel a b) ≤ D := by
    intro b
    rw [card_filter_subtype A (fun a => ∃ e, ¬ Inner ends A e ∧ col e = none ∧ cx e = none ∧
      Incident ends e a ∧ Incident ends e b.1)]
    refine le_trans ?_ (hU b.1)
    refine le_trans (card_le_card (t := (U b.1).image (oth b.1)) ?_) card_image_le
    intro a ha
    obtain ⟨haA, e, hx, hc, hc', hea, heb⟩ := mem_filter.1 ha
    have hab : b.1 ≠ a := fun h => mem_compl.1 b.2 (h ▸ haA)
    exact mem_image.2 ⟨e, mem_filter.2 ⟨mem_univ _, hx, hc, hc', heb⟩, oth_eq heb hea hab⟩
  obtain ⟨σ, hσinj, hσ⟩ := exists_konig hcard Rel D hxdeg hydeg
  -- the colouring with values in `Fin k ⊕ (Fin l ⊕ Fin D)`
  let kon : E → Option (Fin D) := fun e =>
    if h : ∃ j : Fin D, ∃ (ha : aE A ends e ∈ A) (hb : bE A ends e ∈ Aᶜ),
      σ j ⟨aE A ends e, ha⟩ = ⟨bE A ends e, hb⟩ then some h.choose else none
  let fc0 : E → Option (Fin k ⊕ (Fin l ⊕ Fin D)) := fun e =>
    (col e).elim
      (if Inner ends A e then some (Sum.inr (Sum.inl (c3 e))) else
        (cx e).elim ((kon e).map fun j => Sum.inr (Sum.inr j)) fun j => some (Sum.inr (Sum.inl j)))
      fun c => some (Sum.inl c)
  -- classification of the values
  have hcls : ∀ e x, fc0 e = some x →
      (∃ c, x = Sum.inl c ∧ col e = some c) ∨
      (∃ j, x = Sum.inr (Sum.inl j) ∧ lc ends A col c3 cx e = some j) ∨
      (∃ j, x = Sum.inr (Sum.inr j) ∧ ¬ Inner ends A e ∧ ∃ (ha : aE A ends e ∈ A)
        (hb : bE A ends e ∈ Aᶜ), σ j ⟨aE A ends e, ha⟩ = ⟨bE A ends e, hb⟩) := by
    intro e x hx
    rcases hce : col e with _ | c
    · simp only [fc0, hce, Option.elim_none] at hx
      by_cases hi : Inner ends A e
      · rw [if_pos hi] at hx
        right; left
        exact ⟨c3 e, (Option.some_injective _ hx).symm, by simp [lc, hi, hce]⟩
      · rw [if_neg hi] at hx
        rcases hcx : cx e with _ | j
        · simp only [hcx, Option.elim_none] at hx
          obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 hx
          simp only [kon] at hj
          split_ifs at hj with h
          right; right
          refine ⟨j, rfl, hi, ?_⟩
          have := h.choose_spec
          rw [Option.some_injective _ hj] at this
          exact this
        · simp only [hcx, Option.elim_some] at hx
          right; left
          refine ⟨j, (Option.some_injective _ hx).symm, ?_⟩
          simp [lc, hi, hcx]
    · simp only [fc0, hce, Option.elim_some] at hx
      left; exact ⟨c, (Option.some_injective _ hx).symm, rfl⟩
  have htot : ∀ e, fc0 e ≠ none := by
    intro e
    rcases hce : col e with _ | c
    · simp only [fc0, hce, Option.elim_none]
      by_cases hi : Inner ends A e
      · rw [if_pos hi]; simp
      · rw [if_neg hi]
        rcases hcx : cx e with _ | j
        · simp only [Option.elim_none, ne_eq, Option.map_eq_none_iff]
          obtain ⟨hea, heb, haA, hbA, -⟩ := crossing_ends (e := e) hi
          obtain ⟨j, hj⟩ := hσ ⟨_, haA⟩ ⟨_, mem_compl.2 hbA⟩ ⟨e, hi, hce, hcx, hea, heb⟩
          simp only [kon]
          rw [dif_pos ⟨j, haA, mem_compl.2 hbA, hj⟩]; simp
        · simp
    · simp [fc0, hce]
  have hproper : ∀ e f, e ≠ f → (∃ v, Incident ends e v ∧ Incident ends f v) →
      fc0 e ≠ fc0 f := by
    rintro e f hef ⟨v, hev, hfv⟩ heq
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (htot e)
    have hy : fc0 f = some x := heq ▸ hx
    rcases hcls e x hx with ⟨c, rfl, hc⟩ | ⟨j, rfl, hj⟩ | ⟨j, rfl, hxe, hae, hbe, hje⟩
    · rcases hcls f _ hy with ⟨c', hc', hf⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
      · cases hc'; exact hef (hprop.eq_of_incident hc hf hev hfv)
      · cases h
      · cases h
    · rcases hcls f _ hy with ⟨_, h, _⟩ | ⟨j', hj', hf⟩ | ⟨_, h, _⟩
      · cases h
      · cases hj'
        exact hJ.j3 e f hef v hev hfv (by rw [hj]; simp) (hj.trans hf.symm)
      · cases h
    · rcases hcls f _ hy with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨j', hj', hxf, haf, hbf, hjf⟩
      · cases h
      · cases h
      · cases hj'
        obtain ⟨hea, heb, -, -, hve⟩ := crossing_ends (e := e) hxe
        obtain ⟨hfa, hfb, -, -, hvf⟩ := crossing_ends (e := f) hxf
        have hne : aE A ends e ≠ bE A ends e := fun h => mem_compl.1 hbe (h ▸ hae)
        by_cases hvA : v ∈ A
        · have h1 := (hve v hev).1 hvA
          have h2 := (hvf v hfv).1 hvA
          have h12 : aE A ends e = aE A ends f := h1.symm.trans h2
          have h3 : bE A ends e = bE A ends f := by
            have : (⟨aE A ends e, hae⟩ : α) = ⟨aE A ends f, haf⟩ := Subtype.ext h12
            rw [this] at hje
            exact congrArg Subtype.val (hje.symm.trans hjf)
          exact hef (hs e f hxe hxf _ _ hne hea heb (h12 ▸ hfa) (h3 ▸ hfb))
        · have h1 := (hve v hev).2 hvA
          have h2 := (hvf v hfv).2 hvA
          have h12 : bE A ends e = bE A ends f := h1.symm.trans h2
          have h3 : aE A ends e = aE A ends f := by
            have : (⟨bE A ends e, hbe⟩ : β) = ⟨bE A ends f, hbf⟩ := Subtype.ext h12
            rw [this] at hje
            exact congrArg Subtype.val (hσinj j (hje.trans hjf.symm))
          exact hef (hs e f hxe hxf _ _ hne hea heb (h3 ▸ hfa) (h12 ▸ hfb))
  -- the final palette
  have hsum : k + (l + D) = Δ := by omega
  let emb : Fin k ⊕ (Fin l ⊕ Fin D) → Fin Δ := fun x =>
    Fin.cast hsum (finSumFinEquiv (Sum.map id finSumFinEquiv x))
  have hemb : Function.Injective emb := by
    intro x y h
    simp only [emb] at h
    have := finSumFinEquiv.injective (Fin.cast_injective hsum h)
    exact Sum.map_injective.2 ⟨Function.injective_id, finSumFinEquiv.injective⟩ this
  refine ⟨fun e => emb ((fc0 e).getD (Sum.inr (Sum.inl ⟨0, hl0⟩))), fun e f hef hv h => ?_⟩
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (htot e)
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (htot f)
  have h' : emb x = emb y := by simpa [hx, hy] using h
  exact hproper e f hef hv (by rw [hx, hy, hemb h'])

theorem mu_eq_zero {col : E → Option (Fin k)} (hcov : ∀ c v, Covers ends col c v) (S : Finset V) :
    mu ends col S = 0 := by
  unfold mu missed
  refine sum_eq_zero fun c _ => ?_
  rw [card_eq_zero, filter_eq_empty_iff]; exact fun v _ h => h (hcov c v)

/-- **The engine** (Steps 2–4 of Plantholt–Shan, Section 4). -/
theorem engine (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hs : XSimple ends A)
    {n τT t K X KA KB Δ : ℕ} {T L : Finset V} (hA : #A = n) (hB : #Aᶜ = n) (ht : 0 < t)
    (hTA : #(T ∩ A) ≤ τT) (hTB : #(T ∩ Aᶜ) ≤ τT)
    (HG : ∀ w, w ∉ T → n + 2 * (k + t + X / 2 + (X + 1) + 2 * τT + 2 * (2 * (K / 2 + 1) / t)) <
      2 * (dx ends A w + din ends A w))
    (HT : ∀ w, w ∈ T → k + X / 2 + (X + 1) + 2 * τT + 2 * (2 * (K / 2 + 1) / t) <
      dx ends A w + din ends A w)
    (hl : 3 * t / 2 ≤ l) (hl0 : 0 < l)
    (HG3 : ∀ w, w ∉ T → n + 2 * (k + t + l + 2 * (K / 2 / l + 1)) <
      2 * (dx ends A w + din ends A w))
    (HT3 : ∀ w, w ∈ T → k + l + 2 * (K / 2 / l + 1) + 2 * τT ≤ dx ends A w + din ends A w)
    (h4 : 4 * τT ≤ n) (hkl : k + l ≤ Δ) (hΔ : ∀ v, dx ends A v + din ends A v ≤ Δ)
    (hL : ∀ v ∈ L, dx ends A v + din ends A v + l ≤ Δ)
    (hcase : KA = KB ∨ (4 * (K / 2 / l + 1) ≤ #(L ∩ A) ∧ 4 * (K / 2 / l + 1) ≤ #(L ∩ Aᶜ)))
    (col0 : E → Option (Fin k)) (h0 : Inv2 ends A T t K X KA KB col0) :
    ∃ fc : E → Fin Δ, IsProperEdgeColouring ends fc := by
  obtain ⟨col, hI, hcov⟩ := step2 hloop hs hA hB ht hTA hTB HG HT _ col0 rfl h0
  obtain ⟨c3, hc3, hcA, hcB, hbal⟩ := exists_R_colouring (l := l) hloop hI.toPre hl hl0
  have hpot := hI.pot
  have hphi := hI.phi
  rw [mu_eq_zero hcov, mu_eq_zero hcov] at hphi
  have hrA : rsize ends A col A / l ≤ K / 2 / l := Nat.div_le_div_right (by omega)
  have hrB : rsize ends A col Aᶜ / l ≤ K / 2 / l := Nat.div_le_div_right (by omega)
  have hcA' : ∀ j, cls (Rside ends A col A) c3 j ≤ K / 2 / l + 1 := fun j => by
    have := hcA j; omega
  have hcB' : ∀ j, cls (Rside ends A col Aᶜ) c3 j ≤ K / 2 / l + 1 := fun j => by
    have := hcB j; omega
  have hcase' : (∀ j, cls (Rside ends A col A) c3 j = cls (Rside ends A col Aᶜ) c3 j) ∨
      (4 * (K / 2 / l + 1) ≤ #(L ∩ A) ∧ 4 * (K / 2 / l + 1) ≤ #(L ∩ Aᶜ)) := by
    rcases hcase with h | h
    · left; exact hbal (by omega)
    · right; exact h
  obtain ⟨cx, F, hJ⟩ := J_all hloop hs hA hB hI.toPre hcov hc3 hcA' hcB' hcase' hTA hTB HG3 HT3 h4
    _ ∅ (fun _ => none) (fun _ => ∅) rfl (J.init hc3 L)
  exact step4 hs hA hB hI.proper hcov hJ hl0 hkl hΔ hL

end PSLib.Eng
