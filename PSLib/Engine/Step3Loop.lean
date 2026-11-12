/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Step3Colour
public import PSLib.Konig

/-!
# Step 3, second half: completing the new colour classes

After Step 2 every one of the `k` old colours is present at every vertex, and the uncoloured inner
edges `R` carry a proper colouring `c3` with `l` new colours. For each new colour `j` in turn, the
vertices of `A` and `Aᶜ` not covered by the `R`-edges of colour `j` (minus a set `F j ⊆ L` of filler
vertices when the two sides are unbalanced) are matched perfectly by uncoloured crossing edges
(Lemma 2.11), and the matching gets colour `j`. Invariant `J`.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → V × V} {A : Finset V} {k l : ℕ}

variable (ends A) in
/-- The joint colouring by the new colours: `R`-edges by `c3`, crossing edges by `cx`. -/
def lc (col : E → Option (Fin k)) (c3 : E → Fin l) (cx : E → Option (Fin l)) (e : E) :
    Option (Fin l) :=
  if Inner ends A e ∧ col e = none then some (c3 e) else cx e

variable (ends A) in
/-- The number of crossing edges at `v` with a new colour. -/
def ccx (cx : E → Option (Fin l)) (v : V) : ℕ :=
  #(univ.filter fun e => ¬ Inner ends A e ∧ cx e ≠ none ∧ Incident ends e v)

variable (ends A) in
/-- The invariant of the loop of Step 3. -/
structure J (col : E → Option (Fin k)) (c3 : E → Fin l) (L : Finset V) (P : Finset (Fin l))
    (cx : E → Option (Fin l)) (F : Fin l → Finset V) : Prop where
  j1 : ∀ e, cx e ≠ none → ¬ Inner ends A e ∧ col e = none
  j2 : ∀ e j, cx e = some j → j ∈ P
  j3 : ∀ e f, e ≠ f → ∀ v, Incident ends e v → Incident ends f v →
    lc ends A col c3 cx e ≠ none → lc ends A col c3 cx e ≠ lc ends A col c3 cx f
  j4 : ∀ j ∈ P, ∀ v, v ∉ F j → ∃ e, Incident ends e v ∧ lc ends A col c3 cx e = some j
  j5 : ∀ j, F j ⊆ L
  j6 : ∀ v, ccx ends A cx v ≤ #P

variable {col : E → Option (Fin k)} {c3 : E → Fin l}

theorem J.init (hc3 : ProperOn ends (Rset ends A col) c3) (L : Finset V) :
    J ends A col c3 L ∅ (fun _ => none) (fun _ => ∅) := by
  refine ⟨fun e h => absurd rfl h, fun e j h => by simp at h, ?_, fun j hj => by simp at hj,
    fun j => empty_subset _, fun v => by simp [ccx]⟩
  intro e f hef v hev hfv he heq
  unfold lc at he heq
  by_cases hR : Inner ends A e ∧ col e = none
  · rw [if_pos hR] at heq
    by_cases hR' : Inner ends A f ∧ col f = none
    · rw [if_pos hR'] at heq
      exact hc3 e (mem_filter.2 ⟨mem_univ _, hR⟩) f (mem_filter.2 ⟨mem_univ _, hR'⟩) hef
        ⟨v, hev, hfv⟩ (Option.some_injective _ heq)
    · rw [if_neg hR'] at heq; exact Option.some_ne_none _ heq
  · rw [if_neg hR] at he; exact he rfl

variable (ends A) in
/-- The vertices of `S` covered by the `R`-edges of new colour `j` inside `S`. -/
def covR (col : E → Option (Fin k)) (c3 : E → Fin l) (j : Fin l) (S : Finset V) : Finset V :=
  S.filter fun v => ∃ e ∈ Rside ends A col S, c3 e = j ∧ Incident ends e v

theorem card_covR (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hc3 : ProperOn ends (Rset ends A col) c3)
    (j : Fin l) (S : Finset V) (hS : S = A ∨ S = Aᶜ) :
    #(covR ends A col c3 j S) = 2 * cls (Rside ends A col S) c3 j := by
  classical
  set C := (Rside ends A col S).filter fun e => c3 e = j
  have hends : ∀ e ∈ C, ∀ v, Incident ends e v → v ∈ S := by
    intro e he v hv
    have h1 := (mem_filter.1 (mem_filter.1 (mem_filter.1 he).1).1).2.1
    have h2 := (mem_filter.1 (mem_filter.1 he).1).2
    have := side_of_inner h1 (Or.inl rfl) hv
    rcases hS with rfl | rfl
    · exact this.1 h2
    · rw [mem_compl] at h2 ⊢; exact fun h => h2 (this.2 h)
  have hcov : covR ends A col c3 j S = C.biUnion fun e => univ.filter fun v => Incident ends e v := by
    ext v
    simp only [covR, mem_filter, mem_biUnion, mem_univ, true_and, C]
    constructor
    · rintro ⟨-, e, he, hej, hev⟩; exact ⟨e, ⟨he, hej⟩, hev⟩
    · rintro ⟨e, ⟨he, hej⟩, hev⟩
      exact ⟨hends e (mem_filter.2 ⟨he, hej⟩) v hev, e, he, hej, hev⟩
  have hdisj : (C : Set E).PairwiseDisjoint fun e => univ.filter fun v => Incident ends e v := by
    intro e he f hf hef
    rw [Function.onFun, disjoint_left]
    intro v hv hv'
    have he' := mem_filter.1 he
    have hf' := mem_filter.1 hf
    exact hc3 e (mem_filter.1 he'.1).1 f (mem_filter.1 hf'.1).1 hef
      ⟨v, (mem_filter.1 hv).2, (mem_filter.1 hv').2⟩ (he'.2.trans hf'.2.symm)
  rw [hcov, card_biUnion hdisj]
  unfold cls
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun e _ => ?_
  rw [card_filter_incident (e := e) (a := (ends e).1) (b := (ends e).2) (Or.inl rfl) (Or.inr rfl)
    (hloop e)]
  simp

/-- Uncoloured crossing neighbours, for both colourings. -/
theorem card_avail (hs : XSimple ends A) (cx : E → Option (Fin l)) (v : V) :
    dx ends A v ≤ #((side' A v).filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = none ∧
      cx e = none ∧ Incident ends e v ∧ Incident ends e w) + ccol ends A col v + ccx ends A cx v := by
  classical
  set X := univ.filter fun e => ¬ Inner ends A e ∧ col e = none ∧ cx e = none ∧ Incident ends e v
  have hsplit : dx ends A v ≤ #X + ccol ends A col v + ccx ends A cx v := by
    unfold dx ccol ccx
    set Y := univ.filter fun e => ¬ Inner ends A e ∧ col e ≠ none ∧ Incident ends e v
    set Z := univ.filter fun e => ¬ Inner ends A e ∧ cx e ≠ none ∧ Incident ends e v
    have h1 : (univ.filter fun e => ¬ Inner ends A e ∧ Incident ends e v) ⊆ X ∪ Y ∪ Z := by
      intro e he
      obtain ⟨hx, hv⟩ := (mem_filter.1 he).2
      simp only [X, Y, Z, mem_union, mem_filter, mem_univ, true_and]
      by_cases hc : col e = none
      · by_cases hc' : cx e = none
        · exact Or.inl (Or.inl ⟨hx, hc, hc', hv⟩)
        · exact Or.inr ⟨hx, hc', hv⟩
      · exact Or.inl (Or.inr ⟨hx, hc, hv⟩)
    have h2 := card_le_card h1
    have h3 := card_union_le (X ∪ Y) Z
    have h4 := card_union_le X Y
    omega
  let oth : E → V := fun e => if (ends e).1 = v then (ends e).2 else (ends e).1
  have hoth : ∀ e ∈ X, Incident ends e (oth e) ∧ v ≠ oth e := by
    intro e he
    obtain ⟨hx, -, -, hv⟩ := (mem_filter.1 he).2
    simp only [oth]
    split_ifs with h1
    · exact ⟨Or.inr rfl, fun h => ne_of_crossing hx h1 h.symm rfl⟩
    · exact ⟨Or.inl rfl, fun h => h1 h.symm⟩
  have hmaps : ∀ e ∈ X, oth e ∈ (side' A v).filter fun w => ∃ e, ¬ Inner ends A e ∧ col e = none ∧
      cx e = none ∧ Incident ends e v ∧ Incident ends e w := by
    intro e he
    obtain ⟨hx, hc, hc', hv⟩ := (mem_filter.1 he).2
    refine mem_filter.2 ⟨mem_side'.2 (side_of_crossing hx hv (hoth e he).1 (hoth e he).2),
      e, hx, hc, hc', hv, (hoth e he).1⟩
  have hinj : Set.InjOn oth X := by
    intro e he f hf hef
    exact hs e f (mem_filter.1 he).2.1 (mem_filter.1 hf).2.1 v (oth e) (hoth e he).2
      (mem_filter.1 he).2.2.2.2 (hoth e he).1 (mem_filter.1 hf).2.2.2.2 (hef ▸ (hoth f hf).1)
  have := card_le_card_of_injOn oth hmaps hinj
  omega

/-- The filter of a subtype, as a filter of the ambient finset. -/
theorem card_filter_subtype (X : Finset V) (p : V → Prop) [DecidablePred p] :
    #(univ.filter fun x : {v // v ∈ X} => p x) = #(X.filter p) := by
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1; ext v
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
  · rintro ⟨hv, hp⟩; exact ⟨⟨v, hv⟩, hp, rfl⟩

/-- Fillers: a set `F ⊆ L` balancing the two sides. -/
theorem exists_fillers {n cmax : ℕ} (hA : #A = n) (hB : #Aᶜ = n) {L AJ BJ : Finset V}
    (hAJ : AJ ⊆ A) (hBJ : BJ ⊆ Aᶜ) (hAJc : #AJ ≤ 2 * cmax) (hBJc : #BJ ≤ 2 * cmax)
    (hcase : #AJ = #BJ ∨ (4 * cmax ≤ #(L ∩ A) ∧ 4 * cmax ≤ #(L ∩ Aᶜ))) :
    ∃ F ⊆ L, #(A \ (AJ ∪ F)) = #(Aᶜ \ (BJ ∪ F)) ∧ #(A ∩ (AJ ∪ F)) ≤ 2 * cmax ∧
      #(Aᶜ ∩ (BJ ∪ F)) ≤ 2 * cmax := by
  classical
  have key : ∀ (X : Finset V) (Y G : Finset V), X ⊆ A → G ⊆ A → Disjoint X G →
      #(A \ (X ∪ G)) + #X + #G = n := by
    intro X Y G hX hG hXG
    have h1 : X ∪ G ⊆ A := union_subset hX hG
    have h2 := card_le_card h1
    rw [card_union_of_disjoint hXG, hA] at h2
    rw [card_sdiff_of_subset h1, card_union_of_disjoint hXG, hA]
    omega
  have keyB : ∀ (X G : Finset V), X ⊆ Aᶜ → G ⊆ Aᶜ → Disjoint X G →
      #(Aᶜ \ (X ∪ G)) + #X + #G = n := by
    intro X G hX hG hXG
    have h1 : X ∪ G ⊆ Aᶜ := union_subset hX hG
    have h2 := card_le_card h1
    rw [card_union_of_disjoint hXG, hB] at h2
    rw [card_sdiff_of_subset h1, card_union_of_disjoint hXG, hB]
    omega
  have hinterA : ∀ G : Finset V, G ⊆ Aᶜ → A ∩ (AJ ∪ G) = AJ := by
    intro G hG; ext v; simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨hv, h | h⟩
      · exact h
      · exact absurd hv (mem_compl.1 (hG h))
    · intro h; exact ⟨hAJ h, Or.inl h⟩
  have hinterB : ∀ G : Finset V, G ⊆ A → Aᶜ ∩ (BJ ∪ G) = BJ := by
    intro G hG; ext v; simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨hv, h | h⟩
      · exact h
      · exact absurd (hG h) (mem_compl.1 hv)
    · intro h; exact ⟨hBJ h, Or.inl h⟩
  have hsdA : ∀ G : Finset V, G ⊆ Aᶜ → A \ (AJ ∪ G) = A \ AJ := by
    intro G hG; ext v; simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hv, h⟩; exact ⟨hv, fun h' => h (Or.inl h')⟩
    · rintro ⟨hv, h⟩
      refine ⟨hv, fun h' => h'.elim h fun h'' => mem_compl.1 (hG h'') hv⟩
  have hsdB : ∀ G : Finset V, G ⊆ A → Aᶜ \ (BJ ∪ G) = Aᶜ \ BJ := by
    intro G hG; ext v; simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hv, h⟩; exact ⟨hv, fun h' => h (Or.inl h')⟩
    · rintro ⟨hv, h⟩
      refine ⟨hv, fun h' => h'.elim h fun h'' => mem_compl.1 hv (hG h'')⟩
  have hcA : #(A \ AJ) + #AJ = n := by rw [card_sdiff_of_subset hAJ, hA]; have := card_le_card hAJ; omega
  have hcB : #(Aᶜ \ BJ) + #BJ = n := by rw [card_sdiff_of_subset hBJ, hB]; have := card_le_card hBJ; omega
  rcases hcase with heq | ⟨hLA, hLB⟩
  · refine ⟨∅, empty_subset _, ?_, ?_, ?_⟩
    · simp only [union_empty]; omega
    · rw [union_empty, inter_eq_right.2 hAJ]; exact hAJc
    · rw [union_empty, inter_eq_right.2 hBJ]; exact hBJc
  · by_cases hle : #AJ ≤ #BJ
    · have hroom : #BJ - #AJ ≤ #((L ∩ A) \ AJ) := by
        have := le_card_sdiff AJ (L ∩ A); omega
      obtain ⟨G, hG, hGc⟩ := exists_subset_card_eq hroom
      have hGA : G ⊆ A := fun v hv => (mem_inter.1 (mem_sdiff.1 (hG hv)).1).2
      have hGL : G ⊆ L := fun v hv => (mem_inter.1 (mem_sdiff.1 (hG hv)).1).1
      have hdisj : Disjoint AJ G := by
        rw [disjoint_left]; intro v hv hv'; exact (mem_sdiff.1 (hG hv')).2 hv
      refine ⟨G, hGL, ?_, ?_, ?_⟩
      · have := key AJ AJ G hAJ hGA hdisj
        rw [hsdB G hGA]; omega
      · rw [inter_eq_right.2 (union_subset hAJ hGA), card_union_of_disjoint hdisj]; omega
      · rw [hinterB G hGA]; exact hBJc
    · have hroom : #AJ - #BJ ≤ #((L ∩ Aᶜ) \ BJ) := by
        have := le_card_sdiff BJ (L ∩ Aᶜ); omega
      obtain ⟨G, hG, hGc⟩ := exists_subset_card_eq hroom
      have hGB : G ⊆ Aᶜ := fun v hv => (mem_inter.1 (mem_sdiff.1 (hG hv)).1).2
      have hGL : G ⊆ L := fun v hv => (mem_inter.1 (mem_sdiff.1 (hG hv)).1).1
      have hdisj : Disjoint BJ G := by
        rw [disjoint_left]; intro v hv hv'; exact (mem_sdiff.1 (hG hv')).2 hv
      refine ⟨G, hGL, ?_, ?_, ?_⟩
      · have := keyB BJ G hBJ hGB hdisj
        rw [hsdA G hGB]; omega
      · rw [hinterA G hGB]; exact hAJc
      · rw [inter_eq_right.2 (union_subset hBJ hGB), card_union_of_disjoint hdisj]; omega

end PSLib.Eng
