/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Thm12Iter
public import PSLib.Thm12Groups

/-!
# The reductions of Theorem 1.2

`defi G D = ∑_v (D − d(v))` is the total deficiency. For a graph of even order and high minimum
degree, `G` has no `D`-overfull subgraph iff `2D ≤ defi G D + 2 d(z)` for every vertex `z`.

* `case1_step`: removing a perfect matching of `G − W`, where `W` contains every vertex of minimum
  degree, lowers `D` by one and keeps all hypotheses (Case 1 of Plantholt–Shan).
* `case3_rounds`: for `x ≠ y` of minimum degree and all degrees in `{δ, D}`, removing `g/2` pairs
  of perfect matchings of `G − (V_δ ∖ {x})` and `G − (V_δ ∖ {y})` leaves a graph of Condition (b).
* `case2_regular`: removing pairs of perfect matchings along the groups of `exists_groups` makes
  the graph regular (Case 2).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset SimpleGraph Real
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The total deficiency. -/
noncomputable def defi (G : SimpleGraph V) (D : ℕ) : ℕ := ∑ v, (D - G.degree v)

/-- **Case 1: one step.** -/
theorem case1_step {q n D δ : ℕ} (G : SimpleGraph V)
    (hd : ∀ v, (q + 1) * n ≤ q * G.degree v ∧ G.degree v ≤ D) (hδ : ∀ v, δ ≤ G.degree v)
    {x : V} (hx : G.degree x = δ) (W : Finset V) (hWδ : ∀ v, G.degree v = δ → v ∈ W)
    (hWlt : ∀ v ∈ W, G.degree v < D) (hkey : #W + 2 * D ≤ defi G D + 2 * δ + 2)
    (τ : V → V) (hτ : ∀ v, v ∉ W → τ v ∉ W ∧ τ (τ v) = v ∧ G.Adj v (τ v)) :
    (∀ v, (q + 1) * n ≤ q * (G \ pmGraph W τ).degree v ∧ (G \ pmGraph W τ).degree v ≤ D - 1) ∧
      (∀ z, 2 * (D - 1) ≤ defi (G \ pmGraph W τ) (D - 1) + 2 * (G \ pmGraph W τ).degree z) ∧
      ∀ a, (G \ pmGraph W τ).lineGraph.Colorable a → G.lineGraph.Colorable (a + 1) := by
  obtain ⟨hdeg, hcol⟩ := remove_pm G W τ hτ
  set G₁ := G \ pmGraph W τ
  have hxW : x ∈ W := hWδ x hx
  have hδD : δ < D := hx ▸ hWlt x hxW
  have hlow : ∀ v, δ ≤ G₁.degree v := by
    intro v; have h1 := hdeg v; have h2 := hδ v
    by_cases hv : v ∈ W
    · rw [if_pos hv] at h1; omega
    · rw [if_neg hv] at h1
      have : G.degree v ≠ δ := fun h => hv (hWδ v h)
      omega
  have hqx := (hd x).1
  have hterm : ∀ v, (D - 1 - G₁.degree v) + (if v ∈ W then 1 else 0) = D - G.degree v := by
    intro v
    have h1 := hdeg v; have := (hd v).2; have := hlow v; have := hδ v
    by_cases hv : v ∈ W
    · rw [if_pos hv] at h1 ⊢; have := hWlt v hv; omega
    · rw [if_neg hv] at h1 ⊢
      have : G.degree v ≠ δ := fun h => hv (hWδ v h)
      omega
  have hsum : defi G₁ (D - 1) + #W = defi G D := by
    have hW : ∑ v, (if v ∈ W then 1 else 0) = #W := by
      rw [sum_boole]; simp
    unfold defi
    rw [← hW, ← sum_add_distrib]
    exact sum_congr rfl fun v _ => hterm v
  refine ⟨fun v => ⟨?_, ?_⟩, fun z => ?_, hcol⟩
  · exact le_trans hqx (Nat.mul_le_mul_left _ (hx ▸ hlow v))
  · have h1 := hdeg v; have := (hd v).2
    by_cases hv : v ∈ W
    · rw [if_pos hv] at h1; have := hWlt v hv; omega
    · rw [if_neg hv] at h1; omega
  · have := hlow z; omega

/-- **Case (iii): the rounds.** -/
theorem case3_rounds {n p δ D : ℕ} (hn : 0 < n) (hV : Fintype.card V = 2 * n)
    (hch : 4 * n * exp (-((p : ℝ) ^ 2 / (2 * n))) < 1) (G : SimpleGraph V) {x y : V}
    (hxy : x ≠ y) (Vδ : Finset V) (hx : x ∈ Vδ) (hy : y ∈ Vδ) (hodd : Odd #Vδ)
    (hdeg : ∀ v, G.degree v = if v ∈ Vδ then δ else D)
    (hnum1 : n + p + 2 * #Vδ + 2 ≤ δ) (hnum2 : p + 2 * #Vδ + 2 + (D - δ) / 2 ≤ δ)
    (htn : 2 + #Vδ ≤ n) :
    ∀ i, 2 * i ≤ D - δ → ∃ Gi : SimpleGraph V,
      (∀ v, Gi.degree v = if v = x ∨ v = y then δ - i else if v ∈ Vδ then δ else D - 2 * i) ∧
        ∀ a, Gi.lineGraph.Colorable a → G.lineGraph.Colorable (a + 2 * i) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨G, fun v => ?_, fun a h => by simpa using h⟩
    rw [hdeg]
    by_cases hv : v = x ∨ v = y
    · rcases hv with rfl | rfl <;> simp [hx, hy]
    · rw [if_neg hv]; simp
  | succ i ih =>
    intro hi
    obtain ⟨Gi, hdi, hci⟩ := ih (by omega)
    have hev1 : Even #(Vδ.erase x) := by
      rw [card_erase_of_mem hx]; obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩
    have hev2 : Even #(Vδ.erase y) := by
      rw [card_erase_of_mem hy]; obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩
    have hc1 : #(Vδ.erase x) ≤ #Vδ := card_erase_le
    have hc2 : #(Vδ.erase y) ≤ #Vδ := card_erase_le
    -- the first matching avoids `V_δ ∖ {x}`
    obtain ⟨τ₁, hτ₁⟩ := exists_pm_avoiding Gi hn hV (Vδ.erase x) hev1 {x} (t0 := 1) hch
      (fun v hv hvx => by
        have hvx' : v ≠ x := by simpa using hvx
        have hvV : v ∉ Vδ := fun h => hv (mem_erase.2 ⟨hvx', h⟩)
        have hvy : v ≠ y := fun h => hvV (h ▸ hy)
        rw [hdi v, if_neg (show ¬(v = x ∨ v = y) by tauto), if_neg hvV]; omega)
      (fun v _ hvx => by
        rw [mem_singleton] at hvx; subst hvx
        rw [hdi, if_pos (Or.inl rfl)]; omega)
      (by simp) (by omega)
    obtain ⟨hd₁, hc₁⟩ := remove_pm Gi (Vδ.erase x) τ₁ hτ₁
    -- the second matching avoids `V_δ ∖ {y}`
    obtain ⟨τ₂, hτ₂⟩ := exists_pm_avoiding (Gi \ pmGraph (Vδ.erase x) τ₁) hn hV (Vδ.erase y) hev2
      {y} (t0 := 1) hch
      (fun v hv hvy => by
        have hvy' : v ≠ y := by simpa using hvy
        have hvV : v ∉ Vδ := fun h => hv (mem_erase.2 ⟨hvy', h⟩)
        have hvx : v ≠ x := fun h => hvV (h ▸ hx)
        have h1 := hd₁ v
        simp only [hdi v, show ¬(v = x ∨ v = y) by tauto, hvV,
          show v ∉ Vδ.erase x from fun h => hvV (mem_of_mem_erase h), if_false] at h1
        omega)
      (fun v _ hvy => by
        rw [mem_singleton] at hvy; subst hvy
        have h1 := hd₁ v
        rw [hdi, if_pos (Or.inr rfl), if_pos (mem_erase.2 ⟨fun h => hxy h.symm, hy⟩)] at h1
        omega)
      (by simp) (by omega)
    obtain ⟨hd₂, hc₂⟩ := remove_pm (Gi \ pmGraph (Vδ.erase x) τ₁) (Vδ.erase y) τ₂ hτ₂
    refine ⟨(Gi \ pmGraph (Vδ.erase x) τ₁) \ pmGraph (Vδ.erase y) τ₂, fun v => ?_, fun a ha => ?_⟩
    · have h1 := hd₁ v; have h2 := hd₂ v; have h3 := hdi v
      by_cases hvx : v = x
      · subst hvx
        rw [if_pos (Or.inl rfl)] at h3 ⊢
        rw [if_neg (show v ∉ Vδ.erase v by simp)] at h1
        rw [if_pos (mem_erase.2 ⟨hxy, hx⟩)] at h2
        omega
      by_cases hvy : v = y
      · subst hvy
        rw [if_pos (Or.inr rfl)] at h3 ⊢
        rw [if_pos (mem_erase.2 ⟨fun h => hxy h.symm, hy⟩)] at h1
        rw [if_neg (show v ∉ Vδ.erase v by simp)] at h2
        omega
      rw [if_neg (show ¬(v = x ∨ v = y) by tauto)] at h3 ⊢
      by_cases hvV : v ∈ Vδ
      · rw [if_pos hvV] at h3 ⊢
        rw [if_pos (mem_erase.2 ⟨hvx, hvV⟩)] at h1
        rw [if_pos (mem_erase.2 ⟨hvy, hvV⟩)] at h2
        omega
      · rw [if_neg hvV] at h3 ⊢
        rw [if_neg (fun h => hvV (mem_of_mem_erase h))] at h1 h2
        omega
    · have := hci _ (hc₁ _ (hc₂ a ha))
      convert this using 1; ring

/-- **Case 2: regularization.** -/
theorem case2_regular {q n p g D δ : ℕ} (hq : 0 < q) (hn : 0 < n) (hV : Fintype.card V = 2 * n)
    (hch : 4 * n * exp (-((p : ℝ) ^ 2 / (2 * n))) < 1) (h16 : 16 * q ≤ n) (G : SimpleGraph V)
    (hd : ∀ v, δ ≤ G.degree v ∧ G.degree v ≤ D) (hg : D - δ ≤ g)
    (hinv : ∀ z, 2 * D ≤ defi G D + 2 * G.degree z)
    (hnum : n + p + 4 * (n / (8 * q)) + 2 * ((3 * g / 2) * (2 * n / (n / (8 * q)) + 1)) ≤ δ) :
    ∃ (G'' : SimpleGraph V) (r : ℕ), (∀ v, G''.degree v + 2 * r = D) ∧
      r = (3 * g / 2) * (2 * n / (n / (8 * q)) + 1) ∧
      ∀ a, G''.lineGraph.Colorable a → G.lineGraph.Colorable (a + 2 * r) := by
  set s0 := n / (8 * q)
  have hs0 : 0 < s0 := Nat.div_pos (by omega) (by omega)
  have h2s : 2 * s0 ≤ n := by
    have h1 : s0 * (8 * q) ≤ n := Nat.div_mul_le_self n (8 * q)
    have h2 : 2 * s0 ≤ s0 * (8 * q) := by nlinarith
    omega
  have hsum : defi G D + ∑ v, G.degree v = 2 * n * D := by
    unfold defi
    rw [← sum_add_distrib, sum_congr rfl fun v _ => Nat.sub_add_cancel (hd v).2, sum_const,
      card_univ, hV, smul_eq_mul]
  have heven : Even (∑ v, (D - G.degree v)) := by
    have h1 := G.sum_degrees_eq_twice_card_edges
    have h3 : Even (defi G D + ∑ v, G.degree v) := ⟨n * D, by rw [hsum]; ring⟩
    have h4 : Even (∑ v, G.degree v) := ⟨#G.edgeFinset, by rw [h1]; ring⟩
    exact (Nat.even_add.1 h3).2 h4
  obtain ⟨W, hW, hcount⟩ := exists_groups hV hs0 (fun v => D - G.degree v)
    (fun v => by show D - G.degree v ≤ g; have := (hd v).1; omega) heven
    (fun v => by
      show 2 * (D - G.degree v) ≤ ∑ u, (D - G.degree u)
      have := hinv v; unfold defi at this; omega)
  obtain ⟨G'', hd'', hc⟩ := iter_pm hn hV hch s0 h2s W hW univ G
    (fun v => by rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
                 have := (hd v).1; omega)
  refine ⟨G'', #(univ : Finset (Fin (3 * g / 2) × Fin (2 * n / s0 + 1))), fun v => ?_, ?_, hc⟩
  · have h1 := hd'' v
    have h2 := hcount v
    have h3 := (hd v).2
    omega
  · rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

end PSLib.Eng
