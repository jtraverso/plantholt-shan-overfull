/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Thm12Cases
public import PSLib.Thm12Params
public import PSLib.Thm13c
public import LeanPool.Vizing.Main

/-!
# Plantholt–Shan, Theorem 1.2: the core

`thm12_of_ge`: for `q ≥ 1` there is `N` such that every graph on `2n ≥ 2N` vertices with all
degrees `d(v)` satisfying `(q + 1) n ≤ q d(v) ≤ q D` and `2D ≤ defi G D + 2 d(z)` for every `z`
(no `D`-overfull subgraph) is `D`-edge-colourable.

Induction on `D`, with `δ = δ(G)`, `g = D − δ` and `n₁ = |V_δ|`:
* no vertex of degree `D`: Vizing;
* `g = 0`: the regular case (Perković–Reed, registered);
* `g, n₁ ≥ n^{6/7}`: Theorem 1.3 (c);
* `g < n^{6/7}`: Case 2 (`case2_regular`, then the regular case);
* otherwise Case 1: `case1_step` (then induction), or `case3_rounds` and Theorem 1.3 (b).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset SimpleGraph Real
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable

universe u

theorem num_case2 {q n p A δ g s0 K : ℕ} (hq : 0 < q) (hδ : n ≤ q * (δ - n)) (hδn : n ≤ δ)
    (hs0 : 8 * q * s0 ≤ n) (hK : K ≤ 32 * q + 1) (hgA : q * g ≤ 2 ^ 18 * A)
    (hbig : 4 * q * (p + 2 ^ 30 * A + 64 * q + 64) ≤ n) :
    n + p + 4 * s0 + 2 * ((3 * g / 2) * K) ≤ δ ∧ 4 * (2 * ((3 * g / 2) * K)) ≤ δ - n := by
  have h1 : 4 * (p + 2 ^ 30 * A) ≤ δ - n := by
    have : q * (4 * (p + 2 ^ 30 * A)) ≤ q * (δ - n) := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hq
  have h2 : 8 * s0 ≤ δ - n := by
    have : q * (8 * s0) ≤ q * (δ - n) := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hq
  have h3 : (3 * g / 2) * K ≤ 2 ^ 26 * A := by
    have e1 : 3 * g / 2 ≤ 2 * g := by omega
    calc (3 * g / 2) * K ≤ 2 * g * (32 * q + 1) := Nat.mul_le_mul e1 hK
      _ ≤ 2 * g * (33 * q) := by nlinarith
      _ = 66 * (q * g) := by ring
      _ ≤ 66 * (2 ^ 18 * A) := Nat.mul_le_mul_left _ hgA
      _ ≤ 2 ^ 26 * A := by nlinarith
  norm_num at h1 h3 ⊢
  constructor <;> omega

theorem num_small {q n p A δ m : ℕ} (hq : 0 < q) (hδ : n ≤ q * (δ - n)) (hδn : n ≤ δ)
    (hm : m ≤ 2 ^ 18 * A) (hA : A ≤ q * A)
    (hbig : 4 * q * (p + 2 ^ 30 * A + 64 * q + 64) ≤ n) :
    n + p + 2 * m + 4 ≤ δ ∧ 4 * (p + 2 * m + 4) ≤ δ - n := by
  have h1 : 4 * (p + 2 ^ 30 * A + 64 * q + 64) ≤ δ - n := by
    have : q * (4 * (p + 2 ^ 30 * A + 64 * q + 64)) ≤ q * (δ - n) := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hq
  norm_num at h1 hm ⊢
  omega

theorem num_case3 {q n δ D : ℕ} (hq : 0 < q) (hqδ : (q + 1) * n ≤ q * δ) (hD : D + 1 ≤ 2 * n)
    (hδD : δ ≤ D) :
    (q + 3) * n ≤ 2 * q * (δ - (D - δ) / 2) ∧ 2 * q * (δ - (δ - (D - δ) / 2)) ≤ (q - 1) * n := by
  have hnδ : n ≤ δ := by nlinarith
  constructor
  · have h1 : 3 * δ ≤ 2 * (δ - (D - δ) / 2) + 2 * n := by omega
    nlinarith
  · have h1 : 2 * (δ - (δ - (D - δ) / 2)) ≤ 2 * n - δ := by omega
    have h2 : q * (2 * (δ - (δ - (D - δ) / 2))) ≤ q * (2 * n - δ) := Nat.mul_le_mul_left _ h1
    have h3 : q * (2 * n - δ) + q * δ = q * (2 * n) := by rw [← Nat.mul_add]; congr 1; omega
    rcases q with _ | q
    · omega
    · simp only [Nat.add_sub_cancel]
      nlinarith

theorem aux_n1g {a g : ℕ} (ha : 2 ≤ a) (hg : 1 ≤ g) : a + 2 * g ≤ a * g + 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, g = b + 1 := ⟨g - 1, by omega⟩
  nlinarith

theorem aux_K2 {n q s0 : ℕ} (hs0 : 0 < s0) (h : n < 8 * q * (s0 + 1)) :
    2 * n / s0 + 1 ≤ 32 * q + 1 := by
  have : 2 * n / s0 ≤ 32 * q := by
    apply Nat.div_le_of_le_mul
    nlinarith
  omega

theorem aux_h2q {q n δ D r : ℕ} (h5 : 4 * n + 3 * (δ - n) ≤ 4 * (D - 2 * r))
    (h7 : n ≤ q * (δ - n)) : (2 * q + 1) * n ≤ 2 * q * (D - 2 * r) := by
  have h6 := Nat.mul_le_mul_left (2 * q) h5
  nlinarith

theorem aux_big {q p w n : ℕ} (h : 4 * q * (p + 2 ^ 30 * q * w ^ 18 + 64 * q + 64) ≤ n) :
    4 * q * (p + 2 ^ 30 * (q * w ^ 18) + 64 * q + 64) ≤ n := by
  rwa [← mul_assoc]

theorem defi_ge_sum {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {D : ℕ} (W : Finset V) :
    ∑ v ∈ W, (D - G.degree v) ≤ defi G D :=
  sum_le_sum_of_subset_of_nonneg (subset_univ W) fun _ _ _ => Nat.zero_le _

set_option maxHeartbeats 4000000 in
/-- **Theorem 1.2, core.** -/
theorem thm12_of_ge {q : ℕ} (hq : 0 < q) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (n : ℕ), N ≤ n →
      Fintype.card V = 2 * n → ∀ (D : ℕ) (G : SimpleGraph V),
        (∀ v, (q + 1) * n ≤ q * G.degree v ∧ G.degree v ≤ D) →
        (∀ z, 2 * D ≤ defi G D + 2 * G.degree z) → G.lineGraph.Colorable D := by
  obtain ⟨Nb, hNb⟩ := thm13b_of_ge.{u} hq
  obtain ⟨Nc, hNc⟩ := thm13c_of_ge.{u} hq
  obtain ⟨Na, hNa⟩ := AOF.one_factorization_of_ge.{u} hq
  obtain ⟨Na2, hNa2⟩ := AOF.one_factorization_of_ge.{u} (show 0 < 2 * q by omega)
  refine ⟨Nb + Nc + Na + Na2 + (2 ^ 60 * q + 1) ^ 21, fun V _ _ n hN hV D => ?_⟩
  have hpos : 0 < (2 ^ 60 * q + 1) ^ 21 := pow_pos (by omega) _
  have hn : 0 < n := by omega
  obtain ⟨w, hw1, hw2⟩ := exists_root21 hn
  have hw : 2 ^ 60 * q ≤ w := by
    have : (2 ^ 60 * q + 1) ^ 21 ≤ (w + 1) ^ 21 := le_trans (by omega) hw2
    have := (Nat.pow_le_pow_iff_left (by norm_num)).1 this
    omega
  obtain ⟨hp2, hm2, hbig, hn20, hp3, h64⟩ := params_12 hq hw hw1 hw2
  obtain ⟨p, hpdef⟩ : ∃ p, p = (w + 1) ^ 14 := ⟨_, rfl⟩
  rw [← hpdef] at hp2 hbig hp3
  have hch : 4 * (n : ℝ) * exp (-((p : ℝ) ^ 2 / (2 * n))) < 1 := by
    have h1 := chernoff_c hn20 hp3
    have h0 : 0 ≤ exp (-((p : ℝ) ^ 2 / (2 * n))) := (exp_pos _).le
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ h0) h1
    linarith
  have hA : w ^ 18 ≤ q * w ^ 18 := Nat.le_mul_of_pos_left _ hq
  have hNonempty : Nonempty V := by
    rw [← Fintype.card_pos_iff, hV]; omega
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro G hd hinv
  obtain ⟨x, hx⟩ := G.exists_minimal_degree_vertex
  set δ := G.degree x
  have hδ : ∀ v, δ ≤ G.degree v := fun v => hx ▸ G.minDegree_le_degree v
  obtain ⟨hδn, hδw⟩ := aux_n_le hq (hd x).1
  -- Vizing when `D` is not attained
  by_cases hatt : ∃ v, G.degree v = D
  swap
  · push Not at hatt
    have hmax : G.maxDegree + 1 ≤ D := by
      have := G.maxDegree_le_of_forall_degree_le (D - 1) fun v => by
        have := hatt v; have := (hd v).2; omega
      have : 0 < D := by have := (hd x).2; have := hatt x; omega
      omega
    exact (LeanPool.Vizing.lineGraph_colorable G).mono hmax
  obtain ⟨vD, hvD⟩ := hatt
  have hD2n : D + 1 ≤ 2 * n := by
    have := G.degree_lt_card_verts vD; rw [hV, hvD] at this; omega
  set g := D - δ with hgdef
  set Vδ := univ.filter fun v => G.degree v = δ
  have hxV : x ∈ Vδ := mem_filter.2 ⟨mem_univ _, rfl⟩
  -- the regular case
  by_cases hg0 : g = 0
  · have hreg : G.IsRegularOfDegree D := fun v => by
      have := hδ v; have := (hd v).2; omega
    have hDδ : D = δ := (hreg x).symm
    exact hNa V G n D (by omega) hV hreg (by rw [hDδ]; exact (hd x).1)
  -- Theorem 1.3 (c)
  by_cases hc : n ^ 6 ≤ g ^ 7 ∧ n ^ 6 ≤ #Vδ ^ 7
  · exact hNc V G n D δ (by omega) hV (fun v => ⟨hδ v, (hd v).2⟩) ⟨vD, hvD⟩ (hd x).1 hc.1 hc.2
  -- the sets are small
  have hsmall : ∀ m : ℕ, m ^ 7 < n ^ 6 → m ≤ 2 ^ 18 * w ^ 18 := by
    intro m hm
    have : m ^ 7 < ((w + 1) ^ 18) ^ 7 := by
      calc m ^ 7 < n ^ 6 := hm
        _ ≤ ((w + 1) ^ 21) ^ 6 := Nat.pow_le_pow_left hw2 6
        _ = ((w + 1) ^ 18) ^ 7 := by ring
    have := (Nat.pow_lt_pow_iff_left (by norm_num)).1 this
    omega
  by_cases hcase2 : g ^ 7 < n ^ 6
  · -- Case 2
    have hgs := hsmall g hcase2
    set s0 := n / (8 * q)
    have hs0 : 8 * q * s0 ≤ n := Nat.mul_div_le n (8 * q)
    have hs0pos : 0 < s0 := Nat.div_pos (by omega) (by omega)
    have hK : 2 * n / s0 + 1 ≤ 32 * q + 1 :=
      aux_K2 hs0pos (Nat.lt_mul_div_succ n (show 0 < 8 * q by omega))
    have hgA : q * g ≤ 2 ^ 18 * (q * w ^ 18) := by
      calc q * g ≤ q * (2 ^ 18 * w ^ 18) := Nat.mul_le_mul_left _ hgs
        _ = 2 ^ 18 * (q * w ^ 18) := by ring
    obtain ⟨hnum, hnum2⟩ := num_case2 (p := p) (A := q * w ^ 18) (g := g) (s0 := s0) hq hδw hδn
      hs0 hK hgA (aux_big hbig)
    obtain ⟨G'', r, hd'', hr, hc''⟩ := case2_regular hq hn hV hch (by omega) G
      (fun v => ⟨hδ v, (hd v).2⟩) le_rfl hinv hnum
    rw [← hr] at hnum2
    have hreg : G''.IsRegularOfDegree (D - 2 * r) := fun v => by have := hd'' v; omega
    have h2q : (2 * q + 1) * n ≤ 2 * q * (D - 2 * r) :=
      aux_h2q (by omega) hδw
    have := hNa2 V G'' n (D - 2 * r) (by omega) hV hreg h2q
    have := hc'' _ this
    rwa [Nat.sub_add_cancel (by have := hd'' vD; omega)] at this
  -- Case 1: few vertices of minimum degree
  have hn1 : #Vδ ≤ 2 ^ 18 * w ^ 18 := by
    have : #Vδ ^ 7 < n ^ 6 := by
      by_contra h; push Not at h
      exact hc ⟨by push Not at hcase2; exact hcase2, h⟩
    exact hsmall _ this
  obtain ⟨hnum1, hnum1'⟩ := num_small (p := p) (A := q * w ^ 18) (m := #Vδ) hq hδw hδn
    (le_trans hn1 (Nat.mul_le_mul_left _ hA)) (Nat.le_mul_of_pos_left _ hq) (aux_big hbig)
  have hδD : δ < D := by omega
  have hsumδ : #Vδ * g ≤ defi G D := by
    refine le_trans ?_ (defi_ge_sum Vδ)
    rw [sum_congr rfl fun v hv => by rw [(mem_filter.1 hv).2], sum_const, smul_eq_mul]
  -- one perfect matching avoiding `W`, then induction
  have finish : ∀ W : Finset V, Even #W → (∀ v, G.degree v = δ → v ∈ W) →
      (∀ v ∈ W, G.degree v < D) → #W + 2 * D ≤ defi G D + 2 * δ + 2 → #W ≤ #Vδ + 1 →
      G.lineGraph.Colorable D := by
    intro W hWev hWδ hWlt hWkey hWcard
    obtain ⟨τ, hτ⟩ := exists_pm_avoiding G hn hV W hWev ∅ (t0 := 0) hch
      (fun v _ _ => by have := hδ v; omega) (fun v _ h => absurd h (notMem_empty v))
      (by simp) (by omega)
    obtain ⟨hd1, hinv1, hcol1⟩ := case1_step G hd hδ rfl W hWδ hWlt hWkey τ hτ
    have := hcol1 _ (ih (D - 1) (by omega) _ hd1 hinv1)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hn1pos : 0 < #Vδ := card_pos.2 ⟨x, hxV⟩
  by_cases hev : Even #Vδ
  · refine finish Vδ hev (fun v hv => mem_filter.2 ⟨mem_univ _, hv⟩)
      (fun v hv => by rw [(mem_filter.1 hv).2]; exact hδD) ?_ (by omega)
    have h2 : 2 ≤ #Vδ := by obtain ⟨k, hk⟩ := hev; omega
    have h3 : #Vδ + 2 * g ≤ #Vδ * g + 2 := aux_n1g h2 (by omega)
    omega
  have hodd : Odd #Vδ := Nat.not_even_iff_odd.1 hev
  by_cases hmid : ∃ v0, δ < G.degree v0 ∧ G.degree v0 < D
  · obtain ⟨v0, hv0, hv0'⟩ := hmid
    have hv0V : v0 ∉ Vδ := fun h => by rw [(mem_filter.1 h).2] at hv0; omega
    refine finish (insert v0 Vδ) ?_ (fun v hv => mem_insert_of_mem (mem_filter.2 ⟨mem_univ _, hv⟩))
      (fun v hv => ?_) ?_ (by rw [card_insert_of_notMem hv0V])
    · rw [card_insert_of_notMem hv0V]; exact hodd.add_one
    · rcases mem_insert.1 hv with rfl | hv
      · exact hv0'
      · rw [(mem_filter.1 hv).2]; exact hδD
    · rw [card_insert_of_notMem hv0V]
      have hs := defi_ge_sum (G := G) (D := D) (insert v0 Vδ)
      rw [sum_insert hv0V, sum_congr rfl fun v hv => by rw [(mem_filter.1 hv).2], sum_const,
        smul_eq_mul, ← hgdef] at hs
      have hix : 2 * D ≤ defi G D + 2 * δ := hinv x
      rcases Nat.lt_or_ge #Vδ 3 with h | h
      · have : #Vδ = 1 := by obtain ⟨k, hk⟩ := hodd; omega
        omega
      · have h3 : #Vδ + 2 * g ≤ #Vδ * g + 2 := aux_n1g (by omega) (by omega)
        omega
  -- Case (iii): degrees `δ` and `D` only
  push Not at hmid
  have hdeg2 : ∀ v, G.degree v = if v ∈ Vδ then δ else D := by
    intro v
    by_cases hv : v ∈ Vδ
    · rw [if_pos hv]; exact (mem_filter.1 hv).2
    · rw [if_neg hv]
      have h1 : G.degree v ≠ δ := fun h => hv (mem_filter.2 ⟨mem_univ _, h⟩)
      have := hmid v (by have := hδ v; omega); have := (hd v).2; omega
  have hdefi : defi G D = #Vδ * g := by
    unfold defi
    rw [← sum_filter_add_sum_filter_not univ (fun v => G.degree v = δ)]
    rw [sum_congr rfl fun v hv => by rw [(mem_filter.1 hv).2], sum_const, smul_eq_mul]
    rw [sum_eq_zero fun v hv => by
      have hvV : v ∉ Vδ := fun h => (mem_filter.1 hv).2 (mem_filter.1 h).2
      have := hdeg2 v
      rw [if_neg hvV] at this
      omega]
    rfl
  have h3 : 3 ≤ #Vδ := by
    by_contra h
    have : #Vδ = 1 := by obtain ⟨k, hk⟩ := hodd; omega
    have h4 : 2 * D ≤ defi G D + 2 * δ := hinv x
    rw [hdefi, this, one_mul] at h4; omega
  obtain ⟨y, hyV, hxy⟩ : ∃ y ∈ Vδ, y ≠ x := by
    by_contra h; push Not at h
    have : Vδ ⊆ {x} := fun v hv => mem_singleton.2 (h v hv)
    have := card_le_card this; simp at this; omega
  have hgeven : Even g := by
    have hsum : defi G D + ∑ v, G.degree v = 2 * n * D := by
      unfold defi
      rw [← sum_add_distrib, sum_congr rfl fun v _ => Nat.sub_add_cancel (hd v).2, sum_const,
        card_univ, hV, smul_eq_mul]
    have h1 := G.sum_degrees_eq_twice_card_edges
    have h3 : Even (defi G D + ∑ v, G.degree v) := ⟨n * D, by rw [hsum]; ring⟩
    have h4 : Even (∑ v, G.degree v) := ⟨#G.edgeFinset, by rw [h1]; ring⟩
    have hde : Even (#Vδ * g) := hdefi ▸ (Nat.even_add.1 h3).2 h4
    rcases Nat.even_mul.1 hde with h | h
    · exact absurd h hev
    · exact h
  obtain ⟨Gi, hdi, hci⟩ := case3_rounds hn hV hch G (Ne.symm hxy) Vδ hxV hyV hodd hdeg2
    (by omega) (by omega) (by omega) (g / 2) (by omega)
  obtain ⟨hb1, hb2⟩ := num_case3 hq (hd x).1 hD2n hδD.le
  have hdx' : Gi.degree x = δ - g / 2 := (hdi x).trans (if_pos (Or.inl rfl))
  have hdy' : Gi.degree y = δ - g / 2 := (hdi y).trans (if_pos (Or.inr rfl))
  have hz' : ∀ z, z ≠ x → z ≠ y → Gi.degree z = δ := by
    intro z hzx hzy
    rw [hdi z, if_neg (show ¬(z = x ∨ z = y) from fun h => h.elim hzx hzy)]
    by_cases hzV : z ∈ Vδ
    · exact if_pos hzV
    · rw [if_neg hzV]; obtain ⟨k, hk⟩ := hgeven; omega
  have hcolb := hNb V Gi n δ (δ - g / 2) x y (by omega) hV (Ne.symm hxy) hdx' hdy' hz'
    (hd x).1 hb1 hb2 (Nat.sub_le _ _)
  have := hci _ hcolb
  rwa [show δ + 2 * (g / 2) = D by obtain ⟨k, hk⟩ := hgeven; omega] at this

end PSLib.Eng
