/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Thm13bCore
public import PSLib.Engine.Dummy
public import PSLib.Engine.ParamsC

/-!
# Plantholt–Shan, Theorem 1.3 (c)

A graph on `2n` vertices with minimum degree `δ ≥ (1 + ε) n`, `Δ − δ ≥ n^{6/7}` and at least
`n^{6/7}` vertices of degree `δ` has chromatic index `Δ` when `n` is large.

Proof: a balanced split that also balances the vertices of degree `δ`; Vizing on the inner edges;
dummy edges between deficient vertices `S` (`Δ − d(v) ≥ 2p + 2`) on the same side
(`exists_dummies`); equalization; then the engine with the special set
`T = {v : k − d'(v) ≥ 2p + 2}` and the filler set `L = V_δ`.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset Real ShannonColouring AOF

universe u

/-- The integer `w` with `w^21 < n ≤ (w + 1)^21`. -/
theorem exists_root21 {n : ℕ} (hn : 0 < n) : ∃ w : ℕ, w ^ 21 < n ∧ n ≤ (w + 1) ^ 21 := by
  classical
  have hex : ∃ r, n ≤ r ^ 21 := ⟨n, by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ 21 := Nat.pow_le_pow_right hn (by norm_num)⟩
  set r := Nat.find hex
  have hr : n ≤ r ^ 21 := Nat.find_spec hex
  have hr0 : 0 < r := by
    by_contra h; push Not at h
    have : r = 0 := by omega
    rw [this] at hr; simp at hr; omega
  refine ⟨r - 1, ?_, by rwa [Nat.sub_add_cancel hr0]⟩
  have := Nat.find_min hex (show r - 1 < r by omega)
  omega

/-- A proper colouring of real and dummy edges colours the line graph. -/
theorem lineGraph_colorable_of_dends {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k Δ : ℕ} {D : Finset (Fin k × V × V)}
    (fc : DE G D → Fin Δ) (hfc : IsProperEdgeColouring (dends G D) fc) :
    G.lineGraph.Colorable Δ :=
  lineGraph_colorable_of (fun e => fc (Sum.inl e))
    (fun e f hef hv => hfc _ _ (fun h => hef (Sum.inl_injective h)) hv)

theorem aux_div {μ n p k : ℕ} (h1 : μ ≤ 2 * n * (2 * p + 1) + 2 * k) (h2 : n ≤ 2 * k) :
    μ / k ≤ 8 * p + 6 := by
  apply Nat.div_le_of_le_mul
  have : 2 * n * (2 * p + 1) ≤ k * (8 * p + 4) := by nlinarith
  nlinarith

theorem aux_n_le {q n δ : ℕ} (hq : 0 < q) (h : (q + 1) * n ≤ q * δ) :
    n ≤ δ ∧ n ≤ q * (δ - n) := by
  have h1 : n ≤ δ := by nlinarith
  refine ⟨h1, ?_⟩
  have h2 : q * δ = q * (δ - n) + q * n := by rw [← Nat.mul_add]; congr 1; omega
  nlinarith

theorem aux_K {n p k μ μT : ℕ} (h1 : μ ≤ 2 * n * (2 * p + 1) + 2 * k) (h2 : μT ≤ 2 * k)
    (h3 : 2 * k ≤ 2 * n + p) (h4 : p ≤ n) : 3 * μ + 2 * μT + 2 ≤ 12 * n * p + 26 * n + 2 := by
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Theorem 1.3 (c)**, integer form. -/
theorem thm13c_of_ge {q : ℕ} (hq : 0 < q) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n Δ δ : ℕ), N ≤ n → Fintype.card V = 2 * n →
      (∀ v, δ ≤ G.degree v ∧ G.degree v ≤ Δ) → (∃ v, G.degree v = Δ) →
      (q + 1) * n ≤ q * δ → n ^ 6 ≤ (Δ - δ) ^ 7 →
      n ^ 6 ≤ #(univ.filter fun v => G.degree v = δ) ^ 7 →
      G.lineGraph.Colorable Δ := by
  refine ⟨(2 ^ 50 * q + 1) ^ 21,
    fun V _ _ G _ n Δ δ hN hV hdeg hvΔ hδn hgap hVδ => ?_⟩
  classical
  have hn : 0 < n := lt_of_lt_of_le (by positivity) hN
  obtain ⟨w, hw1, hw2⟩ := exists_root21 hn
  have hw : 2 ^ 50 * q ≤ w := by
    have : (2 ^ 50 * q + 1) ^ 21 ≤ (w + 1) ^ 21 := le_trans hN hw2
    have := (Nat.pow_le_pow_iff_left (by norm_num)).1 this
    omega
  obtain ⟨hp1, hp2, hpn, hp3, hn20, hmain, hfill, hlL, hτn⟩ := params_c hq hw hw1 hw2
  set p := (w + 1) ^ 14 with hpdef
  set t := 2 ^ 43 * w ^ 17 with htdef
  set l := 2 ^ 44 * w ^ 17 with hldef
  set Kb := 12 * n * p + 26 * n + 2 with hKbdef
  have hw17 : 0 < w ^ 17 := pow_pos (by omega) _
  have ht0 : 0 < t := Nat.mul_pos (by norm_num) hw17
  have hlt : t ≤ l := Nat.mul_le_mul_right _ (by norm_num)
  -- the degree-`δ` vertices and the gap
  set Vδ := univ.filter fun v => G.degree v = δ
  have hM1 : w ^ 18 < #Vδ := by
    have : (w ^ 18) ^ 7 < #Vδ ^ 7 := by
      calc (w ^ 18) ^ 7 = (w ^ 21) ^ 6 := by ring
        _ < n ^ 6 := Nat.pow_lt_pow_left hw1 (by norm_num)
        _ ≤ #Vδ ^ 7 := hVδ
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 this
  have hM2 : w ^ 18 < Δ - δ := by
    have : (w ^ 18) ^ 7 < (Δ - δ) ^ 7 := by
      calc (w ^ 18) ^ 7 = (w ^ 21) ^ 6 := by ring
        _ < n ^ 6 := Nat.pow_lt_pow_left hw1 (by norm_num)
        _ ≤ (Δ - δ) ^ 7 := hgap
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 this
  obtain ⟨vΔ, hvΔ⟩ := hvΔ
  have hΔ2n : Δ + 1 ≤ 2 * n := by
    have := G.degree_lt_card_verts vΔ; rw [hV, hvΔ] at this; omega
  have hδΔ : δ ≤ Δ := by have := hdeg vΔ; omega
  obtain ⟨hδn', hδw⟩ := aux_n_le hq hδn
  -- the halves
  have hcard : Fintype.card (Fin n × Bool) = Fintype.card V := by simp [hV, mul_comm]
  let e := Fintype.equivOfCardEq hcard
  have hch := chernoff_c hn20 hp3
  obtain ⟨σ, hσ, hσδ⟩ := exists_balanced_split' G hn e Vδ (s := (p : ℝ)) (by positivity) hch
  set A := half e σ
  have hA : #A = n := card_half e σ
  have hB : #Aᶜ = n := by rw [card_compl, hV, hA]; omega
  have hVδA : #Vδ < 2 * #(Vδ ∩ A) + p ∧ #Vδ < 2 * #(Vδ ∩ Aᶜ) + p := by
    have h1 := abs_lt.1 hσδ
    have hsum : #(Vδ ∩ A) + #(Vδ ∩ Aᶜ) = #Vδ := by
      rw [← sdiff_eq_inter_compl, card_inter_add_card_sdiff]
    constructor
    · have : (#(Vδ ∩ Aᶜ) : ℝ) < #(Vδ ∩ A) + p := by linarith
      have : #(Vδ ∩ Aᶜ) < #(Vδ ∩ A) + p := by exact_mod_cast this
      omega
    · have : (#(Vδ ∩ A) : ℝ) < #(Vδ ∩ Aᶜ) + p := by linarith
      have : #(Vδ ∩ A) < #(Vδ ∩ Aᶜ) + p := by exact_mod_cast this
      omega
  -- degrees on the two sides
  have hside : ∀ v, din (gends G) A v < dx (gends G) A v + p ∧
      dx (gends G) A v < din (gends G) A v + p := by
    intro v
    have hw := abs_lt.1 (hσ v)
    have h1 : degIn G A v < degIn G Aᶜ v + p := by
      exact_mod_cast (by linarith : (degIn G A v : ℝ) < degIn G Aᶜ v + p)
    have h2 : degIn G Aᶜ v < degIn G A v + p := by
      exact_mod_cast (by linarith : (degIn G Aᶜ v : ℝ) < degIn G A v + p)
    have hA' : ∀ S : Finset V, degIn G S v = #(univ.filter fun u => G.Adj v u ∧ u ∈ S) := by
      intro S; unfold degIn; congr 1; ext u; simp [and_comm]
    rw [din_eq, dx_eq]
    by_cases hv : v ∈ A
    · have e1 : (univ.filter fun u => G.Adj v u ∧ (v ∈ A ↔ u ∈ A)) =
          univ.filter fun u => G.Adj v u ∧ u ∈ A := by
        ext u; simp [hv]
      have e2 : (univ.filter fun u => G.Adj v u ∧ ¬ (v ∈ A ↔ u ∈ A)) =
          univ.filter fun u => G.Adj v u ∧ u ∈ Aᶜ := by
        ext u; simp [hv]
      rw [e1, e2, ← hA', ← hA']; exact ⟨h1, h2⟩
    · have e1 : (univ.filter fun u => G.Adj v u ∧ (v ∈ A ↔ u ∈ A)) =
          univ.filter fun u => G.Adj v u ∧ u ∈ Aᶜ := by
        ext u; simp [hv]
      have e2 : (univ.filter fun u => G.Adj v u ∧ ¬ (v ∈ A ↔ u ∈ A)) =
          univ.filter fun u => G.Adj v u ∧ u ∈ A := by
        ext u; simp [hv]
      rw [e1, e2, ← hA', ← hA']; exact ⟨h2, h1⟩
  have hdegG : ∀ v, dx (gends G) A v + din (gends G) A v = G.degree v := dx_add_din
  -- the number of colours
  obtain ⟨k, hkdef⟩ : ∃ k, k = (innerGraph G A).maxDegree + 1 := ⟨_, rfl⟩
  have hdin_le : ∀ v, din (gends G) A v + 1 ≤ k := by
    intro v; rw [hkdef, ← innerGraph_degree]
    exact Nat.succ_le_succ ((innerGraph G A).degree_le_maxDegree v)
  have : Nonempty V := ⟨vΔ⟩
  obtain ⟨vm, hvm⟩ := (innerGraph G A).exists_maximal_degree_vertex
  have hk_up : 2 * k ≤ Δ + p + 1 := by
    have := hside vm; have := hdegG vm; have := hdeg vm
    rw [innerGraph_degree] at hvm
    have : k = din (gends G) A vm + 1 := by rw [hkdef, hvm]
    omega
  have hk_low : Δ + 2 < 2 * k + p := by
    have h1 := hside vΔ; have h2 := hdegG vΔ; have h3 := hdin_le vΔ
    rw [hvΔ] at h2; omega
  have hk : 0 < k := by omega
  -- the colouring of the inner edges, with dummy edges
  set S := univ.filter fun v => 2 * p + 2 + G.degree v ≤ Δ
  obtain ⟨c0, hc0⟩ := exists_inner_colouring (G := G) (A := A) (k := k) (by rw [hkdef])
  obtain ⟨D, hD, hfin⟩ := exists_dummies (G := G) (A := A) c0 S
  obtain ⟨c1, hc1, heqA, heqB⟩ := exists_equalized_sides (fun x => dends_loop hD x) (dcol c0 D)
    (dcol_proper hc0 hD)
  set T := univ.filter fun v => 2 * p + 2 ≤ k - din (dends G D) A v
  obtain ⟨hI, hmiss⟩ := init_inv (fun x => dends_loop hD x) hA hB hk c1 hc1 heqA heqB T t
  set col := col0 (dends G D) A c1
  have hdx : ∀ v, dx (dends G D) A v = dx (gends G) A v := dx_dends hD
  have hdin : ∀ v, din (gends G) A v ≤ din (dends G D) A v := fun v => by
    rw [din_dends hD]; omega
  have hdinS : ∀ v, v ∉ S → din (dends G D) A v = din (gends G) A v := by
    intro v hv
    rw [din_dends hD]
    have : #(D.filter fun d => d.2.1 = v ∨ d.2.2 = v) = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro d hd hdv
      rcases hdv with rfl | rfl
      · exact hv (hD.memS d hd).1
      · exact hv (hD.memS d hd).2
    omega
  have hm0 : ∀ v, miss (dends G D) col v = k - din (dends G D) A v := fun v => by
    have := hmiss v; omega
  have hdinE_le : ∀ v, din (dends G D) A v ≤ k := fun v => by have := hmiss v; omega
  -- generic vertices miss few colours
  have hgen : ∀ v, v ∉ S → k - din (dends G D) A v ≤ 2 * p + 1 := by
    intro v hv
    rw [hdinS v hv]
    have h1 := hside v; have h2 := hdegG v; have h3 := hdeg v
    simp only [S, mem_filter, mem_univ, true_and, not_le] at hv
    omega
  have hTS : T ⊆ S := by
    intro v hv
    by_contra hvS
    have := hgen v hvS
    have := (mem_filter.1 hv).2
    omega
  have hsumS : ∀ P : Finset V, (P = S ∩ A ∨ P = S ∩ Aᶜ) →
      ∑ v ∈ P, (k - din (dends G D) A v) ≤ k := fun P hP =>
    sum_missing_S hc0 hD hfin P hP
  -- the special vertices are few
  have hTside : ∀ B : Finset V, (B = A ∨ B = Aᶜ) → #(T ∩ B) ≤ k / (2 * p + 2) := by
    intro B hB
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 : ∑ v ∈ T ∩ B, (k - din (dends G D) A v) ≤ k := by
      refine le_trans ?_ (hsumS (S ∩ B) (by rcases hB with rfl | rfl <;> simp))
      refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
      intro v hv; obtain ⟨hvT, hvB⟩ := mem_inter.1 hv; exact mem_inter.2 ⟨hTS hvT, hvB⟩
    have h2 : #(T ∩ B) * (2 * p + 2) ≤ ∑ v ∈ T ∩ B, (k - din (dends G D) A v) := by
      rw [← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun v hv => (mem_filter.1 (mem_inter.1 hv).1).2
    omega
  set τT := k / (2 * p + 2)
  -- the total number of missing colours
  have hmissS : ∑ v ∈ S, miss (dends G D) col v ≤ 2 * k := by
    rw [← sum_inter_add_sum_sdiff S A, sdiff_eq_inter_compl]
    have h1 := hsumS (S ∩ A) (Or.inl rfl)
    have h2 := hsumS (S ∩ Aᶜ) (Or.inr rfl)
    rw [sum_congr rfl fun v _ => hm0 v, sum_congr rfl fun v _ => hm0 v]
    omega
  have hmissSc : ∑ v ∈ Sᶜ, miss (dends G D) col v ≤ 2 * n * (2 * p + 1) := by
    calc ∑ v ∈ Sᶜ, miss (dends G D) col v ≤ ∑ _v ∈ Sᶜ, (2 * p + 1) := by
          refine sum_le_sum fun v hv => ?_
          rw [hm0]; exact hgen v (mem_compl.1 hv)
      _ ≤ ∑ _v : V, (2 * p + 1) := sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun _ _ _ => Nat.zero_le _
      _ = 2 * n * (2 * p + 1) := by rw [sum_const, card_univ, hV, smul_eq_mul]
  have hmu0 : mu (dends G D) col univ ≤ 2 * n * (2 * p + 1) + 2 * k := by
    rw [mu_eq_sum_miss, ← sum_add_sum_compl S]
    omega
  have hmuT : mu (dends G D) col T ≤ 2 * k := by
    rw [mu_eq_sum_miss]
    exact le_trans (sum_le_sum_of_subset_of_nonneg hTS fun _ _ _ => Nat.zero_le _) hmissS
  set K := 3 * mu (dends G D) col univ + 2 * mu (dends G D) col T with hKdef
  set X := 3 * (mu (dends G D) col univ / k + 4) with hXdef
  have hkn : n + 3 ≤ 2 * k := by omega
  have hkp : 2 * k ≤ 2 * n + p := by omega
  have hKle : K + 2 ≤ Kb := by
    rw [hKdef, hKbdef]; exact aux_K hmu0 hmuT hkp hpn
  have hX : X ≤ 24 * p + 30 := by
    have := aux_div hmu0 (by omega : n ≤ 2 * k)
    rw [hXdef]; omega
  have hτ : τT ≤ n / p + 1 := by
    have h1 : τT ≤ (n + p) / (2 * p + 2) := Nat.div_le_div_right (by omega)
    have h2 : (n + p) / (2 * p + 2) ≤ (n + p) / p := Nat.div_le_div_left (by omega) (by omega)
    have h3 : (n + p) / p = n / p + 1 := by
      rw [Nat.add_div_right _ (by omega)]
    omega
  have hQ : (K + 2) / t ≤ Kb / t := Nat.div_le_div_right hKle
  have h2K : 2 * (K / 2 + 1) / t ≤ Kb / t := le_trans (Nat.div_le_div_right (by omega)) hQ
  have hKl : K / 2 / l ≤ Kb / l := by
    rw [Nat.div_div_eq_div_mul]
    exact le_trans (Nat.div_le_div_left (by omega) (by omega)) (Nat.div_le_div_right (by omega))
  have hKlt : Kb / l ≤ Kb / t := Nat.div_le_div_left hlt ht0
  -- degree identities
  have hdE : ∀ v, dx (dends G D) A v + din (dends G D) A v + miss (dends G D) col v =
      k + dx (gends G) A v := by
    intro v; rw [hdx]; have := hmiss v; omega
  have hgenv : ∀ v, v ∉ T → δ + 2 * k ≤ 2 * (dx (dends G D) A v + din (dends G D) A v) + 5 * p + 4 := by
    intro v hv
    have h1 := hdE v; have h2 := hside v; have h3 := hdegG v; have h4 := hdeg v
    have h5 : miss (dends G D) col v < 2 * p + 2 := by
      rw [hm0]; by_contra h; push Not at h
      exact hv (mem_filter.2 ⟨mem_univ _, h⟩)
    omega
  have hTv' : ∀ v, δ ≤ dx (dends G D) A v + din (dends G D) A v := by
    intro v
    have h2 := hdin v; have h3 := hdegG v; have h4 := hdeg v
    rw [hdx]; omega
  have hl2 : l = 2 * t := by rw [hldef, htdef]; ring
  -- `δ − n` is large
  have hbig : q * (2 * t + 2 * l + 80 * p + 200 + 4 * (n / p + 2) + 8 * (Kb / t)) < q * (δ - n) := by
    omega
  have hbig' : 2 * t + 2 * l + 80 * p + 200 + 4 * (n / p + 2) + 8 * (Kb / t) < δ - n :=
    Nat.lt_of_mul_lt_mul_left hbig
  -- the engine
  obtain ⟨fc, hfc⟩ := engine (ends := dends G D) (A := A) (l := l) (Δ := Δ) (τT := τT) (L := Vδ)
    (fun x => dends_loop hD x) (dends_xsimple hD) hA hB ht0 (hTside A (Or.inl rfl))
    (hTside Aᶜ (Or.inr rfl))
    (fun w hw => by have := hgenv w hw; omega)
    (fun w hw => by have := hTv' w; omega)
    (by omega) (by omega)
    (fun w hw => by have := hgenv w hw; omega)
    (fun w hw => by have := hTv' w; omega)
    (by omega) (by omega)
    (fun v => by
      rw [hdx]
      by_cases hvS : v ∈ S
      · have h1 := hdinE_le v; have h2 := hside v; have h3 := hdegG v
        have h4 := (mem_filter.1 hvS).2
        omega
      · rw [hdinS v hvS, hdegG]; exact (hdeg v).2)
    (fun v hv => by
      rw [hdx]
      have hvd : G.degree v = δ := (mem_filter.1 hv).2
      have h1 := hdinE_le v; have h2 := hside v; have h3 := hdegG v
      omega)
    (Or.inr ⟨by have := hVδA.1; omega, by have := hVδA.2; omega⟩) col hI
  exact lineGraph_colorable_of_dends fc hfc


/-- **Plantholt–Shan, Theorem 1.3 (c).** For `ε > 0` there is `N` such that a graph on `2n ≥ 2N`
vertices with `Δ(G) − δ(G) ≥ n^{6/7}`, at least `n^{6/7}` vertices of degree `δ(G)`, at least
`n + 1` vertices of degree `Δ(G)`, and `δ(G) ≥ (1 + ε) n`, has chromatic index `Δ(G)`. -/
theorem thm13c (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n : ℕ), N ≤ n → Fintype.card V = 2 * n →
      (n : ℝ) ^ ((6 : ℝ) / 7) ≤ (G.maxDegree : ℝ) - G.minDegree →
      (n : ℝ) ^ ((6 : ℝ) / 7) ≤ #(univ.filter fun v => G.degree v = G.minDegree) →
      n + 1 ≤ #(univ.filter fun v => G.degree v = G.maxDegree) →
      (1 + ε) * n ≤ G.minDegree →
      G.lineGraph.Colorable G.maxDegree := by
  obtain ⟨q0, hq0⟩ := exists_nat_one_div_lt hε
  set q := q0 + 1
  have hq : 0 < q := Nat.succ_pos q0
  have hqε : 1 / (q : ℝ) < ε := by simpa [q] using hq0
  obtain ⟨N, hN⟩ := thm13c_of_ge.{u} hq
  refine ⟨N + 1, fun V _ _ G _ n hn hV hgap hVδ _ hδ => ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hεq : 1 < ε * q := by rwa [div_lt_iff₀ hqpos] at hqε
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnpos : 0 < n := by omega
  have : Nonempty V := by
    rw [← Fintype.card_pos_iff, hV]; omega
  obtain ⟨vΔ, hvΔ⟩ := G.exists_maximal_degree_vertex
  have hmM : G.minDegree ≤ G.maxDegree := le_trans (G.minDegree_le_degree vΔ) (G.degree_le_maxDegree vΔ)
  -- `n^6 ≤ m^7` from `n^{6/7} ≤ m`
  have hpow : ∀ m : ℕ, (n : ℝ) ^ ((6 : ℝ) / 7) ≤ m → n ^ 6 ≤ m ^ 7 := by
    intro m hm
    have h1 : ((n : ℝ) ^ ((6 : ℝ) / 7)) ^ (7 : ℕ) = (n : ℝ) ^ (6 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
    have h2 : ((n : ℝ) ^ ((6 : ℝ) / 7)) ^ (7 : ℕ) ≤ (m : ℝ) ^ (7 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hm 7
    rw [h1] at h2
    exact_mod_cast h2
  refine hN V G n G.maxDegree G.minDegree (by omega) hV
    (fun v => ⟨G.minDegree_le_degree v, G.degree_le_maxDegree v⟩) ⟨vΔ, hvΔ.symm⟩ ?_ ?_ ?_
  · have h1 : ((q : ℝ) + 1) * n ≤ q * G.minDegree := by
      have := mul_le_mul_of_nonneg_left hδ hqpos.le
      nlinarith
    exact_mod_cast h1
  · apply hpow
    rw [Nat.cast_sub hmM]; exact hgap
  · exact hpow _ hVδ

end PSLib.Eng
