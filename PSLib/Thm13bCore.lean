/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Thm13b

/-!
# Plantholt–Shan, Theorem 1.3 (b): the integer form

`thm13b_of_ge`: for `q ≥ 1` there is `N` such that a graph on `2n ≥ 2N` vertices with
`(q + 1) n ≤ q Δ`, two vertices `x ≠ y` of degree `δ` with `(q + 3) n ≤ 2 q δ`, all other vertices
of degree `Δ`, and `2 q (Δ − δ) ≤ (q − 1) n`, has chromatic index at most `Δ`.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset Real ShannonColouring AOF

universe u

set_option maxHeartbeats 1600000 in
/-- **Theorem 1.3 (b)**, integer form. -/
theorem thm13b_of_ge {q : ℕ} (hq : 0 < q) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n Δ δ : ℕ) (x y : V), N ≤ n → Fintype.card V = 2 * n → x ≠ y →
      G.degree x = δ → G.degree y = δ → (∀ z, z ≠ x → z ≠ y → G.degree z = Δ) →
      (q + 1) * n ≤ q * Δ → (q + 3) * n ≤ 2 * q * δ → 2 * q * (Δ - δ) ≤ (q - 1) * n → δ ≤ Δ →
      G.lineGraph.Colorable Δ := by
  refine ⟨(100000 * q * q) * (512 * (100000 * q * q) ^ 3 + 4),
    fun V _ _ G _ n Δ δ x y hN hV hxy hdx hdy hz hΔn hδn hgap hδΔ => ?_⟩
  classical
  obtain ⟨ht0, hn4, hch, ha1, ht1, hK8, hp1000, ha100k⟩ := params_b hq hN
  set a := n / q
  set p := n / (100000 * q * q)
  set t := a / 100
  have hn : 0 < n := by omega
  -- the halves
  obtain ⟨e, hex, hey⟩ := exists_pairing hn hV hxy
  have hch' := chernoff_cond hn hch
  obtain ⟨σ, hσ⟩ := exists_balanced_split G hn e (s := (p : ℝ)) (by positivity) hch'
  set A := half e σ
  have hA : #A = n := card_half e σ
  have hB : #Aᶜ = n := by rw [card_compl, hV, hA]; omega
  have hxyA : (x ∈ A ↔ y ∉ A) := by
    have h1 := mem_half e σ ⟨0, hn⟩ false
    have h2 := mem_half e σ ⟨0, hn⟩ true
    rw [hex] at h1; rw [hey] at h2
    rw [h1, h2]; cases σ ⟨0, hn⟩ <;> simp
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
  have hdeg : ∀ v, dx (gends G) A v + din (gends G) A v = G.degree v := dx_add_din
  have hdegle : ∀ v, G.degree v ≤ Δ := by
    intro v
    by_cases hvx : v = x
    · subst hvx; omega
    by_cases hvy : v = y
    · subst hvy; omega
    rw [hz v hvx hvy]
  -- the number of colours
  obtain ⟨k, hkdef⟩ : ∃ k, k = (innerGraph G A).maxDegree + 1 := ⟨_, rfl⟩
  have hdin_le : ∀ v, din (gends G) A v + 1 ≤ k := by
    intro v; rw [hkdef, ← innerGraph_degree]
    exact Nat.succ_le_succ ((innerGraph G A).degree_le_maxDegree v)
  haveI : Nonempty V := ⟨x⟩
  obtain ⟨vm, hvm⟩ := (innerGraph G A).exists_maximal_degree_vertex
  have hk_up : 2 * k ≤ Δ + p + 1 := by
    have := hside vm; have := hdeg vm; have := hdegle vm
    rw [innerGraph_degree] at hvm
    have : k = din (gends G) A vm + 1 := by rw [hkdef, hvm]
    omega
  obtain ⟨z, hzz⟩ : ∃ z, z ≠ x ∧ z ≠ y := by
    have : 2 < #(univ : Finset V) := by rw [card_univ, hV]; omega
    obtain ⟨z, hz⟩ : ((univ : Finset V) \ {x, y}).Nonempty := by
      rw [← card_pos]; have := card_sdiff_add_card_eq_card (subset_univ ({x, y} : Finset V))
      have := card_le_two (a := x) (b := y); omega
    exact ⟨z, by simpa using hz⟩
  have hk_low : Δ + 2 < 2 * k + p := by
    have h1 := hside z; have h2 := hdeg z; have h3 := hdin_le z
    rw [hz z hzz.1 hzz.2] at h2; omega
  have hk : 0 < k := by omega
  -- the colouring of the inner edges
  obtain ⟨c0, hc0⟩ := exists_inner_colouring (G := G) (A := A) (k := k) (by rw [hkdef])
  obtain ⟨c1, hc1, heqA, heqB⟩ := exists_equalized_sides (fun e => gends_loop e) c0 hc0
  set T : Finset V := {x, y}
  obtain ⟨hI, hmiss⟩ := init_inv (fun e => gends_loop e) hA hB hk c1 hc1 heqA heqB T t
  set col := col0 (gends G) A c1
  -- bounds on the initial missing colours
  have hmissle : ∀ v, miss (gends G) col v ≤ p + if v ∈ T then n else 0 := by
    intro v
    have h1 := hmiss v; have h2 := hside v; have h3 := hdeg v
    by_cases hvT : v ∈ T
    · rw [if_pos hvT]
      have : Δ - δ ≤ n := by
        have : 2 * q * (Δ - δ) ≤ 2 * q * n := le_trans hgap (by
          have := Nat.mul_le_mul_right n (Nat.sub_le q 1); nlinarith)
        exact Nat.le_of_mul_le_mul_left this (by positivity)
      have hv' : G.degree v = δ := by
        simp only [T, mem_insert, mem_singleton] at hvT
        rcases hvT with rfl | rfl <;> assumption
      omega
    · rw [if_neg hvT]
      have hv' : G.degree v = Δ := hz v (fun h => hvT (by simp [T, h]))
        (fun h => hvT (by simp [T, h]))
      omega
  have hmu0 : mu (gends G) col univ ≤ 3 * n * (p + 1) := by
    rw [mu_eq_sum_miss]
    calc ∑ v, miss (gends G) col v ≤ ∑ v, (p + if v ∈ T then n else 0) := sum_le_sum fun v _ => hmissle v
      _ = 2 * n * p + n * #T := by
          rw [sum_add_distrib, sum_const, card_univ, hV, smul_eq_mul, sum_ite_mem, univ_inter,
            sum_const, smul_eq_mul]; ring
      _ ≤ 3 * n * (p + 1) := by
          have : #T ≤ 2 := card_le_two
          nlinarith
  have hmuT : mu (gends G) col T ≤ mu (gends G) col univ := by
    rw [mu_eq_sum_miss, mu_eq_sum_miss]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
  set K := 3 * mu (gends G) col univ + 2 * mu (gends G) col T with hKdef
  set X := 3 * (mu (gends G) col univ / k + 4) with hXdef
  have hKle : K + 2 ≤ 15 * n * (p + 1) + 2 := by rw [hKdef]; nlinarith
  have hX : X ≤ 18 * p + 30 := by
    have h2k : n ≤ 2 * k := by
      have : n + p ≤ Δ := by
        have : q * (n + a) ≤ q * Δ := by nlinarith
        have := Nat.le_of_mul_le_mul_left this hq
        omega
      omega
    have : mu (gends G) col univ / k ≤ 6 * (p + 1) := by
      apply Nat.div_le_of_le_mul
      nlinarith
    rw [hXdef]; omega
  -- `Q` bounds `(K + 2) / t`
  set Q := (15 * n * (p + 1) + 2) / t
  have hQ : 8 * Q < a := by
    have h1 : Q * t ≤ 15 * n * (p + 1) + 2 := Nat.div_mul_le_self _ _
    by_contra h
    push Not at h
    have : a * t ≤ 8 * Q * t := Nat.mul_le_mul_right t h
    nlinarith
  have hKQ : (K + 2) / t ≤ Q := Nat.div_le_div_right hKle
  have hDn : n + a ≤ Δ := by
    have : q * (n + a) ≤ q * Δ := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hq
  have h2δ : Δ + 2 * a ≤ 2 * δ := by
    have h1 : 2 * q * (Δ + 2 * a) ≤ 2 * q * (2 * δ) := by
      have e1 : 2 * q * Δ = 2 * q * (Δ - δ) + 2 * q * δ := by
        rw [← Nat.mul_add]; congr 1; omega
      have e2 : (q - 1) * n + 4 * n = (q + 3) * n := by
        cases q with
        | zero => omega
        | succ q => simp; ring
      nlinarith
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  -- the engine
  have h2K : 2 * (K / 2 + 1) / t ≤ Q := le_trans (Nat.div_le_div_right (by omega)) hKQ
  have hKl : 4 * (K / 2 / (2 * t)) ≤ Q := by
    have : K / 2 / (2 * t) ≤ (K + 2) / t / 4 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
      exact Nat.div_le_div (by omega) (by ring_nf; exact le_rfl) (by positivity)
    have := Nat.div_mul_le_self ((K + 2) / t) 4
    omega
  have hTA : #(T ∩ A) ≤ 1 := by
    have : T ∩ A ⊆ if x ∈ A then {x} else {y} := by
      intro v hv
      obtain ⟨hvT, hvA⟩ := mem_inter.1 hv
      simp only [T, mem_insert, mem_singleton] at hvT
      split_ifs with hx
      · rcases hvT with rfl | rfl
        · simp
        · exact absurd hvA (hxyA.1 hx)
      · rcases hvT with rfl | rfl
        · exact absurd hvA hx
        · simp
    refine (card_le_card this).trans ?_
    split_ifs <;> simp
  have hTB : #(T ∩ Aᶜ) ≤ 1 := by
    have : T ∩ Aᶜ ⊆ if x ∈ A then {y} else {x} := by
      intro v hv
      obtain ⟨hvT, hvA⟩ := mem_inter.1 hv
      rw [mem_compl] at hvA
      simp only [T, mem_insert, mem_singleton] at hvT
      split_ifs with hx
      · rcases hvT with rfl | rfl
        · exact absurd hx hvA
        · simp
      · rcases hvT with rfl | rfl
        · simp
        · exact absurd (by by_contra h; exact hx (hxyA.2 h)) hvA
    refine (card_le_card this).trans ?_
    split_ifs <;> simp
  have hKAB : mu (gends G) col A = mu (gends G) col Aᶜ := by
    -- both sides carry the same degree sum and the same number of crossing edges
    have hsum : ∀ S : Finset V, (S = A ∨ S = Aᶜ) → #S = n → #(T ∩ S) = 1 →
        mu (gends G) col S + ∑ v ∈ S, din (gends G) A v = k * n := by
      intro S _ hSn _
      rw [mu_eq_sum_miss, ← sum_add_distrib, sum_congr rfl fun v _ => hmiss v, sum_const, hSn,
        smul_eq_mul, mul_comm]
    have hdsum : ∀ S : Finset V, #S = n → #(T ∩ S) = 1 →
        ∑ v ∈ S, G.degree v + (Δ - δ) = n * Δ := by
      intro S hSn hTS
      have hpt : ∀ v ∈ S, G.degree v + (if v ∈ T then Δ - δ else 0) = Δ := by
        intro v _
        by_cases hvT : v ∈ T
        · rw [if_pos hvT]
          have hv' : G.degree v = δ := by
            simp only [T, mem_insert, mem_singleton] at hvT
            rcases hvT with rfl | rfl <;> assumption
          omega
        · rw [if_neg hvT, hz v (fun h => hvT (by simp [T, h])) (fun h => hvT (by simp [T, h]))]
          rfl
      have h1 := sum_congr rfl hpt
      rw [sum_add_distrib, sum_ite_mem, sum_const, sum_const, smul_eq_mul, smul_eq_mul, inter_comm,
        hTS, hSn] at h1
      linarith
    have hT2 : #(T ∩ A) + #(T ∩ Aᶜ) = 2 := by
      rw [← sdiff_eq_inter_compl, card_inter_add_card_sdiff]
      exact card_pair hxy
    have hTA1 : #(T ∩ A) = 1 := by omega
    have hTB1 : #(T ∩ Aᶜ) = 1 := by omega
    have e1 := hsum A (Or.inl rfl) hA hTA1
    have e2 := hsum Aᶜ (Or.inr rfl) hB hTB1
    have e3 := hdsum A hA hTA1
    have e4 := hdsum Aᶜ hB hTB1
    have e5 := sum_dx_side (ends := gends G) (A := A) A (Or.inl rfl)
    have e6 := sum_dx_side (ends := gends G) (A := A) Aᶜ (Or.inr rfl)
    have e7 : ∑ v ∈ A, dx (gends G) A v + ∑ v ∈ A, din (gends G) A v = ∑ v ∈ A, G.degree v := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => hdeg v
    have e8 : ∑ v ∈ Aᶜ, dx (gends G) A v + ∑ v ∈ Aᶜ, din (gends G) A v =
        ∑ v ∈ Aᶜ, G.degree v := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => hdeg v
    omega
  -- degrees outside and inside `T`
  have hdT : ∀ w, w ∈ T → dx (gends G) A w + din (gends G) A w = δ := by
    intro w hw; rw [hdeg]
    simp only [T, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl <;> assumption
  have hdnT : ∀ w, w ∉ T → dx (gends G) A w + din (gends G) A w = Δ := by
    intro w hw; rw [hdeg]
    exact hz w (fun h => hw (by simp [T, h])) (fun h => hw (by simp [T, h]))
  obtain ⟨fc, hfc⟩ := engine (ends := gends G) (A := A) (l := 2 * t) (Δ := Δ) (τT := 1)
    (L := ∅) (fun e => gends_loop e) gends_xsimple hA hB ht0 hTA hTB
    (fun w hw => by rw [hdnT w hw]; omega)
    (fun w hw => by rw [hdT w hw]; omega)
    (by omega) (by omega)
    (fun w hw => by rw [hdnT w hw]; omega)
    (fun w hw => by rw [hdT w hw]; omega)
    (by omega) (by omega)
    (fun v => by rw [hdeg]; exact hdegle v)
    (fun v hv => absurd hv (Finset.notMem_empty v))
    (Or.inl hKAB) col hI
  exact lineGraph_colorable_of fc hfc

/-- **Plantholt–Shan, Theorem 1.3 (b).** For `0 < ε < 1` there is `N` such that a graph on
`2n ≥ 2N` vertices with two distinct vertices `x`, `y` with `d(x) = d(y) ≥ (1/2 + 3ε/2) n`, all
other vertices of degree `Δ(G) ≥ (1 + ε) n`, and `Δ(G) − δ(G) ≤ (1/2 − ε/2) n`, has chromatic
index `Δ(G)`. -/
theorem thm13b (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n : ℕ), N ≤ n → Fintype.card V = 2 * n →
      (∃ x y : V, x ≠ y ∧ G.degree x = G.degree y ∧ (1 / 2 + 3 * ε / 2) * n ≤ G.degree x ∧
        (∀ z, z ≠ x → z ≠ y → G.degree z = G.maxDegree) ∧ (1 + ε) * n ≤ G.maxDegree ∧
        (G.maxDegree : ℝ) - G.minDegree ≤ (1 / 2 - ε / 2) * n) →
      G.lineGraph.Colorable G.maxDegree := by
  obtain ⟨q0, hq0⟩ := exists_nat_one_div_lt hε
  set q := q0 + 1
  have hq : 0 < q := Nat.succ_pos q0
  have hqε : 1 / (q : ℝ) < ε := by simpa [q] using hq0
  obtain ⟨N, hN⟩ := thm13b_of_ge.{u} hq
  refine ⟨N, fun V _ _ G _ n hn hV ⟨x, y, hxy, hxyd, hδ, hz, hΔ, hgap⟩ => ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hmin : G.minDegree ≤ G.degree x := G.minDegree_le_degree x
  have hδΔ : G.degree x ≤ G.maxDegree := G.degree_le_maxDegree x
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hεq : 1 < ε * q := by rwa [div_lt_iff₀ hqpos] at hqε
  refine hN V G n G.maxDegree (G.degree x) x y hn hV hxy rfl hxyd.symm hz ?_ ?_ ?_ hδΔ
  · -- `(q + 1) n ≤ q Δ`
    have h1 : ((q : ℝ) + 1) * n ≤ q * G.maxDegree := by
      have := mul_le_mul_of_nonneg_left hΔ hqpos.le
      nlinarith
    exact_mod_cast h1
  · -- `(q + 3) n ≤ 2 q δ`
    have h1 : ((q : ℝ) + 3) * n ≤ 2 * q * G.degree x := by
      have := mul_le_mul_of_nonneg_left hδ hqpos.le
      nlinarith
    exact_mod_cast h1
  · -- `2 q (Δ − δ) ≤ (q − 1) n`
    have h1 : (G.maxDegree : ℝ) - G.degree x ≤ (1 / 2 - ε / 2) * n := by
      have : (G.minDegree : ℝ) ≤ G.degree x := by exact_mod_cast hmin
      linarith
    have h2 : 2 * (q : ℝ) * ((G.maxDegree : ℝ) - G.degree x) ≤ ((q : ℝ) - 1) * n := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * q)
      nlinarith
    have h3 : ((G.maxDegree - G.degree x : ℕ) : ℝ) = (G.maxDegree : ℝ) - G.degree x := by
      push_cast [hδΔ]; ring
    have h4 : (((q - 1 : ℕ)) : ℝ) = (q : ℝ) - 1 := by
      have : 1 ≤ q := hq
      push_cast [this]; ring
    have : (2 * q * (G.maxDegree - G.degree x) : ℕ) ≤ ((q - 1) * n : ℕ) := by
      have h5 : ((2 * q * (G.maxDegree - G.degree x) : ℕ) : ℝ) ≤ (((q - 1) * n : ℕ) : ℝ) := by
        push_cast; rw [h3, h4]; exact h2
      exact_mod_cast h5
    exact this

end PSLib.Eng
