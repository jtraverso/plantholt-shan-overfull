/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Partition
public import AOF.Chernoff

/-!
# Balanced splits with prescribed pairs (Plantholt–Shan, Lemma 4.1)

For a pairing `e : Fin n × Bool ≃ V` of the `2n` vertices, some choice of one vertex from every
pair gives a set `A` (`AOF.half e σ`) with `|d_A(v) − d_{Aᶜ}(v)| < s` for every vertex, provided
`4 n exp(−s² / 2n) < 1`. Unlike `AOF.exists_balanced_half`, the pairing is prescribed, so the
prescribed pairs are split.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset Real AOF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Balanced split along a prescribed pairing.** -/
theorem exists_balanced_split (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (hn : 0 < n)
    (e : Fin n × Bool ≃ V) {s : ℝ} (hs : 0 ≤ s)
    (hch : 4 * n * exp (-(s ^ 2 / (2 * n))) < 1) :
    ∃ σ : Fin n → Bool, ∀ v, |(degIn G (half e σ) v : ℝ) - degIn G (half e σ)ᶜ v| < s := by
  classical
  have hV : Fintype.card V = 2 * n := by
    rw [← Fintype.card_congr e]; simp [mul_comm]
  -- the signed coefficients of a vertex
  let c : V → Fin n → ℝ := fun v i => (if G.Adj v (e (i, true)) then (1 : ℝ) else 0) -
    (if G.Adj v (e (i, false)) then 1 else 0)
  have hc : ∀ v i, |c v i| ≤ 1 := by
    intro v i; simp only [c]; split_ifs <;> norm_num
  -- the bad sign vectors, one family per vertex
  set bad : Finset (Fin n → Bool) :=
    univ.biUnion fun v => univ.filter fun σ => s ≤ |signedSum (c v) σ|
  have hcount : (#bad : ℝ) < #(univ : Finset (Fin n → Bool)) := by
    have h1 : (#bad : ℝ) ≤ ∑ v : V, ((univ.filter fun σ => s ≤ |signedSum (c v) σ|).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    have h2 : ∑ v : V, ((univ.filter fun σ => s ≤ |signedSum (c v) σ|).card : ℝ) ≤
        ∑ _v : V, 2 * 2 ^ n * exp (-(s ^ 2 / (2 * n))) :=
      sum_le_sum fun v _ => card_abs_signedSum_ge_le hn (c v) (hc v) s hs
    have h3 : ∑ _v : V, 2 * 2 ^ n * exp (-(s ^ 2 / (2 * n))) =
        2 ^ n * (4 * n * exp (-(s ^ 2 / (2 * n)))) := by
      rw [sum_const, card_univ, hV, nsmul_eq_mul]; push_cast; ring
    have h4 : (2 : ℝ) ^ n * (4 * n * exp (-(s ^ 2 / (2 * n)))) < 2 ^ n := by
      have := mul_lt_mul_of_pos_left hch (by positivity : (0 : ℝ) < 2 ^ n)
      linarith
    have h5 : (#(univ : Finset (Fin n → Bool)) : ℝ) = 2 ^ n := by simp
    linarith
  obtain ⟨σ, -, hσ⟩ := exists_mem_notMem_of_card_lt_card (by exact_mod_cast hcount)
  refine ⟨σ, fun v => ?_⟩
  rw [degIn_sub_eq_signedSum G e σ v]
  by_contra h
  exact hσ (mem_biUnion.2 ⟨v, mem_univ v, mem_filter.2 ⟨mem_univ σ, not_lt.1 h⟩⟩)

/-- The difference of the parts of a set `S0` on the two sides, as a signed sum over the pairs. -/
theorem card_inter_sub_eq_signedSum {n : ℕ} (e : Fin n × Bool ≃ V) (σ : Fin n → Bool)
    (S0 : Finset V) :
    (#(S0 ∩ half e σ) : ℝ) - #(S0 ∩ (half e σ)ᶜ) =
      signedSum (fun i => (if e (i, true) ∈ S0 then (1 : ℝ) else 0) -
        (if e (i, false) ∈ S0 then 1 else 0)) σ := by
  classical
  have hcount : ∀ P : Finset V, (#(S0 ∩ P) : ℝ) =
      ∑ i : Fin n, ∑ b : Bool, if e (i, b) ∈ P ∧ e (i, b) ∈ S0 then (1 : ℝ) else 0 := by
    intro P
    have h1 : #(S0 ∩ P) = #(univ.filter fun u => u ∈ P ∧ u ∈ S0) := by
      congr 1; ext u; simp [and_comm]
    rw [h1, card_filter, Nat.cast_sum, ← e.sum_comp, Fintype.sum_prod_type]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hcount, hcount, ← sum_sub_distrib, signedSum]
  refine sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [mem_compl, mem_half]
  cases σ i <;> simp

/-- **Balanced split along a prescribed pairing, also balancing a set `S0`.** -/
theorem exists_balanced_split' (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (hn : 0 < n)
    (e : Fin n × Bool ≃ V) (S0 : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (hch : (4 * n + 2) * exp (-(s ^ 2 / (2 * n))) < 1) :
    ∃ σ : Fin n → Bool, (∀ v, |(degIn G (half e σ) v : ℝ) - degIn G (half e σ)ᶜ v| < s) ∧
      |(#(S0 ∩ half e σ) : ℝ) - #(S0 ∩ (half e σ)ᶜ)| < s := by
  classical
  have hV : Fintype.card V = 2 * n := by
    rw [← Fintype.card_congr e]; simp [mul_comm]
  let c : Option V → Fin n → ℝ := fun o i => match o with
    | some v => (if G.Adj v (e (i, true)) then (1 : ℝ) else 0) - (if G.Adj v (e (i, false)) then 1 else 0)
    | none => (if e (i, true) ∈ S0 then (1 : ℝ) else 0) - (if e (i, false) ∈ S0 then 1 else 0)
  have hc : ∀ o i, |c o i| ≤ 1 := by
    intro o i; rcases o with _ | v <;> simp only [c] <;> split_ifs <;> norm_num
  set bad : Finset (Fin n → Bool) :=
    univ.biUnion fun o => univ.filter fun σ => s ≤ |signedSum (c o) σ|
  have hcount : (#bad : ℝ) < #(univ : Finset (Fin n → Bool)) := by
    have h1 : (#bad : ℝ) ≤ ∑ o : Option V,
        ((univ.filter fun σ => s ≤ |signedSum (c o) σ|).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    have h2 : ∑ o : Option V, ((univ.filter fun σ => s ≤ |signedSum (c o) σ|).card : ℝ) ≤
        ∑ _o : Option V, 2 * 2 ^ n * exp (-(s ^ 2 / (2 * n))) :=
      sum_le_sum fun o _ => card_abs_signedSum_ge_le hn (c o) (hc o) s hs
    have h3 : ∑ _o : Option V, 2 * 2 ^ n * exp (-(s ^ 2 / (2 * n))) =
        2 ^ n * ((4 * n + 2) * exp (-(s ^ 2 / (2 * n)))) := by
      rw [sum_const, card_univ, Fintype.card_option, hV, nsmul_eq_mul]; push_cast; ring
    have h4 : (2 : ℝ) ^ n * ((4 * n + 2) * exp (-(s ^ 2 / (2 * n)))) < 2 ^ n := by
      have := mul_lt_mul_of_pos_left hch (by positivity : (0 : ℝ) < 2 ^ n)
      linarith
    have h5 : (#(univ : Finset (Fin n → Bool)) : ℝ) = 2 ^ n := by simp
    linarith
  obtain ⟨σ, -, hσ⟩ := exists_mem_notMem_of_card_lt_card (by exact_mod_cast hcount)
  refine ⟨σ, fun v => ?_, ?_⟩
  · rw [degIn_sub_eq_signedSum G e σ v]
    by_contra h
    exact hσ (mem_biUnion.2 ⟨some v, mem_univ _, mem_filter.2 ⟨mem_univ σ, not_lt.1 h⟩⟩)
  · rw [card_inter_sub_eq_signedSum e σ S0]
    by_contra h
    exact hσ (mem_biUnion.2 ⟨none, mem_univ _, mem_filter.2 ⟨mem_univ σ, not_lt.1 h⟩⟩)

end PSLib.Eng
