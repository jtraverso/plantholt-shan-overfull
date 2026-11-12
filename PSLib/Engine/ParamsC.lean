/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Parameters for Theorem 1.3 (c)

Write `w^21 < n ≤ 2^21 w^21` and take `p = (w + 1)^14` (about `n^{2/3}`), `t = 2^43 w^17`,
`l = 2^44 w^17` (about `n^{17/21}`). For `w ≥ 2^50 q` the numerical conditions hold
(`params_c`), and the Chernoff condition `(4n + 2) exp(−p²/2n) < 1` holds as soon as `n² ≤ p³` and
`n ≥ 2^20` (`chernoff_c`).
-/

@[expose] public section

namespace PSLib.Eng

open Real

/-- The Chernoff condition from `n² ≤ p³`. -/
theorem chernoff_c {n p : ℕ} (hn : 2 ^ 20 ≤ n) (hp : n ^ 2 ≤ p ^ 3) :
    (4 * (n : ℝ) + 2) * exp (-((p : ℝ) ^ 2 / (2 * n))) < 1 := by
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) < 2 ^ 20 := by norm_num
    exact lt_of_lt_of_le this (by exact_mod_cast hn)
  have hn' : (2 : ℝ) ^ 20 ≤ n := by exact_mod_cast hn
  set x : ℝ := (p : ℝ) ^ 2 / (2 * n)
  have hx : 0 ≤ x := by positivity
  have hexp := Real.pow_div_factorial_le_exp x hx 6
  have hp' : ((n : ℝ) ^ 2) ^ 4 ≤ ((p : ℝ) ^ 3) ^ 4 := by
    have : (n : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 := by exact_mod_cast hp
    gcongr
  have hx6 : x ^ 6 = (p : ℝ) ^ 12 / (64 * (n : ℝ) ^ 6) := by
    simp only [x]; field_simp; ring
  have hx6' : (n : ℝ) ^ 2 / 64 ≤ x ^ 6 := by
    rw [hx6, div_le_div_iff₀ (by norm_num) (by positivity)]
    have : (n : ℝ) ^ 8 ≤ (p : ℝ) ^ 12 := by
      calc (n : ℝ) ^ 8 = ((n : ℝ) ^ 2) ^ 4 := by ring
        _ ≤ ((p : ℝ) ^ 3) ^ 4 := hp'
        _ = (p : ℝ) ^ 12 := by ring
    nlinarith [pow_pos hn0 6]
  have hbig : 4 * (n : ℝ) + 2 < exp x := by
    have h720 : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
    have : 4 * (n : ℝ) + 2 < (n : ℝ) ^ 2 / 64 / 720 := by
      rw [div_div, lt_div_iff₀ (by norm_num)]
      nlinarith
    calc 4 * (n : ℝ) + 2 < (n : ℝ) ^ 2 / 64 / 720 := this
      _ ≤ x ^ 6 / 720 := by gcongr
      _ = x ^ 6 / ((Nat.factorial 6 : ℕ) : ℝ) := by rw [h720]
      _ ≤ exp x := hexp
  rw [exp_neg, ← div_eq_mul_inv, div_lt_one (exp_pos x)]
  exact hbig

set_option maxHeartbeats 2000000 in
/-- The numerical facts used for Theorem 1.3 (c). -/
theorem params_c {q w n : ℕ} (hq : 0 < q) (hw : 2 ^ 50 * q ≤ w) (hn1 : w ^ 21 < n)
    (hn2 : n ≤ (w + 1) ^ 21) :
    w ^ 14 ≤ (w + 1) ^ 14 ∧ (w + 1) ^ 14 ≤ 2 ^ 14 * w ^ 14 ∧ (w + 1) ^ 14 ≤ n ∧
      n ^ 2 ≤ ((w + 1) ^ 14) ^ 3 ∧ 2 ^ 20 ≤ n ∧
      q * (2 * (2 ^ 43 * w ^ 17) + 2 * (2 ^ 44 * w ^ 17) + 80 * (w + 1) ^ 14 + 200 +
        4 * (n / (w + 1) ^ 14 + 2) +
        8 * ((12 * n * (w + 1) ^ 14 + 26 * n + 2) / (2 ^ 43 * w ^ 17))) ≤ w ^ 21 ∧
      8 * ((12 * n * (w + 1) ^ 14 + 26 * n + 2) / (2 ^ 44 * w ^ 17)) + 2 * (w + 1) ^ 14 + 16 ≤
        w ^ 18 ∧
      2 * (2 ^ 44 * w ^ 17) + 2 * (w + 1) ^ 14 + 2 ≤ w ^ 18 ∧
      4 * (n / (w + 1) ^ 14 + 2) ≤ n := by
  have hq1 : 1 ≤ q := hq
  have hw50 : 2 ^ 50 ≤ w := le_trans (by nlinarith) hw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw50
  set p := (w + 1) ^ 14 with hp
  have hp1 : w ^ 14 ≤ p := Nat.pow_le_pow_left (by omega) 14
  have hp2 : p ≤ 2 ^ 14 * w ^ 14 := by
    rw [hp, ← mul_pow]; exact Nat.pow_le_pow_left (by omega) 14
  have hn3 : n ≤ 2 ^ 21 * w ^ 21 := by
    refine le_trans hn2 ?_
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) 21
  -- powers of `w`
  have e17 : w ^ 18 = w * w ^ 17 := by ring
  have e21 : w ^ 21 = w ^ 4 * w ^ 17 := by ring
  have e14 : w ^ 17 = w ^ 3 * w ^ 14 := by ring
  have e7 : w ^ 14 = w ^ 7 * w ^ 7 := by ring
  have e35 : w ^ 21 * w ^ 14 = w ^ 18 * w ^ 17 := by ring
  have hw3 : 2 ^ 50 ≤ w ^ 3 := by
    calc 2 ^ 50 ≤ w := hw50
      _ = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 3 := Nat.pow_le_pow_right hw1 (by norm_num)
  have hw3q : 2 ^ 50 * q ≤ w ^ 3 := by
    calc 2 ^ 50 * q ≤ w := hw
      _ = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 3 := Nat.pow_le_pow_right hw1 (by norm_num)
  have hw4q : 2 ^ 100 * q ≤ w ^ 4 := by
    calc 2 ^ 100 * q = 2 ^ 50 * (2 ^ 50 * q) := by ring
      _ ≤ w ^ 3 * w := Nat.mul_le_mul (le_trans (by norm_num) hw3) hw
      _ = w ^ 4 := by ring
  have hw7 : 2 ^ 50 ≤ w ^ 7 := by
    calc 2 ^ 50 ≤ w := hw50
      _ = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 7 := Nat.pow_le_pow_right hw1 (by norm_num)
  have hw14 : 1 ≤ w ^ 14 := Nat.one_le_pow _ _ (by omega)
  have hw17pos : 0 < w ^ 17 := pow_pos (by omega) _
  -- `n / p ≤ 2^21 w^7`
  have hnp : n / p ≤ 2 ^ 21 * w ^ 7 := by
    have h1 : n / p ≤ n / w ^ 14 := Nat.div_le_div_left hp1 (pow_pos (by omega) _)
    have h2 : n / w ^ 14 ≤ 2 ^ 21 * w ^ 7 := by
      apply Nat.div_le_of_le_mul
      calc n ≤ 2 ^ 21 * w ^ 21 := hn3
        _ = w ^ 14 * (2 ^ 21 * w ^ 7) := by ring
    omega
  -- `Kb ≤ 13 · 2^35 w^35`
  set Kb := 12 * n * p + 26 * n + 2 with hKb
  have hKb1 : Kb ≤ 2 ^ 39 * (w ^ 18 * w ^ 17) := by
    have h1 : 12 * n * p ≤ 12 * (2 ^ 21 * w ^ 21) * (2 ^ 14 * w ^ 14) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hn3) hp2
    have h2 : 12 * (2 ^ 21 * w ^ 21) * (2 ^ 14 * w ^ 14) = 12 * 2 ^ 35 * (w ^ 18 * w ^ 17) := by
      rw [← e35]; ring
    have h3 : 26 * n + 2 ≤ 2 ^ 35 * (w ^ 18 * w ^ 17) := by
      have : w ^ 21 ≤ w ^ 18 * w ^ 17 := by
        calc w ^ 21 ≤ w ^ 35 := Nat.pow_le_pow_right hw1 (by norm_num)
          _ = w ^ 18 * w ^ 17 := by ring
      have : 1 ≤ w ^ 21 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    omega
  have hKbt : Kb / (2 ^ 43 * w ^ 17) ≤ w ^ 18 := by
    apply Nat.div_le_of_le_mul
    calc Kb ≤ 2 ^ 39 * (w ^ 18 * w ^ 17) := hKb1
      _ ≤ 2 ^ 43 * w ^ 17 * w ^ 18 := by nlinarith [Nat.zero_le (w ^ 18 * w ^ 17)]
  have hKbl : 32 * (Kb / (2 ^ 44 * w ^ 17)) ≤ w ^ 18 := by
    have hl0 : 0 < 2 ^ 44 * w ^ 17 := Nat.mul_pos (by norm_num) hw17pos
    have h1 := Nat.div_mul_le_self Kb (2 ^ 44 * w ^ 17)
    have h2 : 32 * Kb ≤ 2 ^ 44 * w ^ 17 * w ^ 18 := by nlinarith [Nat.zero_le (w ^ 18 * w ^ 17)]
    have h3 : 32 * (Kb / (2 ^ 44 * w ^ 17)) * (2 ^ 44 * w ^ 17) ≤ w ^ 18 * (2 ^ 44 * w ^ 17) := by
      nlinarith
    exact Nat.le_of_mul_le_mul_right h3 hl0
  refine ⟨hp1, hp2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `p ≤ n`
    have : 2 ^ 14 * w ^ 14 ≤ w ^ 21 := by
      calc 2 ^ 14 * w ^ 14 ≤ w ^ 7 * w ^ 14 := Nat.mul_le_mul_right _ (le_trans (by norm_num) hw7)
        _ = w ^ 21 := by ring
    omega
  · -- `n² ≤ p³`
    calc n ^ 2 ≤ ((w + 1) ^ 21) ^ 2 := Nat.pow_le_pow_left hn2 2
      _ = ((w + 1) ^ 14) ^ 3 := by ring
  · -- `2^20 ≤ n`
    have : 2 ^ 20 ≤ w ^ 21 := le_trans (le_trans (by norm_num) hw50)
      (by calc w = w ^ 1 := (pow_one w).symm
            _ ≤ w ^ 21 := Nat.pow_le_pow_right hw1 (by norm_num))
    omega
  · -- the main inequality
    have h1 : q * (3 * 2 ^ 44 * w ^ 17) * 8 ≤ w ^ 21 := by
      rw [e21]
      have : q * (3 * 2 ^ 44) * 8 ≤ w ^ 4 := le_trans (by nlinarith) hw4q
      nlinarith
    have h2 : q * (80 * (2 ^ 14 * w ^ 14)) * 8 ≤ w ^ 21 := by
      have : w ^ 21 = w ^ 4 * w ^ 3 * w ^ 14 := by ring
      rw [this]
      have : q * (80 * 2 ^ 14) * 8 ≤ w ^ 4 * w ^ 3 :=
        calc q * (80 * 2 ^ 14) * 8 ≤ 2 ^ 100 * q * 2 ^ 50 := by nlinarith
          _ ≤ w ^ 4 * w ^ 3 := Nat.mul_le_mul hw4q hw3
      nlinarith
    have h3 : q * (208 + 4 * (2 ^ 21 * w ^ 7)) * 8 ≤ w ^ 21 := by
      have : w ^ 21 = w ^ 4 * w ^ 3 * w ^ 7 * w ^ 7 := by ring
      rw [this]
      have hw7' : 1 ≤ w ^ 7 := Nat.one_le_pow _ _ (by omega)
      have : q * (208 + 4 * 2 ^ 21) * 8 ≤ w ^ 4 * w ^ 3 :=
        calc q * (208 + 4 * 2 ^ 21) * 8 ≤ 2 ^ 100 * q * 2 ^ 50 := by nlinarith
          _ ≤ w ^ 4 * w ^ 3 := Nat.mul_le_mul hw4q hw3
      nlinarith
    have h4 : q * (8 * w ^ 18) * 8 ≤ w ^ 21 := by
      have : w ^ 21 = w ^ 3 * w ^ 18 := by ring
      rw [this]
      have : q * 64 ≤ w ^ 3 := le_trans (by nlinarith) hw3q
      nlinarith
    have h5 : 2 * (2 ^ 43 * w ^ 17) + 2 * (2 ^ 44 * w ^ 17) = 3 * 2 ^ 44 * w ^ 17 := by ring
    have h6 : 8 * (q * (2 * (2 ^ 43 * w ^ 17) + 2 * (2 ^ 44 * w ^ 17) + 80 * p + 200 +
        4 * (n / p + 2) + 8 * (Kb / (2 ^ 43 * w ^ 17)))) ≤ 8 * w ^ 21 := by
      rw [h5]
      have := Nat.mul_le_mul_left q (show 3 * 2 ^ 44 * w ^ 17 + 80 * p + 200 + 4 * (n / p + 2) +
          8 * (Kb / (2 ^ 43 * w ^ 17)) ≤ 3 * 2 ^ 44 * w ^ 17 + 80 * (2 ^ 14 * w ^ 14) +
          (208 + 4 * (2 ^ 21 * w ^ 7)) + 8 * w ^ 18 by omega)
      nlinarith
    omega
  · -- fill
    have : 2 * (2 ^ 14 * w ^ 14) + 16 ≤ w ^ 18 / 2 := by
      have : w ^ 18 = w ^ 4 * w ^ 14 := by ring
      rw [this, Nat.le_div_iff_mul_le (by norm_num)]
      have : 2 ^ 100 ≤ w ^ 4 := le_trans (by nlinarith) hw4q
      nlinarith
    omega
  · -- `2 l + 2 p + 2 ≤ w^18`
    have h1 : 2 ^ 46 * w ^ 17 ≤ w ^ 18 := by rw [e17]; exact Nat.mul_le_mul_right _ (le_trans (by norm_num) hw50)
    have h2 : 2 * (2 ^ 14 * w ^ 14) + 2 ≤ 2 ^ 45 * w ^ 17 := by
      rw [e14]
      have : 1 ≤ w ^ 14 := hw14
      nlinarith
    omega
  · -- `4 (n / p + 2) ≤ n`
    have : 4 * (2 ^ 21 * w ^ 7 + 2) ≤ w ^ 21 := by
      have : w ^ 21 = w ^ 7 * w ^ 7 * w ^ 7 := by ring
      rw [this]
      have hw7' : 1 ≤ w ^ 7 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    omega

end PSLib.Eng
