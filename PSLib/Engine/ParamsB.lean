/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Parameters for Theorem 1.3 (b)

With `a = n / q`, `p = n / L` for `L = 10⁵ q²` and `t = a / 100`, the numerical conditions of the
engine hold for `n ≥ L (512 L³ + 4)` (`params_b`).
-/

@[expose] public section

namespace PSLib.Eng

/-- The numerical facts used for Theorem 1.3 (b). -/
theorem params_b {q n : ℕ} (hq : 0 < q)
    (hn : (100000 * q * q) * (512 * (100000 * q * q) ^ 3 + 4) ≤ n) :
    let a := n / q; let p := n / (100000 * q * q); let t := a / 100
    0 < t ∧ 4 ≤ n ∧ 32 * n ^ 3 < p ^ 4 ∧ q * a ≤ n ∧ 100 * t ≤ a ∧
      8 * (15 * n * (p + 1) + 2) < a * t ∧ 1000 * p ≤ a ∧ 100000 ≤ a := by
  intro a p t
  obtain ⟨L, hL⟩ : ∃ L, L = 100000 * q * q := ⟨_, rfl⟩
  have hpdef : p = n / L := by simp only [p, hL]
  rw [← hL] at hn
  have hL1 : 100000 ≤ L := by rw [hL]; nlinarith
  have ha1 : q * a ≤ n := Nat.mul_div_le n q
  have ha2 : n < q * (a + 1) := by
    have := Nat.lt_mul_div_succ n hq; simp only [a]; linarith
  have hpL : p = a / (100000 * q) := by
    rw [hpdef]; simp only [a]; rw [Nat.div_div_eq_div_mul, hL]; congr 1; ring
  have hp1 : 100000 * q * p ≤ a := by rw [hpL]; exact Nat.mul_div_le a (100000 * q)
  have hp2 : a < 100000 * q * (p + 1) := by rw [hpL]; exact Nat.lt_mul_div_succ a (by positivity)
  have ht1 : 100 * t ≤ a := Nat.mul_div_le a 100
  have ht2 : a < 100 * (t + 1) := Nat.lt_mul_div_succ a (by norm_num)
  have hpbig : 512 * L ^ 3 + 4 ≤ p := by
    rw [hpdef]; exact (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hn)
  have hnL : n < L * (p + 1) := by rw [hpdef]; exact Nat.lt_mul_div_succ n (by omega)
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hpge : 516 ≤ p := by nlinarith
  have hq1 : 1 ≤ q := hq
  have hage : 100000 * 516 ≤ a := by nlinarith
  refine ⟨by omega, by nlinarith, ?_, ha1, ht1, ?_, by nlinarith, by omega⟩
  · -- `32 n³ < p⁴`
    have h1 : n ≤ L * (2 * p) := by nlinarith
    have h2 : 32 * n ^ 3 ≤ 32 * (L * (2 * p)) ^ 3 := by gcongr
    have h3 : 32 * (L * (2 * p)) ^ 3 = 256 * L ^ 3 * p ^ 3 := by ring
    have h4 : 256 * L ^ 3 * p ^ 3 < p ^ 4 := by
      have : 256 * L ^ 3 < p := by omega
      have hp3 : 0 < p ^ 3 := by positivity
      calc 256 * L ^ 3 * p ^ 3 < p * p ^ 3 := by gcongr
        _ = p ^ 4 := by ring
    omega
  · -- `8 (15 n (p + 1) + 2) < a t`
    have e1 : 100000 * (q * (p + 1)) ≤ a + 100000 * q := by nlinarith
    have e2 : n * (p + 1) ≤ q * (a + 1) * (p + 1) := by
      have : n ≤ q * (a + 1) := ha2.le
      exact Nat.mul_le_mul_right _ this
    have e3 : 100000 * (q * (a + 1) * (p + 1)) ≤ (a + 1) * (a + 100000 * q) := by
      calc 100000 * (q * (a + 1) * (p + 1)) = (a + 1) * (100000 * (q * (p + 1))) := by ring
        _ ≤ (a + 1) * (a + 100000 * q) := Nat.mul_le_mul_left _ e1
    have e4 : 100000 * q ≤ a / 516 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      nlinarith
    have e5 : 516 * (100000 * q) ≤ a := by
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 516)).1 e4; linarith
    have e6 : a ≤ 100 * t + 99 := by omega
    nlinarith

end PSLib.Eng
