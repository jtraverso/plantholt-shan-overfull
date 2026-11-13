/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.ParamsC

/-!
# Parameters for Theorem 1.2

With `w^21 < n ≤ (w + 1)^21` and `w ≥ 2^60 q`: the Chernoff deviation `p = (w + 1)^14`, the sets
of size below `(w + 1)^18` (about `n^{6/7}`) and the `O(q g)` rounds of Case 2 are all small
compared with `n / q` (`params_12`).
-/

@[expose] public section

namespace PSLib.Eng

set_option maxHeartbeats 1000000 in
/-- The numerical facts used for Theorem 1.2. -/
theorem params_12 {q w n : ℕ} (hq : 0 < q) (hw : 2 ^ 60 * q ≤ w) (hn1 : w ^ 21 < n)
    (hn2 : n ≤ (w + 1) ^ 21) :
    (w + 1) ^ 14 ≤ 2 ^ 14 * w ^ 14 ∧ (w + 1) ^ 18 ≤ 2 ^ 18 * w ^ 18 ∧
      4 * q * ((w + 1) ^ 14 + 2 ^ 30 * q * w ^ 18 + 64 * q + 64) ≤ n ∧
      2 ^ 20 ≤ n ∧ n ^ 2 ≤ ((w + 1) ^ 14) ^ 3 ∧ 64 * q ≤ n := by
  have hq1 : 1 ≤ q := hq
  have hw60 : 2 ^ 60 ≤ w := le_trans (by nlinarith) hw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw60
  have hp2 : (w + 1) ^ 14 ≤ 2 ^ 14 * w ^ 14 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) 14
  have hm2 : (w + 1) ^ 18 ≤ 2 ^ 18 * w ^ 18 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) 18
  have hw3 : 2 ^ 60 * q ≤ w ^ 3 :=
    le_trans hw (by calc w = w ^ 1 := (pow_one w).symm
                      _ ≤ w ^ 3 := Nat.pow_le_pow_right hw1 (by norm_num))
  have hw4 : 2 ^ 60 * q * w ≤ w ^ 4 := by
    calc 2 ^ 60 * q * w ≤ w ^ 3 * w := Nat.mul_le_mul_right _ hw3
      _ = w ^ 4 := by ring
  have hq2 : 2 ^ 60 * q * q ≤ w ^ 3 * q := Nat.mul_le_mul_right _ hw3
  have hw18 : 1 ≤ w ^ 18 := Nat.one_le_pow _ _ (by omega)
  have hw14 : w ^ 14 ≤ w ^ 18 := Nat.pow_le_pow_right hw1 (by norm_num)
  have hkey : 4 * q * (2 ^ 14 * w ^ 14 + 2 ^ 30 * q * w ^ 18 + 64 * q + 64) ≤ w ^ 21 := by
    have e : w ^ 21 = w ^ 3 * w ^ 18 := by ring
    rw [e]
    have h1 : 4 * q * (2 ^ 14 * w ^ 14) ≤ 4 * q * (2 ^ 14 * w ^ 18) := by gcongr
    have h2 : 4 * q * (64 * q + 64) ≤ 4 * q * (128 * q * w ^ 18) := by
      gcongr; nlinarith
    have h3 : 4 * q * (2 ^ 14 * w ^ 18 + 2 ^ 30 * q * w ^ 18 + 128 * q * w ^ 18) ≤
        w ^ 3 * w ^ 18 := by
      have : 4 * q * (2 ^ 14 + 2 ^ 30 * q + 128 * q) ≤ w ^ 3 := by
        have h4 : 4 * q * (2 ^ 14 + 2 ^ 30 * q + 128 * q) ≤ 2 ^ 60 * q * q := by nlinarith
        have h5 : 2 ^ 60 * q * q ≤ w ^ 3 := by
          calc 2 ^ 60 * q * q ≤ (2 ^ 60 * q) * (2 ^ 60 * q) := by nlinarith
            _ ≤ w * w := Nat.mul_le_mul hw hw
            _ ≤ w ^ 3 := by nlinarith
        exact le_trans h4 h5
      calc 4 * q * (2 ^ 14 * w ^ 18 + 2 ^ 30 * q * w ^ 18 + 128 * q * w ^ 18)
          = 4 * q * (2 ^ 14 + 2 ^ 30 * q + 128 * q) * w ^ 18 := by ring
        _ ≤ w ^ 3 * w ^ 18 := Nat.mul_le_mul_right _ this
    nlinarith
  refine ⟨hp2, hm2, ?_, ?_, ?_, ?_⟩
  · have : 4 * q * ((w + 1) ^ 14 + 2 ^ 30 * q * w ^ 18 + 64 * q + 64) ≤
        4 * q * (2 ^ 14 * w ^ 14 + 2 ^ 30 * q * w ^ 18 + 64 * q + 64) := by gcongr
    omega
  · have : 2 ^ 20 ≤ w ^ 21 := le_trans (le_trans (by norm_num) hw60)
      (by calc w = w ^ 1 := (pow_one w).symm
            _ ≤ w ^ 21 := Nat.pow_le_pow_right hw1 (by norm_num))
    omega
  · calc n ^ 2 ≤ ((w + 1) ^ 21) ^ 2 := Nat.pow_le_pow_left hn2 2
      _ = ((w + 1) ^ 14) ^ 3 := by ring
  · nlinarith

end PSLib.Eng
