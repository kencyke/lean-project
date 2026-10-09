/-
Copyright (c) 2026 suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: suzuki
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# Infinitude of primes

This file proves Euclid's theorem: for every natural number `n` there is a prime `p > n`.

## Main results

- `Example.infinitely_many_primes`: every natural number is exceeded by some prime.
-/

namespace Example


/-- There are infinitely many primes: for every `n : ℕ` there is a prime `p` with `n < p`.
1. Consider N = n! + 1 for any natural number n.
2. N is greater than 1, so it has a prime divisor.
3. Let p be the smallest prime divisor of N.
4. If p ≤ n, then p divides n! and also divides N, leading to a contradiction since p cannot divide 1.
5. Therefore, p > n, proving that there are infinitely many primes.
-/
theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, n < p ∧ Nat.Prime p := by
  intro n
  let N := Nat.factorial n + 1
  have N_gt_one : 1 < N := Nat.succ_lt_succ (Nat.factorial_pos n)
  let p := Nat.minFac N
  have N_not_one : N ≠ 1 := Nat.ne_of_gt N_gt_one
  have pp : Nat.Prime p := Nat.minFac_prime N_not_one
  have np : n < p := lt_of_not_ge fun h =>
    -- If 0 < p, p ≤ n, then p divides n!.
    have h₁ : p ∣ Nat.factorial n := Nat.dvd_factorial (Nat.minFac_pos _) h
    -- If p | n! and p | N, then p must divide N - n! = 1.
    have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).mpr (Nat.minFac_dvd _)
    pp.not_dvd_one h₂
  exact ⟨p, np, pp⟩

end Example
