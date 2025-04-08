/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra
  done

example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra
  done

example : ∃ (k : ℕ), ∀ n > k, (2:ℤ) ^ n ≥ n ^ 2 + 4 := by
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc
      (2:ℤ)^(k+1) = 2*(2 ^ k) := by ring
      _ ≥ 2* (k^2 + 4) := by rel[IH] --(Lean problem here if not (2:ℤ))
      _ = k^2 + k*k + 5 + 3 := by ring
      _ ≥ k^2 + 5*k + 5 + 3 := by sorry -- lean problem here (as he considers k is still in ℤ instead of ℕ)
      _ = (k^2 +2*k+ 5) + 3*k  + 3 := by ring
      _ ≥ (k^2 +2*k+ 5) + 3*5  + 3 := by sorry  -- lean problem here
      _ = (k^2 +2*k+ 5) + 18 := by ring
      _ ≥ k^2 +2*k+ 5 := by extra
      _ = (k+1)^2 + 4 := by ring
    done
  done


/-! # Exercises -/

example : ∃ (k : ℕ), ∀ n > k, 3 ^ n ≥ 2 ^ n + 100 := by
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc
      (3:ℕ)^(k+1) = 3^k * 3 := by ring
      _ ≥ (2^k + 100) * 3 := by rel[IH]
    sorry


example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  sorry
  done

-- À partir d'ici on ne peut pas utiliser la subtraction, les variable sont dans `ℕ`!

example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with n HR
  · numbers
  · calc
      (3:ℕ)^(n+1) = 3*3^n := by ring
      _ ≥ 3*(n ^ 2 + n + 1) := by rel[HR]
      _ = 3*n^2+3*n+3 := by ring
      _ = (n+1)^2+(n+1)+1+2*n^2 := by ring
      _ ≥ (n+1)^2+(n+1)+1 := by extra
  done

example : ∃ (k : ℕ), ∀ n > k, 2 ^ n ≥ n ^ 2 := by
  use 3
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · calc
      2 ^ succ 3 = 2^4 := by numbers
      _ ≥ 4^2 := by numbers
  · calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k ^ 2 + k*k := by ring
      _ ≥ k ^ 2 + 4*k := by rel [hk]
      _ = k^2+2*k+2*k := by ring
      _ ≥ k^2+2*k+2*4 := by rel [hk]
      _ = (k+1)^2+7 := by ring
      _ ≥ (k+1)^2 := by extra
  done

example : ∃ (k : ℕ), ∀ n > k, 2 ^ n ≥ n ^ 3 := by
  sorry
  done
