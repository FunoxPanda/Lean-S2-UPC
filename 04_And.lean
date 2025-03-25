/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- lemma abs_le_of_sq_le_sq' {a b : ℝ} (h1 : a ^ 2 ≤ b ^ 2) (h2 : 0 ≤ b) : -b ≤ a ∧ a ≤ b

example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h -- ça c'est évident sur papier
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring
  done


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3 := by
    apply abs_le_of_sq_le_sq'
    · calc
        p ^ 2 ≤ 9 := by addarith [hp]
        _ = 3 ^ 2 := by numbers
    · numbers
  sorry
  done

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor -- deux objectifs différents divisés en deux cas.
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]
  done

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb
  done


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0 := by
    apply le_antisymm
    · calc
        a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
        _ = 0 := by rw [h1]
    · extra
  sorry
  done

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  · calc 2 * a + b = a + (a + b) := by ring
      _ ≤ 1 + (a + b) := by rel[h1]
      _ ≤ 1 + 3 := by rel[h2]
      _ = 4 := by numbers
    done

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  · calc
      2 * r = r + r + s -s := by ring
      _ = (r + s) + (r - s) := by ring
      _ ≤ 1 + 5 := by rel[h1,h2]
      _ = 6 := by numbers
  done

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  · calc
    m ≤ n - 5 := by addarith[h2]
    _ ≤ 8 - 5 := by rel[h1]
    _ = 3 := by numbers
  done

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
    have h : p ≥ 7 := by addarith[hp]
    constructor
    · calc
        p^2 = p * p := by ring
        _  ≥ 7 * 7 := by rel[h]
        _ ≥ 49 := by numbers
    · assumption
    done

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h0 : a ≥ 6 := by addarith[h]

  constructor
  · assumption
  · calc
    3 * a ≥ 3*6 := by rel[h0]
    _ = 18 := by numbers
    _ ≥ 10 := by numbers
  done

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · sorry
  · sorry
  done

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  sorry
  -- Need to specify wether we are demonstrating left or right. Priority goes to ∧
  done
