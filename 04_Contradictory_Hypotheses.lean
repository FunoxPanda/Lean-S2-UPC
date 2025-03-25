/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- mul_eq_zero {a b : ℝ} : a * b = 0 ↔ a = 0 ∨ b = 0
-- not_lt_of_ge {a b : ℝ} (h : a ≥ b) : ¬a < b

example (x y : ℝ) (hx1 : x = 1) (hx2 : x = 2) : y = 4 := by
  have hx3 : x ≠ 1 := by
    rw [hx2]
    numbers
  contradiction
  done


example (x y : ℝ) (hx1 : x = 1) (hx2 : x = 2) : y = 4 := by
  rw [hx1] at hx2
  numbers at hx2
  done



example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have H : ¬(0 < x * y)
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    assumption
  done


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H : (7 : ℤ) < 3 :=
    calc
      7 = t := by addarith [h]
      _ < 3 := h2
  have H1 : ¬(7 : ℤ) < 3 := by numbers
  contradiction
  done


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H : (7 : ℤ) < 3 :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!
  done


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  have H1 := le_or_succ_le a 2
  obtain H2 | H3 := H1
  · have H4 := le_or_succ_le b 1
    obtain H5 | H6 := H4
    · interval_cases b
      interval_cases a
      · sorry
      · sorry
    · have H7 : c < b + 1 := by sorry
      have H8 : ¬ c < b + 1 := by
        apply not_lt_of_le
        sorry
      contradiction
  · assumption
  done

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) : y ≤ x := by
  obtain hy_le | hy_ge : y ≤ x ∨ x < y := le_or_lt y x
  · assumption
  · have H3 : x^n < y^n := by rel [hy_ge]
    have HF : ¬(x^n < y^n) := by
      apply not_lt_of_ge -- on dit que la négat° c'est la même chose que l'hypothèse h
      assumption
    contradiction
  done


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 : (x + 2) * (x - 2) = 0 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain H1 | H2 := h3
  · have H4 : x+2>0 := by calc
      x + 2 > 1+ 2 := by rel[h2]
      _ > 0 := by numbers
    have H5 : ¬ (x+2=0) := by
      apply ne_of_gt
      assumption
    contradiction
  · calc
      x = x - 2 + 2 := by ring
      _ = 0 + 2 := by rw[H2]
      _ = 2 := by numbers
    done
  done
