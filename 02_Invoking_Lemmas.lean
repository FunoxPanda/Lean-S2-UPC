/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


-- lemma ne_of_lt (a b : ℝ ) (h : a < b) : a ≠ b

-- lemma ne_of_gt {a b : ℝ} (h : a > b) : a ≠ b

-- lemma le_antisymm {a b : ℝ} (h1 : a ≤ b) (h2 : b ≤ a) : a = b


example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers
  done

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt;
  extra

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1
  extra
  done


/-! # Exercises -/

example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  have hM : m = 4 := by addarith[hm]
  calc
    3*m = 3*4 := by rw[hM]
    _ > 6 := by numbers
  done


example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by

  have hx : s ≤ -2 := by
    calc
      s = (3*s)/3 := by ring
      _ ≤ -6/3 := by rel[h1]
      _ ≤ -2 := by numbers
    done

  have hy : s ≥ -2 := by
    calc
      s = (2*s)/2 := by ring
      _ ≥ -4/2 := by rel[h2]
      _ ≥ -2 := by numbers
    done

  apply le_antisymm

  addarith [hx]
  addarith [hy]
  done
