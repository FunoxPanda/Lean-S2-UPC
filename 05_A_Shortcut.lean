/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.5: A shortcut -/

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  addarith [h1]
  done

example {a b : ℤ} (ha : a - 2 * b = 1) : a = 2 * b + 1 := by
  addarith[ha]
  done

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 := by
  calc
    x + y ^ 2 = 2 + (-7) := by rw[hx,hy]
    _ = -5 := by ring -- hy==>1 (l'enoncé est vrai logiquement, mais pas mathématiquement, même si y^2 ne PEUT PAS = -7)
  done

example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 := by
  calc
    t + s*t = 4 := by addarith[h]
    _ > 0 := by numbers
  done

example {m n : ℝ} (h1 : m ≤ 8 - n) : 10 > m + n := by
  calc
    m + n ≤ 8 := by addarith[h1]
    _ < 10 := by numbers
  done

-- Vérifiez que `addarith` ne peut pas vérifier cette déduction
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  addarith [h1]
  done
