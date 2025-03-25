/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.4: Proving inequalities -/


-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers
  done

-- Example 1.4.2
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  calc
    r = ((s + r) + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by rel[h1,h2]
    _ = 3 := by ring
  done

-- Example 1.4.3
-- Exercice : écrire l'ensemble de la preuve dans comme une preuve en Lean.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 := by
  calc
    x + y ≤ -2 + y := by rel[h2]
    _ ≤ -2 + (x + 5) := by rel[h1]
    _ ≤ -2 + (-2 + 5) := by rel[h2]
    _ = 1 := by ring
    _ < 2 := by numbers
  done

-- Example 1.4.4
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B := by
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel[h4,h5]
    _ ≤ A * B + A * B + A * v := by rel[h8, h9]
    _ ≤ A * B + A * B + 1 * v := by rel[h2]
    _ ≤ A * B + A * B + B * v := by rel[h3]
    _ < A * B + A * B + B * A := by rel[h9]
    _ = 3 * A * B := by ring
  done

-- Example 1.4.5
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by
  calc
    t ^ 2 - 3 * t - 17 = t*t - 3*t -17 := by ring
    _ ≥ 10*t - 3*t - 17 := by rel[ht]
    _ = 7*t - 17 := by ring
    _ ≥ 7*10 - 17 := by rel[ht]
    _ ≥ 5 := by numbers
  done

-- Example 1.4.6
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 := by
  sorry
  done

-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 := by
  calc
    n ≤ m ^ 2 + n := by extra -- extra: hypothèse de m^2>=0 <==> by rel [m^2>=0]
    _ ≤ 2 := by rel [h]
  done


-- Example 1.4.8
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 := by
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by rel[h]
    _ < 3 := by numbers
  done

-- Example 1.4.9
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) : 3 * a * b + a ≤ 7 * b + 72 := by
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by extra
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by rel[h3]
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by rel[h3]
    _ = 7 * b + 72 := by ring
  done

-- Example 1.4.10
example {a b c : ℝ} :
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
      ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2
          + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
          + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) := by extra
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by ring
  done


/-! # Exercises

Résolvez ces problèmes vous-même.  Il peut être utile de les résoudre sur papier avant de
les saisir dans Lean. -/


example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2*y -3 := by rel[h1]
    _ ≥ 2*1 -3  := by rel[h2]
    _ = -1 := by numbers
  done

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by
  calc
    a + b = (2*a+2*b)/2 := by ring
    _ = (a + (a + 2*b))/2 := by ring
    _ ≥ (a+4)/2 := by rel[h2]
    _ ≥ (3+4)/2 := by rel[h1]
    _ ≥ 3 := by numbers
  done

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x*x^2 - 8 * x ^ 2 + 2 * x := by ring
    _ ≥ 9*x^2 - 8 * x ^ 2 + 2 * x := by rel[hx]
    _ = x^2 +2*x := by ring
    _ ≥ 9^2 + 2*9 := by rel[hx]
    _ ≥ 3 := by numbers
  done

example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 := by
  sorry
    /-
    n ^ 4 - 2 * n ^ 2 = n ^ 2 * n ^ 2 - 2*n ^ 2 := by ring
    _ = n*n *n^2 -2*n^2 := by ring
    _ ≤ 10*10*n^10 - 2*n^2 := by rel[hn]
    _ = 98*n^2 := by ring-/
  done

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 := by
  sorry
  done

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := by
  sorry
  done

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  sorry
  done
