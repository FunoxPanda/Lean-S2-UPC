/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init

example {P : Prop} (hP : ¬¬P) : P := by
  by_cases hP1 : P
  --· apply hP
  · assumption
  · contradiction
  done

/-! # Exercises -/

example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intro h -- on introduit ¬P → ¬Q (h), puis on dit que Q est vrai (hQ)
    intro hQ
    by_cases hP : P
    · assumption
    · -- à cette étape, on veut exhiber une contradiction DANS LES HYPOTHESES (car on a l'hypothèse ¬P et on veut montrer P)
      -- on sait que ¬P → ¬Q et ¬P est vrai. Montrons alors que ¬Q est vrai
      have hnotQ : ¬Q := by
        apply h -- on sait qu'on a ¬P, alors on utilise h pour montrer ¬Q
        assumption -- on a déjà ¬P en hypothèse
      contradiction -- on a Q et ¬Q, donc on conclut n'importe quoi.
  -- Montrons maintenant (Q → P) → (¬P → ¬Q)
  · intro h hP
    by_cases hQ : Q
    · have hposP : P := by -- Montrons que P est vrai (absurde)
        apply h
        assumption
      contradiction
    · assumption
  done
