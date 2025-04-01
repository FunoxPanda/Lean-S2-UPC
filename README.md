# Introduction

Il s'agit de mon travail relatif au cours **Démontrer avec un ordinateur** visant à présenter une première approche de Lean. Le cours est réalisé par *Ricardo Brasca*. 

Tous droits réservés à l'Université Paris Cité.
Année universaire 2024-2025, semestre 2 - Université Paris Cité

# Sommaire

Ce cours est divisé en plusieurs chapitres. Vous trouverez ci-dessous lesdits chapitres vus en cours.
**Merci de signaler tout lien cassé, ce sommaire permet une navigation plus simple et claire.**

Les cours suivant sont triés par ordre chronologique.

### Preuves par calculs
- [Prouver des égalités](02_Proving_Equalities_in_Lean.lean)
- [Tips and tricks](03_Tips_and_Tricks.lean)
- [Prouver des inégalités](04_Proving_Inequalities.lean)
- [Raccourcis](05_A_Shortcut.lean)

### Preuves avec structure (partie 1)
- [Utiliser des étapes intermédiaires](01_Intermediate_Steps.lean)
- [Appliquer des lemmes & théorèmes](02_Invoking_Lemmas.lean)
- [Preuves de disjonctions](03_Or.lean)
- [Preuves de conjonctions](04_And.lean)
- [Preuves d'existence](05_Exists.lean)

### Preuves avec structure (partie 2)
- [Implication pour tout objet](01_Forall_Implies.lean)
- [Relation d'équivalence (ssi.)](02_Iff.lean)
- [Contradiction d'hypothèses](04_Contradictory_Hypotheses.lean)
- [Preuves par contradiction](05_Proofs_by_Contradiction.lean)

### Logique
- [Sous-cas de proposition mathématiques](02_Excluded_Middle.lean)

### Méthodes de raisonnement (Induction)
- [Preuves par récurrence](01_Induction.lean)

### Fonctions
- [Fonctions injectives et surjectives](01_Injective_Surjective.lean)

# Tactiques
- ``sorry`` : quand on ne sait pas, ou que Lean ne fonctionne pas _(ce qui arrive souvent visiblement)_
- ``calc`` : faire un calcul _(i.e. débuter une sous-preuve)_
- ``ring`` : faire calcul littéral
- ``rw[hypothese]`` : remplacer une hypothèse connue
- ``apply [lemme]`` : appeler un [lemme](lemmes.lean)
- ``numbers`` : faire une relation entre nombres (calcul ou relation d'ordre)
- ``extra`` : rappeler à Lean qu'un carré est positif *(à vérifier)*
- ``addarith`` : faire une opération algébrique rapide (y+2=-4 alors y=-2)
- ``have [nom] : [hypothese] := by [tactique]`` : créer une nouvelle hypothèse
- ``obtain hx | hy := [hypothese]`` : découper une hypothèse avec un "ou" ou un "et" en deux
- ``constructor`` : diviser un objectif avec un "ou", "ssi" ou un "et" en deux
- ``intro [var]`` : introduire une variable d'un "quelque soit" *(si var est une hypothèse, il suppose que l'hypothèse est vraie)*
- ``assumption`` : rappeler à Lean qu'on a déjà ce qu'on attend dans les hypothèses
- ``cancel [var] at [hypothese]`` : simplifier par [var] l'énoncé
- ``use [nombre]`` : mettre en avant un témoin existentiel *(pratique pour montrer un il existe)*
- ``contradiction`` : rappeler à Lean qu'on a deux **hypothèses** contradictoires
- ``interval_cases`` : ***ne sait pas, à revoir***
- ``by_cases`` : vérifier les deux cas d'une proposition (P et non P)
- ``simple_induction n with k IH`` : démarrer une récurrence pour n >= 0
- ``induction_from_starting_point n, hn with k hk IH`` : démarrer une récurrence pour n à partir de n >= ?? *(?? = hypothèse)*
- **(New, 1er avril 🐟)** ``def [nom de la fonction] (x : ℝ) : ℝ := [valeur de f(x)]`` : définir une fonction
- **(New, 1er avril 🐟)** ``dsimp [définition]`` : met la définion en hypothèse **(dans notre cas: Injective, Surjective)**fonction
- **(New, 1er avril 🐟)** ``dsimp [définition] at [hypothese]`` : met la définion dans l'hypothèse **(dans notre cas: expliciter ``f(x)``)**
- **(New, 1er avril 🐟)** ``pushneg ([hypothese])`` : développe la négation dans l'énoncé de l'hypothèse _(si non spécifiée, dans toutes)_
  
  # Autres et utile

  Si on ne veut pas nommer une fonction, on peut faire une syntaxe dans ce style :
  ```lean
  example : ¬Injective(fun x : ℝ ↦ x^2)
  ```
