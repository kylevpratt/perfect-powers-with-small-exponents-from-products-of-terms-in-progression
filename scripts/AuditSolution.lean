module

import Solution

/-! # Dependency audit for all Comparator targets

Each target should depend only on `propext`, `Classical.choice`, and
`Quot.sound`. This module imports Solution, never Challenge.
-/

#print axioms PerfectPowersChallenge.main_results
#print axioms PerfectPowersChallenge.lemma_3_6
#print axioms PerfectPowersChallenge.consecutive_product_nonsquare
