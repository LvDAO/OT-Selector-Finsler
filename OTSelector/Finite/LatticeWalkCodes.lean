import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Finite.LatticeWalkCodes

## Lemma skeleton

* **Conditions:** A natural lattice dimension d and step count m≥1.

* **Objects:** A finite code type for a bounded starting point and ternary coordinate steps, with its exact and exponential cardinality.

* **Proof detail:** Multiply cardinalities of the starting box and the m step vectors. Bound the polynomial starting factor and fixed step factor by exponentials and combine their exponents.

## Mathematical sources

- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
- [OTSelector project, Finite phase-animal counting in the high-dimensional localization proof](main.tex#eq:highd-phase-animal-tail): main.tex label eq:highd-phase-animal-tail, line 3267.

Source relation (composition): The particular code and exponential constant are project-specific deterministic counting; no claim is made that every geometric phase curve already has such a code.
-/

/-!
# Finite phase-walk codes with an internal exponential cardinality bound

A code records a lattice starting point in a radius-m box and m coordinate
steps in {-1,0,1}. It provides a deterministic candidate family before any
adaptive phase curve is observed.
-/
open scoped BigOperators
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1200000

/-- A finite code for m bounded lattice steps in d phase coordinates. -/
abbrev PhaseWalkCode (d m : ℕ) := (Fin d → Fin (2 * m + 1)) × (Fin m → Fin d → Fin 3)

/-- The exact size of the deterministic code space. -/
theorem card_phaseWalkCode (d m : ℕ) :
    Fintype.card (PhaseWalkCode d m) = (2 * m + 1) ^ d * (3 ^ d) ^ m := by
  simp [PhaseWalkCode, Fintype.card_prod]

/-- The polynomial number of roots is absorbed in one dimension-dependent exponential.
No candidate-cardinality estimate is supplied by the user of the eventual count bound. -/
theorem card_phaseWalkCode_le_exp (d m : ℕ) (hm : 1 ≤ m) :
    (Fintype.card (PhaseWalkCode d m) : ℝ) ≤
      Real.exp ((3 * (d : ℝ) + (3 : ℝ) ^ d) * (m : ℝ)) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : (2 * m + 1 : ℝ) ≤ Real.exp (3 * (m : ℝ)) := by
    have he := Real.add_one_le_exp (3 * (m : ℝ))
    linarith
  have hs : (3 : ℝ) ^ d ≤ Real.exp ((3 : ℝ) ^ d) := by
    have he := Real.add_one_le_exp ((3 : ℝ) ^ d)
    linarith
  have hroot := pow_le_pow_left₀ (show 0 ≤ (2 * m + 1 : ℝ) by positivity) hr d
  have hstep := pow_le_pow_left₀ (show 0 ≤ (3 : ℝ) ^ d by positivity) hs m
  rw [card_phaseWalkCode]
  push_cast
  calc
    _ ≤ (Real.exp (3 * (m : ℝ))) ^ d * (Real.exp ((3 : ℝ) ^ d)) ^ m :=
      mul_le_mul hroot hstep (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

end OTSelector.Reconstruction
