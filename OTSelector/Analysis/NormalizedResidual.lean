import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

/-!
## Lemma skeleton

* **Conditions:** Eventually nonnegative denominators and an absolute majorant whose normalized value tends to zero.
* **Objects:** A signed normalized residual along any filter.
* **Proof detail:** Divide the absolute bound using nonnegativity, then apply the zero/squeeze test.

## Mathematical sources

* Terence Tao, *Analysis I*, Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).
  https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean

**Relationship to the sources:** The source is sequential; the arbitrary-filter formulation and totalized division at zero are Lean-specific generalizations proved here.
-/

/-! # Normalized error estimates

A signed error vanishes whenever its absolute value has a vanishing nonnegative
normalized majorant. The normalization and filter are arbitrary.

## Mathematical source

Terence Tao, *Analysis I*, §6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17
(zero test). The author's companion formalization records these statement numbers:
https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean .
The lemma here is the filter-form corollary; the eventual nonnegative denominator
and Lean's real division convention also allow a zero denominator.

-/

open Filter
open scoped Topology

namespace OTSelector.Analysis

/-- A vanishing normalized absolute majorant controls the signed normalized error. -/
theorem tendsto_div_zero_of_abs_le
    {J : Type*} {l : Filter J} (R ρ b : J → ℝ)
    (hb : ∀ᶠ j in l, 0 ≤ b j) (hbound : ∀ᶠ j in l, |R j| ≤ ρ j)
    (hlim : Tendsto (fun j ↦ ρ j / b j) l (𝓝 0)) :
    Tendsto (fun j ↦ R j / b j) l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) _ hlim
  filter_upwards [hb, hbound] with j hj hR
  rw [abs_div, abs_of_nonneg hj]
  exact div_le_div_of_nonneg_right hR hj

end OTSelector.Analysis
