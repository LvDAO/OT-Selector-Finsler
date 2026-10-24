import Mathlib.Order.Filter.Curry
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Topology.CurriedIteratedLimit

Conditions: A nonnegative extended-real array has row limits and a compatible outer limit, and the reindexed array tends to zero on the curried filter.

Objects: The same iterated limiting value is zero.

Proof detail: A curried eventual upper bound gives eventual outer bounds on each row limit; pass first through the inner limit, then through the outer limit and use uniqueness.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=86): Section 1.6.2, Definition 1.6.15 and Exercise 1.6.8, pp. 77–78.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean): Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation: Derived ordered-limit corollary with explicit ENNReal conventions.
-/

/-! A vanishing curried readout fixes the same iterated limiting expectation. -/
open Filter
open scoped Topology ENNReal
namespace OTSelector.Reconstruction

/-- The sample limit at fixed tilt followed by the outer limit is zero when
the actual sample-before-tilt readouts vanish on the curried filter. -/
theorem ennreal_iterated_readout_eq_zero_of_curry_tendsto_zero
    (A : ℕ → ℕ → ℝ≥0∞) (B : ℕ → ℝ≥0∞) (C : ℝ≥0∞) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (A ℓ) atTop (𝓝 (B ℓ)))
    (houter : Tendsto (fun ℓ ↦ B (ψ ℓ)) atTop (𝓝 C))
    (hzero : Tendsto (fun p : ℕ × ℕ ↦ A (ψ p.1) p.2)
      ((atTop : Filter ℕ).curry atTop) (𝓝 0)) : C = 0 := by
  apply tendsto_nhds_unique houter
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hA := eventually_curry_iff.mp (ENNReal.tendsto_nhds_zero.mp hzero ε hε)
  filter_upwards [hA] with ℓ hℓ
  exact le_of_tendsto (hinner (ψ ℓ)) hℓ

end OTSelector.Reconstruction
