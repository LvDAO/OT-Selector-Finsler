import Mathlib.MeasureTheory.Measure.Haar.Unique
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.TubeParameterProduct.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.TubeParameterProduct`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.TubeParameterProduct

* **Conditions:** A continuous linear normalization R×W≃E and an additive Haar reference, with finite dimensions only for constructing the product decomposition.
* **Objects:** An exact time-Lebesgue/transverse-Haar product reference, including the full scalar normalization and a unit-slab identity.
* **Proof detail:** Use uniqueness of Haar measure up to a positive scalar, absorb that scalar into transverse Haar measure and evaluate a product rectangle of unit time length.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 44](https://www1.essex.ac.uk/maths/people/fremlin/chap44.pdf#page=12): Theorem 442B, pp. 12–13; Lemma 442A, p. 12 (Haar positivity/local finiteness).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.

Source relation (derived): A derived product-Haar normalization valid also for zero-dimensional W; no Euclidean inner product is introduced.
-/

/-!
# Exact time and label product reference for normalized parameters

The actual reference transported by a continuous linear normalization is a product
of ordinary time Lebesgue measure and an additive Haar measure on the label space.
The latter retains the complete positive normalization factor. No inner product or
nontriviality of the label space is required, including in dimension zero.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace W] [BorelSpace W]

/-- The actual transported parameter measure has an exact product decomposition;
the label Haar measure absorbs the entire normalization scalar. -/
theorem exists_tubeParameterMeasure_eq_volume_prod
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
    (ℓ : (ℝ × W) ≃L[ℝ] E) (m : Measure E) [m.IsAddHaarMeasure] :
    ∃ κ : Measure W, κ.IsAddHaarMeasure ∧
      tubeParameterMeasure ℓ m = (volume : Measure ℝ).prod κ := by
  let κ₀ : Measure W := Measure.addHaar
  let ν : Measure (ℝ × W) := tubeParameterMeasure ℓ m
  let q : Measure (ℝ × W) := (volume : Measure ℝ).prod κ₀
  have : κ₀.IsAddHaarMeasure := inferInstance
  have : ν.IsAddHaarMeasure := ℓ.symm.isAddHaarMeasure_map m
  have : q.IsAddHaarMeasure := inferInstance
  let c : ℝ≥0 := Measure.addHaarScalarFactor ν q
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν q
  refine ⟨c • κ₀, Measure.IsAddHaarMeasure.nnreal_smul κ₀ hc.ne', ?_⟩
  change ν = (volume : Measure ℝ).prod (c • κ₀)
  rw [Measure.prod_smul_right]
  exact Measure.isAddLeftInvariant_eq_smul ν q

omit [BorelSpace E] [BorelSpace W] in
/-- A unit time slab recovers the exact label normalization on every label set. -/
theorem tubeParameterMeasure_unitTimeSlab
    (ℓ : (ℝ × W) ≃L[ℝ] E) (m : Measure E) (κ : Measure W) [SFinite κ]
    (hprod : tubeParameterMeasure ℓ m = (volume : Measure ℝ).prod κ) (A : Set W) :
    tubeParameterMeasure ℓ m (Icc (0 : ℝ) 1 ×ˢ A) = κ A := by
  rw [hprod, Measure.prod_prod, Real.volume_Icc]
  simp

end OTSelector.Geometry

end
end
