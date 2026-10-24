import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.MeasureTheory.LusinCompactProperty
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11CompactSecondJet

* **Conditions:** The actual calibrated core and its full-measure complete second-jet family property under a finite original coordinate law.
* **Objects:** A compact arbitrarily small-loss subcore with continuous actual extension Hessian and all retained family witnesses.
* **Proof detail:** Apply Lusin to the Borel actual Hessian, combine inner regularity with the full-measure good set and retain original core/family properties.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110): Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3): Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11.
- [Sébastien Gouëzel; Yury Kudryashov, mathlib: Derivative is measurable (pinned formal primary source)](https://github.com/leanprover-community/mathlib4/blob/d77ef0741c6da1ff12df68fb4145ea0ae0850c54/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean#L380): Mathlib/Analysis/Calculus/FDeriv/Measurable.lean, module proof description lines 17–55; measurableSet_of_differentiableAt_of_isComplete lines 362–367; measurableSet_of_differentiableAt lines 374–377; measurable_fderiv lines 380–390; measurable_fderiv_apply_const lines 393–395.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11CompactSecondJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11CompactSecondJet`; the selected original proof blocks follow. -/
section

/-!
# Compact original-measure cores carrying complete second-jet families

Discard arbitrarily little of the original coordinate measure to obtain a compact core
with continuous actual extension Hessian. Every retained point has the complete original
potential-level family and its matching second jet, supplied by the calibrated C1,1 theorem.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Every positive original-measure tolerance gives a compact subset with continuous
actual C1,1 Hessian and complete matching potential-level families at all its points.
The density-one and within-derivative conclusions refer to the original contact core. -/
theorem exists_compact_complete_potentialFamily_core (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) (t₀ : ℝ)
    {m ν : Measure E} [IsAddHaarMeasure m] (hν : ν ≪ m)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hνK : ν K ≠ ⊤) {u : M → ℝ}
    (hu : let _instCompactFamilyLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hinterior : let _instCompactFamilyInterior : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm K (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ x ∈ K, HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)
      (fderiv ℝ G x) x) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K' ⊆ K, IsCompact K' ∧ ν (K \ K') < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K' ∧
      ∀ x ∈ K', F.HasC11PotentialFamilyAt m old t₀ u G K x := by
  exact exists_lusin_compact_core_with_ae_property hK.measurableSet hνK
    (measurable_fderiv ℝ (fderiv ℝ G))
    (hF.ae_complete_potentialFamily_of_calibrated_C11_core hcomplete old t₀ hν
      hK hKt hu hinterior hG hLip hval hactual) hε

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
