import OTSelector.Reconstruction.FinslerOriginalPoissonClockSupport
import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation

/-!
# Conditional clock support bounds from the raw Poisson input construction

`FinslerOriginalPoissonClockSupport` derived the finite clock-marginal second
moments from `ConditionalClockSupportBounds`, taking the conditional support
bounds as hypotheses.  This file closes the two remaining gaps of that file.

## 1.  `ConditionalClockSupportBounds` from the raw Poisson input data

`exists_population_conditional_separation` (FinslerPopulationConditionalSeparation)
produces, from the raw original input laws `μ`, `ν` on the physical carrier `M`, a
measurable label map `a`, the continuous clock `u`, compact disjoint carriers `A`,
`B` carrying the two inputs almost surely, and the ordered-calibration condition,
a positive separation `δ` and the diameter `D = diam (A ∪ B)` such that for the
label law `μ.map a`, almost every label `z` satisfies
`ConditionalClockSupportBounds (condDistrib u a μ z) (condDistrib u a ν z) δ D`.
We restate this in the exact interface of the clock support file and add the
finite square moments of the conditional clock laws.

## 2.  Arbitrary legal matching and bounded measurable probe

The reserve construction works for an arbitrary bounded measurable probe `g`, not
only the zero probe.  We run the reserve theorem with `g` and the second-moment
class capstone on the resulting matching, extending the capstone to
`exists_boundedSecondMomentClass_legal_reserve_probe`.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology
  Matrix Module Manifold OTSelector.PointProcess OTSelector.Geometry
  ContinuousFinslerNorm OTSelector.Probability
open scoped Topology ContDiff BigOperators Matrix.Norms.Operator

noncomputable section

set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

open OTSelector.PointProcess
open OTSelector.PointProcess.StationaryForwardMatching

/-! ## 1. Conditional clock support bounds from raw input data -/

/-- From the raw Poisson input data (original input laws on the carrier, a
measurable label map, the continuous clock, compact disjoint carriers and the
ordered-calibration condition) the conditional clock laws of almost every label
satisfy `ConditionalClockSupportBounds` and have finite square moments. -/
theorem exists_conditionalClockSupportBounds_and_sqMoments_of_raw_input
    {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z] [MeasurableEq Z]
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : M → Z} (ha : Measurable a) (hbalance : μ.map a = ν.map a)
    {u : M → ℝ} (hu : Continuous u) {A B N : Set M}
    (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hN : MeasurableSet N)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ x ∂ν, x ∈ B)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ x ∂ν, x ∈ N)
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    ∃ δ > 0, ∃ D : ℝ,
      ∀ᵐ z ∂(μ.map a),
        ConditionalClockSupportBounds (condDistrib u a μ z) (condDistrib u a ν z) δ D ∧
        Integrable (fun t : ℝ ↦ t ^ 2) (condDistrib u a μ z) ∧
        Integrable (fun t : ℝ ↦ t ^ 2) (condDistrib u a ν z) := by
  obtain ⟨δ, hδ, hlaw⟩ := exists_population_conditional_separation μ ν ha hbalance
    hu hA hB hAB hN hμA hνB hμN hνN horder
  refine ⟨δ, hδ, Metric.diam (A ∪ B), ?_⟩
  filter_upwards [hlaw] with z hz
  haveI : IsProbabilityMeasure (condDistrib u a μ z) := inferInstance
  haveI : IsProbabilityMeasure (condDistrib u a ν z) := inferInstance
  exact ⟨hz, integrable_sq_clockLaws_of_conditionalSupportBounds hz⟩

/-! ## 2. The reserve capstone for an arbitrary bounded measurable probe -/

/-- Unconditional capstone for the concrete legal Poisson input construction with an
arbitrary bounded measurable clock probe `g`: the reserve stationary Poisson
matching with probe `g` exists and its recoded legal Palm has a genuinely nonempty
abstract bounded second-moment class with an explicit nonnegative bound. -/
theorem exists_boundedSecondMomentClass_legal_reserve_probe
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {F : ContinuousFinslerNorm E M} {u : M → ℝ}
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
          (D.originalFocalKinetic gap) g) (Bnd : ℝ),
      0 ≤ Bnd ∧
      (boundedSecondMomentClass
        (α := (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).map
          carrierRecodePair |>.map (fun p ↦ p.1.2))
        (β := (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).map
          carrierRecodePair |>.map (fun p ↦ p.2.2)) Bnd).Nonempty := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨Q, _hsecond⟩ := D.exists_original_focal_finiteSecondMoment_stationaryMatching
    hF hw hq hgap hbounds π hπ horder (G := G) (g := g) hg hgb
  obtain ⟨Bnd, hBnd0, hne⟩ :=
    exists_nonnegative_bound_boundedSecondMomentClass_legal_compact Q
      hbounds.source_compact hbounds.target_compact
      (measure_compl_support_eq_zero μ) (measure_compl_support_eq_zero ν)
  exact ⟨Q, Bnd, hBnd0, hne⟩

end OTSelector.Reconstruction

end
