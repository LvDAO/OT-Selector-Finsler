import OTSelector.Reconstruction.FinslerOriginalLegalClockMomentsConcrete

/-!
# Compact support of the concrete Poisson clock laws from the input construction

`FinslerOriginalLegalClockMomentsConcrete` reduced the unconditional nonemptiness of
the abstract bounded second-moment class to compact-support data for the two original
clock marginals.  In the legal Poisson input construction those clock laws are the
original conditional clock laws `μ`, `ν` of `OriginalSeedConditionalMoments`, and
their compact supports are exactly the fields of `ConditionalClockSupportBounds`
(compact source/target supports with the original separation and diameter bounds).

This file derives the support data from that construction:

* `measure_compl_support_eq_zero`: the complement of the support of a measure on `ℝ`
  carries no mass, so `μ` is supported in `μ.support`.
* `integrable_sq_clockLaws_of_conditionalSupportBounds`: the two original clock laws
  have finite square moments because their supports are compact.
* `exists_boundedSecondMomentClass_legal_reserve`: the unconditional capstone for the
  concrete legal input construction.  For every original seed conditional-moment
  datum with conditional clock support bounds and a legal coupling of the two clock
  laws, the reserve stationary Poisson matching exists and the abstract bounded
  second-moment class of its recoded legal Palm is genuinely nonempty, with a
  nonnegative bound on the second moment.  No compact-support hypothesis is taken as
  data: it is produced from the conditional support bounds.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology
  Matrix Module Manifold OTSelector.PointProcess OTSelector.Geometry
  ContinuousFinslerNorm OTSelector.Probability
open scoped Topology ContDiff BigOperators Matrix.Norms.Operator

noncomputable section

namespace OTSelector.Reconstruction

open OTSelector.PointProcess
open OTSelector.PointProcess.StationaryForwardMatching

/-! ## Supports and square moments of the clock marginals -/

/-- The complement of the support of a measure on `ℝ` is null. -/
theorem measure_compl_support_eq_zero (μ : Measure ℝ) : μ μ.supportᶜ = 0 :=
  (ae_iff (μ := μ) (p := fun t : ℝ ↦ t ∈ μ.support)).mp μ.support_mem_ae

/-- The two original conditional clock laws have finite square moments: their
supports are compact by the conditional separation bounds. -/
theorem integrable_sq_clockLaws_of_conditionalSupportBounds
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {gap diameter : ℝ}
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) :
    Integrable (fun t : ℝ ↦ t ^ 2) μ ∧ Integrable (fun t : ℝ ↦ t ^ 2) ν :=
  ⟨integrable_sq_of_compact_support hbounds.source_compact
      (measure_compl_support_eq_zero μ),
    integrable_sq_of_compact_support hbounds.target_compact
      (measure_compl_support_eq_zero ν)⟩

/-! ## The concrete reserve matching and its bounded second-moment class -/

/-- Unconditional capstone for the concrete legal Poisson input construction.  Every
original seed conditional-moment datum with conditional clock support bounds and a
legal coupling of its clock laws yields a reserve stationary Poisson matching whose
recoded legal Palm has a genuinely nonempty abstract bounded second-moment class,
with an explicit nonnegative bound.  The compact support of the clock laws is derived
from `ConditionalClockSupportBounds`, not assumed. -/
theorem exists_boundedSecondMomentClass_legal_reserve
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
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2) :
    ∃ (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
          (D.originalFocalKinetic gap) (fun _ _ ↦ (0 : ℝ))) (Bnd : ℝ),
      0 ≤ Bnd ∧
      (boundedSecondMomentClass
        (α := (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).map
          carrierRecodePair |>.map (fun p ↦ p.1.2))
        (β := (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).map
          carrierRecodePair |>.map (fun p ↦ p.2.2)) Bnd).Nonempty := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨Q, _hsecond⟩ := D.exists_original_focal_finiteSecondMoment_stationaryMatching
    hF hw hq hgap hbounds π hπ horder (G := 0) (g := fun _ _ ↦ 0) measurable_const
    (fun _ _ ↦ by simp)
  obtain ⟨Bnd, hBnd0, hne⟩ :=
    exists_nonnegative_bound_boundedSecondMomentClass_legal_compact Q
      hbounds.source_compact hbounds.target_compact
      (measure_compl_support_eq_zero μ) (measure_compl_support_eq_zero ν)
  exact ⟨Q, Bnd, hBnd0, hne⟩

end OTSelector.Reconstruction

end
