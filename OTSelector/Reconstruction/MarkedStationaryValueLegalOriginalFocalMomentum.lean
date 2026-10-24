import OTSelector.LinearAlgebra.Matrix.QuadraticMomentumBound
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryTightCut
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalKinetic

/-!
# Genuine original focal weighted energy gives a finite momentum second moment

The original coefficient is uniformly bounded above by its actual support
separation, while its lower eigenvalues may tend to zero at focal endpoints.
The momentum square is therefore dominated by the original weighted kinetic
energy, with no unweighted displacement second-moment premise.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
local instance markedStationaryValueLegalOriginalFocalMomentumPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The literal original coefficient times the entire original transverse
matching displacement, in the fixed original seed basis. -/
def originalSeedPairMomentum (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) : Fin (finrank ℝ S.covector.ker) → ℝ :=
  originalSeedPairCoefficient S w m.1 *ᵥ m.2

theorem measurable_originalSeedPairMomentum (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels) :
    Measurable (originalSeedPairMomentum S w) := by
  have hc : Continuous (fun p : Matrix (Fin (finrank ℝ S.covector.ker))
      (Fin (finrank ℝ S.covector.ker)) ℝ × (Fin (finrank ℝ S.covector.ker) → ℝ) ↦ p.1 *ᵥ p.2) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  exact hc.measurable.comp (((measurable_originalSeedPairCoefficient S hF hw).comp measurable_fst).prodMk
    measurable_snd)

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Every actual original weighted stationary matching has finite original
momentum and momentum-square readouts, without a finite unweighted displacement
moment. All matrix bounds come from the original conditional geometry. -/
theorem integrable_original_pair_momentum_of_weighted_stationary
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    Integrable (originalSeedPairMomentum S w) (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      Integrable (fun m ↦ ‖originalSeedPairMomentum S w m‖ ^ 2)
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have : IsProbabilityMeasure η := Q.palm_probability
  have hs : ∀ᵐ m ∂η, m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support := by
    have h : ∀ᵐ a ∂μ, a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support :=
      D.support.source.ae_open.and μ.support_mem_ae
    have hmap : ∀ᵐ a ∂η.map (fun m ↦ m.1.1),
        a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support := by
      simpa only [η, Q.source_clock] using h
    exact ae_of_ae_map measurable_fst.fst.aemeasurable hmap
  have ht : ∀ᵐ m ∂η, m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support := by
    have h : ∀ᵐ b ∂ν, b - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support :=
      D.support.target.ae_open.and ν.support_mem_ae
    have hmap : ∀ᵐ b ∂η.map (fun m ↦ m.1.2),
        b - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support := by
      simpa only [η, Q.target_clock] using h
    exact ae_of_ae_map measurable_fst.snd.aemeasurable hmap
  obtain ⟨C, hC, hbound⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  have hm := measurable_originalSeedPairMomentum S hF hw
  have hsq : Integrable (fun m ↦ ‖originalSeedPairMomentum S w m‖ ^ 2) η := by
    apply (Q.kinetic_integrable.const_mul (4 * C)).mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hs, ht, Q.ae_palm_forward] with m hms hmt hmf
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hpd := (D.pair_compliance_posDef hF hw hms.1 hmt.1 hmf).2
    have hquad (v : Fin (finrank ℝ S.covector.ker) → ℝ) :
        |matrixQuadratic (originalSeedPairCoefficient S w m.1) v| ≤ C * ∑ i, v i ^ 2 := by
      rw [← D.originalFocalKinetic_eq_of_original_support hbounds hms hmt hmf v]
      exact hbound m.1.1 m.1.2 v
    have h := norm_mulVec_sq_le_quadratic_of_sum_bound hpd.posSemidef hC hquad m.2
    rw [← D.originalFocalKinetic_eq_of_original_support hbounds hms hmt hmf m.2] at h
    exact h
  refine ⟨?_, hsq⟩
  apply ((integrable_const (1 : ℝ)).add hsq).mono' hm.aestronglyMeasurable
  filter_upwards with m
  change ‖originalSeedPairMomentum S w m‖ ≤ 1 + ‖originalSeedPairMomentum S w m‖ ^ 2
  nlinarith [sq_nonneg (‖originalSeedPairMomentum S w m‖ - 1 / 2)]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
