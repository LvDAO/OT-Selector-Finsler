import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostFiniteValue
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostCount
import OTSelector.Reconstruction.OriginalReserveWorkingFullTotalCounts

/-! The same original working experiment has its true finite legal-value marginal and integrability. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace OriginalReserveFullWorkingInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))} {rho R : ℝ}
  (X : OriginalReserveFullWorkingInputExperiment Main Reserve b rho R)

/-- The literal FULL finite value has exactly its genuine original full-cloud
mean. This uses the full marginal only as a scalar readout, without introducing
FULL as auxiliary data in any selected-position iid statement. -/
theorem integral_original_screening_fullValue
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    (∫ p, originalScreeningFullValue b R kin g t p.2
      ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))) =
      ∫ cloud, originalScreeningFullValue b R kin g t cloud
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (1+rho) *
          (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal) := by
  have hp : MeasurePreserving Prod.snd
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
      (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (1+rho) *
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) :=
    ⟨measurable_snd,X.fullLaw_full_sampler⟩
  exact hp.hasLaw.integral_comp (measurable_originalScreeningFullValue b R hk hg t).aestronglyMeasurable

/-- Original FULL-array identities make the physical finite legal optimum L1
on the same working experiment and bound it by the exact main-plus-raw count.
No screened plan, independent bad event or finite-value estimate is supplied. -/
theorem original_screening_fullValue_integrable_and_ae_bound
    (hR : 0 ≤ R) {C G : ℝ} (hC : 0 ≤ C)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C*∑ i, v i^2)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (fun p ↦ originalScreeningFullValue b R kin g t p.2)
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) ∧
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      |originalScreeningFullValue b R kin g t p.2| ≤
        originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))
          (p.1.1,p.1.2.2) * (4*C*(q : ℝ)*R^2+|t| * G) := by
  let rate := Real.toNNReal (1+rho) * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal
  have hp : MeasurePreserving Prod.snd
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
      (twoMarkedCloudLaw q ℝ ℝ α β rate) := ⟨measurable_snd,X.fullLaw_full_sampler⟩
  have h := originalScreeningFullValue_integrable_and_ae_bound α β b hR rate hC hk hkb hg hgb t
  refine ⟨hp.integrable_comp_of_integrable h.1,?_⟩
  filter_upwards [hp.quasiMeasurePreserving.ae h.2,X.ae_fullArray_total_counts] with p hb hc
  have heq : (mSourceCount p.2 : ℝ)+(mTargetCount p.2 : ℝ) =
      originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))
        (p.1.1,p.1.2.2) := by
    simpa only [originalScreeningFullExperimentCount,mSourceCount,mTargetCount,add_assoc] using hc.2
  have hA : 0 ≤ 4*C*(q : ℝ)*R^2+|t| * G := by
    have hG : 0 ≤ G := (abs_nonneg (g 0 0)).trans (hgb 0 0)
    positivity
  exact hb.trans (mul_le_mul_of_nonneg_right
    ((le_add_of_nonneg_right (Nat.cast_nonneg (mTargetCount p.2))).trans_eq heq) hA)

end OriginalReserveFullWorkingInputExperiment
end OTSelector.Reconstruction
