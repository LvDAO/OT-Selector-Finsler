import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostWorkingValue

/-! Actual finite legal optima on bad observations pay the original joint count cost. -/
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

/-- The actual FULL optimum on any jointly selected bad observation costs at
most its genuine coarse physical bound times the unchanged main/raw count.
Full-array and sampler identities, L1 and count bounds are all supplied internally. -/
theorem integral_bad_original_screening_fullValue_le
    (hR : 0 ≤ R) {C G : ℝ} (hC : 0 ≤ C)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C*∑ i, v i^2)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (bad : Set (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)) (hbad : MeasurableSet bad) :
    let view := fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (p.1.1,p.1.2.2)
    (∫ p, (view ⁻¹' bad).indicator (fun p ↦ originalScreeningFullValue b R kin g t p.2) p
      ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))) ≤
      (4*C*(q : ℝ)*R^2+|t| * G) *
        ∫ p, bad.indicator (originalScreeningFullExperimentCount
          (originalCenteredPhysicalCubeRegion b (2*R))) p
          ∂originalMainReserveExperimentLaw Main (Real.toNNReal rho *
            (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal) := by
  let A := 4*C*(q : ℝ)*R^2+|t| * G
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  let P := originalMainReserveExperimentLaw Main (Real.toNNReal rho * (volume K).toNNReal)
  let J := (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
  let view := fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
    (p.1.1,p.1.2.2)
  have hv : Measurable view := measurable_fst.fst.prodMk measurable_fst.snd.snd
  have hp : MeasurePreserving view J P := ⟨hv,X.fullLaw_main_sampler⟩
  have hN := (Main.original_screening_fullExperimentCount
    (Real.toNNReal rho * (volume K).toNNReal)
    (isCompact_originalStagePhysicalCube b (2*R)).measurableSet
    (isCompact_originalStagePhysicalCube b (2*R)).measure_ne_top).1.indicator hbad
  have hnI := hp.integrable_comp_of_integrable hN
  have hV := X.original_screening_fullValue_integrable_and_ae_bound hR hC hk hkb hg hgb t
  have hb : (∫ p, (view ⁻¹' bad).indicator (fun p ↦ originalScreeningFullValue b R kin g t p.2) p ∂J) ≤
      ∫ p, A*bad.indicator (originalScreeningFullExperimentCount K) (view p) ∂J := by
    apply integral_mono_ae (hV.1.indicator (hbad.preimage hv)) (hnI.const_mul A)
    filter_upwards [hV.2] with p hvb
    by_cases hpb : view p ∈ bad
    · change (view ⁻¹' bad).indicator (fun p ↦ originalScreeningFullValue b R kin g t p.2) p ≤
        A*bad.indicator (originalScreeningFullExperimentCount K) (view p)
      rw [indicator_of_mem (show p ∈ view ⁻¹' bad from hpb),indicator_of_mem hpb]
      exact (le_abs_self _).trans (hvb.trans_eq (by ring))
    · simp [hpb]
  exact hb.trans_eq ((integral_const_mul A _).trans
    (congrArg (fun x : ℝ ↦ A*x) (hp.hasLaw.integral_comp hN.aestronglyMeasurable)))

end OriginalReserveFullWorkingInputExperiment
end OTSelector.Reconstruction
