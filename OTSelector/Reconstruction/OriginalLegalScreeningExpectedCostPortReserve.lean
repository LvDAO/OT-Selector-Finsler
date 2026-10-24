import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostCount
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedPortCountRealMean

/-! Actual unused-endpoint tilt costs pay ports plus raw reserves, without a unit main-count error. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology Module Manifold
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {α β : Measure ℝ}

/-- Actual source and target port masses plus both original raw prefix counts.
These are the possible unused labels charged by bounded probe terms. -/
def originalScreeningRepairCountBudget
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ)
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) : ℝ :=
  ((originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R ell)
    (originalCenteredPhysicalCubeRegion b (2*R)) p.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ).toReal +
  ((originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R ell)
    (originalCenteredPhysicalCubeRegion b (2*R)) p.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ).toReal +
  ((mSourceCount p.2 : ℝ)+(mTargetCount p.2 : ℝ))

/-- The genuine same-frame repair-count budget is integrable, and its normalized
mean tends to twice the raw reserve intensity. The port contribution vanishes
by the actual path-retention proof; the raw contribution uses its exact original law. -/
theorem OriginalSeedConditionalMoments.original_screening_repairCountBudget_mean
    (D : OriginalSeedConditionalMoments S w α β)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {rho : ℝ} (hrho : 0 ≤ rho) {ell : ℝ → ℝ}
    (hell : ∀ᶠ R in atTop, 0 ≤ ell R) (hlarge : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun R ↦ ell R/R) atTop (𝓝 0)) :
    let K := fun R ↦ originalCenteredPhysicalCubeRegion b (2*R)
    let L := fun R ↦ originalMainReserveExperimentLaw Q (Real.toNNReal rho * (volume (K R)).toNNReal)
    (∀ R, Integrable (originalScreeningRepairCountBudget S w b R (ell R)) (L R)) ∧
      Tendsto (fun R : ℝ ↦
        (∫ p, originalScreeningRepairCountBudget S w b R (ell R) p ∂L R) / volume.real (K R))
        atTop (𝓝 (2*rho)) := by
  let q := finrank ℝ S.covector.ker
  let P := (Q.law : Measure (LegalMarkedOptimalInputScene q))
  let K := fun R ↦ originalCenteredPhysicalCubeRegion b (2*R)
  let rate := fun R ↦ Real.toNNReal rho * (volume (K R)).toNNReal
  let Z := fun R ↦ twoMarkedCloudLaw q ℝ ℝ α β (rate R)
  let L := fun R ↦ originalMainReserveExperimentLaw Q (rate R)
  let ports := fun R scene ↦
    ((originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R (ell R))
      (K R) scene : Measure (LegalMarkedPhysicalEdge q)) univ).toReal +
    ((originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R (ell R))
      (K R) scene : Measure (LegalMarkedPhysicalEdge q)) univ).toReal
  let raw := fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦
    (mSourceCount p.2 : ℝ)+(mTargetCount p.2 : ℝ)
  have hp := D.originalOrientedStagePortCount_mean_density_zero hF hw Q b hell hlarge hsmall
  have hpi (R) : Integrable (fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦
      ports R p.1) (L R) := ((hp.1 R).2).comp_fst (Z R)
  have hri (R) : Integrable raw (L R) :=
    ((integrable_mSourceCount q α β (rate R)).add (integrable_mTargetCount q α β (rate R))).comp_snd P
  have hI (R) : Integrable (originalScreeningRepairCountBudget S w b R (ell R)) (L R) :=
    (hpi R).add (hri R)
  refine ⟨hI,?_⟩
  have hl := hp.2.add_const (2*rho)
  simp only [zero_add] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  have hV : 0 < volume.real (K R) := by
    change 0 < (volume (originalCenteredPhysicalCubeRegion b (2*R))).toReal
    rw [volume_originalOrientedTraffic_cube]
    change 0 < volume.real (haarRootCube (Fin q) R)
    rw [volume_real_haarRootCube (Fin q) hR.le,Fintype.card_fin]
    positivity
  have hr : (rate R : ℝ) = rho*volume.real (K R) := by
    simp only [rate,NNReal.coe_mul,Real.coe_toNNReal _ hrho,
      ENNReal.coe_toNNReal_eq_toReal,measureReal_def]
  have hpm : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ,
      ports R p.1 ∂L R) = ∫ scene, ports R scene ∂P := by
    simpa only [L,originalMainReserveExperimentLaw,P,Z,measureReal_def,measure_univ,
      ENNReal.toReal_one,one_smul] using integral_fun_fst (μ := P) (ν := Z R) (ports R)
  have hrm : (∫ p, raw p ∂L R) = 2*(rate R : ℝ) := by
    have h := integral_fun_snd (μ := P) (ν := Z R)
      (fun z ↦ (mSourceCount z : ℝ)+(mTargetCount z : ℝ))
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at h
    change (∫ p, raw p ∂L R) = 2*(rate R : ℝ)
    exact h.trans (by
      rw [integral_add (integrable_mSourceCount q α β (rate R))
        (integrable_mTargetCount q α β (rate R)),integral_mSourceCount_eq,integral_mTargetCount_eq]
      ring)
  have hadd : (∫ p, originalScreeningRepairCountBudget S w b R (ell R) p ∂L R) =
      (∫ p, ports R p.1 ∂L R)+(∫ p, raw p ∂L R) := integral_add (hpi R) (hri R)
  change (∫ scene, ports R scene ∂P) / volume.real (K R)+2*rho =
    (∫ p, originalScreeningRepairCountBudget S w b R (ell R) p ∂L R) / volume.real (K R)
  rw [hadd,hpm,hrm,add_div,hr]
  field_simp [hV.ne']

end OTSelector.Reconstruction
