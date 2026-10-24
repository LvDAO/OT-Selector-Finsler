import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostCompleteBudget
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostWorkingValue
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostRetained
import OTSelector.MeasureTheory.SignedGoodBadBound

/-! The genuine same-experiment good-event comparator extends through actual bad observations. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {α β : Measure ℝ}

omit [BorelSpace E] in
/-- Every actual repair term is nonnegative; the signed retained core is excluded. -/
theorem originalScreeningCompleteCostBudget_repair_nonneg
    {I J : Type*} [Fintype I] [Fintype J]
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : I → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) (R ell : ℝ)
    (s t weight : I → ℝ)
    (hj : ∀ i k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (s i) (t i)) scene k) 2 (Q.law : Measure _))
    (rho : ℝ) (grid : OriginalStageClockGrid) (r : ℝ) (cuts ε : J → ℝ) (C Ltilt : ℝ)
    {H : Type*} [Fintype H] (RS RT RCs RCt RDs RDt : H → Set ℝ) (τ : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hL : 0 ≤ Ltilt) (hweight : ∀ i, 0 ≤ weight i)
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) :
    let core := ∫ e, originalWeightedEdgeCost kin g τ e
      ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) p.1 :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
    let bad := originalScreeningAllFailure S w α β (Q.law : Measure _) b rho R grid r cuts ε
    0 ≤ originalScreeningCompleteCostBudget S w Q b K R ell s t weight hj rho grid r cuts ε C Ltilt
      RS RT RCs RCt RDs RDt τ p-core-
        (4*C*(finrank ℝ S.covector.ker : ℝ)*R^2+2*Ltilt)*bad.indicator
          (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))) p := by
  have hs : 0 ≤ ∑ i, weight i*originalOrientedStageCurrentInputNeumannBudget S w Q b
      (K i) R ell (s i) (t i) (hj i) p.1 :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hweight i)
      (originalOrientedStageCurrentInputNeumannBudget_nonneg Q b (K i) hR ell (s i) (t i) (hj i) p.1)
  have hrsv : 0 ≤ originalScreeningReserveEndpointEnergy b R RS RT RCs RCt RDs RDt p := by
    unfold originalScreeningReserveEndpointEnergy
    apply Finset.sum_nonneg
    intro i _
    apply add_nonneg <;> unfold originalReserveBlockClassOrientedAtomEnergy <;>
      exact Finset.sum_nonneg fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)
  have hp0 : 0 ≤
      ((originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R ell)
        (originalCenteredPhysicalCubeRegion b (2*R)) p.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ).toReal +
      ((originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R ell)
        (originalCenteredPhysicalCubeRegion b (2*R)) p.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ).toReal :=
    add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hrep : 0 ≤ originalScreeningRepairCountBudget S w b R ell p := by
    unfold originalScreeningRepairCountBudget
    exact add_nonneg hp0 (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hD : 0 ≤ originalFullClockSlabDiscrepancy (α := α) (β := β) grid
      (originalCenteredPhysicalCubeRegion b (2*R)) p :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hA : 0 ≤ 4*C*(finrank ℝ S.covector.ker : ℝ)*R^2+Ltilt := by positivity
  have hcport := mul_nonneg (show 0 ≤ 3*C by positivity) hp0
  have hcrsv := mul_nonneg (show 0 ≤ 3*C by positivity) hrsv
  have hcD := mul_nonneg hA hD
  have hcRep := mul_nonneg hL hrep
  dsimp only [originalScreeningCompleteCostBudget,originalScreeningLowerOrderCostBudget]
  linarith only [hs,hcport,hcrsv,hcD,hcRep]

/-- A genuine actual good-observation scalar comparison extends to the complete
unmasked budget on the same working experiment. The FULL coarse bound, retained
negative-core control and all repair signs are proved internally. This consumer
names the still separately constructed good-event comparator explicitly. -/
theorem OriginalSeedConditionalMoments.ae_original_screening_fullValue_le_budget_of_actualGood
    {I J : Type*} [Fintype I] [Fintype J]
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (D : OriginalSeedConditionalMoments S w α β) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : I → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) (R ell : ℝ)
    (s t weight : I → ℝ)
    (hj : ∀ i k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (s i) (t i)) scene k) 2 (Q.law : Measure _))
    (rho : ℝ) (grid : OriginalStageClockGrid) (r : ℝ) (cuts ε : J → ℝ) (C Ltilt : ℝ)
    {H : Type*} [Fintype H] (RS RT RCs RCt RDs RDt : H → Set ℝ) (τ : ℝ)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hR : 0 ≤ R) (hell : 0 ≤ ell) (hcollar : 2*(originalStageFrameCollarFactor b*ell) ≤ R)
    (hC : 0 ≤ C) (hL : Ltilt = |τ| * Gbound) (hweight : ∀ i, 0 ≤ weight i)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hk0 : ∀ a b v, 0 ≤ kin a b v) (hkb : ∀ a b v, |kin a b v| ≤ C*∑ i, v i^2)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ Gbound)
    (Reserve : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (X : OriginalReserveFullWorkingInputExperiment Q Reserve b rho R)
    (hgood : ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
      (p.1.1,p.1.2.2) ∉ originalScreeningAllFailure S w α β (Q.law : Measure _) b rho R grid r cuts ε →
      originalScreeningFullValue b R kin g τ p.2 ≤
        originalScreeningCompleteCostBudget S w Q b K R ell s t weight hj rho grid r cuts ε C Ltilt
          RS RT RCs RCt RDs RDt τ (p.1.1,p.1.2.2)) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)), originalScreeningFullValue b R kin g τ p.2 ≤
      originalScreeningCompleteCostBudget S w Q b K R ell s t weight hj rho grid r cuts ε C Ltilt
        RS RT RCs RCt RDs RDt τ (p.1.1,p.1.2.2) := by
  let q := finrank ℝ S.covector.ker
  let Jlaw := (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
  let Law := originalMainReserveExperimentLaw Q (Real.toNNReal rho *
    (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
  let view := fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
    (p.1.1,p.1.2.2)
  let bad := originalScreeningAllFailure S w α β (Q.law : Measure _) b rho R grid r cuts ε
  let N := fun p ↦ originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R)) (view p)
  let core := fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
    ∫ e, originalWeightedEdgeCost kin g τ e
      ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) p.1.1 :
        Measure (LegalMarkedPhysicalEdge q))
  let budget := fun p ↦ originalScreeningCompleteCostBudget S w Q b K R ell s t weight hj
    rho grid r cuts ε C Ltilt RS RT RCs RCt RDs RDt τ (view p)
  let A := 4*C*(q:ℝ)*R^2+Ltilt
  let repair := fun p ↦ budget p-core p-(A+Ltilt)*(view ⁻¹' bad).indicator N p
  have hL0 : 0 ≤ Ltilt := by rw [hL]; exact mul_nonneg (abs_nonneg _) ((abs_nonneg (g 0 0)).trans (hgb 0 0))
  have hview : MeasurePreserving view Jlaw Law := ⟨by fun_prop,X.fullLaw_main_sampler⟩
  have hlow := D.ae_original_screening_retainedCost_lower hF hw hk0 hgb Q b hell hcollar τ
  have hlow' : ∀ᵐ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ∂Law,
      -(Ltilt*originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2*R)) p.1) ≤
        ∫ e, originalWeightedEdgeCost kin g τ e
          ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) p.1 :
            Measure (LegalMarkedPhysicalEdge q)) := by
    change ∀ᵐ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal rho *
          (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)), _
    rw [hL]
    exact ae_fst_of_ae hlow
  have hcore : ∀ᵐ p ∂Jlaw, -(Ltilt*N p) ≤ core p := by
    filter_upwards [hview.quasiMeasurePreserving.ae hlow'] with p hp
    have hn : originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2*R)) (view p).1 ≤ N p := by
      exact (le_add_of_nonneg_right (Nat.cast_nonneg (mSourceCount (view p).2))).trans
        (le_add_of_nonneg_right (Nat.cast_nonneg (mTargetCount (view p).2)))
    exact (neg_le_neg (mul_le_mul_of_nonneg_left hn hL0)).trans hp
  have hv := (X.original_screening_fullValue_integrable_and_ae_bound hR hC hk hkb hg hgb τ).2
  have hv' : ∀ᵐ p ∂Jlaw, |originalScreeningFullValue b R kin g τ p.2| ≤ N p*A := by
    simpa only [A,hL] using hv
  have hr : ∀ᵐ p ∂Jlaw, 0 ≤ repair p := by
    apply ae_of_all
    intro p
    have hh := originalScreeningCompleteCostBudget_repair_nonneg S w Q b K R ell s t weight hj
      rho grid r cuts ε C Ltilt RS RT RCs RCt RDs RDt τ hR hC hL0 hweight (view p)
    have hi : (view ⁻¹' bad).indicator N p = bad.indicator
        (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))) (view p) := by
      by_cases h : view p ∈ bad
      · rw [indicator_of_mem (show p ∈ view ⁻¹' bad from h),indicator_of_mem h]
      · rw [indicator_of_notMem (show p ∉ view ⁻¹' bad from h),indicator_of_notMem h]
    have hcoef : A+Ltilt = 4*C*(q:ℝ)*R^2+2*Ltilt := by dsimp only [A]; ring
    have hh' : 0 ≤ budget p-core p-(4*C*(q:ℝ)*R^2+2*Ltilt)*bad.indicator
        (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))) (view p) := hh
    have heq : repair p = budget p-core p-(4*C*(q:ℝ)*R^2+2*Ltilt)*bad.indicator
        (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))) (view p) :=
      congrArg (fun z : ℝ ↦ budget p-core p-z) (congrArg₂ (fun a z : ℝ ↦ a*z) hcoef hi)
    exact hh'.trans_eq heq.symm
  have hg' : ∀ᵐ p ∂Jlaw, p ∉ view ⁻¹' bad →
      originalScreeningFullValue b R kin g τ p.2 ≤ core p+repair p := by
    filter_upwards [hgood] with p hp
    intro hpb
    have hn : view p ∉ bad := hpb
    have hbzero : (view ⁻¹' bad).indicator N p = 0 := indicator_of_notMem hpb _
    have hh := hp hn
    dsimp only [repair]
    rw [hbzero,mul_zero,sub_zero]
    linarith
  have hh := screeningValue_ae_le_unmaskedCost_of_good (P := Jlaw)
    (fun p ↦ originalScreeningFullValue b R kin g τ p.2) core repair N (view ⁻¹' bad) A Ltilt
    hv' hcore hr hg'
  filter_upwards [hh] with p hp
  change originalScreeningFullValue b R kin g τ p.2 ≤ budget p
  have hcancel (x y z : ℝ) : y+(x-y-z)+z = x := by ring
  exact hp.trans_eq (hcancel (budget p) (core p) ((A+Ltilt)*(view ⁻¹' bad).indicator N p))

end OTSelector.Reconstruction
