import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostCount
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedRetainedCostLimit

/-! Bad-event masking preserves the genuine retained signed core without a quadratic core moment. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology Module Manifold
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {α β : Measure ℝ}

/-- Actual window conservation bounds the same retained plan's negative signed
cost by the bounded tilt times the original full input count. No kinetic or
Euclidean second-moment bound is needed for this scene-wise statement. -/
theorem OriginalSeedConditionalMoments.ae_original_screening_retainedCost_lower
    (D : OriginalSeedConditionalMoments S w α β)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hk0 : ∀ s t v, 0 ≤ kin s t v) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hgb : ∀ s t, |g s t| ≤ G)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R) (t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      -(|t| * G*originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2*R)) scene) ≤
        ∫ e, originalWeightedEdgeCost kin g t e
          ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene :
            Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) := by
  let q := finrank ℝ S.covector.ker
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  have hK := (isCompact_originalStagePhysicalCube b (2*R)).measurableSet
  have hG : 0 ≤ G := (abs_nonneg (g 0 0)).trans (hgb 0 0)
  have hC : 0 ≤ |t| * G := mul_nonneg (abs_nonneg _) hG
  have hlow (e : LegalMarkedPhysicalEdge q) : -(|t| * G) ≤ originalWeightedEdgeCost kin g t e := by
    have he := (abs_mul t (g e.1.2 e.2.2)).trans_le
      (mul_le_mul_of_nonneg_left (hgb e.1.2 e.2.2) (abs_nonneg t))
    change _ ≤ kin e.1.2 e.2.2 (e.2.1-e.1.1)+t*g e.1.2 e.2.2
    linarith [neg_abs_le (t*g e.1.2 e.2.2),hk0 e.1.2 e.2.2 (e.2.1-e.1.1)]
  filter_upwards [D.ae_originalOriented_windows_eq_retained_add_ports hF hw Q b hell hR,
    (Q.originalScreeningActualColorCount_moments K 0 hK
      (isCompact_originalStagePhysicalCube b (2*R)).measure_ne_top).1] with scene hwindow hfinite
  let core : Measure (LegalMarkedPhysicalEdge q) :=
    originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene
  have hcap : core.fst ≤ (legalInputColorMeasure q scene.2 0).restrict {p | p.1 ∈ K} := by
    rw [hwindow.1]
    exact Measure.le_add_right le_rfl
  have hmass : core univ ≤ (scene.2 : Measure (LegalColoredInputPoint q)) ((K ×ˢ univ) ×ˢ {0}) := by
    calc
      _ = core.fst univ := (Measure.fst_univ).symm
      _ ≤ ((legalInputColorMeasure q scene.2 0).restrict {p | p.1 ∈ K}) univ := hcap univ
      _ = _ := by
        rw [Measure.restrict_apply_univ]
        rw [show {p : LegalMarkedPhysicalPoint q | p.1 ∈ K} = K ×ˢ univ from by ext p; simp]
        exact legalInputColorMeasure_apply_prod q scene.2 0 (hK.prod MeasurableSet.univ)
  let : IsFiniteMeasure core := ⟨hmass.trans_lt hfinite⟩
  have hmassR : core.real univ ≤ originalScreeningActualCount K scene := by
    exact (ENNReal.toReal_mono hfinite.ne hmass).trans
      (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  by_cases hI : Integrable (originalWeightedEdgeCost kin g t) core
  · have hb := integral_mono (integrable_const (- (|t| * G))) hI hlow
    have hconst : (∫ _e : LegalMarkedPhysicalEdge q, -(|t| * G) ∂core) = -(|t| * G*core.real univ) := by
      rw [integral_const]
      simp only [smul_eq_mul]
      ring
    rw [hconst] at hb
    exact (neg_le_neg (mul_le_mul_of_nonneg_left hmassR hC)).trans hb
  · change -(|t| * G*originalScreeningActualCount K scene) ≤ ∫ e, originalWeightedEdgeCost kin g t e ∂core
    rw [integral_undef hI]
    exact neg_nonpos.mpr (mul_nonneg hC (originalScreeningActualCount_nonneg K scene))

/-- Restricting the genuine signed core to an arbitrary jointly selected good
observation costs at most the bounded tilt times the full joint bad-event count.
Campbell supplies the core L1 and the original product law supplies count L1. -/
theorem OriginalSeedConditionalMoments.integral_good_original_screening_retainedCost_le
    (D : OriginalSeedConditionalMoments S w α β)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hk0 : ∀ s t v, 0 ≤ kin s t v) {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    {G : ℝ} (hgb : ∀ s t, |g s t| ≤ G)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R)
    (t : ℝ) (rate : ℝ≥0)
    (bad : Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)) (hbad : MeasurableSet bad) :
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let cost := fun scene ↦ ∫ e, originalWeightedEdgeCost kin g t e
      ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
    let M := originalMainReserveExperimentLaw Q rate
    (∫ p, badᶜ.indicator (fun p ↦ cost p.1) p ∂M) ≤ (∫ scene, cost scene ∂(Q.law : Measure _)) +
      |t| * G*(∫ p, bad.indicator (originalScreeningFullExperimentCount K) p ∂M) := by
  let q := finrank ℝ S.covector.ker
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  let cost := fun scene ↦ ∫ e, originalWeightedEdgeCost kin g t e
    ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene :
      Measure (LegalMarkedPhysicalEdge q))
  let P := (Q.law : Measure (LegalMarkedOptimalInputScene q))
  let Z := twoMarkedCloudLaw q ℝ ℝ α β rate
  let M := originalMainReserveExperimentLaw Q rate
  have hc : Integrable cost P :=
    (originalOrientedPathRetainedPlan_weightedCost_integrable_and_integral hF hw Q hk hg b R ell t).1
  have hcp : Integrable (fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦ cost p.1) M :=
    hc.comp_fst Z
  have hN := (Q.original_screening_fullExperimentCount rate
    (isCompact_originalStagePhysicalCube b (2*R)).measurableSet
    (isCompact_originalStagePhysicalCube b (2*R)).measure_ne_top).1
  have hlow := D.ae_original_screening_retainedCost_lower hF hw hk0 hgb Q b hell hR t
  have hp : ∀ᵐ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ∂M,
      -(|t| * G*originalScreeningActualCount K p.1) ≤ cost p.1 :=
    ae_fst_of_ae hlow
  have hG : 0 ≤ |t| * G := mul_nonneg (abs_nonneg _) ((abs_nonneg (g 0 0)).trans (hgb 0 0))
  have hb : (∫ p, badᶜ.indicator (fun p ↦ cost p.1) p ∂M) ≤
      ∫ p, cost p.1+|t| * G*bad.indicator (originalScreeningFullExperimentCount K) p ∂M := by
    apply integral_mono_ae (hcp.indicator hbad.compl) (hcp.add ((hN.indicator hbad).const_mul (|t| * G)))
    filter_upwards [hp] with p hl
    change badᶜ.indicator (fun p ↦ cost p.1) p ≤ cost p.1 +
      |t| * G*bad.indicator (originalScreeningFullExperimentCount K) p
    by_cases hpb : p ∈ bad
    · simp only [indicator_of_notMem (show p ∉ badᶜ from fun h ↦ h hpb),indicator_of_mem hpb]
      have hn : originalScreeningActualCount K p.1 ≤ originalScreeningFullExperimentCount K p := by
        unfold originalScreeningFullExperimentCount
        exact (le_add_of_nonneg_right (Nat.cast_nonneg (mSourceCount p.2) :
          (0:ℝ) ≤ (mSourceCount p.2 : ℝ))).trans
            (le_add_of_nonneg_right (Nat.cast_nonneg (mTargetCount p.2)))
      linarith [mul_le_mul_of_nonneg_left hn hG]
    · simp [hpb]
  have heq := integral_add hcp ((hN.indicator hbad).const_mul (|t| * G))
  have hmean : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ, cost p.1 ∂M) =
      ∫ scene, cost scene ∂P := by
    simpa only [M,originalMainReserveExperimentLaw,P,Z,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using
      (integral_fun_fst (μ := P) (ν := Z) cost)
  exact hb.trans_eq (heq.trans (by rw [hmean,integral_const_mul]))

end OTSelector.Reconstruction
