import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedCurrentDivergence
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedCurrentFaces
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetPhysicalBulk
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedReflectedInputs
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficMean

/-! One actual same-frame current/input coefficient controls all physical mean-zero tests. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A vector field zero on the actual physical faces can be subtracted without changing
any true-normal coordinate-area boundary pairing on that same cube. -/
theorem originalScreeningPhysicalCurrentBoundaryPairing_sub_eq_of_faces_zero {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (J H : (Fin q → ℝ) → Fin q → ℝ) (R : ℝ)
    (hH : ∀ z i, (orthonormalPhysicalCubeMap b).symm z i = R ∨
      (orthonormalPhysicalCubeMap b).symm z i = -R → H z = 0) (φ : (Fin q → ℝ) → ℝ) :
    originalScreeningPhysicalCurrentBoundaryPairing b (fun z ↦ J z-H z) (2*R) φ =
      originalScreeningPhysicalCurrentBoundaryPairing b J (2*R) φ := by
  cases q with
  | zero => rfl
  | succ r =>
    change originalPhysicalCubeVectorBoundaryPairing b (fun z ↦ J z-H z) (2*R) φ =
      originalPhysicalCubeVectorBoundaryPairing b J (2*R) φ
    apply originalPhysicalCubeVectorBoundaryPairing_congr_ae
    intro a
    apply Eventually.of_forall
    intro y
    have hh := hH (orthonormalPhysicalCubeMap b
      (a.1.insertNth (if a.2=0 then -(2*R)/2 else (2*R)/2) y)) a.1 (by
        have hp : (2*R)/2=R := by ring
        have hn : -(2*R)/2= -R := by ring
        by_cases ha : a.2=0 <;> simp [ha, hp, hn])
    simp only [hh, sub_zero]

private theorem four_signed_sq_le (a b c d : ℝ) :
    (a-b+c-d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a+b), sq_nonneg (a-c), sq_nonneg (a+d),
    sq_nonneg (b+c), sq_nonneg (b-d), sq_nonneg (c+d)]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}

/-- The same-scene literal omitted divergence and two genuine full-input reflection pairings. -/
def originalOrientedStageCurrentInputPairing (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) : ℝ :=
  (∫ z in originalCenteredPhysicalCubeRegion b (2*R), originalStageCurrentDivergence
    (fun z ↦ originalOrientedOmittedSeedPathClockSetCurrent S w b R ell
      (fun x ↦ originalEuclideanMollifier _ (x-z)) (Ioc s t) scene) z * φ z) +
  (∫ z in originalCenteredPhysicalCubeRegion b (2*R),
    originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier _) (2*R) (Ico s t)
      (legalInputColorMeasure _ scene.2 0) z * φ z) -
  (∫ z in originalCenteredPhysicalCubeRegion b (2*R),
    originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier _) (2*R) (Ioc s t)
      (legalInputColorMeasure _ scene.2 1) z * φ z)

/-- The actual common coefficient is omitted Euclidean energy plus full-current physical
face coefficient plus both same-kernel full-input reflection coefficients. -/
def originalOrientedStageCurrentInputNeumannBudget (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) (R ell s t : ℝ)
    (hj : ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc s t) scene k) 2 (Q.law : Measure _))
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  4*(originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R ell (Ioc s t) scene +
    originalScreeningPhysicalFaceBudget Q b
      (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _) (Ioc s t)) hj (2*R) scene +
    originalStageOrientedSourceReflectedInputBound K b R s t scene +
    originalStageOrientedTargetReflectedInputBound K b R s t scene)

/-- The actual oriented omitted-current balance has one common Neumann bound for every
physical mean-zero smooth test on a single original-scene event. Every current regularity,
retained face cancellation, true physical trace and full-input bound is proved internally. -/
theorem OriginalSeedConditionalMoments.ae_originalOrientedStageCurrentInput_Neumann_bound
    {μ ν : Measure ℝ} (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R)
    {s t : ℝ} (hst : s ≤ t)
    (hj : ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc s t) scene k) 2 (Q.law : Measure _)) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ),
      (∫ z in originalCenteredPhysicalCubeRegion b (2*R), φ z) = 0 →
      (originalOrientedStageCurrentInputPairing S w b R ell s t scene φ)^2 ≤
        originalOrientedStageCurrentInputNeumannBudget S w Q b K R ell s t hj scene *
          ‖smoothPhysicalGradientLtwo K (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))) φ‖^2 := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  let j := originalSeedPathClockSetCurrent S w η (Ioc s t)
  have hRone : 1 ≤ R := by nlinarith [one_le_originalStageFrameCollarFactor b]
  have hmη : Measurable η := (contDiff_originalEuclideanMollifier q).continuous.measurable
  have hmj : Measurable j := by
    have h := (stronglyMeasurable_originalFullCurrent_joint_spatial S hF hw hmη (Ioc s t)).measurable.comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : LegalMarkedOptimalInputScene q ↦ (0 : Fin q → ℝ))))
    simpa only [Function.comp_def, id_eq, sub_zero] using h
  have hi := Q.originalStageOriented_reflectedInput_bounds K b hq hRone s t
  filter_upwards [D.ae_originalOrientedOmittedCurrent_C1_divergence_balance hF hw hbounds Q b R ell hst,
    D.ae_all_originalOrientedRetainedCurrent_eq_zero_on_physical_faces hF hw Q b hell hR,
    ae_all_originalScreeningPhysicalCurrentBoundaryPairing_sq_le Q b j hj hmj (show 0 < 2*R by linarith),
    hi.2.2.2.2.2.2] with scene hcurrent hret hface hinput
  intro φ hmean
  let J := fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene
  let H := fun z ↦ originalPairRestrictedSeedPathClockSetCurrent S w
    (originalOrientedPathLengthRetained S w b R ell) (fun x ↦ η (x-z)) (Ioc s t) scene
  let O := fun z ↦ originalOrientedOmittedSeedPathClockSetCurrent S w b R ell
    (fun x ↦ η (x-z)) (Ioc s t) scene
  have hfun : (fun z ↦ j (legalMarkedInputSceneReroot q z scene)) = J := by
    funext z
    exact originalSeedPathClockSetCurrent_reroot S hF hw hmη (Ioc s t) z scene
  have hfaceSq := hface K φ hmean
  rw [hfun] at hfaceSq
  have hfaces := originalScreeningPhysicalCurrentBoundaryPairing_sub_eq_of_faces_zero b J H R
    (hret (Ioc s t)) φ
  have hGG := originalScreeningPhysicalCurrent_gauss_green b hcurrent.1 (show 0 ≤ 2*R by linarith)
    (φ.contDiff.of_le (by norm_num))
  change (∫ z in originalCenteredPhysicalCubeRegion b (2*R), originalStageCurrentDivergence O z * φ z) =
    originalScreeningPhysicalCurrentBoundaryPairing b (fun z ↦ J z-H z) (2*R) φ -
      originalScreeningPhysicalCurrentGradientPairing b O (2*R) φ at hGG
  rw [hfaces] at hGG
  have hgrad := originalScreeningPhysicalCurrentGradientPairing_sq_le b hcurrent.1.continuous (2*R) K φ
  have hsrc := (hinput φ hmean).1
  have htgt := (hinput φ hmean).2
  unfold originalOrientedStageCurrentInputPairing
  rw [hGG]
  apply (four_signed_sq_le _ _ _ _).trans
  unfold originalOrientedStageCurrentInputNeumannBudget
  change _ ≤ 4*(originalScreeningPhysicalCurrentEnergy b O (2*R) + _ + _ + _) * _
  nlinarith [hfaceSq, hgrad, hsrc, htgt]

end OTSelector.Reconstruction
