import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetPhysicalFaces
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetGaussGreen
import OTSelector.Analysis.Calculus.OrthonormalDivergence

/-! The same actual physical cube obeys genuine weighted Gauss-Green in every dimension. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The derivative of a scalar test evaluated on the actual physical vector current. -/
def originalScreeningPhysicalCurrentGradientPairing {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (J : (Fin q → ℝ) → Fin q → ℝ) (L : ℝ) (φ : (Fin q → ℝ) → ℝ) : ℝ :=
  ∫ z in originalCenteredPhysicalCubeRegion b L, fderiv ℝ φ z (J z)

/-- Genuine orthonormal Gauss-Green on the same physical cube retains the original raw
current divergence and the true-normal, coordinate-area boundary integrals. -/
theorem originalScreeningPhysicalCurrent_gauss_green_integral {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {J : (Fin q → ℝ) → Fin q → ℝ} (hJ : ContDiff ℝ 1 J) {L : ℝ} (hL : 0 ≤ L)
    {φ : (Fin q → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ z in originalCenteredPhysicalCubeRegion b L,
      φ z * originalStageCurrentDivergence J z + fderiv ℝ φ z (J z)) =
        originalScreeningPhysicalCurrentBoundaryPairing b J L φ := by
  cases q with
  | zero =>
    have hzero (z : Fin 0 → ℝ) : J z = 0 := Subsingleton.elim _ _
    have hd (z : Fin 0 → ℝ) : fderiv ℝ φ z (J z) = 0 := by rw [hzero]; exact map_zero _
    simp only [originalStageCurrentDivergence, Fin.sum_univ_zero, mul_zero, hd, zero_add,
      integral_zero]
    rfl
  | succ r =>
    let e := EuclideanSpace.equiv (Fin (r+1)) ℝ
    have h := smooth_orthonormal_cube_weighted_gauss_green b
      (fun _ ↦ -L/2) (fun _ ↦ L/2) (fun _ ↦ by linarith)
      (hφ.comp e.contDiff) (e.symm.contDiff.comp (hJ.comp e.contDiff))
    have hdiv (y : Fin (r+1) → ℝ) :=
      orthonormal_divergence_physical_raw_current b hJ ((orthonormalCubeCoordinates b).symm y)
    have hdφ (y : Fin (r+1) → ℝ) :
        fderiv ℝ (φ ∘ e) ((orthonormalCubeCoordinates b).symm y)
          (e.symm (J (e ((orthonormalCubeCoordinates b).symm y)))) =
        fderiv ℝ φ (orthonormalPhysicalCubeMap b y) (J (orthonormalPhysicalCubeMap b y)) := by
      rw [fderiv_comp _ (hφ.differentiable one_ne_zero _) e.differentiableAt]
      simp only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply]
      rfl
    rw [show originalCenteredPhysicalCubeRegion b L =
      orthonormalPhysicalCubeRegion b (fun _ ↦ -L/2) (fun _ ↦ L/2) from rfl,
      integral_orthonormalPhysicalCubeRegion]
    calc
      _ = ∫ y in Icc (fun _ : Fin (r+1) ↦ -L/2) (fun _ ↦ L/2),
          (φ ∘ e) ((orthonormalCubeCoordinates b).symm y) *
            (∑ i, ⟪b i, fderiv ℝ (fun z ↦ e.symm (J (e z)))
              ((orthonormalCubeCoordinates b).symm y) (b i)⟫_ℝ) +
            fderiv ℝ (φ ∘ e) ((orthonormalCubeCoordinates b).symm y)
              (e.symm (J (e ((orthonormalCubeCoordinates b).symm y)))) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro y _
        dsimp only
        rw [hdiv y, hdφ y]
        rfl
      _ = _ := h
      _ = originalScreeningPhysicalCurrentBoundaryPairing b J L φ := by
        change _ = originalPhysicalCubeVectorBoundaryPairing b J L φ
        unfold originalPhysicalCubeVectorBoundaryPairing
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        simp only [Fin.sum_univ_two, h10, ↓reduceIte, neg_one_mul, one_mul]
        change ((∫ t in Icc (fun _ : Fin r ↦ -L/2) (fun _ ↦ L/2),
          φ (orthonormalPhysicalCubeMap b (i.insertNth (L/2) t)) *
            originalEuclideanNormalReadout (b i) (J (orthonormalPhysicalCubeMap b (i.insertNth (L/2) t)))) -
          (∫ t in Icc (fun _ : Fin r ↦ -L/2) (fun _ ↦ L/2),
          φ (orthonormalPhysicalCubeMap b (i.insertNth (-L/2) t)) *
            originalEuclideanNormalReadout (b i) (J (orthonormalPhysicalCubeMap b (i.insertNth (-L/2) t))))) = _
        simp_rw [mul_comm]
        ring

/-- Splitting the genuine physical Gauss-Green integral gives its literal divergence,
true-normal boundary pairing and actual derivative-current pairing separately. -/
theorem originalScreeningPhysicalCurrent_gauss_green {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {J : (Fin q → ℝ) → Fin q → ℝ} (hJ : ContDiff ℝ 1 J) {L : ℝ} (hL : 0 ≤ L)
    {φ : (Fin q → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ z in originalCenteredPhysicalCubeRegion b L, originalStageCurrentDivergence J z * φ z) =
      originalScreeningPhysicalCurrentBoundaryPairing b J L φ -
        originalScreeningPhysicalCurrentGradientPairing b J L φ := by
  have hc : IsCompact (originalCenteredPhysicalCubeRegion b L) :=
    isCompact_Icc.image (orthonormalPhysicalCubeMap b).continuous
  have hdiv : Continuous (originalStageCurrentDivergence J) := by
    unfold originalStageCurrentDivergence
    fun_prop (disch := exact hJ.continuous_fderiv (by norm_num))
  have hdi : IntegrableOn (fun z ↦ φ z * originalStageCurrentDivergence J z)
      (originalCenteredPhysicalCubeRegion b L) volume :=
    (hφ.continuous.mul hdiv).continuousOn.integrableOn_compact hc
  have hgr : Continuous (fun z ↦ fderiv ℝ φ z (J z)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply hJ.continuous
  have h := originalScreeningPhysicalCurrent_gauss_green_integral b hJ hL hφ
  rw [integral_add hdi (hgr.continuousOn.integrableOn_compact hc)] at h
  change (∫ z in originalCenteredPhysicalCubeRegion b L, φ z * originalStageCurrentDivergence J z) +
    originalScreeningPhysicalCurrentGradientPairing b J L φ = _ at h
  have he : (∫ z in originalCenteredPhysicalCubeRegion b L,
      originalStageCurrentDivergence J z * φ z) =
      ∫ z in originalCenteredPhysicalCubeRegion b L, φ z * originalStageCurrentDivergence J z := by
    simp_rw [mul_comm]
  rw [he]
  linarith

end OTSelector.Reconstruction
