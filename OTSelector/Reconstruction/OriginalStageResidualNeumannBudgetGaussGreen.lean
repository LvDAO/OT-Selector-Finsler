import OTSelector.Analysis.Calculus.BoxGaussGreen
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessCanonicalSmoothCube

/-! Actual axisaligned current divergence, gradient pairing and signed face flux. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The true coordinate divergence of a spatial current, in its original physical coordinates. -/
def originalStageCurrentDivergence {q : ℕ} (J : (Fin q → ℝ) → Fin q → ℝ)
    (z : Fin q → ℝ) : ℝ := ∑ i : Fin q, fderiv ℝ J z (Pi.single i 1) i

/-- The actual signed normal face flux, including its original coordinate area measure. -/
def originalStageAxisBoundaryPairing : {q : ℕ} →
    ((Fin q → ℝ) → Fin q → ℝ) → ℝ → ((Fin q → ℝ) → ℝ) → ℝ
  | 0, _, _, _ => 0
  | r+1, J, R, φ => ∑ i : Fin (r+1),
      ((∫ y in Icc (fun _ : Fin r ↦ -R) (fun _ ↦ R),
        φ (i.insertNth R y) * J (i.insertNth R y) i) -
       ∫ y in Icc (fun _ : Fin r ↦ -R) (fun _ ↦ R),
        φ (i.insertNth (-R) y) * J (i.insertNth (-R) y) i)

/-- The exact original physical coordinate derivative-current pairing on the same raw cube. -/
def originalStageCurrentGradientPairing {q : ℕ} (J : (Fin q → ℝ) → Fin q → ℝ)
    (R : ℝ) (φ : (Fin q → ℝ) → ℝ) : ℝ :=
  ∫ z in haarRootCube (Fin q) R, ∑ i : Fin q, (fderiv ℝ φ z (Pi.single i 1)) * J z i

/-- Genuine weighted Gauss-Green gives the original current's divergence pairing as its
actual boundary flux minus its actual physical gradient pairing. -/
theorem originalStageCurrent_gauss_green {q : ℕ} {J : (Fin q → ℝ) → Fin q → ℝ}
    (hJ : ContDiff ℝ 1 J) {R : ℝ} (hR : 0 ≤ R)
    {φ : (Fin q → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ z in haarRootCube (Fin q) R, originalStageCurrentDivergence J z * φ z) =
      originalStageAxisBoundaryPairing J R φ - originalStageCurrentGradientPairing J R φ := by
  cases q with
  | zero => simp [originalStageCurrentDivergence, originalStageAxisBoundaryPairing,
      originalStageCurrentGradientPairing]
  | succ r =>
    have hdiv : Continuous (fun z ↦ originalStageCurrentDivergence J z) := by
      unfold originalStageCurrentDivergence
      fun_prop (disch := exact hJ.continuous_fderiv (by norm_num))
    have hd : IntegrableOn (fun z ↦ φ z * originalStageCurrentDivergence J z)
        (haarRootCube (Fin (r+1)) R) :=
      (hφ.continuous.mul hdiv).continuousOn.integrableOn_Icc
    have hg : IntegrableOn (fun z ↦ ∑ i : Fin (r+1),
        (fderiv ℝ φ z (Pi.single i 1)) * J z i) (haarRootCube (Fin (r+1)) R) := by
      have hJc := hJ.continuous
      have hφd := hφ.continuous_fderiv (by norm_num)
      exact (show Continuous (fun z ↦ ∑ i : Fin (r+1),
        (fderiv ℝ φ z (Pi.single i 1)) * J z i) by fun_prop).continuousOn.integrableOn_Icc
    have h := smooth_box_weighted_gauss_green
      (fun _ : Fin (r+1) ↦ -R) (fun _ ↦ R) (fun _ ↦ by linarith) hφ hJ
    change (∫ z in haarRootCube (Fin (r+1)) R,
      φ z * originalStageCurrentDivergence J z +
        ∑ i : Fin (r+1), (fderiv ℝ φ z (Pi.single i 1)) * J z i) =
        originalStageAxisBoundaryPairing J R φ at h
    rw [integral_add hd hg] at h
    change (∫ z in haarRootCube (Fin (r+1)) R,
      φ z * originalStageCurrentDivergence J z) + originalStageCurrentGradientPairing J R φ =
        originalStageAxisBoundaryPairing J R φ at h
    have hcomm : (∫ z in haarRootCube (Fin (r+1)) R,
        originalStageCurrentDivergence J z * φ z) =
        ∫ z in haarRootCube (Fin (r+1)) R, φ z * originalStageCurrentDivergence J z := by
      simp_rw [mul_comm]
    rw [hcomm]
    linarith

/-- An actually vanishing vector field on all cube faces has no signed flux against any test. -/
theorem originalStageAxisBoundaryPairing_eq_zero {q : ℕ}
    {J : (Fin q → ℝ) → Fin q → ℝ} (R : ℝ)
    (hJ : ∀ z i, z i = R ∨ z i = -R → J z = 0) (φ : (Fin q → ℝ) → ℝ) :
    originalStageAxisBoundaryPairing J R φ = 0 := by
  cases q with
  | zero => rfl
  | succ r =>
    unfold originalStageAxisBoundaryPairing
    apply Finset.sum_eq_zero
    intro i _
    have hu (y : Fin r → ℝ) : J (i.insertNth R y) = 0 :=
      hJ _ i (Or.inl (by simp))
    have hl (y : Fin r → ℝ) : J (i.insertNth (-R) y) = 0 :=
      hJ _ i (Or.inr (by simp))
    simp only [hu, hl, Pi.zero_apply, mul_zero, integral_zero, sub_self]

end OTSelector.Reconstruction
