import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetGaussGreen
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessAffineScale

/-! A common boundary coefficient constructed from the actual vector current on its faces. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual normal component of a current on each normalized physical cube face. -/
def originalStageNormalizedFaceData {r : ℕ}
    (J : (Fin (r+1) → ℝ) → Fin (r+1) → ℝ) (R : ℝ)
    (j : Fin (r+1) × Fin 2) (y : Fin r → ℝ) : ℝ :=
  J (j.1.insertNth (if j.2 = 0 then -R else R) (fun k ↦ -R + (2*R)*y k)) j.1

/-- The actual trace coefficient, with its proved area and volume scaling, controls every
smooth mean-zero test simultaneously. No asymptotic rate is part of its definition. -/
def originalStageCurrentBoundaryTraceBound : {q : ℕ} →
    ((Fin q → ℝ) → Fin q → ℝ) → ℝ → ℝ
  | 0, _, _ => 0
  | r+1, J, R => (2*R)^(r+1) *
      originalRawUnitCubeBoundaryTraceDualBound (originalStageNormalizedFaceData J R)

/-- The actual common face coefficient is nonnegative on positive-radius cubes. -/
theorem originalStageCurrentBoundaryTraceBound_nonneg {q : ℕ}
    (J : (Fin q → ℝ) → Fin q → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ originalStageCurrentBoundaryTraceBound J R := by
  cases q with
  | zero => exact le_rfl
  | succ r =>
    exact mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hR) _)
      (originalRawUnitCubeBoundaryTraceDualBound_nonneg _)

/-- Actual continuous current traces lie in the true finite face L2 spaces. -/
theorem originalStageNormalizedFaceData_memLp_two {r : ℕ}
    {J : (Fin (r+1) → ℝ) → Fin (r+1) → ℝ} (hJ : Continuous J) (R : ℝ)
    (j : Fin (r+1) × Fin 2) :
    MemLp (originalStageNormalizedFaceData J R j) 2
      (volume.restrict (Icc (0 : Fin r → ℝ) 1)) := by
  have hc : Continuous (originalStageNormalizedFaceData J R j) := by
    unfold originalStageNormalizedFaceData
    fun_prop
  exact (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
    (hc.pow 2).continuousOn.integrableOn_Icc

/-- The actual signed boundary flux is controlled uniformly in the same mean-zero smooth
tests by the actual face coefficient and original physical gradient norm. -/
theorem originalStageAxisBoundaryPairing_sq_le {q : ℕ}
    {J : (Fin q → ℝ) → Fin q → ℝ} (hJ : Continuous J) {R : ℝ} (hR : 0 < R)
    (K : Compacts (Fin q → ℝ)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ))
    (hmean : (∫ z in haarRootCube (Fin q) R, φ z) = 0) :
    (originalStageAxisBoundaryPairing J R φ)^2 ≤
      originalStageCurrentBoundaryTraceBound J R *
        ‖smoothPhysicalGradientLtwo K (volume.restrict (haarRootCube (Fin q) R)) φ‖^2 := by
  cases q with
  | zero => simp [originalStageAxisBoundaryPairing, originalStageCurrentBoundaryTraceBound]
  | succ r =>
    let a : Fin (r+1) → ℝ := fun _ ↦ -R
    let g : Fin (r+1) × Fin 2 → (Fin r → ℝ) → ℝ :=
      fun j y ↦ J (j.1.insertNth (if j.2 = 0 then -R else R) y) j.1
    have ha : a + (2*R) • 1 = (fun _ : Fin (r+1) ↦ R) := by
      funext k
      simp [a]
      ring
    have hn (j : Fin (r+1) × Fin 2) :
        (fun y ↦ g j (a ∘ j.1.succAbove + (2*R) • y)) =
          originalStageNormalizedFaceData J R j := rfl
    have hm : (∫ z in Icc a (a + (2*R) • 1), φ z) = 0 := by
      rw [ha]
      exact hmean
    have hg (j : Fin (r+1) × Fin 2) :
        MemLp (fun y ↦ g j (a ∘ j.1.succAbove + (2*R) • y)) 2
          (volume.restrict (Icc (0 : Fin r → ℝ) 1)) := by
      rw [hn]
      exact originalStageNormalizedFaceData_memLp_two hJ R j
    have hb := smooth_affineCube_all_faces_pairing_sq_le a (by linarith : 0 < 2*R)
      hg (φ.contDiff.of_le (by norm_num)) hm
    have hp : originalAffineCubeBoundaryPairing a (2*R) g φ =
        originalStageAxisBoundaryPairing J R φ := by
      unfold originalAffineCubeBoundaryPairing originalStageAxisBoundaryPairing
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.sum_univ_two]
      have hat : a ∘ i.succAbove + (2*R) • (1 : Fin r → ℝ) =
          (fun _ : Fin r ↦ R) := by
        funext k
        simp [a]
        ring
      have hi10 : (1 : Fin 2) ≠ 0 := by decide
      have hcancel : -R + 2*R = R := by ring
      simp only [hat]
      simp only [g, a, hi10, ↓reduceIte, neg_one_mul, one_mul, hcancel, Function.comp_def]
      simp_rw [mul_comm]
      ring
    rw [hp] at hb
    change (originalStageAxisBoundaryPairing J R φ)^2 ≤
      (2*R)^(r+1) * originalRawUnitCubeBoundaryTraceDualBound
        (originalStageNormalizedFaceData J R) *
        originalRawBoxGradientEnergy a (a + (2*R) • 1) φ at hb
    rw [originalHaarRootCubeGradientLtwo_norm_sq]
    simpa only [originalStageCurrentBoundaryTraceBound, originalRawBoxGradientEnergy, ha, a, haarRootCube] using hb

/-- Equality on the actual faces preserves every signed boundary test pairing. -/
theorem originalStageAxisBoundaryPairing_congr {q : ℕ}
    {J H : (Fin q → ℝ) → Fin q → ℝ} (R : ℝ)
    (h : ∀ z i, z i = R ∨ z i = -R → J z = H z) (φ : (Fin q → ℝ) → ℝ) :
    originalStageAxisBoundaryPairing J R φ = originalStageAxisBoundaryPairing H R φ := by
  cases q with
  | zero => rfl
  | succ r =>
    unfold originalStageAxisBoundaryPairing
    apply Finset.sum_congr rfl
    intro i _
    congr 1 <;> apply setIntegral_congr_fun measurableSet_Icc <;> intro y _
    · dsimp only
      rw [h _ i (Or.inl (by simp))]
    · dsimp only
      rw [h _ i (Or.inr (by simp))]

end OTSelector.Reconstruction
