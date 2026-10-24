import OTSelector.Reconstruction.OriginalOrientedCubeReflectedKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! One actual nonnegative smooth radial unit-mass Euclidean mollifier in every dimension. -/
open Set Function MeasureTheory TopologicalSpace
open scoped ENNReal ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

private def euclideanMollifierBase (q : ℕ) (v : Fin q → ℝ) : ℝ :=
  Real.smoothTransition (1 - 4 * ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖^2)

private theorem contDiff_euclideanMollifierBase (q : ℕ) :
    ContDiff ℝ ∞ (euclideanMollifierBase q) := by
  have hn : ContDiff ℝ ∞ (fun v : Fin q → ℝ ↦ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖^2) :=
    (EuclideanSpace.equiv (Fin q) ℝ).symm.contDiff.norm_sq ℝ
  exact Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul hn))

private theorem euclideanMollifierBase_nonneg (q : ℕ) (v : Fin q → ℝ) :
    0 ≤ euclideanMollifierBase q v := Real.smoothTransition.nonneg _

private theorem euclideanMollifierBase_zero (q : ℕ) (v : Fin q → ℝ)
    (hv : (1 / 2 : ℝ) ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖) :
    euclideanMollifierBase q v = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin q) ℝ).symm v)]

private theorem hasCompactSupport_euclideanMollifierBase (q : ℕ) :
    HasCompactSupport (euclideanMollifierBase q) := by
  apply HasCompactSupport.intro (K := haarRootCube (Fin q) 1) isCompact_Icc
  intro v hv
  apply euclideanMollifierBase_zero
  have hn : ¬‖v‖ ≤ 1 := fun h ↦ hv ((mem_haarRootCube_iff_norm_le (by norm_num) v).mpr h)
  have he := raw_norm_le_euclidean_norm v
  linarith

private theorem euclideanMollifierBase_integral_pos (q : ℕ) :
    0 < ∫ v, euclideanMollifierBase q v := by
  apply (contDiff_euclideanMollifierBase q).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_euclideanMollifierBase q) (euclideanMollifierBase_nonneg q) (x := 0)
  simp only [euclideanMollifierBase, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero, Real.smoothTransition.one, ne_eq, one_ne_zero, not_false_eq_true]

/-- The actual physical Euclidean radial mollifier, normalized by its genuine positive
original Haar integral, rather than by an assumed mass or a supplied kernel. -/
def originalEuclideanMollifier (q : ℕ) (v : Fin q → ℝ) : ℝ :=
  euclideanMollifierBase q v / ∫ w, euclideanMollifierBase q w

/-- A concrete finite amplitude bound for the actual normalized original kernel. -/
def originalEuclideanMollifierBound (q : ℕ) : ℝ :=
  (∫ w, euclideanMollifierBase q w)⁻¹

/-- The actual normalized physical kernel is infinitely continuously differentiable. -/
theorem contDiff_originalEuclideanMollifier (q : ℕ) :
    ContDiff ℝ ∞ (originalEuclideanMollifier q) :=
  (contDiff_euclideanMollifierBase q).div_const _

/-- The actual normalized kernel is nonnegative. -/
theorem originalEuclideanMollifier_nonneg (q : ℕ) (v : Fin q → ℝ) :
    0 ≤ originalEuclideanMollifier q v :=
  div_nonneg (euclideanMollifierBase_nonneg q v) (euclideanMollifierBase_integral_pos q).le

/-- The actual normalized kernel is genuinely integrable for original physical Haar volume. -/
theorem integrable_originalEuclideanMollifier (q : ℕ) :
    Integrable (originalEuclideanMollifier q) volume :=
  ((contDiff_euclideanMollifierBase q).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_euclideanMollifierBase q)).div_const _

/-- The actual positive normalizing mass produces original Haar mass exactly one. -/
theorem integral_originalEuclideanMollifier_eq_one (q : ℕ) :
    (∫ v, originalEuclideanMollifier q v) = 1 := by
  unfold originalEuclideanMollifier
  rw [integral_div]
  exact div_self (euclideanMollifierBase_integral_pos q).ne'

/-- Radiality is literal equality under the genuine physical Euclidean norm. -/
theorem originalEuclideanMollifier_radial (q : ℕ) :
    IsOriginalEuclideanRadial (originalEuclideanMollifier q) := by
  intro v w hvw
  unfold originalEuclideanMollifier euclideanMollifierBase
  rw [hvw]

/-- This actual kernel already vanishes on and beyond the physical half-unit sphere. -/
theorem originalEuclideanMollifier_zero_of_half_le_norm (q : ℕ) (v : Fin q → ℝ)
    (hv : (1 / 2 : ℝ) ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖) :
    originalEuclideanMollifier q v = 0 := by
  rw [originalEuclideanMollifier, euclideanMollifierBase_zero q v hv, zero_div]

/-- The genuine closed unit-range hypothesis used by physical reflected-input consumers. -/
theorem originalEuclideanMollifier_unit_range (q : ℕ) (v : Fin q → ℝ)
    (hv : 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖) :
    originalEuclideanMollifier q v = 0 :=
  originalEuclideanMollifier_zero_of_half_le_norm q v (by linarith)

/-- The actual kernel has genuine compact support. -/
theorem hasCompactSupport_originalEuclideanMollifier (q : ℕ) :
    HasCompactSupport (originalEuclideanMollifier q) := by
  apply HasCompactSupport.intro (K := haarRootCube (Fin q) 1) isCompact_Icc
  intro v hv
  apply originalEuclideanMollifier_zero_of_half_le_norm
  have hn : ¬‖v‖ ≤ 1 := fun h ↦ hv ((mem_haarRootCube_iff_norm_le (by norm_num) v).mpr h)
  linarith [raw_norm_le_euclidean_norm v]

/-- The actual amplitude constant is nonnegative. -/
theorem originalEuclideanMollifierBound_nonneg (q : ℕ) :
    0 ≤ originalEuclideanMollifierBound q :=
  inv_nonneg.mpr (euclideanMollifierBase_integral_pos q).le

/-- The concrete original amplitude bound holds at every physical point. -/
theorem abs_originalEuclideanMollifier_le (q : ℕ) (v : Fin q → ℝ) :
    |originalEuclideanMollifier q v| ≤ originalEuclideanMollifierBound q := by
  rw [abs_of_nonneg (originalEuclideanMollifier_nonneg q v)]
  change euclideanMollifierBase q v / (∫ w, euclideanMollifierBase q w) ≤
    (∫ w, euclideanMollifierBase q w)⁻¹
  rw [← one_div]
  apply (div_le_div_iff_of_pos_right (euclideanMollifierBase_integral_pos q)).mpr
  exact Real.smoothTransition.le_one _

/-- The actual chosen kernel is positive at every point of the open Euclidean half ball. -/
theorem originalEuclideanMollifier_pos_of_norm_lt_half (q : ℕ) (v : Fin q → ℝ)
    (hv : ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ < (1 / 2 : ℝ)) :
    0 < originalEuclideanMollifier q v := by
  apply div_pos _ (euclideanMollifierBase_integral_pos q)
  apply Real.smoothTransition.pos_of_pos
  nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin q) ℝ).symm v)]

/-- A concrete original Euclidean mollifier simultaneously supplies every natural kernel
input needed by the same-scene reflected-input and smooth-current consumers. -/
theorem exists_originalEuclideanMollifier (q : ℕ) :
    ∃ (η : (Fin q → ℝ) → ℝ) (M : ℝ),
      ContDiff ℝ ∞ η ∧ Continuous η ∧ HasCompactSupport η ∧
      (∀ v, 0 ≤ η v) ∧ Integrable η volume ∧ (∫ v, η v) = 1 ∧
      IsOriginalEuclideanRadial η ∧
      (∀ v, 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ → η v = 0) ∧
      (∀ v, ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ < (1 / 2 : ℝ) → 0 < η v) ∧
      0 ≤ M ∧ ∀ v, |η v| ≤ M :=
  ⟨originalEuclideanMollifier q, originalEuclideanMollifierBound q,
    contDiff_originalEuclideanMollifier q, (contDiff_originalEuclideanMollifier q).continuous,
    hasCompactSupport_originalEuclideanMollifier q, originalEuclideanMollifier_nonneg q,
    integrable_originalEuclideanMollifier q, integral_originalEuclideanMollifier_eq_one q,
    originalEuclideanMollifier_radial q, originalEuclideanMollifier_unit_range q,
    originalEuclideanMollifier_pos_of_norm_lt_half q, originalEuclideanMollifierBound_nonneg q,
    abs_originalEuclideanMollifier_le q⟩

end OTSelector.Reconstruction
