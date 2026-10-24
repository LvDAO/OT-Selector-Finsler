import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Analysis.ContractivePerturbationZero

Conditions: The stated affine phase map, small Lipschitz perturbation with contraction factor at most one half, and complete ambient normed space.

Objects: A backward phase map, its unique zero/fixed point and explicit factor-two phase and momentum bounds.

Proof detail: Apply Banach’s contraction theorem to the backward map; rewrite its fixed point equation and estimate each side using the small perturbation coefficient.

## Mathematical sources

- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (author version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46): Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36.

Source relation: Explicit application of Banach contraction; map packaging and factor-two estimates are local corollaries.
-/

/-!
# The inverse zero of a small Lipschitz phase perturbation

A small genuine linear mobility perturbation of the identity has one inverse
zero. Its position and momentum are bounded by the original field at zero.
-/
open Set Function
open scoped NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The backward phase map whose fixed point is the inverse image of zero. -/
def phaseBackwardMap (P : V → V) (R : V →L[ℝ] V) (z : V) : V := -R (P z)

omit [CompleteSpace V] in
/-- The actual small-mobility bound internally gives a Banach contraction. -/
theorem contractingWith_phaseBackwardMap {P : V → V} {L : ℝ}
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {R : V →L[ℝ] V} (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ)) :
    ContractingWith (1 / 2 : ℝ≥0) (phaseBackwardMap P R) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun z w ↦ ?_⟩
  simp only [dist_eq_norm, phaseBackwardMap, neg_sub_neg, norm_sub_rev]
  rw [← R.map_sub]
  calc
    _ ≤ ‖R‖ * ‖P z - P w‖ := R.le_opNorm _
    _ ≤ ‖R‖ * (L * ‖z - w‖) := mul_le_mul_of_nonneg_left (hP z w) (norm_nonneg _)
    _ ≤ (1 / 2 : ℝ) * ‖z - w‖ := by
      have h := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (z - w))
      nlinarith

/-- The genuine inverse zero, constructed by the proved Banach contraction. -/
def phaseInverseZero (P : V → V) {L : ℝ}
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    (R : V →L[ℝ] V) (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ)) : V :=
  (contractingWith_phaseBackwardMap hP hsmall).fixedPoint (phaseBackwardMap P R)

/-- The constructed point maps to zero under the actual perturbed identity. -/
theorem phaseInverseZero_eq {P : V → V} {L : ℝ}
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    (R : V →L[ℝ] V) (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ)) :
    phaseInverseZero P hP R hsmall + R (P (phaseInverseZero P hP R hsmall)) = 0 := by
  have h := (contractingWith_phaseBackwardMap hP hsmall).fixedPoint_isFixedPt
  change -R (P (phaseInverseZero P hP R hsmall)) = phaseInverseZero P hP R hsmall at h
  calc
    _ = -R (P (phaseInverseZero P hP R hsmall)) +
        R (P (phaseInverseZero P hP R hsmall)) := congrArg
      (fun z ↦ z + R (P (phaseInverseZero P hP R hsmall))) h.symm
    _ = 0 := neg_add_cancel _

/-- Any zero of the same actual perturbed identity is this unique constructed point. -/
theorem phaseInverseZero_unique {P : V → V} {L : ℝ}
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    (R : V →L[ℝ] V) (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ))
    {z : V} (hz : z + R (P z) = 0) : z = phaseInverseZero P hP R hsmall := by
  apply (contractingWith_phaseBackwardMap hP hsmall).fixedPoint_unique
  change -R (P z) = z
  calc
    _ = z - (z + R (P z)) := by abel_nf
    _ = z := by rw [hz, sub_zero]

omit [CompleteSpace V] in
/-- Any inverse zero has a position bound in terms of the original field value at zero. -/
theorem norm_phaseZero_le {P : V → V} {L : ℝ}
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {R : V →L[ℝ] V} (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ))
    {z : V} (hz : z + R (P z) = 0) : ‖z‖ ≤ 2 * ‖R‖ * ‖P 0‖ := by
  have hzneg : z = -R (P z) := by
    calc
      _ = z - (z + R (P z)) := by rw [hz, sub_zero]
      _ = _ := by abel_nf
  have hPn : ‖P z‖ ≤ L * ‖z‖ + ‖P 0‖ := by
    have h := (norm_le_norm_sub_add (P z) (P 0)).trans (add_le_add (hP z 0) (le_refl ‖P 0‖))
    simpa only [sub_zero] using h
  have hbound : ‖z‖ ≤ ‖R‖ * (L * ‖z‖ + ‖P 0‖) := by
    calc
      _ = ‖R (P z)‖ := (congrArg norm hzneg).trans (norm_neg _)
      _ ≤ ‖R‖ * ‖P z‖ := R.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left hPn (norm_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hsmall (norm_nonneg z)
  nlinarith

omit [CompleteSpace V] in
/-- The field evaluated on its inverse zero has no extra random amplitude. -/
theorem norm_momentum_at_phaseZero_le {P : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {R : V →L[ℝ] V} (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ))
    {z : V} (hz : z + R (P z) = 0) : ‖P z‖ ≤ 2 * ‖P 0‖ := by
  have hnorm := norm_phaseZero_le hP hsmall hz
  have hPn : ‖P z‖ ≤ L * ‖z‖ + ‖P 0‖ := by
    have h := (norm_le_norm_sub_add (P z) (P 0)).trans (add_le_add (hP z 0) (le_refl ‖P 0‖))
    simpa only [sub_zero] using h
  have hmul := mul_le_mul_of_nonneg_left hnorm hL
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (P 0))
  nlinarith

end OTSelector.Reconstruction
