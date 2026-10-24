import OTSelector.Analysis.ContractivePerturbationZero
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ContractivePhaseCurveBounds.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ContractivePhaseCurveBounds`; the selected original proof blocks follow. -/
section

/-!
Conditions: An L-Lipschitz field and mobilities with norm times L at most one-half; completeness is used for existence and the physical/error bounds are explicit.

Objects: Stability of inverse zeros, residual-to-zero bounds, contributor position/momentum tubes and a canonical inverse curve.

Proof detail: Subtract the zero equations, absorb the half-Lipschitz term and apply the triangle/operator-norm inequalities; Banach contraction gives the curve.

Sources: Gerald Teschl, Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46).
Relation: Quantitative small-Lipschitz-perturbation consequences with the actual constants locally derived.
-/

/-!
# Inverse phase-curve stability and the fixed contributor tube

The curve amplitude is controlled by the original field at zero. Actual rough
phase points that contribute to a bounded physical kernel lie in a fixed tube
around the inverse phase curve, with no condition-number factor.
-/
open Set Function
open scoped NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2200000
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Two inverse zeros are stable under their actual linear mobility difference. -/
theorem norm_phaseZeros_sub_le {P : V → V} {L : ℝ}
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {R S : V →L[ℝ] V} (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ))
    {z w : V} (hz : z + R (P z) = 0) (hw : w + S (P w) = 0) :
    ‖z - w‖ ≤ 2 * ‖R - S‖ * ‖P w‖ := by
  have hzneg : z = -R (P z) := by
    calc
      _ = z - (z + R (P z)) := by rw [hz, sub_zero]
      _ = _ := by abel_nf
  have hwneg : w = -S (P w) := by
    calc
      _ = w - (w + S (P w)) := by rw [hw, sub_zero]
      _ = _ := by abel_nf
  have heq : z - w = -R (P z - P w) - (R - S) (P w) := by
    calc
      _ = (-R (P z)) - (-S (P w)) := congrArg₂ (· - ·) hzneg hwneg
      _ = _ := by rw [R.map_sub, sub_apply]; abel_nf
  have hbound : ‖z - w‖ ≤ ‖R‖ * (L * ‖z - w‖) + ‖R - S‖ * ‖P w‖ := by
    calc
      _ = ‖-R (P z - P w) - (R - S) (P w)‖ := congrArg norm heq
      _ ≤ ‖R (P z - P w)‖ + ‖(R - S) (P w)‖ := by
        simpa only [norm_neg] using norm_sub_le (-R (P z - P w)) ((R - S) (P w))
      _ ≤ ‖R‖ * ‖P z - P w‖ + ‖R - S‖ * ‖P w‖ :=
        add_le_add (R.le_opNorm _) ((R - S).le_opNorm _)
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hP z w) (norm_nonneg _)) le_rfl
  have hmul := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (z - w))
  nlinarith

/-- Small mobilities make the inverse position vary with the original amplitude P(0). -/
theorem norm_phaseZeros_sub_le_original_amplitude {P : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {R S : V →L[ℝ] V} (hR : ‖R‖ * L ≤ (1 / 2 : ℝ))
    (hS : ‖S‖ * L ≤ (1 / 2 : ℝ))
    {z w : V} (hz : z + R (P z) = 0) (hw : w + S (P w) = 0) :
    ‖z - w‖ ≤ 4 * ‖R - S‖ * ‖P 0‖ := by
  have h := norm_phaseZeros_sub_le hP hR hz hw
  have hp := norm_momentum_at_phaseZero_le hL hP hS hw
  have hmul := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * ‖R - S‖)
  nlinarith

/-- An actual near-zero physical point stays near the inverse position. -/
theorem norm_sub_phaseZero_le_residual {P : V → V} {L : ℝ}
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {R : V →L[ℝ] V} (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ))
    {w : V} (hw : w + R (P w) = 0) (z : V) :
    ‖z - w‖ ≤ 2 * ‖z + R (P z)‖ := by
  have hfix : IsFixedPt (phaseBackwardMap P R) w := by
    change -R (P w) = w
    calc
      _ = w - (w + R (P w)) := by abel_nf
      _ = w := by rw [hw, sub_zero]
  have h := (contractingWith_phaseBackwardMap hP hsmall).dist_le_of_fixedPoint z hfix
  norm_num [dist_eq_norm, phaseBackwardMap, sub_neg_eq_add] at h
  nlinarith

/-- A rough-momentum phase point in a bounded physical kernel lies in a fixed position tube. -/
theorem norm_actual_phasePosition_sub_zero_le
    {P : V → V} {L : ℝ} (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {R : V →L[ℝ] V} (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ))
    {w z p : V} (hw : w + R (P w) = 0)
    {a b ρ : ℝ} (hR : ‖R‖ ≤ ρ) (hphysical : ‖z + R p‖ ≤ a)
    (hrough : ‖p - P z‖ ≤ b) : ‖z - w‖ ≤ 2 * (a + ρ * b) := by
  have hb : 0 ≤ b := (norm_nonneg _).trans hrough
  have hrev : ‖P z - p‖ ≤ b := by simpa only [norm_sub_rev] using hrough
  have heq : z + R (P z) = (z + R p) + R (P z - p) := by rw [R.map_sub]; abel_nf
  have hres : ‖z + R (P z)‖ ≤ a + ρ * b := by
    calc
      _ = ‖(z + R p) + R (P z - p)‖ := congrArg norm heq
      _ ≤ ‖z + R p‖ + ‖R (P z - p)‖ := norm_add_le _ _
      _ ≤ a + ‖R‖ * b := add_le_add hphysical
        ((R.le_opNorm _).trans (mul_le_mul_of_nonneg_left hrev (norm_nonneg _)))
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hR hb)
  exact (norm_sub_phaseZero_le_residual hP hsmall hw z).trans
    (mul_le_mul_of_nonneg_left hres (by norm_num))

/-- The same actual contributor has a fixed momentum tube around the inverse phase curve. -/
theorem norm_actual_phaseMomentum_sub_zero_le
    {P : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {R : V →L[ℝ] V} (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ))
    {w z p : V} (hw : w + R (P w) = 0)
    {a b ρ : ℝ} (hR : ‖R‖ ≤ ρ) (hphysical : ‖z + R p‖ ≤ a)
    (hrough : ‖p - P z‖ ≤ b) : ‖p - P w‖ ≤ b + 2 * L * (a + ρ * b) := by
  have hpos := norm_actual_phasePosition_sub_zero_le hP hsmall hw hR hphysical hrough
  calc
    _ ≤ ‖p - P z‖ + ‖P z - P w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ b + L * ‖z - w‖ := add_le_add hrough (hP z w)
    _ ≤ b + L * (2 * (a + ρ * b)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hpos hL)
    _ = _ := by ring

/-- A complete inverse phase curve is produced from the original field and mobility family. -/
theorem exists_phaseInverseCurve {X : Type*} [CompleteSpace V]
    {P : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    (R : X → V →L[ℝ] V) (hsmall : ∀ r, ‖R r‖ * L ≤ (1 / 2 : ℝ)) :
    ∃ z : X → V,
      (∀ r, z r + R r (P (z r)) = 0) ∧
      (∀ r, ‖z r‖ ≤ 2 * ‖R r‖ * ‖P 0‖) ∧
      (∀ r, ‖P (z r)‖ ≤ 2 * ‖P 0‖) ∧
      ∀ r s, ‖z r - z s‖ ≤ 4 * ‖R r - R s‖ * ‖P 0‖ := by
  let z := fun r ↦ phaseInverseZero P hP (R r) (hsmall r)
  have hz : ∀ r, z r + R r (P (z r)) = 0 := fun r ↦ phaseInverseZero_eq hP (R r) (hsmall r)
  exact ⟨z, hz, fun r ↦ norm_phaseZero_le hP (hsmall r) (hz r),
    fun r ↦ norm_momentum_at_phaseZero_le hL hP (hsmall r) (hz r),
    fun r s ↦ norm_phaseZeros_sub_le_original_amplitude hL hP (hsmall r) (hsmall s) (hz r) (hz s)⟩

end OTSelector.Reconstruction

end
end
