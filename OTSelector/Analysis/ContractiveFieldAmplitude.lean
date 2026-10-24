import Mathlib.Tactic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ActualPhaseMomentumAmplitude.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ActualPhaseMomentumAmplitude`; the selected original proof blocks follow. -/
section

/-!
Conditions: A small-Lipschitz phase perturbation with explicit physical residual and rough momentum error.

Objects: Two-sided comparison between the original field amplitude and each actual contributor momentum.

Proof detail: Use the physical residual to control position, apply the field Lipschitz bound and absorb the half-mobility term; use the large-amplitude threshold for comparability.

Sources: Gerald Teschl, Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46).
Relation: Elementary quantitative norm inequalities; no selected-cloud or independence law is used.
-/

/-!
# Original amplitude and the actual contributor momentum

A physical contributor and its rough-node error give both amplitude bounds.
Large field amplitude is comparable to the actual momentum of each contributor;
no independent or selected-cloud distribution is used.
-/
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The literal physical residual bounds the original reference position. -/
theorem norm_actual_phasePosition_le_of_physical
    (R : V →L[ℝ] V) {x p : V} {a : ℝ} (hphysical : ‖x + R p‖ ≤ a) :
    ‖x‖ ≤ a + ‖R‖ * ‖p‖ := by
  calc
    _ = ‖(x + R p) - R p‖ := by congr 1; abel_nf
    _ ≤ ‖x + R p‖ + ‖R p‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hphysical (R.le_opNorm _)

/-- Both directions of amplitude control use the same actual momentum and field. -/
theorem original_phaseAmplitude_actualMomentum_bounds
    {P : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {R : V →L[ℝ] V} (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ))
    {x p : V} {a b : ℝ} (hphysical : ‖x + R p‖ ≤ a)
    (hrough : ‖p - P x‖ ≤ b) :
    ‖P 0‖ ≤ (3 / 2 : ℝ) * ‖p‖ + L * a + b ∧
      ‖p‖ ≤ 2 * ‖P 0‖ + 2 * (L * a + b) := by
  have hx := norm_actual_phasePosition_le_of_physical R hphysical
  have hLp : L * ‖x‖ ≤ L * a + (1 / 2 : ℝ) * ‖p‖ := by
    have hmul := mul_le_mul_of_nonneg_right hsmall (norm_nonneg p)
    have hpos := mul_le_mul_of_nonneg_left hx hL
    nlinarith
  have hPzero : ‖P 0 - P x‖ ≤ L * ‖x‖ := by
    simpa only [zero_sub, norm_neg] using hP 0 x
  have hPzero' : ‖P x - P 0‖ ≤ L * ‖x‖ := by
    simpa only [sub_zero] using hP x 0
  have hrough' : ‖P x - p‖ ≤ b := by simpa only [norm_sub_rev] using hrough
  have hlow : ‖P 0‖ ≤ L * ‖x‖ + b + ‖p‖ := by
    calc
      _ ≤ ‖P 0 - P x‖ + ‖P x - p‖ + ‖p‖ := by
        have ht := norm_sub_le_norm_sub_add_norm_sub (P 0) (P x) p
        have hu := norm_le_norm_sub_add (P 0) p
        linarith
      _ ≤ _ := add_le_add (add_le_add hPzero hrough') le_rfl
  have hupp : ‖p‖ ≤ b + L * ‖x‖ + ‖P 0‖ := by
    calc
      _ ≤ ‖p - P x‖ + ‖P x - P 0‖ + ‖P 0‖ := by
        have ht := norm_sub_le_norm_sub_add_norm_sub p (P x) (P 0)
        have hu := norm_le_norm_sub_add p (P 0)
        linarith
      _ ≤ _ := add_le_add (add_le_add hrough hPzero') le_rfl
  constructor <;> nlinarith

/-- For large amplitude every contributor has comparable actual momentum.
This supplies the pointwise weight needed by the good-event traffic estimate. -/
theorem original_phaseAmplitude_comparable_to_actualMomentum
    {P : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {R : V →L[ℝ] V} (hsmall : ‖R‖ * L ≤ (1 / 2 : ℝ))
    {x p : V} {a b : ℝ} (hphysical : ‖x + R p‖ ≤ a)
    (hrough : ‖p - P x‖ ≤ b) (hlarge : 2 * (L * a + b) ≤ ‖P 0‖) :
    ‖P 0‖ ≤ 3 * ‖p‖ ∧ ‖p‖ ≤ 3 * ‖P 0‖ := by
  have h := original_phaseAmplitude_actualMomentum_bounds hL hP hsmall hphysical hrough
  constructor <;> nlinarith [h.1, h.2]

end OTSelector.Reconstruction

end
end
