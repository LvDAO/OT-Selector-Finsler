import OTSelector.Analysis.ContractiveFieldAmplitude
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalAmplitudeBallContainment.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalAmplitudeBallContainment`; the selected original proof blocks follow. -/
section

/-!
Conditions: Small-Lipschitz phase data with explicit physical/node error bounds, and the stated inverse-frame/readout distortion bounds.

Objects: Explicit position/momentum radii and chart/manifold ball containment.

Proof detail: Insert the amplitude bound into the contributor inequalities, apply the actual inverse matrix estimate and then the metric readout estimate.

Sources: Gerald Teschl, Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46).
Relation: Quantitative norm/coordinate corollaries. Application terminology does not add distributional assumptions to these general inequalities.
-/

/-!
# Amplitude event to explicit ball containment

This file closes gap (a) of FinslerOriginalFrozenCoreEntryBound.lean: the
pressure-lane amplitude event (bounded normalized phase-field amplitude) is
converted into explicit ball containments for the retained coordinates, both in
the retained normalized chart space and on the manifold through a chart readout.

Contents:

1. norm_position_le_of_phaseAmplitude: from the physical residual bound and the
   rough-node error of the original phase amplitude data, the retained reference
   position is bounded by a + ||R|| * (2 ||P 0|| + 2 (L a + b)).
2. phaseAmplitude_ball_bounds: if the amplitude event bounds the field at the
   base clock, ||P 0|| <= PB, then the retained position and momentum are bounded
   by the explicit radii
     Drad  = a + ||R|| * (2 PB + 2 (L a + b)),
     Dmom  = 2 PB + 2 (L a + b).
   These are the amplitude-event ball radii; no distributional input is used.
3. norm_sub_center_le_of_amplitude: the normalized amplitude bound
   ||T * x - z0|| <= R demultiplies to the chart ball
   ||x - T^{-1} z0|| <= C R around the pulled-back normalized center, with the
   explicit inverse-frame distortion constant C.
4. dist_le_of_chartAmplitude: an inverse-Lipschitz chart readout turns a chart
   amplitude bound into a metric ball on the manifold.
5. frozenCoreEntry_ballContainment_of_amplitude: the resulting containment
   forall i, dist (X i) c <= Drad is exactly the hypothesis consumed by
   FinslerOriginalFrozenCoreEntryBound.lean, so gap (a) reduces to the explicit
   readout distortion constant and the amplitude radius.
-/
open Set Function Filter Matrix Module
open scoped Topology BigOperators Matrix

noncomputable section
namespace OTSelector.Reconstruction

/-! ## Bounded amplitude gives bounded retained position and momentum -/

/-- **Position bound from the phase-amplitude data.**  The physical residual
bound and the rough-node error of the original phase amplitude data bound the
retained reference position by an explicit constant. -/
theorem norm_position_le_of_phaseAmplitude {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {P : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {Rc : V →L[ℝ] V} (hsmall : ‖Rc‖ * L ≤ (1 / 2 : ℝ))
    {x p : V} {a b : ℝ} (hphysical : ‖x + Rc p‖ ≤ a)
    (hrough : ‖p - P x‖ ≤ b) :
    ‖x‖ ≤ a + ‖Rc‖ * (2 * ‖P 0‖ + 2 * (L * a + b)) := by
  have hp := (original_phaseAmplitude_actualMomentum_bounds hL hP hsmall hphysical hrough).2
  calc ‖x‖ ≤ a + ‖Rc‖ * ‖p‖ := norm_actual_phasePosition_le_of_physical Rc hphysical
    _ ≤ a + ‖Rc‖ * (2 * ‖P 0‖ + 2 * (L * a + b)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (norm_nonneg Rc))

/-- **Ball radii of the amplitude event.**  If the amplitude event bounds the
normalized phase field at the base clock by PB, then the retained reference
position and momentum are bounded by the explicit radii Drad and Dmom.  This is
the quantitative ball containment extracted from the bounded-amplitude event. -/
theorem phaseAmplitude_ball_bounds {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {P : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    {Rc : V →L[ℝ] V} (hsmall : ‖Rc‖ * L ≤ (1 / 2 : ℝ))
    {x p : V} {a b PB : ℝ} (hphysical : ‖x + Rc p‖ ≤ a)
    (hrough : ‖p - P x‖ ≤ b) (hamp : ‖P 0‖ ≤ PB) :
    ‖x‖ ≤ a + ‖Rc‖ * (2 * PB + 2 * (L * a + b)) ∧
      ‖p‖ ≤ 2 * PB + 2 * (L * a + b) := by
  have hp := (original_phaseAmplitude_actualMomentum_bounds hL hP hsmall hphysical hrough).2
  have hPB : ‖p‖ ≤ 2 * PB + 2 * (L * a + b) := by
    have h2 : 2 * ‖P 0‖ ≤ 2 * PB := by linarith
    linarith
  refine ⟨?_, hPB⟩
  calc ‖x‖ ≤ a + ‖Rc‖ * ‖p‖ := norm_actual_phasePosition_le_of_physical Rc hphysical
    _ ≤ a + ‖Rc‖ * (2 * PB + 2 * (L * a + b)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hPB (norm_nonneg Rc))

/-! ## Demultiplication: the normalized amplitude bound is a chart ball -/

/-- **Chart ball around the pulled-back normalized center.**  If the normalized
path coordinate obeys the amplitude bound ||T * x - z0|| <= R and the inverse
frame has distortion constant C, then x lies in the chart ball of radius C * R
around the pulled-back center T^{-1} z0. -/
theorem norm_sub_center_le_of_amplitude {q : ℕ}
    {T : Matrix (Fin q) (Fin q) ℝ} [Invertible T]
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, ‖T⁻¹ *ᵥ v‖ ≤ C * ‖v‖)
    {x z₀ : Fin q → ℝ} {R : ℝ} (hamp : ‖T *ᵥ x - z₀‖ ≤ R) :
    ‖x - T⁻¹ *ᵥ z₀‖ ≤ C * R := by
  have hsplit : x - T⁻¹ *ᵥ z₀ = T⁻¹ *ᵥ (T *ᵥ x - z₀) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec]
  rw [hsplit]
  exact (hC _).trans (mul_le_mul_of_nonneg_left hamp hC0)

/-- **Closed-ball form.**  The demultiplied normalized coordinate lies in the
closed ball of the pulled-back normalized center at radius C * R. -/
theorem mem_closedBall_of_normalized_amplitude {q : ℕ}
    {T : Matrix (Fin q) (Fin q) ℝ} [Invertible T]
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, ‖T⁻¹ *ᵥ v‖ ≤ C * ‖v‖)
    {x z₀ : Fin q → ℝ} {R : ℝ} (hamp : ‖T *ᵥ x - z₀‖ ≤ R) :
    x ∈ Metric.closedBall (T⁻¹ *ᵥ z₀) (C * R) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact norm_sub_center_le_of_amplitude hC0 hC hamp

/-! ## From chart amplitude to manifold metric ball -/

/-- **Manifold metric ball from a chart amplitude bound.**  An inverse-Lipschitz
chart readout with distortion constant C turns the chart amplitude bound
||Phi (X i) - Phi c|| <= R into the metric ball containment
dist (X i) c <= C * R.  This is the form consumed by the frozen core entry
bound. -/
theorem dist_le_of_chartAmplitude {M G : Type*} [PseudoMetricSpace M]
    [NormedAddCommGroup G] {Φ : M → G} {c : M} {C R : ℝ} (hC0 : 0 ≤ C)
    (hread : ∀ x, dist x c ≤ C * ‖Φ x - Φ c‖)
    (hamp : ∀ x, ‖Φ x - Φ c‖ ≤ R) (x : M) :
    dist x c ≤ C * R :=
  (hread x).trans (mul_le_mul_of_nonneg_left (hamp x) hC0)

/-- **The frozen core entry ball containment.**  Every retained source or target
of the rooted scene satisfies the amplitude bound for its chart readout, hence
lies in the manifold ball of explicit radius C * R around the readout center.
This is exactly the hypothesis forall i, dist (X i) c <= Drad consumed by
FinslerOriginalFrozenCoreEntryBound.lean. -/
theorem frozenCoreEntry_ballContainment_of_amplitude {ι M G : Type*}
    [PseudoMetricSpace M] [NormedAddCommGroup G] {X : ι → M} {Φ : M → G}
    {c : M} {C_R Drad : ℝ} (hC0 : 0 ≤ C_R)
    (hread : ∀ x, dist x c ≤ C_R * ‖Φ x - Φ c‖)
    (hamp : ∀ i, ‖Φ (X i) - Φ c‖ ≤ Drad) :
    ∀ i, dist (X i) c ≤ C_R * Drad := by
  intro i
  exact (hread (X i)).trans (mul_le_mul_of_nonneg_left (hamp i) hC0)

end OTSelector.Reconstruction

end
end
