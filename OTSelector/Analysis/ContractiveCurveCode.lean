import OTSelector.Analysis.ContractivePairCurve
import OTSelector.Finite.LatticePairCoordinates
import OTSelector.Finite.LatticeWalkCodes
import OTSelector.Finite.LatticeWalkGeometry
import OTSelector.Finite.SampledLipschitzCurveCover
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ContractivePhaseCurveCode.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ContractivePhaseCurveCode`; the selected original proof blocks follow. -/
section

/-!
# Analysis.ContractiveCurveCode

Conditions: The contractive field/mobility bounds and a positive integer code scale dominating the explicit amplitude and speed bounds.
Objects: A finite sampled phase-walk code covering every approximate contributor to the same inverse curve.
Proof detail: Construct the bounded Lipschitz inverse phase curve, apply the existing sampled curve code and add its fixed discretization error to the contributor tube radius.

## Mathematical sources

- Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (author version)*: Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36. https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46
- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Lemma lem:highd-perturbed-traffic, proof paragraph defining F_r and its inverse trajectory; phase-tube and rescaling bounds. ../main.tex#L3688
- OTSelector project, *Finite phase-animal counting in the high-dimensional localization proof*: main.tex label eq:highd-phase-animal-tail, line 3267. main.tex#eq:highd-phase-animal-tail

Source relation: A deterministic finite-code adapter to the manuscript’s phase-curve covering argument, not a probabilistic selection theorem or a new optimal covering-rate claim.
-/

/-! # Finite original phase codes for every contributor to an inverse curve -/
open Set
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2400000

/-- The actual inverse curve determines one finite code covering all its rough
contributors. The code is chosen after the field, without a probabilistic selection premise. -/
theorem exists_phaseWalkCode_cover_of_contractive_nodes {q m : ℕ} (hm : 1 ≤ m)
    {P : (Fin q → ℝ) → (Fin q → ℝ)} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ))
    {ρ A : ℝ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖R r - R s‖ ≤ A * |r - s|)
    (hroot : 2 * (ρ + 1) * ‖P 0‖ ≤ (m : ℝ))
    (hspeed : 4 * (1 + L) * A * ‖P 0‖ ≤ (m : ℝ)) :
    ∃ code : PhaseWalkCode (2 * q) m,
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ x p : Fin q → ℝ, ∀ a b : ℝ,
        ‖x + R r p‖ ≤ a → ‖p - P x‖ ≤ b →
        ∃ j : Fin (m + 1),
          ‖phasePairVector x p - phaseWalkVertex code j‖ ≤
            max (2 * (a + ρ * b)) (b + 2 * L * (a + ρ * b)) + 2 := by
  obtain ⟨z, γ, _, _, hγroot, hγspeed, htube⟩ :=
    exists_contractive_phasePairCurve hL hP R hsmall hρ hA hR hRLip
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  obtain ⟨code, hcode⟩ := exists_phaseWalkCode_cover_of_curve hm γ
    ((hγroot 0 hzero).trans hroot) (fun r hr s hs ↦
      (hγspeed r hr s hs).trans (mul_le_mul_of_nonneg_right hspeed (abs_nonneg _)))
  refine ⟨code, fun r hr x p a b hphysical hrough ↦ ?_⟩
  obtain ⟨j, hj⟩ := hcode r hr
  refine ⟨j, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ (γ r) _).trans
    (add_le_add (htube r hr x p a b hphysical hrough) hj)

end OTSelector.Reconstruction

end
end
