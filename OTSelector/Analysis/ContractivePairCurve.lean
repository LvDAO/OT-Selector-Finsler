import OTSelector.Analysis.ContractivePerturbationCurveBounds
import OTSelector.Analysis.ContractivePerturbationZero
import OTSelector.Finite.LatticePairCoordinates
import OTSelector.Finite.LatticePairNormBounds
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ContractivePhasePairCurve.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ContractivePhasePairCurve`; the selected original proof blocks follow. -/
section

/-!
# Analysis.ContractivePairCurve

Conditions: A nonnegative Lipschitz constant, a field P, and a linear mobility family with norm times Lipschitz constant at most one half; explicit size and clock-Lipschitz bounds are supplied.
Objects: The inverse position z solving z + R(r)P(z) = 0, its concatenated position/momentum curve, and a tube bound for approximate contributors.
Proof detail: Apply the unique contractive inverse at each clock, derive factor-two amplitude estimates, compare two fixed points for clock-Lipschitz control, and add the explicit approximation defects.

## Mathematical sources

- Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (author version)*: Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36. https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46
- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Lemma lem:highd-perturbed-traffic, proof paragraph defining F_r and its inverse trajectory; phase-tube and rescaling bounds. ../main.tex#L3688

Source relation: Banach contraction plus locally proved quantitative phase-tube estimates. The constants and paired finite-dimensional encoding are this project’s derived interfaces, not the verbatim contraction theorem.
-/

/-!
# The inverse position-momentum curve on the actual unit window

The field at zero controls both curve amplitude and speed. Every original rough
node in a bounded physical kernel stays in a fixed tube of this same curve.
-/
open Set
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2400000

/-- The original field and a small mobility family produce the full phase curve,
including a uniform bound for every actual contributing rough node. -/
theorem exists_contractive_phasePairCurve {q : ℕ}
    {P : (Fin q → ℝ) → (Fin q → ℝ)} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z w, ‖P z - P w‖ ≤ L * ‖z - w‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ))
    {ρ A : ℝ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖R r - R s‖ ≤ A * |r - s|) :
    ∃ z : ℝ → Fin q → ℝ, ∃ γ : ℝ → Fin (2 * q) → ℝ,
      (∀ r ∈ Icc (0 : ℝ) 1, z r + R r (P (z r)) = 0) ∧
      (∀ r, γ r = phasePairVector (z r) (P (z r))) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ‖γ r‖ ≤ 2 * (ρ + 1) * ‖P 0‖) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ‖γ r - γ s‖ ≤ 4 * (1 + L) * A * ‖P 0‖ * |r - s|) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ x p : Fin q → ℝ, ∀ a b : ℝ,
        ‖x + R r p‖ ≤ a → ‖p - P x‖ ≤ b →
        ‖phasePairVector x p - γ r‖ ≤
          max (2 * (a + ρ * b)) (b + 2 * L * (a + ρ * b)) := by
  let z : ℝ → Fin q → ℝ := fun r ↦
    if hr : r ∈ Icc (0 : ℝ) 1 then phaseInverseZero P hP (R r) (hsmall r hr) else 0
  let γ := fun r ↦ phasePairVector (z r) (P (z r))
  have hz : ∀ r ∈ Icc (0 : ℝ) 1, z r + R r (P (z r)) = 0 := by
    intro r hr
    simpa only [z, dite_eq_left hr] using phaseInverseZero_eq hP (R r) (hsmall r hr)
  have hzB : ∀ r ∈ Icc (0 : ℝ) 1, ‖z r‖ ≤ 2 * ρ * ‖P 0‖ := by
    intro r hr
    exact (norm_phaseZero_le hP (hsmall r hr) (hz r hr)).trans
      (by gcongr; exact hR r hr)
  have hpB : ∀ r ∈ Icc (0 : ℝ) 1, ‖P (z r)‖ ≤ 2 * ‖P 0‖ :=
    fun r hr ↦ norm_momentum_at_phaseZero_le hL hP (hsmall r hr) (hz r hr)
  have hroot : ∀ r ∈ Icc (0 : ℝ) 1, ‖γ r‖ ≤ 2 * (ρ + 1) * ‖P 0‖ := by
    intro r hr
    apply (norm_phasePairVector_le _ _).trans
    apply max_le
    · have h := hzB r hr
      nlinarith [norm_nonneg (P 0)]
    · have h := hpB r hr
      have hmul : 0 ≤ ρ * ‖P 0‖ := mul_nonneg hρ (norm_nonneg _)
      nlinarith
  have hspeed : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖γ r - γ s‖ ≤ 4 * (1 + L) * A * ‖P 0‖ * |r - s| := by
    intro r hr s hs
    have hpos : ‖z r - z s‖ ≤ 4 * A * ‖P 0‖ * |r - s| := by
      calc
        _ ≤ 4 * ‖R r - R s‖ * ‖P 0‖ :=
          norm_phaseZeros_sub_le_original_amplitude hL hP (hsmall r hr)
            (hsmall s hs) (hz r hr) (hz s hs)
        _ ≤ 4 * (A * |r - s|) * ‖P 0‖ := by gcongr; exact hRLip r hr s hs
        _ = _ := by ring
    have hmomentum : ‖P (z r) - P (z s)‖ ≤
        L * (4 * A * ‖P 0‖ * |r - s|) :=
      (hP _ _).trans (mul_le_mul_of_nonneg_left hpos hL)
    apply (norm_phasePairVector_sub_le _ _ _ _).trans
    apply max_le
    · have hbase : 0 ≤ 4 * A * ‖P 0‖ * |r - s| := by positivity
      have hprod := mul_nonneg hL hbase
      nlinarith
    · have hbase : 0 ≤ 4 * A * ‖P 0‖ * |r - s| := by positivity
      nlinarith
  refine ⟨z, γ, hz, fun _ ↦ rfl, hroot, hspeed, ?_⟩
  intro r hr x p a b hphysical hrough
  apply (norm_phasePairVector_sub_le _ _ _ _).trans
  apply max_le_max
  · exact norm_actual_phasePosition_sub_zero_le hP (hsmall r hr)
      (hz r hr) (hR r hr) hphysical hrough
  · exact norm_actual_phaseMomentum_sub_zero_le hL hP (hsmall r hr)
      (hz r hr) (hR r hr) hphysical hrough

end OTSelector.Reconstruction

end
end
