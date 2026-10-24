import OTSelector.Analysis.ContractiveFieldAmplitude
import OTSelector.MeasureTheory.Integral.BoundedWeightedCount
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ContractiveContributorTraffic.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ContractiveContributorTraffic`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Integral.ContractiveContributorBound

## Lemma skeleton

* **Conditions:** A Lipschitz field, uniformly small linear displacement operators, actual contributor geometry and a large field amplitude, together with a finite count/amplitude traffic bound.
* **Objects:** A squared traffic integral bounded by three times the original count constants and the actual momentum-weighted integral.
* **Proof detail:** Use the contraction-scale inequalities and contributor geometry to bound field amplitude by three times each actual momentum, then insert that weight into the bounded count integral estimate.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=46): Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.

Source relation (composition): Locally derived contributor algebra followed by an integral comparison; no independence or deterministic momentum cutoff is introduced.
-/

/-!
# Actual-momentum weighting of good-event traffic

The count bound is the original full-scene count. Large field amplitude is
eliminated in favor of the actual momentum of every physical contributor.
-/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2400000
variable {X V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bounded per-edge traffic on the actual contributor family satisfies the
weighted traffic-square estimate, with no independence premise. -/
theorem setIntegral_traffic_sq_le_actual_momentum
    {μ : Measure X} {S : Set X} (hS : MeasurableSet S) (hfinite : μ S < ∞)
    {P : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ x y, ‖P x - P y‖ ≤ L * ‖x - y‖)
    (R : ℝ → V →L[ℝ] V)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) 1, ‖R t‖ * L ≤ (1 / 2 : ℝ))
    (z p : X → V) {a b : ℝ} (hlarge : 2 * (L * a + b) ≤ ‖P 0‖)
    (hcontributors : ∀ x ∈ S, ∃ t ∈ Icc (0 : ℝ) 1,
      ‖z x + R t (p x)‖ ≤ a ∧ ‖p x - P (z x)‖ ≤ b)
    {m B K C : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hcount : μ.real S ≤ K * m) (hm : m ≤ C * ‖P 0‖)
    {u : X → ℝ} (hu : AEStronglyMeasurable u (μ.restrict S))
    (hu0 : ∀ᵐ x ∂μ.restrict S, 0 ≤ u x)
    (huB : ∀ᵐ x ∂μ.restrict S, u x ≤ B)
    (hpu : IntegrableOn (fun x ↦ ‖p x‖ * u x) S μ) :
    IntegrableOn u S μ ∧ (∫ x in S, u x ∂μ) ^ 2 ≤
      3 * B * K * C * ∫ x in S, ‖p x‖ * u x ∂μ := by
  have hcount' : μ.real S ≤ (K * C) * ‖P 0‖ := by
    calc
      _ ≤ K * m := hcount
      _ ≤ K * (C * ‖P 0‖) := mul_le_mul_of_nonneg_left hm hK
      _ = _ := by ring
  have hweight : ∀ᵐ x ∂μ.restrict S, ‖P 0‖ ≤ 3 * ‖p x‖ := by
    filter_upwards [ae_restrict_mem hS] with x hx
    obtain ⟨t, ht, hphysical, hrough⟩ := hcontributors x hx
    exact (original_phaseAmplitude_comparable_to_actualMomentum hL hP
      (hsmall t ht) hphysical hrough hlarge).1
  have h := OTSelector.Probability.setIntegral_sq_le_of_count_and_pointwise_weight
    hfinite hu hB (mul_nonneg hK hC) hu0 huB hcount' hweight hpu
  refine ⟨h.1, ?_⟩
  convert h.2 using 1
  ring

end OTSelector.Reconstruction

end
end
