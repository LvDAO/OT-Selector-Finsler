import Mathlib.Algebra.Order.Chebyshev
import OTSelector.Transport.Coupling.FiniteMeasureGluing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingEnergy`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseStageCouplingEnergy

**Conditions:** Finite couplings share their middle marginal on a standard Borel gluing target; metric/normed path estimates have the explicit finite length or positive weight.

**Objects:** Genuine three-point joint energy and squared endpoint distance bounds.

**Proof detail:** Read each segment through its exact joint marginal; telescope a finite path and apply Cauchy–Schwarz, or apply weighted Young to the two-segment triangle inequality.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185), Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4); [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Genuine joint energies and the literal linear-length squared path bound. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 300000

/-- The actual adjacent joint preserves both stage energies exactly. -/
theorem finiteStageCouplingJoint_lintegral_energy
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace C] [Nonempty C]
    (π₁ : Measure (A × B)) (π₂ : Measure (B × C))
    [IsFiniteMeasure π₁] [IsFiniteMeasure π₂] (hmiddle : π₁.snd = π₂.fst)
    {c₁ : A × B → ℝ≥0∞} {c₂ : B × C → ℝ≥0∞}
    (hc₁ : Measurable c₁) (hc₂ : Measurable c₂) :
    (∫⁻ z, c₁ z.1 + c₂ (z.1.2, z.2) ∂finiteStageCouplingJoint π₁ π₂) =
      (∫⁻ z, c₁ z ∂π₁) + ∫⁻ z, c₂ z ∂π₂ := by
  have hm₁ : Measurable (fun z : (A × B) × C ↦ c₁ z.1) := hc₁.comp measurable_fst
  have hpair : Measurable (fun z : (A × B) × C ↦ (z.1.2, z.2)) := by fun_prop
  rw [lintegral_add_left hm₁]
  have h₁ : (∫⁻ z, c₁ z.1 ∂finiteStageCouplingJoint π₁ π₂) = ∫⁻ z, c₁ z ∂π₁ := by
    rw [← lintegral_map hc₁ measurable_fst]
    exact congrArg (fun μ ↦ ∫⁻ z, c₁ z ∂μ) (finiteStageCouplingJoint_fst π₁ π₂)
  have h₂ : (∫⁻ z, c₂ (z.1.2, z.2) ∂finiteStageCouplingJoint π₁ π₂) = ∫⁻ z, c₂ z ∂π₂ := by
    rw [← lintegral_map hc₂ hpair]
    exact congrArg (fun μ ↦ ∫⁻ z, c₂ z ∂μ)
      (finiteStageCouplingJoint_snd_pair π₁ π₂ hmiddle)
  rw [h₁, h₂]

/-- Every actual finite path has endpoint square cost at most its number of
segments times its exact sum of squared segment costs, including zero segments. -/
theorem finiteStagePath_endpoint_sq_le
    {E : Type*} [NormedAddCommGroup E] {n : ℕ} (z : Fin (n + 1) → E) :
    dist (z 0) (z (Fin.last n)) ^ 2 ≤
      (n : ℝ) * ∑ i : Fin n, dist (z i.castSucc) (z i.succ) ^ 2 := by
  have ht : (∑ i : Fin n, (z i.succ - z i.castSucc)) =
      z (Fin.last n) - z 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_sub_iff_add_eq_add]
    calc
      _ = ∑ i : Fin (n + 1), z i := by
        simpa only [add_comm] using (Fin.sum_univ_succ z).symm
      _ = _ := by simpa only [add_comm] using Fin.sum_univ_castSucc z
  have hp : dist (z 0) (z (Fin.last n)) ≤
      ∑ i : Fin n, dist (z i.castSucc) (z i.succ) := by
    rw [dist_comm, dist_eq_norm, ← ht]
    simpa only [dist_eq_norm, norm_sub_rev] using
      norm_sum_le (Finset.univ : Finset (Fin n)) (fun i ↦ z i.succ - z i.castSucc)
  exact (pow_le_pow_left₀ dist_nonneg hp 2).trans (by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i ↦ dist (z i.castSucc) (z i.succ))))

/-- The unequal-weight three-point square bound allows linear, rather than
exponentially repeated, length constants in stage induction. -/
theorem finiteStage_dist_sq_weighted_le
    {E : Type*} [PseudoMetricSpace E] (x y z : E) {k : ℝ} (hk : 0 < k) :
    dist x z ^ 2 ≤ (k + 1) / k * dist x y ^ 2 + (k + 1) * dist y z ^ 2 := by
  have ht := pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist x z) (dist_triangle x y z) 2
  have hscaled : k * dist x z ^ 2 ≤
      (k + 1) * dist x y ^ 2 + k * (k + 1) * dist y z ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left ht hk.le, sq_nonneg (dist x y - k * dist y z)]
  calc
    _ ≤ ((k + 1) * dist x y ^ 2 + k * (k + 1) * dist y z ^ 2) / k :=
      (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using hscaled)
    _ = _ := by field_simp

end OTSelector.Reconstruction

end
end
