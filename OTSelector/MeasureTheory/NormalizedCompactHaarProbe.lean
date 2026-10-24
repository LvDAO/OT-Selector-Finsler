import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Topology.Algebra.Module.Cardinality
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneNormalizedProbe.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneNormalizedProbe`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.NormalizedCompactHaarProbe

## Lemma skeleton

* **Conditions:** Finite-dimensional real coordinate Haar volume.
* **Objects:** An internally constructed nonnegative compact continuous test of integral one.
* **Proof detail:** Choose a nonzero nonnegative compact cutoff on a positive-volume open set, show its integral is finite and positive and divide by that integral.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=143): Section 1.10.1, Lemma 1.10.1, pp. 134–135, and Exercise 1.10.6, p. 136.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22): Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.

Source relation (composition): Elementary compact-probe normalization; the normalized probe is produced, not a supplied hypothesis.
-/

/-! The normalized nonnegative compact Haar probe is constructed internally. -/
open Set Function MeasureTheory OTSelector.Probability
open scoped Topology CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/-- A nonnegative compact spatial Haar probe with integral one exists in every
actual finite-dimensional source coordinate, including dimension zero. -/
theorem exists_nonnegative_normalized_compact_Haar_probe :
    ∃ η : C_c(ι → ℝ, ℝ), (∀ v, 0 ≤ η v) ∧ (∫ v, η v ∂volume) = 1 := by
  obtain ⟨χ, hχone, hχbounds⟩ := LocalFiniteMeasure.exists_compact_cutoff
    (isCompact_closedBall (0 : ι → ℝ) 1)
  have hχ0 : χ (0 : ι → ℝ) = 1 := hχone (by simp)
  have hi : Integrable χ volume := χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport
  have hp : 0 < ∫ v, χ v ∂volume := by
    apply (integral_pos_iff_support_of_nonneg (fun v ↦ (hχbounds v).1) hi).mpr
    apply χ.continuous.isOpen_support.measure_pos volume
    refine ⟨0, ?_⟩
    change χ 0 ≠ 0
    rw [hχ0]
    norm_num
  refine ⟨(∫ v, χ v ∂volume)⁻¹ • χ, ?_, ?_⟩
  · intro v
    change 0 ≤ (∫ v, χ v ∂volume)⁻¹ * χ v
    exact mul_nonneg (inv_nonneg.mpr hp.le) (hχbounds v).1
  · change (∫ v, (∫ v, χ v ∂volume)⁻¹ * χ v ∂volume) = 1
    rw [integral_const_mul, inv_mul_cancel₀ hp.ne']

end OTSelector.Reconstruction

end
end
