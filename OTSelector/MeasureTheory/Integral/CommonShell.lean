import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
## Lemma skeleton

* **Conditions:** A Banach-valued almost-everywhere strongly measurable uniformly bounded f, common measurable core contained in both sets, and both sets contained in a finite-mass outer carrier.
* **Objects:** Norm of the two set integrals differs by at most 2 C times the outer-minus-core real mass.
* **Proof detail:** Cancel the common core, bound the two remaining Bochner integral norms by C times their masses, and compare each shell with outer minus core.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99

**Relationship to the sources:** Derived Banach-valued common-shell estimate. The theorem permits nonmeasurable s,t/outer under the explicit measurable-core and outer-finite assumptions.
-/

/-! A common-shell estimate for genuine Banach-valued set integrals. This
is shared by scalar Haar observables and Hilbert-valued spatial averages. -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- Two actual set integrals sharing a geometric core differ only through
its outer shell. The bound uses a deterministic bound on the Banach norm. -/
theorem norm_setIntegral_sub_le_common_shell_banach
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (μ : Measure X)
    {s t core outer : Set X} (hcore : MeasurableSet core)
    (hfinite : μ outer < ∞) (hcs : core ⊆ s) (hct : core ⊆ t)
    (hso : s ⊆ outer) (hto : t ⊆ outer)
    {f : X → V} (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C) :
    ‖(∫ x in s, f x ∂μ) - ∫ x in t, f x ∂μ‖ ≤
      2 * C * (μ.real outer - μ.real core) := by
  have hio : IntegrableOn f outer μ := by
    have : IsFiniteMeasure (μ.restrict outer) := ⟨by simpa using hfinite⟩
    exact ⟨hf.restrict, HasFiniteIntegral.of_bounded (.of_forall hbound)⟩
  have hs : ‖∫ x in s \ core, f x ∂μ‖ ≤ C * μ.real (outer \ core) := by
    apply (norm_setIntegral_le_of_norm_le_const
      (lt_of_le_of_lt (measure_mono (sdiff_subset.trans hso)) hfinite)
      (fun x _ ↦ hbound x)).trans
    exact mul_le_mul_of_nonneg_left
      (measureReal_mono (sdiff_subset_sdiff_left hso)
        (ne_of_lt ((measure_mono sdiff_subset).trans_lt hfinite))) hC
  have ht : ‖∫ x in t \ core, f x ∂μ‖ ≤ C * μ.real (outer \ core) := by
    apply (norm_setIntegral_le_of_norm_le_const
      (lt_of_le_of_lt (measure_mono (sdiff_subset.trans hto)) hfinite)
      (fun x _ ↦ hbound x)).trans
    exact mul_le_mul_of_nonneg_left
      (measureReal_mono (sdiff_subset_sdiff_left hto)
        (ne_of_lt ((measure_mono sdiff_subset).trans_lt hfinite))) hC
  have hid : (∫ x in s, f x ∂μ) - ∫ x in t, f x ∂μ =
      (∫ x in s \ core, f x ∂μ) - ∫ x in t \ core, f x ∂μ := by
    rw [setIntegral_sdiff hcore (hio.mono_set hso) hcs,
      setIntegral_sdiff hcore (hio.mono_set hto) hct]
    abel
  rw [hid]
  calc
    _ ≤ ‖∫ x in s \ core, f x ∂μ‖ + ‖∫ x in t \ core, f x ∂μ‖ := norm_sub_le _ _
    _ ≤ C * μ.real (outer \ core) + C * μ.real (outer \ core) := add_le_add hs ht
    _ = _ := by
      rw [measureReal_sdiff (hcs.trans hso) hcore (ne_of_lt hfinite)]
      ring

end OTSelector.Probability
