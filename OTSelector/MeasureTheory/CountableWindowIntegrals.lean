import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
## Lemma skeleton

* **Conditions:** Countably many measurable windows cover almost everywhere.
* **Objects:** First-containing-window indicator weights on the unchanged windows.
* **Proof detail:** Disjointify the windows and commute a nonnegative sum with the integral.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
  https://measure.axler.net/MIRA.pdf

**Relationship to the sources:** The ownership indicator formula is a local countable-additivity/Tonelli corollary.
-/

/-!
# Integration over countable windows without repeated mass

An almost-everywhere cover by Borel windows gives an exact sum of integrals on
those same windows. The first containing window owns each point through an
indicator weight, so the integration domains themselves need not be changed.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

/-- A countable measurable window cover splits any nonnegative integral exactly.
Each term keeps its original window and uses an indicator to remove earlier
windows. Neither the measure nor the integrand needs a finiteness hypothesis,
and the integrand need not be measurable. -/
theorem setLIntegral_eq_tsum_window_indicator
    {M : Type*} [MeasurableSpace M] (η : Measure M)
    (O : ℕ → Set M) (hO : ∀ j, MeasurableSet (O j))
    (hcover : ∀ᵐ x ∂η, x ∈ ⋃ j, O j)
    {S : Set M} (hS : MeasurableSet S) (g : M → ℝ≥0∞) :
    (∫⁻ x in S, g x ∂η) =
      ∑' j, ∫⁻ x in O j ∩ S, (disjointed O j).indicator g x ∂η := by
  have hC : ∀ j, MeasurableSet (disjointed O j) := MeasurableSet.disjointed hO
  have hfull : ∀ᵐ x ∂η.restrict S, x ∈ ⋃ j, disjointed O j := by
    simpa only [iUnion_disjointed] using (ae_restrict_of_ae (s := S) hcover)
  calc
    (∫⁻ x in S, g x ∂η) =
        ∫⁻ x in ⋃ j, disjointed O j, g x ∂η.restrict S := by
      rw [Measure.restrict_eq_self_of_ae_mem hfull]
    _ = ∑' j, ∫⁻ x in disjointed O j, g x ∂η.restrict S :=
      lintegral_iUnion hC (disjoint_disjointed O) g
    _ = _ := by
      apply tsum_congr
      intro j
      rw [Measure.restrict_restrict' hS, setLIntegral_indicator (hC j)]
      have hset : disjointed O j ∩ S = disjointed O j ∩ (O j ∩ S) := by
        ext x
        exact ⟨fun hx ↦ ⟨hx.1, disjointed_subset O j hx.1, hx.2⟩,
          fun hx ↦ ⟨hx.1, hx.2.2⟩⟩
      rw [hset]

end OTSelector.Reconstruction
