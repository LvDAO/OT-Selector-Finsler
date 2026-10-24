import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
## Lemma skeleton

* **Conditions:** An almost-everywhere measurable window cover and one sigma-finite dominating reference.
* **Objects:** Radon–Nikodym densities of disjointified pushforward pieces.
* **Proof detail:** Disjointify, sum measures, then apply uniqueness of densities against the common reference.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
  https://measure.axler.net/MIRA.pdf

**Relationship to the sources:** The exact pushforward/window formula is a locally proved countable RN decomposition.
-/

/-!
# Common-reference densities of actual window mass pieces

Disjointed Borel windows partition an almost-everywhere covered measure. The
Radon–Nikodym densities of their actual pushforward masses sum to the full
pushforward density against one fixed sigma-finite reference. Each density
retains its exact physical test-integral identity.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

/-- Actual restricted window masses reconstruct their full pushforward by the
sum of their Radon–Nikodym densities against the same reference. Every individual
density integrates measurable nonnegative tests exactly as its physical piece. -/
theorem withDensity_tsum_rnDeriv_map_disjointed
    {M Y : Type*} [MeasurableSpace M] [MeasurableSpace Y]
    (eta : Measure M) [SFinite eta] (R : Measure Y) [SigmaFinite R]
    {T : M → Y} (hT : Measurable T)
    (O : ℕ → Set M) (hO : ∀ j, MeasurableSet (O j))
    (hcover : ∀ᵐ x ∂eta, x ∈ ⋃ j, O j)
    (hQR : eta.map T ≪ R) :
    let C := disjointed O
    let Q := fun j ↦ (eta.restrict (C j)).map T
    let p := fun j ↦ (Q j).rnDeriv R
    let h := fun y ↦ ∑' j, p j y
    Measurable h ∧ R.withDensity h = eta.map T ∧
      (∀ j, R.withDensity (p j) = Q j) ∧
      ∀ j, ∀ Phi : Y → ℝ≥0∞, Measurable Phi →
        (∫⁻ y, p j y * Phi y ∂R) = ∫⁻ x in C j, Phi (T x) ∂eta := by
  let C := disjointed O
  let Q := fun j ↦ (eta.restrict (C j)).map T
  let p := fun j ↦ (Q j).rnDeriv R
  let h := fun y ↦ ∑' j, p j y
  change Measurable h ∧ R.withDensity h = eta.map T ∧
    (∀ j, R.withDensity (p j) = Q j) ∧
    ∀ j, ∀ Phi : Y → ℝ≥0∞, Measurable Phi →
      (∫⁻ y, p j y * Phi y ∂R) = ∫⁻ x in C j, Phi (T x) ∂eta
  have hC : ∀ j, MeasurableSet (C j) := MeasurableSet.disjointed hO
  have hfull : ∀ᵐ x ∂eta, x ∈ ⋃ j, C j := by
    simpa only [C, iUnion_disjointed] using hcover
  have hsum : Measure.sum (fun j ↦ eta.restrict (C j)) = eta := by
    rw [← Measure.restrict_iUnion (disjoint_disjointed O) hC]
    exact Measure.restrict_eq_self_of_ae_mem hfull
  have hsumQ : Measure.sum Q = eta.map T := by
    change Measure.sum (fun j ↦ (eta.restrict (C j)).map T) = eta.map T
    rw [← Measure.map_sum hT.aemeasurable, hsum]
  have hQ : ∀ j, Q j ≪ R := fun j ↦
    (Measure.map_mono (Measure.restrict_le_self (s := C j)) hT).absolutelyContinuous.trans hQR
  have hp : ∀ j, Measurable (p j) := fun j ↦ Measure.measurable_rnDeriv (Q j) R
  have hpiece : ∀ j, R.withDensity (p j) = Q j := fun j ↦
    Measure.withDensity_rnDeriv_eq (Q j) R (hQ j)
  have hh : Measurable h := Measurable.tsum hp
  have hfun : h = ∑' j, p j := by
    funext y
    exact (tsum_apply (Pi.summable.2 fun _ ↦ ENNReal.summable)).symm
  refine ⟨hh, ?_, hpiece, ?_⟩
  · calc
      R.withDensity h = Measure.sum Q := by
        rw [hfun, withDensity_tsum hp]
        congr 1
        funext j
        exact hpiece j
      _ = eta.map T := hsumQ
  · intro j Phi hPhi
    calc
      (∫⁻ y, p j y * Phi y ∂R) = ∫⁻ y, Phi y ∂Q j :=
        lintegral_rnDeriv_mul (hQ j) hPhi.aemeasurable
      _ = ∫⁻ x in C j, Phi (T x) ∂eta := lintegral_map hPhi hT

end OTSelector.Reconstruction
