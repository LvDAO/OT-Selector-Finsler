import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import OTSelector.MeasureTheory.CountableWindowDensities
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.LabelClockWindowDensities.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.LabelClockWindowDensities`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.LabelClockWindowDensities

## Lemma skeleton

* **Conditions:** A finite original law, a countable measurable window cover, joint label-clock absolute continuity and a measurable almost-everywhere inverse of the label-clock map.
* **Objects:** Normalized sum of window RN densities and exact reconstruction of all measurable nonnegative original observables.
* **Proof detail:** Disjointify the windows, sum their pushforward RN densities, use the exact first marginal to show section integrals equal one almost everywhere, then change variables through the given inverse.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.

Source relation (composition): Window-density reconstruction under the unchanged original label marginal; no inverse is inferred without its stated premise.
-/

/-!
# Normalized window densities in the original label and clock

The actual window mass densities share the original label law times Lebesgue
reference. Their sum has normalized sections and reconstructs original observables
through any measurable almost-everywhere inverse of the original label-clock map.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

/-- A product density whose first marginal is its original reference has section
mass one almost everywhere. No finiteness of individual sections is assumed. -/
theorem ae_lintegral_eq_one_of_prod_withDensity_fst
    {Z S : Type*} [MeasurableSpace Z] [MeasurableSpace S]
    (lambda : Measure Z) [SigmaFinite lambda] (tau : Measure S) [SFinite tau]
    {h : Z × S → ℝ≥0∞} (hh : Measurable h)
    (hfst : ((lambda.prod tau).withDensity h).fst = lambda) :
    ∀ᵐ z ∂lambda, ∫⁻ s, h (z, s) ∂tau = 1 := by
  let H := fun z ↦ ∫⁻ s, h (z, s) ∂tau
  have hH : Measurable H := hh.lintegral_prod_right'
  have heq : lambda.withDensity H = ((lambda.prod tau).withDensity h).fst := by
    ext A hA
    rw [withDensity_apply _ hA, Measure.fst_apply hA,
      withDensity_apply _ (measurable_fst hA), ← prod_univ]
    simpa only [H, setLIntegral_univ] using
      (setLIntegral_prod (μ := lambda) (ν := tau) (s := A) (t := univ)
        h hh.aemeasurable.restrict).symm
  have hunit : lambda.withDensity H = lambda.withDensity (1 : Z → ℝ≥0∞) := by
    rw [withDensity_one]
    exact heq.trans hfst
  exact (withDensity_eq_iff_of_sigmaFinite hH.aemeasurable
    (measurable_const : Measurable (1 : Z → ℝ≥0∞)).aemeasurable).mp hunit

/-- The explicit sum of actual window mass densities is normalized under the
original label law and reconstructs every original nonnegative observable through
the existing measurable label-clock inverse. -/
theorem labelClock_window_density_reconstruction
    {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]
    (eta : Measure M) [IsFiniteMeasure eta]
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (O : ℕ → Set M) (hO : ∀ j, MeasurableSet (O j))
    (hcover : ∀ᵐ x ∂eta, x ∈ ⋃ j, O j)
    (hjoint : eta.map (fun x ↦ (a x, u x)) ≪ (eta.map a).prod volume)
    (b : Z × ℝ → M) (hb : Measurable b)
    (hbinv : ∀ᵐ x ∂eta, b (a x, u x) = x) :
    let R := (eta.map a).prod (volume : Measure ℝ)
    let C := disjointed O
    let p := fun j ↦ ((eta.restrict (C j)).map (fun x ↦ (a x, u x))).rnDeriv R
    let h := fun y ↦ ∑' j, p j y
    Measurable h ∧ R.withDensity h = eta.map (fun x ↦ (a x, u x)) ∧
      (∀ᵐ z ∂eta.map a, ∫⁻ s, h (z, s) ∂volume = 1) ∧
      ∀ g : M → ℝ≥0∞, Measurable g →
        (∫⁻ x, g x ∂eta) =
          ∫⁻ z, ∫⁻ s, h (z, s) * g (b (z, s)) ∂volume ∂eta.map a := by
  let R := (eta.map a).prod (volume : Measure ℝ)
  let C := disjointed O
  let p := fun j ↦ ((eta.restrict (C j)).map (fun x ↦ (a x, u x))).rnDeriv R
  let h := fun y ↦ ∑' j, p j y
  obtain ⟨hh, hden, _, _⟩ :=
    withDensity_tsum_rnDeriv_map_disjointed eta R (ha.prodMk hu) O hO hcover hjoint
  have hnorm : ∀ᵐ z ∂eta.map a, ∫⁻ s, h (z, s) ∂volume = 1 :=
    ae_lintegral_eq_one_of_prod_withDensity_fst (eta.map a) volume hh (by
      rw [hden]
      exact Measure.fst_map_prodMk hu)
  refine ⟨hh, hden, hnorm, ?_⟩
  intro g hg
  calc
    (∫⁻ x, g x ∂eta) = ∫⁻ x, g (b (a x, u x)) ∂eta :=
      lintegral_congr_ae (hbinv.mono fun x hx ↦ congrArg g hx.symm)
    _ = ∫⁻ y, g (b y) ∂eta.map (fun x ↦ (a x, u x)) :=
      (lintegral_map (hg.comp hb) (ha.prodMk hu)).symm
    _ = ∫⁻ y, g (b y) ∂R.withDensity h := by rw [hden]
    _ = ∫⁻ y, h y * g (b y) ∂R :=
      lintegral_withDensity_eq_lintegral_mul R hh (hg.comp hb)
    _ = _ := lintegral_prod _ (hh.mul (hg.comp hb)).aemeasurable

end OTSelector.Reconstruction

end
