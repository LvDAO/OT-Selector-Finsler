import OTSelector.MeasureTheory.CountableWindowDensities
import OTSelector.MeasureTheory.LabelClockWindowDensities
import OTSelector.MeasureTheory.ProductReferenceDensity
import OTSelector.Probability.LabelClockConditionalDensity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.GeometricWindowDensities.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.GeometricWindowDensities`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.GeometricWindowDensities

## Lemma skeleton

* **Conditions:** Countably covered finite original law whose disjoint window joint pieces have supplied geometric product-reference densities, with sigma-finite local label references and full joint absolute continuity.
* **Objects:** Reference-change factors identify each window RN density and their normalized sum recovers the actual joint and conditional clock laws.
* **Proof detail:** Change each geometric label reference to the actual label law using RN multiplication, sum disjoint window densities by Tonelli, then use exact first-marginal normalization and conditional density uniqueness.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25): 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.

Source relation (composition): Geometric density inputs are explicit; this module supplies only their reference-change and reconstruction layer.
-/

/-!
# Geometric factors for the existing conditional window densities

Actual physical mass pieces have geometric product-reference densities. Their
reference-change factors identify the existing RN pieces and give the same
normalized conditional clock laws through one measurable sum.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

/-- Actual geometric window factors identify each existing RN density and their
sum gives the original normalized conditional clock law. -/
theorem labelClock_geometric_window_densities
    {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]
    (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (O : ℕ → Set M) (hO : ∀ j, MeasurableSet (O j))
    (hcover : ∀ᵐ x ∂η, x ∈ ⋃ j, O j)
    (hjoint : η.map (fun x ↦ (a x, u x)) ≪ (η.map a).prod volume)
    (β : ℕ → Measure Z) (hβ : ∀ j, SigmaFinite (β j))
    (G : ℕ → Z × ℝ → ℝ≥0∞) (hG : ∀ j, Measurable (G j))
    (hpiece : ∀ j,
      (η.restrict (disjointed O j)).map (fun x ↦ (a x, u x)) =
        ((β j).prod (volume : Measure ℝ)).withDensity (G j)) :
    let lambda := η.map a
    let R := lambda.prod (volume : Measure ℝ)
    let p := fun j ↦
      ((η.restrict (disjointed O j)).map (fun x ↦ (a x, u x))).rnDeriv R
    let H := fun y : Z × ℝ ↦ ∑' j, (β j).rnDeriv lambda y.1 * G j y
    (∀ j, p j =ᵐ[R] (fun y ↦ (β j).rnDeriv lambda y.1 * G j y)) ∧
      Measurable H ∧ R.withDensity H = η.map (fun x ↦ (a x, u x)) ∧
      (∀ᵐ z ∂lambda, ∫⁻ s, H (z, s) ∂volume = 1) ∧
      (∀ᵐ z ∂lambda,
        (volume : Measure ℝ).withDensity (fun s ↦ H (z, s)) = condDistrib u a η z)
 := by
  let R := (η.map a).prod (volume : Measure ℝ)
  let p := fun j ↦
    ((η.restrict (disjointed O j)).map (fun x ↦ (a x, u x))).rnDeriv R
  let H := fun y : Z × ℝ ↦ ∑' j, (β j).rnDeriv (η.map a) y.1 * G j y
  have hp (j : ℕ) : p j =ᵐ[R]
      (fun y ↦ (β j).rnDeriv (η.map a) y.1 * G j y) := by
    let _instGeometricReference : SigmaFinite (β j) := hβ j
    change ((η.restrict (disjointed O j)).map (fun x ↦ (a x, u x))).rnDeriv R
      =ᵐ[R] _
    rw [hpiece j]
    exact rnDeriv_prod_withDensity (η.map a) (β j) volume (hG j)
  have hH : Measurable H := Measurable.tsum fun j ↦
    ((Measure.measurable_rnDeriv (β j) (η.map a)).comp measurable_fst).mul (hG j)
  obtain ⟨_, hden, _, _⟩ :=
    withDensity_tsum_rnDeriv_map_disjointed η R (ha.prodMk hu) O hO hcover hjoint
  have heq : (fun y ↦ ∑' j, p j y) =ᵐ[R] H := by
    filter_upwards [ae_all_iff.mpr hp] with y hy
    exact tsum_congr (fun j ↦ hy j)
  have hHden : R.withDensity H = η.map (fun x ↦ (a x, u x)) :=
    (withDensity_congr_ae heq).symm.trans hden
  have hnorm : ∀ᵐ z ∂η.map a, ∫⁻ s, H (z, s) ∂volume = 1 :=
    ae_lintegral_eq_one_of_prod_withDensity_fst (η.map a) volume hH (by
      rw [hHden]
      exact Measure.fst_map_prodMk hu)
  have hconditional : ∀ᵐ z ∂η.map a,
      (volume : Measure ℝ).withDensity (fun s ↦ H (z, s)) = condDistrib u a η z :=
    ae_withDensity_clock_eq_condDistrib (a := a) (h := H) η hu hH hHden
  exact ⟨hp, hH, hHden, hnorm, hconditional⟩

end OTSelector.Reconstruction

end
