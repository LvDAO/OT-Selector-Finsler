import Mathlib.Probability.Kernel.Basic
import OTSelector.MeasureTheory.ConditionalDensityVariation
import OTSelector.MeasureTheory.LusinCompactProperty
import OTSelector.MeasureTheory.MeasurableL1Sections
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ConditionalLawCompactCore.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ConditionalLawCompactCore`; the selected original proof blocks follow. -/
section

/-!
# Probability.ConditionalLawCompactCore

## Lemma skeleton

* **Conditions:** Two measurable normalized scalar densities representing finite conditional kernels, a finite-mass measurable label region in a Polish carrier and an arbitrary almost-everywhere property.
* **Objects:** A large compact core where both actual laws vary continuously in full variation, with measurable L1 representatives and the property retained.
* **Proof detail:** Treat each normalized density section as an L1-valued measurable map, apply Lusin to the pair and retain a compact subset of its conull good event; density variation equals the L1 distance.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=47): Section 253, especially Exercises 253Y(f)–(i), L1-valued sections and Bochner integrability.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110): Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).

Source relation (composition): Lusin continuity of unchanged whole conditional laws; no restriction or normalization of the conditional laws is performed.
-/

/-!
# Simultaneous compact continuity of original scalar conditional laws

Measurable normalized densities give one compact set on which both original scalar
laws are continuous in full total variation. The same set retains any specified
almost-everywhere property; the laws are neither restricted nor renormalized.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace OTSelector.Reconstruction

/-- On one arbitrarily large compact label set, two original scalar laws have continuous
L1 classes and continuous pairwise total variation, retaining an arbitrary ae property. -/
theorem exists_conditionalLaw_compact_core
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (lambda : Measure Z) (H : Fin 2 → Z × ℝ → ℝ≥0∞)
    (κ : Fin 2 → Kernel Z ℝ) [∀ i, IsFiniteKernel (κ i)]
    (hH : ∀ i, Measurable (H i))
    (hnorm : ∀ i, ∀ᵐ z ∂lambda, ∫⁻ t, H i (z, t) = 1)
    (hκ : ∀ i, ∀ᵐ z ∂lambda,
      (volume : Measure ℝ).withDensity (fun t ↦ H i (z, t)) = κ i z)
    {P : Z → Prop} (hP : ∀ᵐ z ∂lambda, P z)
    {s : Set Z} (hs : MeasurableSet s) (hlambdas : lambda s ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (S : Fin 2 → Z → Lp ℝ 1 (volume : Measure ℝ)) (K : Set Z),
      (∀ i, @Measurable _ _ _ (borel _) (S i)) ∧ K ⊆ s ∧ IsCompact K ∧
      lambda (s \ K) < ε ∧ ContinuousOn (fun z i ↦ S i z) K ∧
      (∀ z ∈ K, P z ∧ ∀ i,
        (∫⁻ t, H i (z, t)) = 1 ∧
        (volume : Measure ℝ).withDensity (fun t ↦ H i (z, t)) = κ i z ∧
        (⇑(S i z)) =ᵐ[volume] (fun t ↦ (H i (z, t)).toReal)) ∧
      (∀ i, ∀ z ∈ K, ∀ z' ∈ K,
        ((κ i z).toSignedMeasure - (κ i z').toSignedMeasure).totalVariation univ =
          ENNReal.ofReal ‖S i z - S i z'‖) ∧
      ∀ i, ContinuousOn (fun p : Z × Z ↦
        ((κ i p.1).toSignedMeasure - (κ i p.2).toSignedMeasure).totalVariation univ)
        (K ×ˢ K) := by
  classical
  let Y := Lp ℝ 1 (volume : Measure ℝ)
  let : MeasurableSpace Y := borel Y
  let : BorelSpace Y := ⟨rfl⟩
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  choose S hSm hS hSzero using fun i ↦ exists_measurable_L1_sections (hH i)
  have hgood : ∀ᵐ z ∂lambda, P z ∧ ∀ i,
      (∫⁻ t, H i (z, t)) = 1 ∧
      (volume : Measure ℝ).withDensity (fun t ↦ H i (z, t)) = κ i z ∧
      (⇑(S i z)) =ᵐ[volume] (fun t ↦ (H i (z, t)).toReal) := by
    filter_upwards [hP, ae_all_iff.mpr hnorm, ae_all_iff.mpr hκ] with z hz hn hk
    refine ⟨hz, fun i ↦ ⟨hn i, hk i, hS i z ?_⟩⟩
    rw [hn i]
    exact ENNReal.one_ne_top
  have hm : Measurable (fun z i ↦ S i z) := measurable_pi_lambda _ hSm
  obtain ⟨K, hKs, hK, hsmall, hc, hgoodK⟩ :=
    Geometry.exists_lusin_compact_core_with_ae_property hs hlambdas hm
      (ae_restrict_of_ae hgood) hε
  have htv (i : Fin 2) (z : Z) (hz : z ∈ K) (z' : Z) (hz' : z' ∈ K) :
      ((κ i z).toSignedMeasure - (κ i z').toSignedMeasure).totalVariation univ =
        ENNReal.ofReal ‖S i z - S i z'‖ := by
    exact totalVariation_sub_eq_norm_L1_of_withDensity volume (κ i z) (κ i z')
      ((hH i).comp (measurable_const.prodMk measurable_id)).aemeasurable
      ((hH i).comp (measurable_const.prodMk measurable_id)).aemeasurable
      ((hgoodK z hz).2 i).2.1 ((hgoodK z' hz').2 i).2.1 (S i z) (S i z')
      ((hgoodK z hz).2 i).2.2 ((hgoodK z' hz').2 i).2.2
  refine ⟨S, K, hSm, hKs, hK, hsmall, hc, hgoodK, htv, ?_⟩
  intro i
  have hi : ContinuousOn (S i) K := (continuous_apply i).comp_continuousOn hc
  have hleft : ContinuousOn (fun p : Z × Z ↦ S i p.1) (K ×ˢ K) :=
    hi.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)
  have hright : ContinuousOn (fun p : Z × Z ↦ S i p.2) (K ×ˢ K) :=
    hi.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hcont := ENNReal.continuous_ofReal.comp_continuousOn (hleft.sub hright).norm
  exact hcont.congr (fun p hp ↦ htv i p.1 hp.1 p.2 hp.2)

end OTSelector.Reconstruction

end
