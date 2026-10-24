import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.CondDistrib

/-!
## Lemma skeleton

* **Conditions:** Finite measures with absolute continuity and a measurable label into a standard conditional-law setting.
* **Objects:** Conditional distributions and their jointly measurable densities.
* **Proof detail:** Disintegrate the Radon–Nikodym density and use kernel almost-everywhere identities.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
  https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** The label-and-conditional-law iff and reference-density transport are combinations of disintegration and Radon–Nikodym, not verbatim statements from the book.
-/

/-!
# Absolute continuity of original conditional laws

Absolute continuity of two original finite measures is equivalent to absolute
continuity of their label laws and of their actual conditional distributions.
Consequently geometric absolute continuity of conditional volume in a coordinate
transfers to any original population absolutely continuous with respect to that volume.
The measurable label and the conditional-volume estimate remain geometric inputs.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] {μ m : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure m]
  {label : M → Z}

/-- The actual conditional population law is absolutely continuous with respect to
the actual conditional reference law at almost every original population label. -/
theorem condDistrib_absolutelyContinuous_of_absolutelyContinuous
    (hμ : μ ≪ m) (hlabel : Measurable label) :
    ∀ᵐ z ∂μ.map label, condDistrib id label μ z ≪ condDistrib id label m z := by
  have hgraph := hμ.map (hlabel.prodMk measurable_id)
  have hμgraph := compProd_map_condDistrib (mβ := inferInstance)
    (X := label) (measurable_id.aemeasurable : AEMeasurable (id : M → M) μ)
  have hmgraph := compProd_map_condDistrib (mβ := inferInstance)
    (X := label) (measurable_id.aemeasurable : AEMeasurable (id : M → M) m)
  rw [← hμgraph, ← hmgraph] at hgraph
  exact hgraph.kernel_of_compProd

/-- Original absolute continuity is exactly label-law absolute continuity together
with conditional absolute continuity under the original population label law. -/
theorem absolutelyContinuous_iff_label_and_condDistrib (hlabel : Measurable label) :
    μ ≪ m ↔ μ.map label ≪ m.map label ∧
      ∀ᵐ z ∂μ.map label, condDistrib id label μ z ≪ condDistrib id label m z := by
  constructor
  · intro hμ
    exact ⟨hμ.map hlabel,
      condDistrib_absolutelyContinuous_of_absolutelyContinuous hμ hlabel⟩
  · rintro ⟨hlaw, hcond⟩
    have hcomp := hlaw.comp hcond
    have hμrec := condDistrib_comp_map hlabel.aemeasurable
      (measurable_id.aemeasurable : AEMeasurable (id : M → M) μ)
    have hmrec := condDistrib_comp_map hlabel.aemeasurable
      (measurable_id.aemeasurable : AEMeasurable (id : M → M) m)
    simpa only [hμrec, hmrec, Measure.map_id] using hcomp

/-- A geometric conditional-volume estimate in possibly label-dependent coordinates
transfers to the original population without a positive lower density bound. -/
theorem condDistrib_map_absolutelyContinuous_of_reference
    {T : Type*} [MeasurableSpace T] (hμ : μ ≪ m) (hlabel : Measurable label)
    (coordinate : Z → M → T) (hcoordinate : ∀ z, Measurable (coordinate z))
    (reference : Z → Measure T)
    (hreference : ∀ᵐ z ∂m.map label,
      (condDistrib id label m z).map (coordinate z) ≪ reference z) :
    ∀ᵐ z ∂μ.map label,
      (condDistrib id label μ z).map (coordinate z) ≪ reference z := by
  have href := (hμ.map hlabel).ae_le hreference
  have hcond := condDistrib_absolutelyContinuous_of_absolutelyContinuous hμ hlabel
  filter_upwards [href, hcond] with z hz hcz
  exact (hcz.map (hcoordinate z)).trans hz

/-- Original absolute continuity produces jointly measurable, normalized densities
of the actual conditional population laws against the conditional reference laws. -/
theorem exists_measurable_condDistrib_density
    (hμ : μ ≪ m) (hlabel : Measurable label) :
    ∃ w : Z → M → ℝ≥0∞, Measurable (Function.uncurry w) ∧
      ∀ᵐ z ∂μ.map label,
        (condDistrib id label m z).withDensity (w z) = condDistrib id label μ z ∧
          ∫⁻ x, w z x ∂condDistrib id label m z = 1 := by
  let κ := condDistrib id label μ
  let η := condDistrib id label m
  refine ⟨κ.rnDeriv η, κ.measurable_rnDeriv η, ?_⟩
  filter_upwards [condDistrib_absolutelyContinuous_of_absolutelyContinuous hμ hlabel]
    with z hz
  have hd := Kernel.withDensity_rnDeriv_eq hz
  rw [Kernel.withDensity_apply _ (κ.measurable_rnDeriv η)] at hd
  exact ⟨hd, by simpa only [measure_univ] using Kernel.lintegral_rnDeriv hz⟩

/-- The same normalized jointly measurable conditional density reconstructs every
nonnegative label-dependent observable of the original population exactly. -/
theorem exists_condDistrib_density_lintegral
    (hμ : μ ≪ m) (hlabel : Measurable label) :
    ∃ w : Z → M → ℝ≥0∞, Measurable (Function.uncurry w) ∧
      (∀ᵐ z ∂μ.map label,
        (condDistrib id label m z).withDensity (w z) = condDistrib id label μ z ∧
          ∫⁻ x, w z x ∂condDistrib id label m z = 1) ∧
      ∀ g : Z × M → ℝ≥0∞, Measurable g →
        (∫⁻ x, g (label x, x) ∂μ) =
          ∫⁻ z, ∫⁻ x, w z x * g (z, x) ∂condDistrib id label m z ∂μ.map label := by
  obtain ⟨w, hw, hcond⟩ := exists_measurable_condDistrib_density hμ hlabel
  refine ⟨w, hw, hcond, fun g hg ↦ ?_⟩
  have hgraph := compProd_map_condDistrib (mβ := inferInstance)
    (X := label) (measurable_id.aemeasurable : AEMeasurable (id : M → M) μ)
  calc
    (∫⁻ x, g (label x, x) ∂μ) = ∫⁻ p, g p ∂μ.map (fun x ↦ (label x, x)) :=
      (lintegral_map hg (hlabel.prodMk measurable_id)).symm
    _ = ∫⁻ z, ∫⁻ x, g (z, x) ∂condDistrib id label μ z ∂μ.map label := by
      simp only [id_eq] at hgraph
      rw [← hgraph, Measure.lintegral_compProd hg]
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hcond] with z hz
      rw [← hz.1]
      exact lintegral_withDensity_eq_lintegral_mul _
        (hw.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left)

end OTSelector.Reconstruction
