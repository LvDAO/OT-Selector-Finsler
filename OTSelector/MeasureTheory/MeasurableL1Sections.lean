import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
## Lemma skeleton

* **Conditions:** A jointly measurable function with integrable sections, or a measurable nonnegative density.
* **Objects:** A Borel map into L1 with zero extension off the finite-integral labels.
* **Proof detail:** Show distances to L1 points are measurable section integrals; paste on the measurable finite-integral set.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Section 253, especially Exercises 253Y(f)–(i), L1-valued sections and Bochner integrability.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=47
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
  https://measure.axler.net/MIRA.pdf
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106

**Relationship to the sources:** Fremlin 253Y(g) treats Bochner-integrable section maps under product integrability; this file proves the more local every-section/measurable-parameter version directly.
-/

/-!
# Measurable L¹ sections

Jointly measurable real functions with integrable sections define Borel measurable L¹ maps.
For a nonnegative density, the same construction uses its finite-integral label set and extends
by zero elsewhere; no integrability assumption is imposed on the exceptional labels.
-/

open Set MeasureTheory Filter TopologicalSpace Metric
open scoped ENNReal Topology

noncomputable section

namespace OTSelector.Reconstruction

/-- Joint measurability and integrability of every real section give a Borel L¹ section map. -/
theorem measurable_toL1_sections
    {Z : Type*} [MeasurableSpace Z] {f : Z × ℝ → ℝ} (hf : Measurable f)
    (hfi : ∀ z, Integrable (fun s ↦ f (z, s)) volume) :
    @Measurable Z (Lp ℝ 1 (volume : Measure ℝ)) _ (borel _)
      (fun z ↦ (hfi z).toL1 (fun s ↦ f (z, s))) := by
  let Y : Type := Lp ℝ 1 (volume : Measure ℝ)
  let S : Z → Y := fun z ↦ (hfi z).toL1 (fun s ↦ f (z, s))
  have hd (g : Y) : Measurable (fun z ↦ edist (S z) g) := by
    have hm : Measurable (fun z ↦ ∫⁻ s, edist (f (z, s)) (g s) ∂volume) :=
      (hf.edist ((L1.measurable_coeFn g).comp measurable_snd)).lintegral_prod_right'
    convert hm using 1
    funext z
    rw [L1.edist_def]
    apply lintegral_congr_ae
    filter_upwards [(hfi z).coeFn_toL1] with s hs
    exact congrArg (fun v ↦ edist v (g s)) hs
  have hb : IsTopologicalBasis (range (fun p : Y × ℝ≥0∞ ↦ eball p.1 p.2)) := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨⟨g, r⟩, rfl⟩
      exact isOpen_eball
    · intro g U hg hU
      obtain ⟨r, hr, hsub⟩ := EMetric.isOpen_iff.mp hU g hg
      exact ⟨eball g r, ⟨(g, r), rfl⟩, mem_eball_self hr, hsub⟩
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  rw [hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro _ ⟨⟨g, r⟩, rfl⟩
  exact measurableSet_lt (hd g) measurable_const

/-- A nonnegative measurable density has measurable L¹ sections on its finite-integral labels,
with the section map set to zero at all other labels. -/
theorem exists_measurable_L1_sections
    {Z : Type*} [MeasurableSpace Z] {H : Z × ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∃ S : Z → Lp ℝ 1 (volume : Measure ℝ),
      @Measurable Z (Lp ℝ 1 (volume : Measure ℝ)) _ (borel _) S ∧
      (∀ z, (∫⁻ s, H (z, s)) ≠ ∞ →
        (⇑(S z)) =ᵐ[volume] (fun s ↦ (H (z, s)).toReal)) ∧
      (∀ z, (∫⁻ s, H (z, s)) = ∞ → S z = 0) := by
  classical
  let Y : Type := Lp ℝ 1 (volume : Measure ℝ)
  let : MeasurableSpace Y := borel Y
  let B : Set Z := {z | (∫⁻ s, H (z, s)) ≠ ∞}
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun hH.lintegral_prod_right' measurable_const).compl
  let f : B × ℝ → ℝ := fun p ↦ (H (p.1.val, p.2)).toReal
  have hf : Measurable f :=
    (hH.comp ((measurable_subtype_coe.comp measurable_fst).prodMk
      measurable_snd)).ennreal_toReal
  have hfi (z : B) : Integrable (fun s ↦ f (z, s)) volume := by
    have hz : Measurable (fun s : ℝ ↦ H (z.val, s)) :=
      hH.comp (measurable_const.prodMk measurable_id)
    exact integrable_toReal_of_lintegral_ne_top hz.aemeasurable z.property
  let T : B → Y := fun z ↦ (hfi z).toL1 (fun s ↦ f (z, s))
  have hT : Measurable T := measurable_toL1_sections hf hfi
  let S : Z → Y := Function.extend ((↑) : B → Z) T (fun _ ↦ 0)
  refine ⟨S, (MeasurableEmbedding.subtype_coe hB).measurable_extend hT measurable_const,
    ?_, ?_⟩
  · intro z hz
    have heq : S z = T ⟨z, hz⟩ :=
      Subtype.val_injective.extend_apply T (fun _ ↦ 0) ⟨z, hz⟩
    rw [heq]
    exact (hfi ⟨z, hz⟩).coeFn_toL1
  · intro z hz
    apply Function.extend_apply'
    rintro ⟨w, rfl⟩
    exact w.property hz

end OTSelector.Reconstruction
