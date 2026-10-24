import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Geometry.Manifold.ChartOccupationAbsoluteContinuity

## Lemma skeleton

* **Conditions:** A continuous joint map on a measurable time×input rectangle and arbitrary original measures; every section law is absolutely continuous in every specified output chart.

* **Objects:** An a.e.-measurable occupation map and chart absolute continuity of its actual product-pushforward law.

* **Proof detail:** Concentrate the product measure on the legal rectangle. Express chart-null preimages as measurable relative preimages, use the section-wise domination to make each section null, and apply the product-null implication before pushing forward.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=2): Sections 251A–251I, pp. 2–6: rectangular covers, product outer measures and the product-measure rectangle formula.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=24): Corollary 252F, p. 24.
- [John M. Lee, Introduction to Smooth Manifolds, second edition (2013)](https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10): Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.

Source relation (generalization): A one-direction measurable-section null-set transfer, formalized without finiteness/s-finiteness assumptions. It is not mislabeled as an unrestricted equality form of Fubini’s theorem.
-/

/-!
# Chart absolute continuity of actual occupation laws

A continuous joint map on a measurable time-domain rectangle defines its actual
occupation law for arbitrary original measures. If every section law is absolutely
continuous in every output chart, so is this occupation law. Relative measurable
preimages and product concentration suffice; no global measurable extension or
finite-measure hypothesis is required.
-/

open Set Filter Metric Manifold MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal ENNReal

namespace OTSelector.Geometry

private theorem measurableSet_relative_preimage
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {D : Set α} (hD : MeasurableSet D) {f : α → β} (hf : ContinuousOn f D)
    {N : Set β} (hN : MeasurableSet N) : MeasurableSet (D ∩ f ⁻¹' N) := by
  have hsub : Measurable (fun x : D ↦ f x) :=
    (continuousOn_iff_continuous_domRestrict.mp hf).measurable
  have heq : D ∩ f ⁻¹' N = ((↑) : D → α) '' {x : D | f x ∈ N} := by
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨x, hx⟩, hfx, rfl⟩
    · rintro ⟨⟨y, hy⟩, hfy, rfl⟩
      exact ⟨hy, hfy⟩
  rw [heq]
  exact hD.subtype_image (hsub hN)

variable {X E M : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M]

/-- Actual averaging on a measurable time-domain rectangle preserves chart absolute
continuity of all section laws, without finite or s-finite measure assumptions. -/
theorem chartAC_occupation_of_continuousOn
    (m : Measure E) (κ : Measure ℝ) (η : Measure X)
    {I : Set ℝ} {K : Set X} (hI : MeasurableSet I) (hK : MeasurableSet K)
    {T : ℝ × X → M} (hT : ContinuousOn T (I ×ˢ K))
    (hsection : ∀ t ∈ I, ∀ terminal : M,
      (((η.restrict K).map (fun x ↦ T (t, x))).restrict
        (extChartAt 𝓘(ℝ, E) terminal).source).map
        (extChartAt 𝓘(ℝ, E) terminal) ≪ m) :
    let θ := (κ.restrict I).prod (η.restrict K)
    AEMeasurable T θ ∧
      ∀ terminal : M,
        ((θ.map T).restrict (extChartAt 𝓘(ℝ, E) terminal).source).map
          (extChartAt 𝓘(ℝ, E) terminal) ≪ m := by
  let θ := (κ.restrict I).prod (η.restrict K)
  let R := I ×ˢ K
  have hRmeas : MeasurableSet R := hI.prod hK
  have ht : ∀ᵐ q ∂θ, q.1 ∈ I :=
    (Measure.quasiMeasurePreserving_fst (μ := κ.restrict I) (ν := η.restrict K)).ae
      (ae_restrict_mem hI)
  have hx : ∀ᵐ q ∂θ, q.2 ∈ K :=
    (Measure.quasiMeasurePreserving_snd (μ := κ.restrict I) (ν := η.restrict K)).ae
      (ae_restrict_mem hK)
  have hR : ∀ᵐ q ∂θ, q ∈ R := ht.and hx
  have hrestrict : θ.restrict R = θ := Measure.restrict_eq_self_of_ae_mem hR
  have hTae : AEMeasurable T θ := by
    rw [← hrestrict]
    exact hT.aemeasurable hRmeas
  refine ⟨hTae, ?_⟩
  intro terminal
  let ψ := extChartAt 𝓘(ℝ, E) terminal
  have hψsource : MeasurableSet ψ.source :=
    (isOpen_extChartAt_source terminal).measurableSet
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hzero
  let B := ψ.source ∩ ψ ⁻¹' N
  have hB : MeasurableSet B :=
    measurableSet_relative_preimage hψsource (continuousOn_extChartAt terminal) hN
  let S := R ∩ T ⁻¹' B
  have hS : MeasurableSet S := measurableSet_relative_preimage hRmeas hT hB
  have hsections : ∀ t ∈ I, (η.restrict K) (Prod.mk t ⁻¹' S) = 0 := by
    intro t htI
    let f : X → M := fun x ↦ T (t, x)
    let ν := (η.restrict K).map f
    have hf : AEMeasurable f (η.restrict K) :=
      (hT.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hxK ↦ ⟨htI, hxK⟩)).aemeasurable hK
    have hψ : AEMeasurable ψ (ν.restrict ψ.source) :=
      (continuousOn_extChartAt terminal).aemeasurable hψsource
    have hνB : ν B = 0 := by
      have hz : ((ν.restrict ψ.source).map ψ) N = 0 := hsection t htI terminal hzero
      rw [Measure.map_apply_of_aemeasurable hψ hN,
        Measure.restrict_apply' hψsource] at hz
      simpa only [B, inter_comm] using hz
    have hpre : (η.restrict K) (f ⁻¹' B) = 0 :=
      Measure.preimage_null_of_map_null hf hνB
    exact measure_mono_null (fun _ hxS ↦ hxS.2) hpre
  have hSzero : θ S = 0 := Measure.measure_prod_null_of_ae_null hS
    ((ae_restrict_mem hI).mono fun t htI ↦ hsections t htI)
  have hprezero : θ (T ⁻¹' B) = 0 := by
    have h : θ (T ⁻¹' B ∩ R) = θ (T ⁻¹' B) :=
      measure_inter_conull (t := R) (mem_ae_iff.mp hR)
    apply h.symm.trans
    simpa only [S, inter_comm] using hSzero
  have hΩB : (θ.map T) B = 0 := by
    rw [Measure.map_apply_of_aemeasurable hTae hB]
    exact hprezero
  have hψ : AEMeasurable ψ ((θ.map T).restrict ψ.source) :=
    (continuousOn_extChartAt terminal).aemeasurable hψsource
  rw [Measure.map_apply_of_aemeasurable hψ hN, Measure.restrict_apply' hψsource]
  simpa only [B, inter_comm] using hΩB

end OTSelector.Geometry
