import Mathlib.Probability.Kernel.CondDistrib
import OTSelector.Probability.LabelDependentKernel
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationCoreRecovery.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationCoreRecovery`; the selected original proof blocks follow. -/
section

/-!
# Probability.ConditionalLabelCoreRecovery

## Lemma skeleton

* **Conditions:** Finite original laws with a measurable label-clock inverse and, for the two-color package, one common label marginal.
* **Objects:** Exact reconstruction on every measurable label core, unchanged conditional kernel on that core and complementary population recovery.
* **Proof detail:** Commute the label restriction with composition product, use conditional-distribution reconstruction and the inverse, identify restricted kernels by uniqueness and add the core/complement restrictions.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Restriction/disintegration assembly; the measurable inverse and common label marginal remain explicit.
-/

/-!
# Exact physical recovery after restricting the common label core

The original scalar conditional kernels and the same measurable inverse recover
each physical population on every measurable label core. Both restricted colors
retain the same restricted label marginal and mass, and the complementary pieces
recover the original populations exactly.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- Restricting the base labels restricts exactly the first coordinate of the joint law. -/
theorem restrict_label_compProd {X : Type*} [MeasurableSpace X]
    (lambda : Measure Z) [SFinite lambda] (k : Kernel Z X) [IsSFiniteKernel k]
    {K : Set Z} (hK : MeasurableSet K) :
    lambda.restrict K ⊗ₘ k = (lambda ⊗ₘ k).restrict (K ×ˢ univ) := by
  unfold Measure.compProd
  rw [← Kernel.restrict_const hK, Kernel.compProd_restrict_left hK, Kernel.restrict_apply]

/-- The original conditional clock and original inverse recover the physical restriction
on every measurable label core, without changing any conditional distribution. -/
theorem reconstruct_original_clock_on_label_set (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} {b : Z × ℝ → M}
    (ha : Measurable a) (hu : Measurable u) (hb : Measurable b)
    (hinv : ∀ᵐ x ∂η, b (a x, u x) = x) {K : Set Z} (hK : MeasurableSet K) :
    mapWithLabel (condDistrib u a η) b ∘ₘ (η.map a).restrict K = η.restrict (a ⁻¹' K) := by
  rw [mapWithLabel_comp _ _ hb, restrict_label_compProd _ _ hK,
    compProd_map_condDistrib hu.aemeasurable,
    Measure.restrict_map (ha.prodMk hu) (hK.prod MeasurableSet.univ)]
  have hpre : (fun x ↦ (a x, u x)) ⁻¹' (K ×ˢ univ) = a ⁻¹' K := by
    ext x
    simp only [mem_preimage, mem_prod, mem_univ, and_true]
  rw [hpre, Measure.map_map hb (ha.prodMk hu)]
  calc
    _ = (η.restrict (a ⁻¹' K)).map id :=
      Measure.map_congr (ae_restrict_of_ae hinv)
    _ = _ := Measure.map_id

/-- Core and complement recover the complete original physical population exactly. -/
theorem reconstruct_original_clock_core_complement (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} {b : Z × ℝ → M}
    (ha : Measurable a) (hu : Measurable u) (hb : Measurable b)
    (hinv : ∀ᵐ x ∂η, b (a x, u x) = x) {K : Set Z} (hK : MeasurableSet K) :
    mapWithLabel (condDistrib u a η) b ∘ₘ (η.map a).restrict K +
      mapWithLabel (condDistrib u a η) b ∘ₘ (η.map a).restrict Kᶜ = η := by
  rw [reconstruct_original_clock_on_label_set η ha hu hb hinv hK,
    reconstruct_original_clock_on_label_set η ha hu hb hinv hK.compl,
    preimage_compl, Measure.restrict_add_restrict_compl (ha hK)]

/-- Restricting physical points by their original labels gives exactly the original
conditional clock kernel over the restricted original label measure. -/
theorem original_label_clock_restrict_eq_compProd (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    {K : Set Z} (hK : MeasurableSet K) :
    (η.restrict (a ⁻¹' K)).map (fun x ↦ (a x, u x)) =
      (η.map a).restrict K ⊗ₘ condDistrib u a η := by
  rw [restrict_label_compProd _ _ hK, compProd_map_condDistrib hu.aemeasurable,
    Measure.restrict_map (ha.prodMk hu) (hK.prod MeasurableSet.univ)]
  congr 2
  ext x
  simp only [mem_preimage, mem_prod, mem_univ, and_true]

/-- Restricting only the common label variable retains the original conditional clock
law almost everywhere on that core. -/
theorem condDistrib_restrict_label_eq (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    {K : Set Z} (hK : MeasurableSet K) :
    condDistrib u a (η.restrict (a ⁻¹' K)) =ᵐ[(η.map a).restrict K] condDistrib u a η := by
  have hm : (η.restrict (a ⁻¹' K)).map a = (η.map a).restrict K :=
    (Measure.restrict_map ha hK).symm
  have hjoint := original_label_clock_restrict_eq_compProd η ha hu hK
  rw [← hm] at hjoint
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable ha hu hjoint
  rwa [hm] at h

/-- Every measurable common label core preserves exact recovery, balance and mass
for both original physical populations. -/
def PopulationLabelCoreRecoveryLaw (u : M → ℝ) (a : M → Z) (b : Z × ℝ → M)
    (lambda : Measure Z) (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] : Prop :=
  ∀ K : Set Z, MeasurableSet K →
    (η₀.restrict (a ⁻¹' K)).map a = lambda.restrict K ∧
    (η₁.restrict (a ⁻¹' K)).map a = lambda.restrict K ∧
    mapWithLabel (condDistrib u a η₀) b ∘ₘ lambda.restrict K = η₀.restrict (a ⁻¹' K) ∧
    mapWithLabel (condDistrib u a η₁) b ∘ₘ lambda.restrict K = η₁.restrict (a ⁻¹' K) ∧
    η₀ (a ⁻¹' K) = lambda K ∧ η₁ (a ⁻¹' K) = lambda K ∧
    mapWithLabel (condDistrib u a η₀) b ∘ₘ lambda.restrict K +
      mapWithLabel (condDistrib u a η₀) b ∘ₘ lambda.restrict Kᶜ = η₀ ∧
    mapWithLabel (condDistrib u a η₁) b ∘ₘ lambda.restrict K +
      mapWithLabel (condDistrib u a η₁) b ∘ₘ lambda.restrict Kᶜ = η₁ ∧
    (condDistrib u a (η₀.restrict (a ⁻¹' K)) =ᵐ[lambda.restrict K] condDistrib u a η₀) ∧
    (condDistrib u a (η₁.restrict (a ⁻¹' K)) =ᵐ[lambda.restrict K] condDistrib u a η₁)

/-- The already constructed common label marginal and inverse produce the complete
core-restriction and recovery interface for the original two colors. -/
theorem populationLabelCoreRecoveryLaw_of_inverse (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {a : M → Z} {u : M → ℝ} {b : Z × ℝ → M} {lambda : Measure Z}
    (ha : Measurable a) (hu : Measurable u) (hb : Measurable b)
    (hlabel₀ : η₀.map a = lambda) (hlabel₁ : η₁.map a = lambda)
    (hinv₀ : ∀ᵐ x ∂η₀, b (a x, u x) = x)
    (hinv₁ : ∀ᵐ x ∂η₁, b (a x, u x) = x) :
    PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁ := by
  intro K hK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Measure.restrict_map ha hK, hlabel₀]
  · rw [← Measure.restrict_map ha hK, hlabel₁]
  · rw [← hlabel₀]
    exact reconstruct_original_clock_on_label_set η₀ ha hu hb hinv₀ hK
  · rw [← hlabel₁]
    exact reconstruct_original_clock_on_label_set η₁ ha hu hb hinv₁ hK
  · rw [← hlabel₀, Measure.map_apply ha hK]
  · rw [← hlabel₁, Measure.map_apply ha hK]
  · rw [← hlabel₀]
    exact reconstruct_original_clock_core_complement η₀ ha hu hb hinv₀ hK
  · rw [← hlabel₁]
    exact reconstruct_original_clock_core_complement η₁ ha hu hb hinv₁ hK
  · rw [← hlabel₀]
    exact condDistrib_restrict_label_eq η₀ ha hu hK
  · rw [← hlabel₁]
    exact condDistrib_restrict_label_eq η₁ ha hu hK

end OTSelector.Reconstruction

end
end
