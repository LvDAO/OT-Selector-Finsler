import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic
import OTSelector.Transport.Coupling.LabelDisintegration

/-!
Conditions: An original probability coupling on a standard-Borel point space, measurable common-label/scalar-clock readouts and an a.e. lower bound on the original clock gap.

Objects: An actual Markov pair-clock conditional kernel with the original conditional marginals and the same a.e. gap, over the unchanged common label law.

Proof detail: Push the original pair to label and two clocks, disintegrate that joint law and use uniqueness to identify both original conditional marginals; transfer the full-measure gap through the same composition product.

References: D. H. Fremlin: 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary; D. H. Fremlin: 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.
Relation: A conditional coupling constructed from the unchanged original joint law. The gap is inherited from that law, and no new independent scalar pair is substituted.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalClockClassCoupling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalClockClassCoupling`; the selected original proof blocks follow. -/
section

/-!
An unchanged original common-label population coupling constructs an actual conditional scalar-clock pair kernel with the original conditional marginals.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The actual original common-label population coupling constructs a Markov
clock-pair kernel with both literal original conditional clock marginals. -/
theorem exists_original_clockPair_kernel
    {M Z : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace Z]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (M × M)) (hπ : Vlasov.IsCoupling π μ ν)
    (a : M → Z) (u : M → ℝ) (ha : Measurable a) (hu : Measurable u)
    (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2)
    (δ : ℝ) (hgap : ∀ᵐ p ∂π, δ ≤ u p.2 - u p.1) :
    ∃ γ : Kernel Z (ℝ × ℝ), IsMarkovKernel γ ∧
      μ.map a = ν.map a ∧
      (μ.map a ⊗ₘ condDistrib u a μ = μ.map (fun x ↦ (a x, u x))) ∧
      (μ.map a ⊗ₘ condDistrib u a ν = ν.map (fun y ↦ (a y, u y))) ∧
      ∀ᵐ z ∂μ.map a,
        Vlasov.IsCoupling (γ z) (condDistrib u a μ z) (condDistrib u a ν z) ∧
        ∀ᵐ p ∂γ z, δ ≤ p.2 - p.1 := by
  let _instMapProbability : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.symm ▸ inferInstance
  let _instPlanProbability : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  obtain ⟨hbalance, κ, hκ, _, _, hsupp⟩ := exists_coupling_disintegration_of_common_label
    hπ ha ha hlabel hgap
  let _instConditionalMarkov : IsMarkovKernel κ := hκ
  let clockPair : M × M → ℝ × ℝ := Prod.map u u
  have hclock : Measurable clockPair := hu.prodMap hu
  let γ := κ.map clockPair
  have hγ : IsMarkovKernel γ := Kernel.IsMarkovKernel.map κ hclock
  have hleft : condDistrib u a μ =ᵐ[μ.map a] (condDistrib id a μ).map u := by
    simpa only [Function.comp_id] using condDistrib_comp a
      (measurable_id.aemeasurable : AEMeasurable (id : M → M) μ) hu
  have hright : condDistrib u a ν =ᵐ[μ.map a] (condDistrib id a ν).map u := by
    rw [hbalance]
    simpa only [Function.comp_id] using condDistrib_comp a
      (measurable_id.aemeasurable : AEMeasurable (id : M → M) ν) hu
  refine ⟨γ, hγ, hbalance, compProd_map_condDistrib hu.aemeasurable, ?_, ?_⟩
  · rw [hbalance]
    exact compProd_map_condDistrib hu.aemeasurable
  · filter_upwards [hsupp, hleft, hright] with z hz hl hr
    constructor
    · have h := hz.1.map u u hu hu
      rw [← Kernel.map_apply _ hu, ← hl, ← Kernel.map_apply _ hu, ← hr] at h
      exact (Kernel.map_apply κ hclock z).symm ▸ h
    · rw [show γ z = (κ z).map clockPair from Kernel.map_apply κ hclock z]
      have hGapMeas : MeasurableSet {p : ℝ × ℝ | δ ≤ p.2 - p.1} :=
        measurableSet_le measurable_const
          (measurable_sub.comp (measurable_snd.prodMk measurable_fst))
      apply (ae_map_iff hclock.aemeasurable hGapMeas).mpr
      exact hz.2

end OTSelector.Reconstruction

end
end
