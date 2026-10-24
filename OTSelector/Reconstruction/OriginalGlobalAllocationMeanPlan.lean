import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMeanMarginals
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! The unchanged original target/Dirichlet experiment produces a mean physical
plan with exactly the original source marginal and the actual mean energy. -/
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {M : Type*} [MeasurableSpace M]

/-- The mean of the actual original physical allocation plans. -/
def originalGlobalAllocationMeanPlan (μ ν : Measure M) (n : ℕ)
    (a : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ) :
    Measure (M × M) :=
  ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)).bind
    (physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1))

/-- Every measurable nonnegative physical readout keeps its exact original
sampled allocation expectation in the mean plan. -/
theorem lintegral_originalGlobalAllocationMeanPlan
    (μ ν : Measure M) [IsFiniteMeasure μ] (n : ℕ)
    (a : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (ha : ∀ j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ a z.1 z.2 j))
    (e : M × M → ℝ≥0∞) (he : Measurable e) :
    (∫⁻ p, e p ∂originalGlobalAllocationMeanPlan μ ν n a) =
      ∫⁻ z, ∫⁻ p, e p ∂physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1) z
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) := by
  exact Measure.lintegral_bind
    (measurable_physicalSceneGlobalAllocationFamily μ a ha (fun z ↦ z.1)
      (fun j ↦ (measurable_pi_apply j).comp measurable_fst)).aemeasurable he.aemeasurable

/-- Feasibility on the unchanged experiment gives the original full source
marginal of the mean plan, without a local balance or retained-column input. -/
theorem originalGlobalAllocationMeanPlan_source
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (a : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (ha : ∀ j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ a z.1 z.2 j))
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (a z)) :
    (originalGlobalAllocationMeanPlan μ ν n a).map Prod.fst = μ := by
  ext K hK
  calc
    _ = ∫⁻ p, K.indicator (fun _ ↦ (1 : ℝ≥0∞)) p.1
        ∂originalGlobalAllocationMeanPlan μ ν n a := by
      rw [← lintegral_map (measurable_const.indicator hK) measurable_fst]
      exact (lintegral_indicator_one hK).symm
    _ = _ := lintegral_originalGlobalAllocationMeanPlan μ ν n a ha _
      ((measurable_const.indicator hK).comp measurable_fst)
    _ = ∫⁻ x, K.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂μ :=
      lintegral_physicalSceneGlobalAllocationFamily_source_eq_population
        μ ν n a hfeas _ (measurable_const.indicator hK)
    _ = μ K := lintegral_indicator_one hK

end OTSelector.Reconstruction
