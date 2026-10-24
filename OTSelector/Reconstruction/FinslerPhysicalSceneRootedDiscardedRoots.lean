import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMeanMarginals
import OTSelector.Reconstruction.FinslerPopulationLocalPressureCore

/-!
# Original discarded-root mass in the actual global allocation scene

The exact original mean target marginal and the produced population core's
remainder mass give a Haar-window bound by window volume times the actual core
loss. The global allocation is restricted only by the stated target and source
sets; it is never assumed to stay inside the retained core.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry Filter
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- The discarded roots of the actual original population core have small
Haar-window intensity under the same global optimizer and original experiment. -/
theorem rooted_original_discarded_roots_expected_le
    [IsProbabilityMeasure η₁]
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (n : ℕ)
    (A : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ η₁)).prod
      (OTSelector.Probability.dirichletOne n)),
      OTSelector.Probability.IsSemidiscreteAllocation η₀ z.2 (A z))
    {ι : Type*} [Fintype ι]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (clock : M → ℝ) (hclock : Measurable clock) (N : ℝ) (hN : 0 < N)
    (rootDomain U : Set (ι → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    (H : Set M) :
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily η₀ A (fun z ↦ z.1) w).restrict
        ((univ ×ˢ (a ⁻¹' D.haar.continuous.population.rootsᶜ)) ∩ (H ×ˢ univ)))
      coord clock N z {e | e.1.1 ∈ U}
      ∂OTSelector.Probability.cavityRootMeasure volume rootDomain N
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ η₁)).prod
        (OTSelector.Probability.dirichletOne n))) ≤ volume U * loss := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  have hK : MeasurableSet (a ⁻¹' D.haar.continuous.population.rootsᶜ) :=
    (D.haar.continuous.population.compact.measurableSet.compl).preimage ha
  exact (lintegral_physicalSceneGlobalAllocationFamily_rooted_discarded_target_le
    η₀ η₁ n A hfeas coord hcoord clock hclock N hN rootDomain U hU hUf H hK).trans
      (mul_le_mul_right D.haar.continuous.population.remainder_mass.2.2.2.le _)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
