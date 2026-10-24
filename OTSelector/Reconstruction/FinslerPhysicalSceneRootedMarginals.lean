import OTSelector.Reconstruction.FinslerPhysicalSceneClockEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedClock
import OTSelector.Probability.SemidiscreteTargetCloud

/-!
# Exact marginals of the same source-restricted rooted allocation

The original allocation is restricted only in its source.  Its rooted source
marginal is the original restricted physical source law in the actual spatial
and clock coordinates.  Its target marginal retains the original physical
target cloud with its realized restricted column masses.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option linter.unusedSectionVars false

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

/-- Actual unnormalized target columns of the same source-restricted allocation. -/
def physicalSceneCellMass (μ : Measure M) (H : Set M)
    (a : M → Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  ∫ x, a x j ∂μ.restrict H

/-- Source restriction is feasible for its actual unnormalized target columns. -/
theorem semidiscreteAllocation_source_restrict
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (H : Set M) :
    IsSemidiscreteAllocation (μ.restrict H) (physicalSceneCellMass μ H a) a :=
  ⟨fun j ↦ (ha.integrable j).restrict, ae_restrict_of_ae ha.nonneg,
    ae_restrict_of_ae ha.sum_one, fun _ ↦ rfl⟩

/-- The physical observation preserves the entire source marginal. -/
theorem physicalSceneAllocationPlan_fst
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (Y : Fin (n + 1) → M) :
    (physicalSceneAllocationPlan μ a Y).fst = μ := by
  have hm : Measurable (Prod.map (id : M → M) Y) :=
    measurable_id.prodMap (measurable_of_finite Y)
  unfold physicalSceneAllocationPlan Measure.fst
  rw [Measure.map_map measurable_fst hm]
  exact ha.isCoupling.1

/-- The physical target atoms retain their actual allocation column masses. -/
theorem physicalSceneAllocationPlan_snd
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (Y : Fin (n + 1) → M) :
    (physicalSceneAllocationPlan μ a Y).snd = (semidiscreteLabelMeasure p).map Y := by
  have hm : Measurable (Prod.map (id : M → M) Y) :=
    measurable_id.prodMap (measurable_of_finite Y)
  unfold physicalSceneAllocationPlan Measure.snd
  rw [Measure.map_map measurable_snd hm]
  change (semidiscreteAllocationMeasure μ a).map (Y ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_of_finite Y) measurable_snd, ha.isCoupling.2]

section Root

variable {ι : Type*} [Fintype ι]

/-- Both actual rooted marginals are the corresponding original physical
marginals observed in precisely the same spatial and clock coordinates. -/
theorem physicalSceneRootedPlan_marginals
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ) :
    let endpoint := fun x : M ↦ (coord x - z, u x)
    (physicalSceneRootedPlan Γ coord u N z).fst = ENNReal.ofReal N • Γ.fst.map endpoint ∧
      (physicalSceneRootedPlan Γ coord u N z).snd = ENNReal.ofReal N • Γ.snd.map endpoint := by
  have hm := measurable_physicalSceneRootedObservation coord hcoord u hu z
  have he : Measurable (fun x : M ↦ (coord x - z, u x)) :=
    (hcoord.sub measurable_const).prodMk hu
  constructor
  · unfold physicalSceneRootedPlan Measure.fst
    rw [Measure.map_smul, Measure.map_map measurable_fst hm, Measure.map_map he measurable_fst]
    rfl
  · unfold physicalSceneRootedPlan Measure.snd
    rw [Measure.map_smul, Measure.map_map measurable_snd hm, Measure.map_map he measurable_snd]
    rfl

/-- The same globally allocated target cloud and the actual random restricted
columns are the exact target marginal of the rooted physical cell plan. -/
theorem physicalSceneRootedPlan_source_restrict_marginals
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (Y : Fin (n + 1) → M)
    (H : Set M) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ) :
    let endpoint := fun x : M ↦ (coord x - z, u x)
    let rooted := physicalSceneRootedPlan (physicalSceneAllocationPlan (μ.restrict H) a Y)
      coord u N z
    rooted.fst = ENNReal.ofReal N • (μ.restrict H).map endpoint ∧
      rooted.snd = semidiscreteTargetCloud (physicalSceneCellMass μ H a)
        (fun j ↦ endpoint (Y j)) N := by
  have hlocal := semidiscreteAllocation_source_restrict ha H
  have hm := physicalSceneRootedPlan_marginals
    (physicalSceneAllocationPlan (μ.restrict H) a Y) coord hcoord u hu N z
  constructor
  · simpa only [physicalSceneAllocationPlan_fst hlocal Y] using hm.1
  · rw [physicalSceneAllocationPlan_snd hlocal Y] at hm
    have he : Measurable (fun x : M ↦ (coord x - z, u x)) :=
      (hcoord.sub measurable_const).prodMk hu
    change _ = ENNReal.ofReal N • (semidiscreteLabelMeasure _).map _
    rw [hm.2, Measure.map_map he (measurable_of_finite Y)]
    rfl

end Root
end OTSelector.Reconstruction
