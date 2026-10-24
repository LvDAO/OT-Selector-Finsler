import OTSelector.Reconstruction.FinslerRelativeLawOriginalRawSeedOptimizer
import OTSelector.Reconstruction.FinslerRelativeLawOriginalAffineRawValue
import OTSelector.Reconstruction.FinslerConcreteUpperClassBinomialShape

/-! The same original-index canonical optimizer has its exact affine shape mean. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal BigOperators Classical unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {q : ℕ}

/-- Artificial strict clock encodings give the same raw finite value whenever
both encode the same literal class mask. -/
theorem unclampedBlockLegalTilted_eq_of_clock_codes
    {A B : Type*} (mask : A → B → Prop)
    (source source' : A → ℝ) (target target' : B → ℝ)
    (hcode : ∀ j k, mask j k ↔ source j < target k)
    (hcode' : ∀ j k, mask j k ↔ source' j < target' k)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (tilt : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) :
    unclampedBlockLegalTilted q source target r kin probe tilt dS dT =
      unclampedBlockLegalTilted q source' target' r kin probe tilt dS dT := by
  unfold unclampedBlockLegalTilted
  congr 1
  ext jk
  simp only [scalarClockLegalGraph, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hcode _ _).symm.trans (hcode' _ _)

/-- Affine restoration also cancels a raw original point reading. -/
theorem mapBlockData_affineHaarCubeCoord_read_restore
    {X A : Type*} (e : V ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) (root : X → V) (mark : X → A)
    (d : BlockData X) :
    mapBlockData (affineMarkedPoint origin side)
      (mapBlockData (fun z ↦ (affineHaarCubeCoord e origin side (root z), mark z)) d) =
      mapBlockData (fun z ↦ (e (root z), mark z)) d := by
  cases d with
  | mk m x =>
    dsimp only [mapBlockData]
    congr 1
    funext j
    exact affineMarkedPoint_affineHaarCubeCoord_restore e origin hside (root (x j), mark (x j))

/-- A literal normalized prefix law identifies the original seed optimizer's
true-coordinate cost and mean, preserving the original indices and mask. -/
theorem PopulationTypedCostData.original_retained_seed_shape_cost_integral
    {X Z A B T : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [MeasurableSpace B] [Nonempty A] [Nonempty B] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {π : Measure (X × X)} [IsFiniteMeasure π] {qAtlas : ℕ} {cost : X → X → ℝ}
    (Cst : PopulationTypedCostData π μ ν T qAtlas cost)
    (ξ : Measure (X × X)) (hξ : ξ ≤ π) (N : ℕ)
    (a : X → Z) (L : Set Z) (hc : MeasurableSet (a ⁻¹' L))
    (root : X → V) (hmroot : Measurable root)
    (e : V ≃L[ℝ] (Fin q → ℝ))
    (markS : X → A) (markT : X → B) (hmS : Measurable markS) (hmT : Measurable markT)
    (mask : A → B → Prop) (source : A → ℝ) (target : B → ℝ)
    (hcode : ∀ j k, mask j k ↔ source j < target k)
    (hs : Measurable source) (ht : Measurable target)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (tilt : ℝ)
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry probe))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (p : unitInterval) (origin : Fin q → ℝ) (side : ℝ≥0) (hside : 0 < side)
    (S : Set (Fin q → ℝ))
    (hlaw : let R := Cst.refineSubplan ξ hξ
      let norm := affineHaarCubeCoord e origin side
      (R.markedLaw N).map (Prod.map
        (fun x ↦ mapBlockData (fun z ↦ (norm (root z.1), markS z.1))
          (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) x))
        (fun y ↦ mapBlockData (fun z ↦ (norm (root z.1), markT z.1))
          (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) y))) =
        (binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S)) :
    let R := Cst.refineSubplan ξ hξ
    let extra := fun (_ : Unit) (cloud : (Fin N → X × Option (Bool × T)) ×
        (Fin N → X × Option (Bool × T))) ↦ Finset.univ.filter (fun jk : Fin N × Fin N ↦
      mask (markS (cloud.1 jk.1).1) (markT (cloud.2 jk.2).1))
    let score := fun (_ : Unit) (cloud : (Fin N → X × Option (Bool × T)) ×
        (Fin N → X × Option (Bool × T))) j k ↦
      (N : ℝ) ^ (2 / (q : ℝ)) * kin (markS (cloud.1 j).1) (markT (cloud.2 k).1)
        (e (root (cloud.2 k).1 - root (cloud.1 j).1)) +
        tilt * probe (markS (cloud.1 j).1) (markT (cloud.2 k).1)
    let value := fun sample ↦ (originalRetainedCellOptimizer a (fun _ : Unit ↦ L)
      extra score () sample).cost (score () sample)
    let F := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target N kin probe tilt
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)
    (Integrable value (R.markedLaw N) ↔
      Integrable F ((binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S))) ∧
      (∫ sample, value sample ∂R.markedLaw N) =
        affineClassBinomialShapeExpectation source target α β N p side origin S kin probe tilt := by
  let R := Cst.refineSubplan ξ hξ
  let norm := affineHaarCubeCoord e origin side
  let obsS := fun x : Fin N → X × Option (Bool × T) ↦
    mapBlockData (fun z ↦ (norm (root z.1), markS z.1))
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) x)
  let obsT := fun y : Fin N → X × Option (Bool × T) ↦
    mapBlockData (fun z ↦ (norm (root z.1), markT z.1))
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) y)
  let obs := Prod.map obsS obsT
  have hobsS : Measurable obsS := (measurable_mapBlockData
    (((measurable_affineHaarCubeCoord e origin side).comp (hmroot.comp measurable_fst)).prodMk
      (hmS.comp measurable_fst))).comp
        (measurable_finiteOriginalRestrictedData (measurableSet_retainedMarkedCellEvent hc))
  have hobsT : Measurable obsT := (measurable_mapBlockData
    (((measurable_affineHaarCubeCoord e origin side).comp (hmroot.comp measurable_fst)).prodMk
      (hmT.comp measurable_fst))).comp
        (measurable_finiteOriginalRestrictedData (measurableSet_retainedMarkedCellEvent hc))
  have hobs : Measurable obs := hobsS.prodMap hobsT
  let F := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
    unclampedBlockLegalTilted q source target N kin probe tilt
      (mapBlockData (affineMarkedPoint origin side) d.1)
      (mapBlockData (affineMarkedPoint origin side) d.2)
  have hF : Measurable F := measurable_unclampedBlockLegalTilted_affine q hs ht N hk hg origin side tilt
  dsimp only at hlaw ⊢
  have heq : (fun sample ↦ (originalRetainedCellOptimizer a (fun _ : Unit ↦ L)
      (fun _ cloud ↦ Finset.univ.filter (fun jk : Fin N × Fin N ↦
        mask (markS (cloud.1 jk.1).1) (markT (cloud.2 jk.2).1)))
      (fun _ cloud j k ↦ (N : ℝ) ^ (2 / (q : ℝ)) *
        kin (markS (cloud.1 j).1) (markT (cloud.2 k).1)
          (e (root (cloud.2 k).1 - root (cloud.1 j).1)) +
        tilt * probe (markS (cloud.1 j).1) (markT (cloud.2 k).1)) () sample).cost
      (fun j k ↦ (N : ℝ) ^ (2 / (q : ℝ)) *
        kin (markS (sample.1 j).1) (markT (sample.2 k).1)
          (e (root (sample.2 k).1 - root (sample.1 j).1)) +
        tilt * probe (markS (sample.1 j).1) (markT (sample.2 k).1))) = F ∘ obs := by
    funext sample
    rcases sample with ⟨x, y⟩
    refine (originalRetainedSeedOptimizer_cost_eq_unclampedBlockLegalTilted a L root e.toLinearMap
      markS markT mask source target hcode N kin probe tilt (x, y)).trans ?_
    dsimp only [Function.comp_apply, F, obs, Prod.map_apply, obsS, obsT]
    rw [mapBlockData_affineHaarCubeCoord_read_restore e origin hside (fun z : X × Option (Bool × T) ↦ root z.1) (fun z ↦ markS z.1),
      mapBlockData_affineHaarCubeCoord_read_restore e origin hside (fun z : X × Option (Bool × T) ↦ root z.1) (fun z ↦ markT z.1)]
    rfl
  rw [heq]
  constructor
  · have h := integrable_map_measure (μ := R.markedLaw N) hF.aestronglyMeasurable hobs.aemeasurable
    rw [hlaw] at h
    exact h.symm
  · have h := integral_map (μ := R.markedLaw N) hobs.aemeasurable hF.aestronglyMeasurable
    rw [hlaw] at h
    exact h.symm

end OTSelector.Reconstruction
