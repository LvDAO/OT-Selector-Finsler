import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTightness
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutLegality
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMarginals

/-!
# Actual allocation scene subsequences

Original allocation feasibility supplies the total mass needed for rooted scene
tightness. The resulting common weak subsequence therefore comes from the same
global allocations, source restrictions, target sample and spatial root.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]

local instance : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Original allocation feasibility fixes the actual global physical mass. -/
theorem lintegral_physicalSceneGlobalAllocationFamily_univ
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure M) [IsFiniteMeasure μ]
    (a : Ω → M → Fin (m + 1) → ℝ) (Y : Ω → Fin (m + 1) → M)
    (p : Ω → Fin (m + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (a w)) :
    (∫⁻ w, physicalSceneGlobalAllocationFamily μ a Y w univ ∂P) = μ univ := by
  calc
    _ = ∫⁻ _, μ univ ∂P := by
      apply lintegral_congr_ae
      filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq P μ a Y p hfeas, hfeas]
        with w heq hw
      rw [heq, ← Measure.fst_univ, physicalSceneAllocationPlan_fst hw (Y w)]
    _ = _ := by simp

/-- The actual original feasible allocations produce their own weak scene
subsequence, retaining all realized source-restricted target columns. -/
theorem exists_tendsto_subseq_actualAllocationRootedSceneLaw
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (m : ℕ → ℕ) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ k, Ω k → M → Fin (m k + 1) → ℝ)
    (hplus : ∀ k j, Measurable (fun z : Ω k × M ↦ aplus k z.1 z.2 j))
    (hminus : ∀ k j, Measurable (fun z : Ω k × M ↦ aminus k z.1 z.2 j))
    (Y : ∀ k, Ω k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (p : ∀ k, Ω k → Fin (m k + 1) → ℝ)
    (hfeasplus : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aplus k w))
    (hfeasminus : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aminus k w))
    (H : ℕ → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ k, 0 < N k)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal (N k)) :
    ∃ Q, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ actualAllocationRootedSceneLaw (P (φ k)) μ
        (aplus (φ k)) (aminus (φ k)) (hplus (φ k)) (hminus (φ k))
        (Y (φ k)) (hY (φ k)) (H (φ k)) (hH (φ k)) (coord (φ k)) (hcoord (φ k))
        u hu (N (φ k)) (hN (φ k)) (D (φ k)) (hD (φ k))) atTop (𝓝 Q) := by
  exact exists_tendsto_subseq_physicalSceneRestrictedRootedLocalSceneLaw P
    (fun k ↦ physicalSceneGlobalAllocationFamily μ (aplus k) (Y k))
    (fun k ↦ physicalSceneGlobalAllocationFamily μ (aminus k) (Y k))
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (aplus k) (hplus k) (Y k) (hY k))
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (aminus k) (hminus k) (Y k) (hY k))
    H hH coord hcoord u hu N hN D hD (μ univ) (measure_ne_top μ univ)
    (fun k ↦ (lintegral_physicalSceneGlobalAllocationFamily_univ (P k) μ
      (aplus k) (Y k) (p k) (hfeasplus k)).le)
    (fun k ↦ (lintegral_physicalSceneGlobalAllocationFamily_univ (P k) μ
      (aminus k) (Y k) (p k) (hfeasminus k)).le)

end OTSelector.Reconstruction
