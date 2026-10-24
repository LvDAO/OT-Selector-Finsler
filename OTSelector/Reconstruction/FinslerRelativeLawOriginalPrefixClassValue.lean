import OTSelector.Reconstruction.FinslerRelativeLawOriginalPrefixOptimizer
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonBlock

/-! The original retained ambient class value and source defect are literally
the existing legal finite-block value and deficiency of the ordered prefix.
Class families may vary from one original coefficient cell to another. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Read the fixed scalar class legality from the unchanged original endpoints.
The class types are permitted to depend on the original cell. -/
def originalCellScalarClassGraph
    {X C T : Type*} {A B : C → Type*} {q N : ℕ}
    (readS : ∀ c, X → (Fin q → ℝ) × A c) (readT : ∀ c, X → (Fin q → ℝ) × B c)
    (source : ∀ c, A c → ℝ) (target : ∀ c, B c → ℝ) (c : C)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    Finset (Fin N × Fin N) :=
  scalarClockLegalGraph (fun i ↦ source c (readS c (sample.1 i).1).2)
    (fun j ↦ target c (readT c (sample.2 j).1).2)

/-- The literal frozen class kinetic/probe score on original endpoint indices. -/
def originalCellScalarClassScore
    {X C T : Type*} {A B : C → Type*} {q N : ℕ}
    (readS : ∀ c, X → (Fin q → ℝ) × A c) (readT : ∀ c, X → (Fin q → ℝ) × B c)
    (r : C → ℝ) (kin : ∀ c, A c → B c → (Fin q → ℝ) → ℝ)
    (probe : ∀ c, A c → B c → ℝ) (tilt : ℝ) (c : C)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T)))
    (i j : Fin N) : ℝ :=
  r c ^ (2 / (q : ℝ)) * kin c (readS c (sample.1 i).1).2 (readT c (sample.2 j).1).2
    (mDisplacement (readS c (sample.1 i).1).1 (readT c (sample.2 j).1).1) +
      tilt * probe c (readS c (sample.1 i).1).2 (readT c (sample.2 j).1).2

/-- The ambient retained graph's signed frozen value equals the actual
existing legal finite-block functional on its original ordered observations. -/
theorem originalRetainedCellGraph_value_eq_blockLegalTilted
    {X Z C T : Type*} {A B : C → Type*} {q N : ℕ}
    (a : X → Z) (cell : C → Set Z)
    (readS : ∀ c, X → (Fin q → ℝ) × A c) (readT : ∀ c, X → (Fin q → ℝ) × B c)
    (source : ∀ c, A c → ℝ) (target : ∀ c, B c → ℝ)
    (r : C → ℝ) (kin : ∀ c, A c → B c → (Fin q → ℝ) → ℝ)
    (probe : ∀ c, A c → B c → ℝ) (tilt : ℝ) (c : C)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    let extra := originalCellScalarClassGraph readS readT source target
    let model := originalCellScalarClassScore readS readT r kin probe tilt
    let dataS := mapBlockData (fun p ↦ readS c p.1)
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1)
    let dataT := mapBlockData (fun p ↦ readT c p.1)
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.2)
    PartialMatching.legalMaximumValue (originalRetainedCellGraph a cell extra c sample) (model c sample) =
      blockLegalTilted q (source c) (target c) (r c) (kin c) (probe c) tilt dataS dataT := by
  have h := originalRetainedCellGraph_value_eq_prefix a cell
    (originalCellScalarClassGraph readS readT source target)
    (originalCellScalarClassScore readS readT r kin probe tilt) c sample
  dsimp only at h ⊢
  rw [originalCellScalarClassGraph, PartialMatching.inducedLegalGraph_scalarClockLegalGraph] at h
  simpa only [blockLegalTilted, mapBlockData, finiteOriginalRestrictedData_point,
    originalCellScalarClassScore, Function.comp_def] using h

/-- The canonical ambient optimizer realizes the exact existing finite-block
value of those same original retained observations, including ties. -/
theorem originalRetainedCellOptimizer_model_cost_eq_blockLegalTilted
    {X Z C T : Type*} {A B : C → Type*} {q N : ℕ}
    (a : X → Z) (cell : C → Set Z)
    (readS : ∀ c, X → (Fin q → ℝ) × A c) (readT : ∀ c, X → (Fin q → ℝ) × B c)
    (source : ∀ c, A c → ℝ) (target : ∀ c, B c → ℝ)
    (r : C → ℝ) (kin : ∀ c, A c → B c → (Fin q → ℝ) → ℝ)
    (probe : ∀ c, A c → B c → ℝ) (tilt : ℝ) (c : C)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    let extra := originalCellScalarClassGraph readS readT source target
    let model := originalCellScalarClassScore readS readT r kin probe tilt
    let dataS := mapBlockData (fun p ↦ readS c p.1)
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1)
    let dataT := mapBlockData (fun p ↦ readT c p.1)
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.2)
    (originalRetainedCellOptimizer a cell extra model c sample).cost (model c sample) =
      blockLegalTilted q (source c) (target c) (r c) (kin c) (probe c) tilt dataS dataT := by
  exact (originalRetainedCellOptimizer_isLegalOptimal a cell _ _ c sample).2.2.trans
    (originalRetainedCellGraph_value_eq_blockLegalTilted a cell readS readT source target r kin probe tilt c sample)

/-- The same original marked experiment's real source-defect term is exactly
the existing legal finite-block source deficiency of its ordered retained data. -/
theorem PopulationTypedCostData.original_retained_cell_defect_eq_blockLegalSourceDefect_ae
    {X Z C T : Type*} [MeasurableSpace X] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {π : Measure (X × X)} [IsFiniteMeasure π] {qAtlas : ℕ} {cost : X → X → ℝ}
    (D : PopulationTypedCostData π μ ν T qAtlas cost) (hπ : Vlasov.IsCoupling π μ ν)
    (ξ : Measure (X × X)) (hξ : ξ ≤ π) (N : ℕ)
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    {A B : C → Type*} {q : ℕ}
    (readS : ∀ c, X → (Fin q → ℝ) × A c) (readT : ∀ c, X → (Fin q → ℝ) × B c)
    (source : ∀ c, A c → ℝ) (target : ∀ c, B c → ℝ)
    (r : C → ℝ) (kin : ∀ c, A c → B c → (Fin q → ℝ) → ℝ)
    (probe : ∀ c, A c → B c → ℝ) (tilt : ℝ) :
    let R := D.refineSubplan ξ hξ
    let extra := originalCellScalarClassGraph readS readT source target
    let model := originalCellScalarClassScore readS readT r kin probe tilt
    ∀ᵐ sample ∂R.markedLaw N, ∀ c : C,
      let dataS := mapBlockData (fun p ↦ readS c p.1)
        (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1)
      let dataT := mapBlockData (fun p ↦ readT c p.1)
        (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.2)
      partitionCount (fun i ↦ originalRetainedCellTag a cell
          (PopulationTypedCostData.selectedSubplanTags (T := T)) (sample.1 i)) (some c) -
        (originalRetainedCellOptimizer a cell extra model c sample).card =
          (blockLegalSourceDefect q (source c) (target c) dataS dataT : ℝ) := by
  have h := D.original_retained_cell_defect_eq_prefix_ae hπ ξ hξ N a cell hdisj
    (originalCellScalarClassGraph readS readT source target)
    (originalCellScalarClassScore readS readT r kin probe tilt)
  filter_upwards [h] with sample hs
  intro c
  have hc := hs c
  dsimp only at hc ⊢
  rw [originalCellScalarClassGraph, PartialMatching.inducedLegalGraph_scalarClockLegalGraph] at hc
  simpa only [blockLegalSourceDefect, mapBlockData, finiteOriginalRestrictedData_point,
    Function.comp_def, Nat.cast_sub ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _))] using hc

end OTSelector.Reconstruction
