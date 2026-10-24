import OTSelector.Reconstruction.FinslerRelativeLawOriginalNullPrefix
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineShape

/-! Exact empty-prefix physical values in the unchanged original experiment.
No regularity or cost domination is needed on a null retained cell. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace PartialMatching
/-- Empty source rows force the true legal value to vanish for any signed cost. -/
@[simp]
theorem legalMaximumValue_of_empty_rows {n : ℕ}
    (allowed : Finset (Fin 0 × Fin n)) (c : Fin 0 → Fin n → ℝ) :
    legalMaximumValue allowed c = 0 := by
  apply abs_nonpos_iff.mp
  simpa only [Nat.zero_min, Nat.cast_zero, zero_mul] using
    abs_legalMaximumValue_le_min allowed c (B := 0) le_rfl (fun i ↦ Fin.elim0 i)

/-- Empty target columns force the same legal value to vanish. -/
@[simp]
theorem legalMaximumValue_of_empty_cols {m : ℕ}
    (allowed : Finset (Fin m × Fin 0)) (c : Fin m → Fin 0 → ℝ) :
    legalMaximumValue allowed c = 0 := by
  apply abs_nonpos_iff.mp
  simpa only [Nat.min_zero, Nat.cast_zero, zero_mul] using
    abs_legalMaximumValue_le_min allowed c (B := 0) le_rfl (fun _ j ↦ Fin.elim0 j)
end PartialMatching

/-- Applying any original observation to the empty prefix retains no points. -/
@[simp]
theorem mapBlockData_emptyOriginalBlockData {X Y : Type*} (f : X → Y) :
    mapBlockData f (emptyOriginalBlockData X) = emptyOriginalBlockData Y := by
  change (⟨0, fun i : Fin 0 ↦ f (Fin.elim0 i)⟩ : BlockData Y) = ⟨0, Fin.elim0⟩
  congr 1
  funext i
  exact Fin.elim0 i

/-- The empty sigma fiber is measurable for every original point law. -/
theorem measurableSet_emptyOriginalBlockData_singleton (X : Type*) [MeasurableSpace X] :
    MeasurableSet {d : BlockData X | d = emptyOriginalBlockData X} := by
  change MeasurableSet[⨅ n : ℕ,
    (inferInstance : MeasurableSpace (Fin n → X)).map (Sigma.mk n)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet ((Sigma.mk n) ⁻¹' {d : BlockData X | d = emptyOriginalBlockData X})
  by_cases hn : n = 0
  · subst n
    have heq : (Sigma.mk 0) ⁻¹' {d : BlockData X | d = emptyOriginalBlockData X} = univ := by
      apply eq_univ_of_forall
      intro f
      change (⟨0, f⟩ : BlockData X) = ⟨0, Fin.elim0⟩
      congr 1
      funext i
      exact Fin.elim0 i
    rw [heq]
    exact MeasurableSet.univ
  · have heq : (Sigma.mk n) ⁻¹' {d : BlockData X | d = emptyOriginalBlockData X} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro f hf
      exact hn (congrArg Sigma.fst hf)
    rw [heq]
    exact MeasurableSet.empty

/-- The untruncated physical cost vanishes on an empty source prefix. -/
@[simp]
theorem unclampedBlockLegalTilted_empty_source {A B : Type*}
    (q : ℕ) (source : A → ℝ) (target : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (dT : BlockData ((Fin q → ℝ) × B)) :
    unclampedBlockLegalTilted q source target r kin probe t
      (emptyOriginalBlockData ((Fin q → ℝ) × A)) dT = 0 := by
  exact PartialMatching.legalMaximumValue_of_empty_rows _ _

/-- The untruncated physical cost also vanishes on an empty target prefix. -/
@[simp]
theorem unclampedBlockLegalTilted_empty_target {A B : Type*}
    (q : ℕ) (source : A → ℝ) (target : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) :
    unclampedBlockLegalTilted q source target r kin probe t dS
      (emptyOriginalBlockData ((Fin q → ℝ) × B)) = 0 := by
  exact PartialMatching.legalMaximumValue_of_empty_cols _ _

/-- Exact original empty-prefix laws imply zero actual expectation for every
observable vanishing at that prefix, including an untruncated physical value.
The observable itself need not be globally measurable or bounded. -/
theorem integrable_integral_zero_of_map_empty_prefix
    {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Ω) (observation : Ω → BlockData X × BlockData Y)
    (hobs : Measurable observation)
    (hlaw : μ.map observation = Measure.dirac (emptyOriginalBlockData X, emptyOriginalBlockData Y))
    (value : BlockData X × BlockData Y → ℝ)
    (hzero : value (emptyOriginalBlockData X, emptyOriginalBlockData Y) = 0) :
    Integrable (fun ω ↦ value (observation ω)) μ ∧
      (∫ ω, value (observation ω) ∂μ) = 0 := by
  have hsingle : MeasurableSet {d : BlockData X × BlockData Y |
      d = (emptyOriginalBlockData X, emptyOriginalBlockData Y)} := by
    convert (measurableSet_emptyOriginalBlockData_singleton X).prod
      (measurableSet_emptyOriginalBlockData_singleton Y) using 1
    ext d
    exact Prod.ext_iff
  have hae : ∀ᵐ d ∂μ.map observation,
      d = (emptyOriginalBlockData X, emptyOriginalBlockData Y) := by
    rw [hlaw]
    exact (ae_dirac_iff hsingle).mpr rfl
  have hobsEmpty := (ae_map_iff hobs.aemeasurable hsingle).mp hae
  have hvalue : (fun ω ↦ value (observation ω)) =ᵐ[μ] (fun _ ↦ 0) :=
    hobsEmpty.mono fun ω hω ↦ by change value (observation ω) = 0; rw [hω, hzero]
  exact ⟨(integrable_zero Ω ℝ μ).congr hvalue.symm, (integral_congr_ae hvalue).trans (integral_zero _ _)⟩

/-- The literal original two-color retained null-cell experiment has zero cost
expectation. Its global residual and all original observations remain unchanged. -/
theorem PopulationTypedCostData.integrable_integral_original_retained_null_cell
    {X Y Z W T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace W] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (hπ : Vlasov.IsCoupling π μ ν) (ξ : Measure (X × Y)) (hξ : ξ ≤ π) (N : ℕ)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hnullA : ((π - ξ).map Prod.fst) A = 0) (hnullB : ((π - ξ).map Prod.snd) B = 0)
    (f : X → Z) (g : Y → W) (hf : Measurable f) (hg : Measurable g)
    (value : BlockData Z × BlockData W → ℝ)
    (hzero : value (emptyOriginalBlockData Z, emptyOriginalBlockData W) = 0) :
    let R := D.refineSubplan ξ hξ
    let observation := Prod.map
      (fun x ↦ mapBlockData (fun p ↦ f p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent A) x))
      (fun y ↦ mapBlockData (fun p ↦ g p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent B) y))
    Integrable (fun ω ↦ value (observation ω)) (R.markedLaw N) ∧
      (∫ ω, value (observation ω) ∂R.markedLaw N) = 0 := by
  have hs : Measurable (fun x : Fin N → X × Option (Bool × T) ↦
      mapBlockData (fun p ↦ f p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent A) x)) :=
    (measurable_mapBlockData (hf.comp measurable_fst)).comp
    (measurable_finiteOriginalRestrictedData (measurableSet_retainedMarkedCellEvent (T := T) hA))
  have ht : Measurable (fun y : Fin N → Y × Option (Bool × T) ↦
      mapBlockData (fun p ↦ g p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent B) y)) :=
    (measurable_mapBlockData (hg.comp measurable_fst)).comp
    (measurable_finiteOriginalRestrictedData (measurableSet_retainedMarkedCellEvent (T := T) hB))
  exact integrable_integral_zero_of_map_empty_prefix _ _ (hs.prodMap ht)
    (D.original_retained_null_cell_prefix_law hπ ξ hξ N hA hB hnullA hnullB f g hf hg) value hzero

end OTSelector.Reconstruction
