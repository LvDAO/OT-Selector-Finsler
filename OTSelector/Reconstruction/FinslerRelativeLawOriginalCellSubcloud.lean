import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellOptimizer
import OTSelector.Reconstruction.MarkedStationaryValueLegalEmbedding
import OTSelector.Finite.BlockRepair

/-! Exact restriction of the actual original retained optimizer to its finite
cell subcloud. Original points, marks, and enumerations are preserved, including
empty color clouds. The real source deficit is the literal finite Hall deficit. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

section Finite
variable {X Z C T : Type*} {N m n : ℕ}
  (a : X → Z) (cell : C → Set Z)
  (extra : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
    Finset (Fin N × Fin N)) (c : C)
  (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T)))
  (e : Fin m ↪ Fin N) (f : Fin n ↪ Fin N)

/-- Restricting the actual retained graph to its original cell observations
removes exactly the flags and spatial gate, leaving the original class graph. -/
theorem originalRetainedCellGraph_induced_eq
    (hs : ∀ i, subplanRetentionFlag (sample.1 (e i)).2 = false ∧
      a (sample.1 (e i)).1 ∈ cell c)
    (ht : ∀ j, subplanRetentionFlag (sample.2 (f j)).2 = false ∧
      a (sample.2 (f j)).1 ∈ cell c) :
    PartialMatching.inducedLegalGraph (originalRetainedCellGraph a cell extra c sample) e f =
      PartialMatching.inducedLegalGraph (extra c sample) e f := by
  classical
  ext p
  simp only [PartialMatching.inducedLegalGraph, Finset.mem_filter, Finset.mem_univ,
    true_and, originalRetainedCellGraph, (hs p.1).1, (ht p.2).1, (hs p.1).2,
    (ht p.2).2, and_self, and_true]

/-- Every allowed original retained edge is carried by any complete original
cell enumeration. No new selected-point sampling law is asserted. -/
theorem originalRetainedCellGraph_carried
    (hs : ∀ i, subplanRetentionFlag (sample.1 i).2 = false ∧ a (sample.1 i).1 ∈ cell c →
      i ∈ range e)
    (ht : ∀ j, subplanRetentionFlag (sample.2 j).2 = false ∧ a (sample.2 j).1 ∈ cell c →
      j ∈ range f) :
    ∀ p ∈ originalRetainedCellGraph a cell extra c sample,
      p.1 ∈ range e ∧ p.2 ∈ range f := by
  intro p hp
  have h := (Finset.mem_filter.mp hp).2
  exact ⟨hs p.1 ⟨h.1, h.2.2.1⟩, ht p.2 ⟨h.2.1, h.2.2.2⟩⟩

variable
  (hs : ∀ i, i ∈ range e ↔
    subplanRetentionFlag (sample.1 i).2 = false ∧ a (sample.1 i).1 ∈ cell c)
  (ht : ∀ j, j ∈ range f ↔
    subplanRetentionFlag (sample.2 j).2 = false ∧ a (sample.2 j).1 ∈ cell c)

include hs ht

/-- Original finite enumeration preserves the actual retained legal rank. -/
theorem originalRetainedCellGraph_card_eq_subcloud :
    PartialMatching.legalMaximumCard (originalRetainedCellGraph a cell extra c sample) =
      PartialMatching.legalMaximumCard (PartialMatching.inducedLegalGraph (extra c sample) e f) := by
  rw [← PartialMatching.legalMaximumCard_inducedLegalGraph _ e f
    (originalRetainedCellGraph_carried a cell extra c sample e f
      (fun i ↦ (hs i).mpr) (fun j ↦ (ht j).mpr))]
  rw [originalRetainedCellGraph_induced_eq a cell extra c sample e f
    (fun i ↦ (hs (e i)).mp ⟨i, rfl⟩) (fun j ↦ (ht (f j)).mp ⟨j, rfl⟩)]

/-- Signed frozen model values are exactly unchanged by the actual retained
cell enumeration, with all original finite counts retained. -/
theorem originalRetainedCellGraph_value_eq_subcloud (score : Fin N → Fin N → ℝ) :
    PartialMatching.legalMaximumValue (originalRetainedCellGraph a cell extra c sample) score =
      PartialMatching.legalMaximumValue (PartialMatching.inducedLegalGraph (extra c sample) e f)
        (fun i j ↦ score (e i) (f j)) := by
  rw [← PartialMatching.legalMaximumValue_inducedLegalGraph _ e f
    (originalRetainedCellGraph_carried a cell extra c sample e f
      (fun i ↦ (hs i).mpr) (fun j ↦ (ht j).mpr)) score]
  rw [originalRetainedCellGraph_induced_eq a cell extra c sample e f
    (fun i ↦ (hs (e i)).mp ⟨i, rfl⟩) (fun j ↦ (ht (f j)).mp ⟨j, rfl⟩)]

/-- Pulling back the canonical ambient optimizer gives an exact legal optimum
on the actual retained subcloud. A separate first-optimizer equality is not
required, and ties cause no change in rank or signed value. -/
theorem originalRetainedCellOptimizer_comap_isLegalOptimal
    (model : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Fin N → Fin N → ℝ) :
    PartialMatching.IsLegalOptimal (PartialMatching.inducedLegalGraph (extra c sample) e f)
      (fun i j ↦ model c sample (e i) (f j))
      ((originalRetainedCellOptimizer a cell extra model c sample).comapEmbedding e f) := by
  let σ := originalRetainedCellOptimizer a cell extra model c sample
  have hopt := originalRetainedCellOptimizer_isLegalOptimal a cell extra model c sample
  have hcarry := originalRetainedCellGraph_carried a cell extra c sample e f
    (fun i ↦ (hs i).mpr) (fun j ↦ (ht j).mpr)
  have hσcarry := fun p hp ↦ hcarry p (hopt.1 hp)
  have hgraph := originalRetainedCellGraph_induced_eq a cell extra c sample e f
    (fun i ↦ (hs (e i)).mp ⟨i, rfl⟩) (fun j ↦ (ht (f j)).mp ⟨j, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hgraph]
    exact PartialMatching.isLegal_comapEmbedding _ e f σ hopt.1
  · rw [OTSelector.PartialMatching.card_comapEmbedding e f σ hσcarry, hopt.2.1]
    exact originalRetainedCellGraph_card_eq_subcloud a cell extra c sample e f hs ht
  · rw [OTSelector.PartialMatching.cost_comapEmbedding e f σ hσcarry, hopt.2.2]
    exact originalRetainedCellGraph_value_eq_subcloud a cell extra c sample e f hs ht _

end Finite

/-- A literal finite retained-cell enumeration has exactly its original
source count. This is an identity of original indices before any matching. -/
theorem originalRetainedCell_source_count_eq
    {X Z C T : Type*} {N m : ℕ} (a : X → Z) (cell : C → Set Z) (c : C)
    (source : Fin N → X × Option (Bool × T)) (e : Fin m ↪ Fin N)
    (hs : ∀ i, i ∈ range e ↔
      subplanRetentionFlag (source i).2 = false ∧ a (source i).1 ∈ cell c) :
    (Finset.univ.filter (fun i ↦ subplanRetentionFlag (source i).2 = false ∧
      a (source i).1 ∈ cell c)).card = m := by
  classical
  have heq : Finset.univ.filter (fun i ↦ subplanRetentionFlag (source i).2 = false ∧
      a (source i).1 ∈ cell c) = Finset.univ.image e := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := (hs i).mpr hi
      exact ⟨j, hj⟩
    · rintro ⟨j, rfl⟩
      exact (hs (e j)).mp ⟨j, rfl⟩
  rw [heq, Finset.card_image_of_injective _ e.injective, Finset.card_univ, Fintype.card_fin]

/-- On actual proper original RN marks, the retained-cell tag count is the
literal original false-flag count, including every retained physical endpoint. -/
theorem originalRetainedCell_partitionCount_eq
    {X Z C T : Type*} [Fintype T] {N m : ℕ}
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell)) (c : C)
    (source : Fin N → X × Option (Bool × T))
    (hproper : ∀ i, ∃ t : Bool × T, (source i).2 = some t) (e : Fin m ↪ Fin N)
    (hs : ∀ i, i ∈ range e ↔
      subplanRetentionFlag (source i).2 = false ∧ a (source i).1 ∈ cell c) :
    partitionCount (fun i ↦ originalRetainedCellTag a cell
      (PopulationTypedCostData.selectedSubplanTags (T := T)) (source i)) (some c) = m := by
  classical
  rw [OTSelector.partitionCount_eq_card_filter]
  have heq : Finset.univ.filter (fun i ↦ originalRetainedCellTag a cell
      (PopulationTypedCostData.selectedSubplanTags (T := T)) (source i) = some c) =
      Finset.univ.filter (fun i ↦ subplanRetentionFlag (source i).2 = false ∧
        a (source i).1 ∈ cell c) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      originalRetainedCellTag_eq_some_iff a cell hdisj]
    obtain ⟨⟨flag, t⟩, hmark⟩ := hproper i
    rw [hmark]
    cases flag <;> simp [PopulationTypedCostData.selectedSubplanTags, subplanRetentionFlag]
  rw [heq, originalRetainedCell_source_count_eq a cell c source e hs]

/-- The global splice's real retained source defect is exactly the actual
finite legal source deficiency on its original subcloud enumeration. -/
theorem originalRetainedCellOptimizer_defect_eq_subcloud
    {X Z C T : Type*} [Fintype T] {N m n : ℕ}
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (extra : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Finset (Fin N × Fin N))
    (model : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Fin N → Fin N → ℝ) (c : C)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T)))
    (hproper : ∀ i, ∃ t : Bool × T, (sample.1 i).2 = some t)
    (e : Fin m ↪ Fin N) (f : Fin n ↪ Fin N)
    (hs : ∀ i, i ∈ range e ↔
      subplanRetentionFlag (sample.1 i).2 = false ∧ a (sample.1 i).1 ∈ cell c)
    (ht : ∀ j, j ∈ range f ↔
      subplanRetentionFlag (sample.2 j).2 = false ∧ a (sample.2 j).1 ∈ cell c) :
    partitionCount (fun i ↦ originalRetainedCellTag a cell
        (PopulationTypedCostData.selectedSubplanTags (T := T)) (sample.1 i)) (some c) -
      (originalRetainedCellOptimizer a cell extra model c sample).card =
      ((m - PartialMatching.legalMaximumCard
        (PartialMatching.inducedLegalGraph (extra c sample) e f) : ℕ) : ℝ) := by
  classical
  rw [originalRetainedCell_partitionCount_eq a cell hdisj c sample.1 hproper e hs,
    (originalRetainedCellOptimizer_isLegalOptimal a cell extra model c sample).2.1,
    originalRetainedCellGraph_card_eq_subcloud a cell extra c sample e f hs ht,
    Nat.cast_sub ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _))]

/-- Full original type coverage discharges the proper-mark condition once on
the same marked experiment, before any cell optimizer or enumeration is chosen. -/
theorem PopulationTypedCostData.original_retained_cell_defect_eq_subcloud_ae
    {X Z C T : Type*} [MeasurableSpace X] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {π : Measure (X × X)} [IsFiniteMeasure π] {q : ℕ} {cost : X → X → ℝ}
    (D : PopulationTypedCostData π μ ν T q cost) (hπ : Vlasov.IsCoupling π μ ν)
    (ξ : Measure (X × X)) (hξ : ξ ≤ π) (N : ℕ)
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (extra : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Finset (Fin N × Fin N))
    (model : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Fin N → Fin N → ℝ) :
    let R := D.refineSubplan ξ hξ
    ∀ᵐ sample ∂R.markedLaw N, ∀ (c : C) (m n : ℕ) (e : Fin m ↪ Fin N) (f : Fin n ↪ Fin N),
      (∀ i, i ∈ range e ↔ subplanRetentionFlag (sample.1 i).2 = false ∧
        a (sample.1 i).1 ∈ cell c) →
      (∀ j, j ∈ range f ↔ subplanRetentionFlag (sample.2 j).2 = false ∧
        a (sample.2 j).1 ∈ cell c) →
      partitionCount (fun i ↦ originalRetainedCellTag a cell
          (PopulationTypedCostData.selectedSubplanTags (T := T)) (sample.1 i)) (some c) -
        (originalRetainedCellOptimizer a cell extra model c sample).card =
        ((m - PartialMatching.legalMaximumCard
          (PartialMatching.inducedLegalGraph (extra c sample) e f) : ℕ) : ℝ) := by
  let R := D.refineSubplan ξ hξ
  have hproper := R.types.iid_marked_ae_some_of_sum_eq (I := Fin N) (J := Fin N) hπ R.sum_eq
  filter_upwards [hproper] with sample hp
  intro c m n e f hs ht
  exact originalRetainedCellOptimizer_defect_eq_subcloud a cell hdisj extra model c sample
    hp.1 e f hs ht

end OTSelector.Reconstruction
