import OTSelector.Reconstruction.OriginalStageResidualDensityExcessIndices
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! The actual sorted mark deletion, expressed on original Nat sampler indices, is measurable. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- Original observed Nat indices whose unchanged marks lie in the selected class. -/
def originalReserveClassNatIndices (n : ℕ) (marks : ℕ → ℝ) (C : Set ℝ) : Finset ℕ :=
  (Finset.range n).filter (fun i ↦ marks i ∈ C)

/-- The same Fin-order initial deletion on original sampler indices. -/
def originalReserveDeletedNatIndices (n : ℕ) (marks : ℕ → ℝ) (C : Set ℝ) (k : ℕ) : Finset ℕ :=
  (((originalReserveClassNatIndices n marks C).sort (· ≤ ·)).take k).toFinset

/-- Actual original sampler indices left after the extreme mark-class deletion. -/
def originalReserveKeptNatIndices (n : ℕ) (marks : ℕ → ℝ) (C : Set ℝ) (k : ℕ) : Finset ℕ :=
  Finset.range n \ originalReserveDeletedNatIndices n marks C k

/-- Borel mark classes give a measurable actual class-index set. -/
theorem measurable_originalReserveClassNatIndices {Z : Type*} [MeasurableSpace Z]
    {n : Z → ℕ} (hn : Measurable n) {marks : Z → ℕ → ℝ} (hm : Measurable marks)
    {C : Set ℝ} (hC : MeasurableSet C) :
    Measurable (fun z ↦ originalReserveClassNatIndices (n z) (marks z) C) := by
  apply measurable_finset_iff.mpr
  intro i
  apply measurableSet_setOfPred.mp
  have heq : {z | i ∈ originalReserveClassNatIndices (n z) (marks z) C} =
      {z | i < n z} ∩ {z | marks z i ∈ C} := by
    ext z
    simp [originalReserveClassNatIndices]
  rw [heq]
  exact (measurableSet_lt measurable_const hn).inter
    (hC.preimage ((measurable_pi_apply i).comp hm))

/-- Taking the sorted initial segment is a measurable countable-index operation. -/
theorem measurable_originalReserveDeletedNatIndices {Z : Type*} [MeasurableSpace Z]
    {n : Z → ℕ} (hn : Measurable n) {marks : Z → ℕ → ℝ} (hm : Measurable marks)
    {C : Set ℝ} (hC : MeasurableSet C) {k : Z → ℕ} (hk : Measurable k) :
    Measurable (fun z ↦ originalReserveDeletedNatIndices (n z) (marks z) C (k z)) := by
  have hsort : Measurable (fun p : Finset ℕ × ℕ ↦ ((p.1.sort (· ≤ ·)).take p.2).toFinset) :=
    measurable_of_countable _
  exact hsort.comp ((measurable_originalReserveClassNatIndices hn hm hC).prodMk hk)

/-- Surviving original indices are a measurable function of original counts and marks alone. -/
theorem measurable_originalReserveKeptNatIndices {Z : Type*} [MeasurableSpace Z]
    {n : Z → ℕ} (hn : Measurable n) {marks : Z → ℕ → ℝ} (hm : Measurable marks)
    {C : Set ℝ} (hC : MeasurableSet C) {k : Z → ℕ} (hk : Measurable k) :
    Measurable (fun z ↦ originalReserveKeptNatIndices (n z) (marks z) C (k z)) := by
  have hsdiff : Measurable (fun p : ℕ × Finset ℕ ↦ Finset.range p.1 \ p.2) :=
    measurable_of_countable _
  exact hsdiff.comp (hn.prodMk (measurable_originalReserveDeletedNatIndices hn hm hC hk))

/-- The original Fin observation and original Nat sampler identify exactly the same class indices. -/
theorem originalReserveClassNatIndices_eq_map_fin (n : ℕ) (marks : ℕ → ℝ) (C : Set ℝ) :
    originalReserveClassNatIndices n marks C =
      (Finset.univ.filter (fun i : Fin n ↦ marks i ∈ C)).map Fin.valEmbedding := by
  ext i
  simp only [originalReserveClassNatIndices, Finset.mem_filter, Finset.mem_range, Finset.mem_map,
    Finset.mem_univ, true_and, Fin.valEmbedding_apply]
  exact ⟨fun h ↦ ⟨⟨i, h.1⟩, h.2, rfl⟩,
    fun ⟨j, hj, hji⟩ ↦ hji ▸ And.intro j.2 hj⟩

/-- The actual Nat deletion is exactly the image of the already verified original Fin deletion. -/
theorem originalReserveDeletedNatIndices_eq_map_fin (n : ℕ) (marks : ℕ → ℝ) (C : Set ℝ) (k : ℕ) :
    originalReserveDeletedNatIndices n marks C k =
      (originalStageMarkInitialIndices (fun i : Fin n ↦ marks i) C k).map Fin.valEmbedding := by
  have hsort := Finset.map_sort (f := Fin.valEmbedding) (r := (· ≤ ·)) (r' := (· ≤ ·))
    (s := Finset.univ.filter (fun i : Fin n ↦ marks i ∈ C)) (fun _ _ _ _ ↦ Iff.rfl)
  unfold originalReserveDeletedNatIndices originalStageMarkInitialIndices
  rw [originalReserveClassNatIndices_eq_map_fin, ← hsort, ← List.map_take]
  ext i
  simp only [List.mem_toFinset, Finset.mem_map, Fin.valEmbedding_apply]
  simp only [List.mem_map]

/-- Fin and Nat formulations preserve exactly the same surviving original indices. -/
theorem originalReserveKeptNatIndices_eq_map_fin (n : ℕ) (marks : ℕ → ℝ) (C : Set ℝ) (k : ℕ) :
    originalReserveKeptNatIndices n marks C k =
      (originalStageKeptAfterMarkRemoval (fun i : Fin n ↦ marks i) C k).map Fin.valEmbedding := by
  rw [originalReserveKeptNatIndices, originalReserveDeletedNatIndices_eq_map_fin,
    originalStageKeptAfterMarkRemoval, Finset.map_sdiff]
  congr 1
  ext i
  simp

/-- A total injection enumerates all actual kept indices on the exact kept-cardinality fibre.
Outside that fibre it enumerates the original Nat sampler's initial coordinates. -/
def originalReserveFiniteSelection (k : ℕ) (kept : Finset ℕ) : Fin k ↪ ℕ :=
  if h : kept.card = k then (kept.orderEmbOfFin h).toEmbedding else Fin.valEmbedding

/-- The total original-index injection is measurable in the mark-selected kept set. -/
theorem measurable_originalReserveFiniteSelection_apply (k : ℕ) (j : Fin k) :
    Measurable (fun kept : Finset ℕ ↦ originalReserveFiniteSelection k kept j) :=
  measurable_of_countable _

/-- On its exact cardinality fibre, the injection selects precisely all kept original indices. -/
theorem originalReserveFiniteSelection_range {k : ℕ} (kept : Finset ℕ) (h : kept.card = k) :
    Finset.univ.map (originalReserveFiniteSelection k kept) = kept := by
  rw [originalReserveFiniteSelection, dite_eq_left h]
  exact Finset.map_orderEmbOfFin_univ kept h

end OTSelector.Reconstruction
