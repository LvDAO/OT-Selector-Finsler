import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockCounts
import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawActualExcess

/-! Actual blockwise excess deletion and its unchanged original iid coordinates. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ}

/-- The signed color excess in one actual physical clock block, using only
main-scene observations, both reserve counts and original marks. -/
def originalReserveBlockExcess (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T : Set ℝ) (z : OriginalReserveSceneAux q) : ℕ :=
  (originalMainPhysicalBlockCount K S own z.1.1 + originalReserveBlockCount z.2.1 z.2.2 S) -
    (originalMainPhysicalBlockCount K T other z.1.1 +
      originalReserveBlockCount z.1.2.1 (fun i ↦ (z.1.2.2 i).2) T)

/-- Keep exactly the original indices of this block after taking its actual
excess from its designated extreme class. Positions never enter the deletion. -/
def originalReserveBlockKept (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : Set ℝ) (z : OriginalReserveSceneAux q) : Finset ℕ :=
  originalReserveClassNatIndices z.2.1 z.2.2 S \
    originalReserveDeletedNatIndices z.2.1 z.2.2 C (originalReserveBlockExcess K own other S T z)

theorem measurable_originalReserveBlockExcess {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (own other : Fin 2) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Measurable (originalReserveBlockExcess K own other S T) := by
  have hsm : Measurable (fun z : OriginalReserveSceneAux q ↦
      originalMainPhysicalBlockCount K S own z.1.1) :=
    (measurable_originalMainPhysicalBlockCount hK hS own).comp measurable_fst.fst
  have htm : Measurable (fun z : OriginalReserveSceneAux q ↦
      originalMainPhysicalBlockCount K T other z.1.1) :=
    (measurable_originalMainPhysicalBlockCount hK hT other).comp measurable_fst.fst
  have hsr : Measurable (fun z : OriginalReserveSceneAux q ↦
      originalReserveBlockCount z.2.1 z.2.2 S) :=
    measurable_originalReserveBlockCount measurable_snd.fst measurable_snd.snd hS
  have htr : Measurable (fun z : OriginalReserveSceneAux q ↦
      originalReserveBlockCount z.1.2.1 (fun i ↦ (z.1.2.2 i).2) T) :=
    measurable_originalReserveBlockCount measurable_fst.snd.fst
    (show Measurable (fun z : OriginalReserveSceneAux q ↦ fun i ↦ (z.1.2.2 i).2) by fun_prop) hT
  exact (measurable_of_countable (fun p : ℕ × ℕ ↦ p.1-p.2)).comp
    ((hsm.add hsr).prodMk (htm.add htr))

theorem measurable_originalReserveBlockKept {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (own other : Fin 2) {S T C : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) :
    Measurable (originalReserveBlockKept K own other S T C) := by
  exact (measurable_of_countable (fun p : Finset ℕ × Finset ℕ ↦ p.1 \ p.2)).comp
    ((measurable_originalReserveClassNatIndices measurable_snd.fst measurable_snd.snd hS).prodMk
      (measurable_originalReserveDeletedNatIndices measurable_snd.fst measurable_snd.snd hC
        (measurable_originalReserveBlockExcess hK own other hS hT)))

/-- Sorted deletion stays in its actual observed original mark class. -/
theorem originalReserveDeletedNatIndices_subset (n : ℕ) (marks : ℕ → ℝ) (C : Set ℝ) (k : ℕ) :
    originalReserveDeletedNatIndices n marks C k ⊆ originalReserveClassNatIndices n marks C := by
  intro i hi
  exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take (List.mem_toFinset.mp hi))

/-- Real extreme-class capacity deletes exactly the requested original excess. -/
theorem card_originalReserveDeletedNatIndices_of_le (n : ℕ) (marks : ℕ → ℝ) (C : Set ℝ)
    {k : ℕ} (hk : k ≤ originalReserveBlockCount n marks C) :
    (originalReserveDeletedNatIndices n marks C k).card = k := by
  rw [originalReserveDeletedNatIndices_eq_map_fin, Finset.card_map]
  apply card_originalStageMarkInitialIndices_of_le
  simpa only [originalReserveBlockCount, originalReserveClassNatIndices_eq_map_fin,
    Finset.card_map] using hk

/-- Deletion in an extreme class inside this block gives its true remaining
count; no balance or successful deletion is assumed as an output callback. -/
theorem originalReserveBlockKept_card (K : Set (Fin q → ℝ)) (own other : Fin 2)
    {S T C : Set ℝ} (hCS : C ⊆ S) (z : OriginalReserveSceneAux q)
    (hcap : originalReserveBlockExcess K own other S T z ≤
      originalReserveBlockCount z.2.1 z.2.2 C) :
    (originalReserveBlockKept K own other S T C z).card =
      originalReserveBlockCount z.2.1 z.2.2 S - originalReserveBlockExcess K own other S T z := by
  have hsub : originalReserveDeletedNatIndices z.2.1 z.2.2 C
      (originalReserveBlockExcess K own other S T z) ⊆
      originalReserveClassNatIndices z.2.1 z.2.2 S := by
    intro i hi
    have hm := Finset.mem_filter.mp (originalReserveDeletedNatIndices_subset _ _ _ _ hi)
    exact Finset.mem_filter.mpr ⟨hm.1, hCS hm.2⟩
  rw [originalReserveBlockKept, Finset.card_sdiff_of_subset hsub,
    card_originalReserveDeletedNatIndices_of_le _ _ _ hcap]
  rfl

/-- A total original-index injection enumerates this actual kept block on its
exact count fibre. The generic fallback is irrelevant on that fibre. -/
def originalReserveBlockSelection (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : Set ℝ) (k : ℕ) (z : OriginalReserveSceneAux q) : Fin k ↪ ℕ :=
  originalReserveFiniteSelection k (originalReserveBlockKept K own other S T C z)

theorem measurable_originalReserveBlockSelection_apply {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (own other : Fin 2) {S T C : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (k : ℕ) (j : Fin k) :
    Measurable (fun z ↦ originalReserveBlockSelection K own other S T C k z j) :=
  (measurable_originalReserveFiniteSelection_apply k j).comp
    (measurable_originalReserveBlockKept hK own other hS hT hC)

theorem originalReserveBlockSelection_range (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : Set ℝ) (k : ℕ) (z : OriginalReserveSceneAux q)
    (hk : (originalReserveBlockKept K own other S T C z).card = k) :
    Finset.univ.map (originalReserveBlockSelection K own other S T C k z) =
      originalReserveBlockKept K own other S T C z := originalReserveFiniteSelection_range _ hk

/-- Every produced coordinate is an observed original reserve point of its
own true clock block, including zero-cardinality fibres. -/
theorem originalReserveBlockSelection_observed_mark (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : Set ℝ) (k : ℕ) (z : OriginalReserveSceneAux q)
    (hk : (originalReserveBlockKept K own other S T C z).card = k) (j : Fin k) :
    originalReserveBlockSelection K own other S T C k z j < z.2.1 ∧
      z.2.2 (originalReserveBlockSelection K own other S T C k z j) ∈ S := by
  have hm : originalReserveBlockSelection K own other S T C k z j ∈
      Finset.univ.map (originalReserveBlockSelection K own other S T C k z) :=
    Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
  rw [originalReserveBlockSelection_range K own other S T C k z hk] at hm
  have h := Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1
  exact ⟨Finset.mem_range.mp h.1, h.2⟩

/-- The real Poisson reserve experiment supplies exact iid positions on each
actual block-kept count fibre after blockwise excess deletion. No selected
spatial law, external enumeration or own-position-dependent auxiliary is used. -/
theorem map_originalReserveBlockSelection_actual_jointLaw
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsFiniteMeasure P]
    (α : Measure ℝ) [IsProbabilityMeasure α] (rate : ℝ≥0)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (own other : Fin 2)
    {S T C : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (k : ℕ) :
    ((P.prod (markedPoissonLaw q ℝ α rate)).restrict
      {p | (originalReserveBlockKept K own other S T C
        ((p.1.1,p.1.2),p.2.1,fun i ↦ (p.2.2 i).2)).card = k}).map
      (fun p ↦ (((p.1.1,p.1.2),p.2.1,fun i ↦ (p.2.2 i).2),
        fun j : Fin k ↦ (p.2.2 (originalReserveBlockSelection K own other S T C k
          ((p.1.1,p.1.2),p.2.1,fun i ↦ (p.2.2 i).2) j)).1)) =
      ((P.prod (originalReserveCountMarkLaw α rate)).restrict
        {z | (originalReserveBlockKept K own other S T C z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  exact map_originalReserveSelectedPositions_joint_restrict_aux P q α rate
    (originalReserveBlockSelection K own other S T C k)
    (measurable_originalReserveBlockSelection_apply hK own other hS hT hC k)
    ((measurableSet_singleton k).preimage
      ((measurable_of_countable (fun s : Finset ℕ ↦ s.card)).comp
        (measurable_originalReserveBlockKept hK own other hS hT hC)))

end OTSelector.Reconstruction
