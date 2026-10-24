import OTSelector.Reconstruction.OriginalStageReserveActualPhysicalMainCounts
import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawIndices

/-! Original physical-window and reserve mark-block counts, before looking at positions. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The literal original colored input count in a spatial window and a clock
block. Natural floor is only a total readout; original finite arrays identify it. -/
def originalMainPhysicalBlockCount {q : ℕ} (K : Set (Fin q → ℝ)) (C : Set ℝ)
    (color : Fin 2) (scene : LegalMarkedOptimalInputScene q) : ℕ :=
  ⌊(scene.2 : Measure (LegalColoredInputPoint q)).real ((K ×ˢ C) ×ˢ {color})⌋₊

/-- The actual count depends measurably only on the original main scene. -/
theorem measurable_originalMainPhysicalBlockCount {q : ℕ}
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) {C : Set ℝ} (hC : MeasurableSet C)
    (color : Fin 2) : Measurable (originalMainPhysicalBlockCount K C color) := by
  have hU := (hK.prod hC).prod (measurableSet_singleton color)
  exact (((Measure.measurable_coe hU).comp
    (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal).nat_floor

/-- A genuine finite original endpoint array identifies the observable with
the number of its unchanged labels in the chosen clock block. -/
theorem originalMainPhysicalBlockCount_eq_original_array {q n : ℕ}
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) {C : Set ℝ} (hC : MeasurableSet C)
    (color : Fin 2) (scene : LegalMarkedOptimalInputScene q)
    (x : Fin n → LegalMarkedPhysicalPoint q)
    (hx : (legalInputColorMeasure q scene.2 color).restrict {p | p.1 ∈ K} =
      ∑ i, Measure.dirac (x i)) :
    originalMainPhysicalBlockCount K C color scene =
      (Finset.univ.filter (fun i ↦ (x i).2 ∈ C)).card := by
  have hKC : MeasurableSet (K ×ˢ C) := hK.prod hC
  have hW : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.2 ∈ C} :=
    hC.preimage measurable_snd
  have he := congrArg (fun m : Measure (LegalMarkedPhysicalPoint q) ↦ m {p | p.2 ∈ C}) hx
  rw [Measure.restrict_apply hW] at he
  have hinter : {p : LegalMarkedPhysicalPoint q | p.2 ∈ C} ∩ {p | p.1 ∈ K} = K ×ˢ C := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, mem_prod]
    tauto
  rw [hinter] at he
  have hm : (legalInputColorMeasure q scene.2 color) (K ×ˢ C) =
      ((Finset.univ.filter (fun i ↦ (x i).2 ∈ C)).card : ℝ≥0∞) := by
    rw [he]
    simp [Measure.finsetSum_apply, Set.indicator_apply, Finset.sum_boole]
  unfold originalMainPhysicalBlockCount
  rw [measureReal_def, ← legalInputColorMeasure_apply_prod q scene.2 color hKC, hm]
  simp

/-- Original reserve count in one clock block, on the actual observed prefix. -/
def originalReserveBlockCount (n : ℕ) (marks : ℕ → ℝ) (C : Set ℝ) : ℕ :=
  (originalReserveClassNatIndices n marks C).card

theorem measurable_originalReserveBlockCount {Z : Type*} [MeasurableSpace Z]
    {n : Z → ℕ} (hn : Measurable n) {marks : Z → ℕ → ℝ} (hm : Measurable marks)
    {C : Set ℝ} (hC : MeasurableSet C) :
    Measurable (fun z ↦ originalReserveBlockCount (n z) (marks z) C) :=
  (measurable_of_countable (fun s : Finset ℕ ↦ s.card)).comp
    (measurable_originalReserveClassNatIndices hn hm hC)

end OTSelector.Reconstruction
