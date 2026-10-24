import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawActualExcess

/-! Actual classwise surviving reserve indices and their original iid spatial fibre law. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual kept indices belonging to a spreading class D. C is the separate extreme
class used only for deletion; D is the actual stage mark class used by its density count. -/
def originalReserveSceneExcessClassKept (R : ℝ) (own other : Fin 2) (C D : Set ℝ)
    (z : OriginalReserveSceneAux q) : Finset ℕ :=
  (originalReserveSceneExcessKept R own other C z).filter (fun i ↦ z.2.2 i ∈ D)

/-- Both deletion class and spreading class are independently Borel, and the actual
classwise surviving-index selector is measurable. -/
theorem measurable_originalReserveSceneExcessClassKept (R : ℝ) (own other : Fin 2)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) :
    Measurable (originalReserveSceneExcessClassKept (q := q) R own other C D) := by
  apply measurable_finset_iff.mpr
  intro i
  apply measurableSet_setOfPred.mp
  have hm : MeasurableSet {z : OriginalReserveSceneAux q | i ∈ originalReserveSceneExcessKept R own other C z} :=
    measurableSet_setOfPred.mpr ((measurable_finset_mem i).comp
      (measurable_originalReserveSceneExcessKept R own other hC))
  have hmark : MeasurableSet {z : OriginalReserveSceneAux q | z.2.2 i ∈ D} :=
    hD.preimage ((measurable_pi_apply i).comp measurable_snd.snd)
  have heq : {z : OriginalReserveSceneAux q | i ∈ originalReserveSceneExcessClassKept R own other C D z} =
      {z | i ∈ originalReserveSceneExcessKept R own other C z} ∩ {z | z.2.2 i ∈ D} := by
    ext z
    simp [originalReserveSceneExcessClassKept]
  rw [heq]
  exact hm.inter hmark

/-- Enumerate the actual classwise original kept indices on their exact cardinality fibre. -/
def originalReserveSceneExcessClassSelection (R : ℝ) (own other : Fin 2) (C D : Set ℝ) (k : ℕ)
    (z : OriginalReserveSceneAux q) : Fin k ↪ ℕ :=
  originalReserveFiniteSelection k (originalReserveSceneExcessClassKept R own other C D z)

/-- Each actual classwise original-coordinate choice is measurable from the real mark/count data. -/
theorem measurable_originalReserveSceneExcessClassSelection_apply (R : ℝ) (own other : Fin 2)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) (j : Fin k) :
    Measurable (fun z : OriginalReserveSceneAux q ↦ originalReserveSceneExcessClassSelection R own other C D k z j) :=
  (measurable_originalReserveFiniteSelection_apply k j).comp
    (measurable_originalReserveSceneExcessClassKept R own other hC hD)

/-- The actual kept stage-class count fibre is measurable. -/
theorem measurableSet_originalReserveSceneExcessClassKept_card (R : ℝ) (own other : Fin 2)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    MeasurableSet {z : OriginalReserveSceneAux q | (originalReserveSceneExcessClassKept R own other C D z).card = k} :=
  (measurableSet_singleton k).preimage ((measurable_of_countable (fun s : Finset ℕ ↦ s.card)).comp
    (measurable_originalReserveSceneExcessClassKept R own other hC hD))

/-- The stage-class source set is precisely the unchanged original kept Fin source indices
whose original clock marks belong to D. The deletion class remains A.firstClass. -/
theorem originalReserveSceneExcessClassKept_source_eq_original_indices {q : ℕ}
    (A : OriginalStageExcessRemovalData q) {R : ℝ} {scene : LegalMarkedOptimalInputScene q}
    (hmain : IsOriginalStageMainWindowArrays R scene A.sourceMain A.targetMain) (D : Set ℝ) :
    originalReserveSceneExcessClassKept R 0 1 A.firstClass D
      ((scene, A.targetReserve), A.sourceReserve.1, fun i ↦ (A.sourceReserve.2 i).2) =
      (A.sourceKept.filter (fun i : Fin A.sourceReserve.1 ↦ (A.sourceReserve.2 i).2 ∈ D)).map Fin.valEmbedding := by
  rw [originalReserveSceneExcessClassKept, originalReserveSceneExcessKept_source_eq_original_indices A hmain,
    Finset.filter_map]
  rfl

/-- The target class set keeps the same original target identities; its deletion class
is A.lastClass, independently of the stage spreading class D. -/
theorem originalReserveSceneExcessClassKept_target_eq_original_indices {q : ℕ}
    (A : OriginalStageExcessRemovalData q) {R : ℝ} {scene : LegalMarkedOptimalInputScene q}
    (hmain : IsOriginalStageMainWindowArrays R scene A.sourceMain A.targetMain) (D : Set ℝ) :
    originalReserveSceneExcessClassKept R 1 0 A.lastClass D
      ((scene, A.sourceReserve), A.targetReserve.1, fun i ↦ (A.targetReserve.2 i).2) =
      (A.targetKept.filter (fun i : Fin A.targetReserve.1 ↦ (A.targetReserve.2 i).2 ∈ D)).map Fin.valEmbedding := by
  rw [originalReserveSceneExcessClassKept, originalReserveSceneExcessKept_target_eq_original_indices A hmain,
    Finset.filter_map]
  rfl

/-- The classwise selector's source cardinality is exactly the literal h_i^S used by
originalStageResidualDensityData.sourceDensity, with its original kept indices. -/
theorem originalReserveSceneExcessClassKept_source_card_eq_density_count {q : ℕ}
    (A : OriginalStageExcessRemovalData q) {R : ℝ} {scene : LegalMarkedOptimalInputScene q}
    (hmain : IsOriginalStageMainWindowArrays R scene A.sourceMain A.targetMain) (D : Set ℝ) :
    (originalReserveSceneExcessClassKept R 0 1 A.firstClass D
      ((scene, A.targetReserve), A.sourceReserve.1, fun i ↦ (A.sourceReserve.2 i).2)).card =
      originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept D := by
  rw [originalReserveSceneExcessClassKept_source_eq_original_indices A hmain D, Finset.card_map]
  rfl

/-- The target selector's class cardinality is exactly the literal original density h_i^T. -/
theorem originalReserveSceneExcessClassKept_target_card_eq_density_count {q : ℕ}
    (A : OriginalStageExcessRemovalData q) {R : ℝ} {scene : LegalMarkedOptimalInputScene q}
    (hmain : IsOriginalStageMainWindowArrays R scene A.sourceMain A.targetMain) (D : Set ℝ) :
    (originalReserveSceneExcessClassKept R 1 0 A.lastClass D
      ((scene, A.sourceReserve), A.targetReserve.1, fun i ↦ (A.targetReserve.2 i).2)).card =
      originalStageRemainingReserveClassCount A.targetReserve A.targetKept D := by
  rw [originalReserveSceneExcessClassKept_target_eq_original_indices A hmain D, Finset.card_map]
  rfl

/-- All and only the actual surviving class indices are selected on their actual count fibre. -/
theorem originalReserveSceneExcessClassSelection_range (R : ℝ) (own other : Fin 2) (C D : Set ℝ)
    (k : ℕ) (z : OriginalReserveSceneAux q)
    (hk : (originalReserveSceneExcessClassKept R own other C D z).card = k) :
    Finset.univ.map (originalReserveSceneExcessClassSelection R own other C D k z) =
      originalReserveSceneExcessClassKept R own other C D z :=
  originalReserveFiniteSelection_range _ hk

/-- Every selected class coordinate is a truly observed original reserve index and has its
actual original mark in D. No selected port or unobserved sampler point receives an iid law. -/
theorem originalReserveSceneExcessClassSelection_observed_mark (R : ℝ) (own other : Fin 2) (C D : Set ℝ)
    (k : ℕ) (z : OriginalReserveSceneAux q)
    (hk : (originalReserveSceneExcessClassKept R own other C D z).card = k) (j : Fin k) :
    originalReserveSceneExcessClassSelection R own other C D k z j < z.2.1 ∧
      z.2.2 (originalReserveSceneExcessClassSelection R own other C D k z j) ∈ D := by
  have hmem : originalReserveSceneExcessClassSelection R own other C D k z j ∈
      Finset.univ.map (originalReserveSceneExcessClassSelection R own other C D k z) :=
    Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
  rw [originalReserveSceneExcessClassSelection_range R own other C D k z hk] at hmem
  have h := Finset.mem_filter.mp hmem
  exact ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp h.1).1, h.2⟩

/-- Restrict the actual independent original reserve experiment to the actual classwise
kept-cardinality fibre. Its selected original positions have the exact iid joint law with
all main/other-color/count/mark data; no selected spatial law or injection is supplied. -/
theorem map_originalReserveSceneExcessClassSelection_actual_jointLaw
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsFiniteMeasure P]
    (α : Measure ℝ) [IsProbabilityMeasure α] (rate : ℝ≥0)
    (R : ℝ) (own other : Fin 2) {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    ((P.prod (markedPoissonLaw q ℝ α rate)).restrict
      {p | (originalReserveSceneExcessClassKept R own other C D
        ((p.1.1, p.1.2), p.2.1, fun i ↦ (p.2.2 i).2)).card = k}).map
      (fun p ↦ (((p.1.1, p.1.2), p.2.1, fun i ↦ (p.2.2 i).2),
        fun j : Fin k ↦ (p.2.2 (originalReserveSceneExcessClassSelection R own other C D k
          ((p.1.1, p.1.2), p.2.1, fun i ↦ (p.2.2 i).2) j)).1)) =
      ((P.prod (originalReserveCountMarkLaw α rate)).restrict
        {z | (originalReserveSceneExcessClassKept R own other C D z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  exact map_originalReserveSelectedPositions_joint_restrict_aux P q α rate
    (originalReserveSceneExcessClassSelection R own other C D k)
    (measurable_originalReserveSceneExcessClassSelection_apply R own other hC hD k)
    (measurableSet_originalReserveSceneExcessClassKept_card R own other hC hD k)

end OTSelector.Reconstruction
