import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawActualClass
import OTSelector.Reconstruction.OriginalStageReserveActualPhysicalMainCounts

/-! Actual kept original reserve class indices and iid fibre law for any physical window. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Literal same-scene physical-window excess deletion, with the stage spreading class
kept separate from the extreme deletion class. It reads no original reserve position. -/
def originalReservePhysicalSceneExcessClassKept {q : ℕ} (K : Set (Fin q → ℝ))
    (own other : Fin 2) (C D : Set ℝ) (z : OriginalReserveSceneAux q) : Finset ℕ :=
  (originalReserveKeptNatIndices z.2.1 z.2.2 C
    ((originalStageMainPhysicalWindowCount K own z.1.1 + z.2.1) -
      (originalStageMainPhysicalWindowCount K other z.1.1 + z.1.2.1))).filter (fun i ↦ z.2.2 i ∈ D)

/-- The original index set is measurable from actual main-window counts and unchanged
reserve marks, for arbitrary independently Borel deletion and spreading classes. -/
theorem measurable_originalReservePhysicalSceneExcessClassKept {q : ℕ} {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (own other : Fin 2) {C D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    Measurable (originalReservePhysicalSceneExcessClassKept K own other C D) := by
  have hown : Measurable (fun z : OriginalReserveSceneAux q ↦ originalStageMainPhysicalWindowCount K own z.1.1) :=
    (measurable_originalStageMainPhysicalWindowCount hK own).comp measurable_fst.fst
  have hother : Measurable (fun z : OriginalReserveSceneAux q ↦ originalStageMainPhysicalWindowCount K other z.1.1) :=
    (measurable_originalStageMainPhysicalWindowCount hK other).comp measurable_fst.fst
  have hsub : Measurable (fun p : ℕ × ℕ ↦ p.1 - p.2) := measurable_of_countable _
  have hkept := measurable_originalReserveKeptNatIndices (n := fun z : OriginalReserveSceneAux q ↦ z.2.1)
    measurable_snd.fst measurable_snd.snd hC
    (hsub.comp ((hown.add measurable_snd.fst).prodMk (hother.add measurable_fst.snd.fst)))
  apply measurable_finset_iff.mpr
  intro i
  apply measurableSet_setOfPred.mp
  have hm := measurableSet_setOfPred.mpr ((measurable_finset_mem i).comp hkept)
  have hmark : MeasurableSet {z : OriginalReserveSceneAux q | z.2.2 i ∈ D} :=
    hD.preimage ((measurable_pi_apply i).comp measurable_snd.snd)
  have heq : {z : OriginalReserveSceneAux q | i ∈ originalReservePhysicalSceneExcessClassKept K own other C D z} =
      {z | i ∈ originalReserveKeptNatIndices z.2.1 z.2.2 C
        ((originalStageMainPhysicalWindowCount K own z.1.1 + z.2.1) -
          (originalStageMainPhysicalWindowCount K other z.1.1 + z.1.2.1))} ∩ {z | z.2.2 i ∈ D} := by
    ext z
    simp [originalReservePhysicalSceneExcessClassKept]
  rw [heq]
  exact hm.inter hmark

/-- The measurable original-index injection enumerates exactly the true kept stage class
on its own cardinality fibre, using a harmless total fallback outside that fibre. -/
def originalReservePhysicalSceneExcessClassSelection {q : ℕ} (K : Set (Fin q → ℝ))
    (own other : Fin 2) (C D : Set ℝ) (k : ℕ) (z : OriginalReserveSceneAux q) : Fin k ↪ ℕ :=
  originalReserveFiniteSelection k (originalReservePhysicalSceneExcessClassKept K own other C D z)

theorem measurable_originalReservePhysicalSceneExcessClassSelection_apply {q : ℕ} {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (own other : Fin 2) {C D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) (j : Fin k) :
    Measurable (fun z : OriginalReserveSceneAux q ↦ originalReservePhysicalSceneExcessClassSelection K own other C D k z j) :=
  (measurable_originalReserveFiniteSelection_apply k j).comp
    (measurable_originalReservePhysicalSceneExcessClassKept hK own other hC hD)

theorem originalReservePhysicalSceneExcessClassSelection_range {q : ℕ} (K : Set (Fin q → ℝ))
    (own other : Fin 2) (C D : Set ℝ) (k : ℕ) (z : OriginalReserveSceneAux q)
    (hk : (originalReservePhysicalSceneExcessClassKept K own other C D z).card = k) :
    Finset.univ.map (originalReservePhysicalSceneExcessClassSelection K own other C D k z) =
      originalReservePhysicalSceneExcessClassKept K own other C D z := originalReserveFiniteSelection_range _ hk

/-- The source set is exactly the same original kept Fin source indices in the literal
stage class, for the same actual physical-window main arrays. -/
theorem originalReservePhysicalSceneExcessClassKept_source_eq_original_indices {q : ℕ}
    (A : OriginalStageExcessRemovalData q) {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    {scene : LegalMarkedOptimalInputScene q}
    (hmain : IsOriginalStageMainPhysicalWindowArrays K scene A.sourceMain A.targetMain) (D : Set ℝ) :
    originalReservePhysicalSceneExcessClassKept K 0 1 A.firstClass D
      ((scene, A.targetReserve), A.sourceReserve.1, fun i ↦ (A.sourceReserve.2 i).2) =
      (A.sourceKept.filter (fun i : Fin A.sourceReserve.1 ↦ (A.sourceReserve.2 i).2 ∈ D)).map Fin.valEmbedding := by
  unfold originalReservePhysicalSceneExcessClassKept
  rw [hmain.mainWindowCounts hK |>.1, hmain.mainWindowCounts hK |>.2]
  change (originalReserveKeptNatIndices A.sourceReserve.1 (fun i ↦ (A.sourceReserve.2 i).2) A.firstClass A.sourceExcess).filter _ = _
  rw [originalReserveKeptNatIndices_eq_map_fin, Finset.filter_map]
  rfl

/-- The target selector keeps precisely the same original kept target Fin identities. -/
theorem originalReservePhysicalSceneExcessClassKept_target_eq_original_indices {q : ℕ}
    (A : OriginalStageExcessRemovalData q) {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    {scene : LegalMarkedOptimalInputScene q}
    (hmain : IsOriginalStageMainPhysicalWindowArrays K scene A.sourceMain A.targetMain) (D : Set ℝ) :
    originalReservePhysicalSceneExcessClassKept K 1 0 A.lastClass D
      ((scene, A.sourceReserve), A.targetReserve.1, fun i ↦ (A.targetReserve.2 i).2) =
      (A.targetKept.filter (fun i : Fin A.targetReserve.1 ↦ (A.targetReserve.2 i).2 ∈ D)).map Fin.valEmbedding := by
  unfold originalReservePhysicalSceneExcessClassKept
  rw [hmain.mainWindowCounts hK |>.1, hmain.mainWindowCounts hK |>.2]
  change (originalReserveKeptNatIndices A.targetReserve.1 (fun i ↦ (A.targetReserve.2 i).2) A.lastClass A.targetExcess).filter _ = _
  rw [originalReserveKeptNatIndices_eq_map_fin, Finset.filter_map]
  rfl

/-- On the actual kept-count fibre every selected original coordinate is observed and
belongs to the true stage mark class. -/
theorem originalReservePhysicalSceneExcessClassSelection_observed_mark {q : ℕ} (K : Set (Fin q → ℝ))
    (own other : Fin 2) (C D : Set ℝ) (k : ℕ) (z : OriginalReserveSceneAux q)
    (hk : (originalReservePhysicalSceneExcessClassKept K own other C D z).card = k) (j : Fin k) :
    originalReservePhysicalSceneExcessClassSelection K own other C D k z j < z.2.1 ∧
      z.2.2 (originalReservePhysicalSceneExcessClassSelection K own other C D k z j) ∈ D := by
  have hm : originalReservePhysicalSceneExcessClassSelection K own other C D k z j ∈
      Finset.univ.map (originalReservePhysicalSceneExcessClassSelection K own other C D k z) :=
    Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
  rw [originalReservePhysicalSceneExcessClassSelection_range K own other C D k z hk] at hm
  have hp := Finset.mem_filter.mp hm
  exact ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp hp.1).1, hp.2⟩

/-- The actual physical-window deletion/class selector has the original iid spatial fibre
law under the same literal independent marked-Poisson experiment. All measurability and
index selection are produced internally; arbitrary finite external original data are kept. -/
theorem map_originalReservePhysicalSceneExcessClassSelection_actual_jointLaw {q : ℕ}
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsFiniteMeasure P]
    (α : Measure ℝ) [IsProbabilityMeasure α] (rate : ℝ≥0) {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (own other : Fin 2) {C D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    ((P.prod (markedPoissonLaw q ℝ α rate)).restrict
      {p | (originalReservePhysicalSceneExcessClassKept K own other C D
        ((p.1.1, p.1.2), p.2.1, fun i ↦ (p.2.2 i).2)).card = k}).map
      (fun p ↦ (((p.1.1, p.1.2), p.2.1, fun i ↦ (p.2.2 i).2),
        fun j : Fin k ↦ (p.2.2 (originalReservePhysicalSceneExcessClassSelection K own other C D k
          ((p.1.1, p.1.2), p.2.1, fun i ↦ (p.2.2 i).2) j)).1)) =
      ((P.prod (originalReserveCountMarkLaw α rate)).restrict
        {z | (originalReservePhysicalSceneExcessClassKept K own other C D z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  have hE : MeasurableSet {z : OriginalReserveSceneAux q |
      (originalReservePhysicalSceneExcessClassKept K own other C D z).card = k} :=
    (measurableSet_singleton k).preimage ((measurable_of_countable (fun s : Finset ℕ ↦ s.card)).comp
      (measurable_originalReservePhysicalSceneExcessClassKept hK own other hC hD))
  exact map_originalReserveSelectedPositions_joint_restrict_aux P q α rate
    (originalReservePhysicalSceneExcessClassSelection K own other C D k)
    (measurable_originalReservePhysicalSceneExcessClassSelection_apply hK own other hC hD k) hE

end OTSelector.Reconstruction
