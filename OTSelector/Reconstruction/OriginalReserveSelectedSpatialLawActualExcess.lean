import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawIndices
import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawPoisson
import OTSelector.Reconstruction.OriginalStageReserveActualMainCounts

/-! Actual full-scene excess removal supplies the original selected-position law. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Auxiliary data retain the original main scene, the other-color reserve observation,
and the observed color's actual count and entire original mark sequence. -/
abbrev OriginalReserveSceneAux (q : ℕ) :=
  (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × (ℕ × (ℕ → ℝ))

/-- Delete the actual full color excess using only measurable main-window counts,
original reserve counts, the original class marks and original sampler indices. -/
def originalReserveSceneExcessKept (R : ℝ) (own other : Fin 2) (C : Set ℝ)
    (z : OriginalReserveSceneAux q) : Finset ℕ :=
  originalReserveKeptNatIndices z.2.1 z.2.2 C
    ((originalStageMainWindowCount R own z.1.1 + z.2.1) -
      (originalStageMainWindowCount R other z.1.1 + z.1.2.1))

/-- The actual excess-selected original index set is measurable, with no measurability callback. -/
theorem measurable_originalReserveSceneExcessKept (R : ℝ) (own other : Fin 2)
    {C : Set ℝ} (hC : MeasurableSet C) :
    Measurable (originalReserveSceneExcessKept (q := q) R own other C) := by
  have hown : Measurable (fun z : OriginalReserveSceneAux q ↦ originalStageMainWindowCount R own z.1.1) :=
    (measurable_originalStageMainWindowCount (q := q) R own).comp measurable_fst.fst
  have hother : Measurable (fun z : OriginalReserveSceneAux q ↦ originalStageMainWindowCount R other z.1.1) :=
    (measurable_originalStageMainWindowCount (q := q) R other).comp measurable_fst.fst
  have hsub : Measurable (fun p : ℕ × ℕ ↦ p.1 - p.2) := measurable_of_countable _
  exact measurable_originalReserveKeptNatIndices measurable_snd.fst measurable_snd.snd hC
    (hsub.comp ((hown.add measurable_snd.fst).prodMk (hother.add measurable_fst.snd.fst)))

/-- This measurable injection enumerates all and only the actual kept indices on its exact
kept-cardinality fibre. The fallback only makes the selector total outside that fibre. -/
def originalReserveSceneExcessSelection (R : ℝ) (own other : Fin 2) (C : Set ℝ) (k : ℕ)
    (z : OriginalReserveSceneAux q) : Fin k ↪ ℕ :=
  originalReserveFiniteSelection k (originalReserveSceneExcessKept R own other C z)

/-- Measurability of every actual original-coordinate choice is produced internally. -/
theorem measurable_originalReserveSceneExcessSelection_apply (R : ℝ) (own other : Fin 2)
    {C : Set ℝ} (hC : MeasurableSet C) (k : ℕ) (j : Fin k) :
    Measurable (fun z : OriginalReserveSceneAux q ↦ originalReserveSceneExcessSelection R own other C k z j) :=
  (measurable_originalReserveFiniteSelection_apply k j).comp
    (measurable_originalReserveSceneExcessKept R own other hC)

/-- The exact original kept-cardinality fibre is measurable. -/
theorem measurableSet_originalReserveSceneExcessKept_card (R : ℝ) (own other : Fin 2)
    {C : Set ℝ} (hC : MeasurableSet C) (k : ℕ) :
    MeasurableSet {z : OriginalReserveSceneAux q | (originalReserveSceneExcessKept R own other C z).card = k} :=
  MeasurableSet.preimage (measurableSet_singleton k) ((measurable_of_countable (fun s : Finset ℕ ↦ s.card)).comp
    (measurable_originalReserveSceneExcessKept R own other hC))

/-- The measured Nat selector is exactly the image of the unchanged original Fin reserve
indices in the verified actual source excess deletion. -/
theorem originalReserveSceneExcessKept_source_eq_original_indices {q : ℕ}
    (A : OriginalStageExcessRemovalData q) {R : ℝ} {scene : LegalMarkedOptimalInputScene q}
    (hmain : IsOriginalStageMainWindowArrays R scene A.sourceMain A.targetMain) :
    originalReserveSceneExcessKept R 0 1 A.firstClass
      ((scene, A.targetReserve), A.sourceReserve.1, fun i ↦ (A.sourceReserve.2 i).2) =
      A.sourceKept.map Fin.valEmbedding := by
  unfold originalReserveSceneExcessKept
  rw [← (A.sourceExcess_eq_actualSceneCounts hmain).1,
    originalReserveKeptNatIndices_eq_map_fin]
  rfl

/-- The analogous target selector retains exactly the original target Fin identities. -/
theorem originalReserveSceneExcessKept_target_eq_original_indices {q : ℕ}
    (A : OriginalStageExcessRemovalData q) {R : ℝ} {scene : LegalMarkedOptimalInputScene q}
    (hmain : IsOriginalStageMainWindowArrays R scene A.sourceMain A.targetMain) :
    originalReserveSceneExcessKept R 1 0 A.lastClass
      ((scene, A.sourceReserve), A.targetReserve.1, fun i ↦ (A.targetReserve.2 i).2) =
      A.targetKept.map Fin.valEmbedding := by
  unfold originalReserveSceneExcessKept
  rw [← (A.sourceExcess_eq_actualSceneCounts hmain).2,
    originalReserveKeptNatIndices_eq_map_fin]
  rfl

/-- On the actual kept-count fibre, the produced injection enumerates exactly all original
surviving reserve indices. No chosen position is a new or unobserved reserve point. -/
theorem originalReserveSceneExcessSelection_range (R : ℝ) (own other : Fin 2) (C : Set ℝ)
    (k : ℕ) (z : OriginalReserveSceneAux q)
    (hk : (originalReserveSceneExcessKept R own other C z).card = k) :
    Finset.univ.map (originalReserveSceneExcessSelection R own other C k z) =
      originalReserveSceneExcessKept R own other C z :=
  originalReserveFiniteSelection_range _ hk

/-- Every selected coordinate on the actual kept-count fibre is inside the observed original
finite prefix; the infinite sampler is used only to describe its original iid law. -/
theorem originalReserveSceneExcessSelection_observed (R : ℝ) (own other : Fin 2) (C : Set ℝ)
    (k : ℕ) (z : OriginalReserveSceneAux q)
    (hk : (originalReserveSceneExcessKept R own other C z).card = k) (j : Fin k) :
    originalReserveSceneExcessSelection R own other C k z j < z.2.1 := by
  have hmem : originalReserveSceneExcessSelection R own other C k z j ∈
      Finset.univ.map (originalReserveSceneExcessSelection R own other C k z) :=
    Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
  rw [originalReserveSceneExcessSelection_range R own other C k z hk] at hmem
  exact Finset.mem_range.mp (Finset.mem_sdiff.mp hmem).1

/-- In the actual independent reserve experiment, deletion by the original main scene counts,
marks and indices produces the exact iid joint spatial law on each actual kept-count fibre.
All measurability, index identities and count/mark factorization are constructed internally.
P may be the actual full-scene law times the independent other-color reserve cloud law. -/
theorem map_originalReserveSceneExcessSelection_actual_jointLaw
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsFiniteMeasure P]
    (α : Measure ℝ) [IsProbabilityMeasure α] (rate : ℝ≥0)
    (R : ℝ) (own other : Fin 2) {C : Set ℝ} (hC : MeasurableSet C) (k : ℕ) :
    ((P.prod (markedPoissonLaw q ℝ α rate)).restrict
      {p | (originalReserveSceneExcessKept R own other C
        ((p.1.1, p.1.2), p.2.1, fun i ↦ (p.2.2 i).2)).card = k}).map
      (fun p ↦ (((p.1.1, p.1.2), p.2.1, fun i ↦ (p.2.2 i).2),
        fun j : Fin k ↦ (p.2.2 (originalReserveSceneExcessSelection R own other C k
          ((p.1.1, p.1.2), p.2.1, fun i ↦ (p.2.2 i).2) j)).1)) =
      ((P.prod (originalReserveCountMarkLaw α rate)).restrict
        {z | (originalReserveSceneExcessKept R own other C z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  exact map_originalReserveSelectedPositions_joint_restrict_aux P q α rate
    (originalReserveSceneExcessSelection R own other C k)
    (measurable_originalReserveSceneExcessSelection_apply R own other hC k)
    (measurableSet_originalReserveSceneExcessKept_card R own other hC k)

end OTSelector.Reconstruction
