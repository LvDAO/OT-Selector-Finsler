import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockSelection

/-! Stage-class original coordinates after actual balanced-block excess deletion. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ}

/-- The fine spreading class is filtered after deleting this block's excess;
the deletion class C and spreading class D are independent arguments. -/
def originalReserveBlockClassKept (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C D : Set ℝ) (z : OriginalReserveSceneAux q) : Finset ℕ :=
  (originalReserveBlockKept K own other S T C z).filter (fun i ↦ z.2.2 i ∈ D)

theorem measurable_originalReserveBlockClassKept {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (own other : Fin 2) {S T C D : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D) :
    Measurable (originalReserveBlockClassKept K own other S T C D) := by
  apply measurable_finset_iff.mpr
  intro i
  apply measurableSet_setOfPred.mp
  have hmem : MeasurableSet {z : OriginalReserveSceneAux q |
      i ∈ originalReserveBlockKept K own other S T C z} :=
    measurableSet_setOfPred.mpr ((measurable_finset_mem i).comp
      (measurable_originalReserveBlockKept hK own other hS hT hC))
  have heq : {z : OriginalReserveSceneAux q | i ∈ originalReserveBlockClassKept K own other S T C D z} =
      {z | i ∈ originalReserveBlockKept K own other S T C z} ∩ {z | z.2.2 i ∈ D} := by
    ext z
    simp [originalReserveBlockClassKept]
  rw [heq]
  exact hmem.inter (hD.preimage ((measurable_pi_apply i).comp measurable_snd.snd))

/-- Original Fin indices retained in one actual block, before spreading. -/
def originalReserveBlockKeptFin (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : Set ℝ) (z : OriginalReserveSceneAux q) : Finset (Fin z.2.1) :=
  (Finset.univ.filter (fun i ↦ z.2.2 i ∈ S)) \
    originalStageMarkInitialIndices (fun i ↦ z.2.2 i) C (originalReserveBlockExcess K own other S T z)

theorem originalReserveBlockKept_eq_map_fin (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : Set ℝ) (z : OriginalReserveSceneAux q) :
    originalReserveBlockKept K own other S T C z =
      (originalReserveBlockKeptFin K own other S T C z).map Fin.valEmbedding := by
  rw [originalReserveBlockKept, originalReserveClassNatIndices_eq_map_fin,
    originalReserveDeletedNatIndices_eq_map_fin, ← Finset.map_sdiff]
  rfl

/-- Fine-class selection preserves the exact original Fin sampler identities. -/
theorem originalReserveBlockClassKept_eq_map_fin (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C D : Set ℝ) (z : OriginalReserveSceneAux q) :
    originalReserveBlockClassKept K own other S T C D z =
      ((originalReserveBlockKeptFin K own other S T C z).filter
        (fun i : Fin z.2.1 ↦ z.2.2 i ∈ D)).map Fin.valEmbedding := by
  rw [originalReserveBlockClassKept, originalReserveBlockKept_eq_map_fin, Finset.filter_map]
  rfl

/-- The selected count is literally the h_D used by stage density formulas. -/
theorem originalReserveBlockClassKept_card_eq_density_count (K : Set (Fin q → ℝ))
    (own other : Fin 2) (S T C D : Set ℝ) (z : OriginalReserveSceneAux q)
    (positions : ℕ → Fin q → ℝ) :
    (originalReserveBlockClassKept K own other S T C D z).card =
      originalStageRemainingReserveClassCount ⟨z.2.1,fun i ↦ (positions i,z.2.2 i)⟩
        (originalReserveBlockKeptFin K own other S T C z) D := by
  rw [originalReserveBlockClassKept_eq_map_fin, Finset.card_map]
  rfl

def originalReserveBlockClassSelection (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C D : Set ℝ) (k : ℕ) (z : OriginalReserveSceneAux q) : Fin k ↪ ℕ :=
  originalReserveFiniteSelection k (originalReserveBlockClassKept K own other S T C D z)

theorem measurable_originalReserveBlockClassSelection_apply {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (own other : Fin 2) {S T C D : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (k : ℕ) (j : Fin k) :
    Measurable (fun z ↦ originalReserveBlockClassSelection K own other S T C D k z j) :=
  (measurable_originalReserveFiniteSelection_apply k j).comp
    (measurable_originalReserveBlockClassKept hK own other hS hT hC hD)

theorem originalReserveBlockClassSelection_range (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C D : Set ℝ) (k : ℕ) (z : OriginalReserveSceneAux q)
    (hk : (originalReserveBlockClassKept K own other S T C D z).card = k) :
    Finset.univ.map (originalReserveBlockClassSelection K own other S T C D k z) =
      originalReserveBlockClassKept K own other S T C D z := originalReserveFiniteSelection_range _ hk

theorem originalReserveBlockClassSelection_observed_mark (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C D : Set ℝ) (k : ℕ) (z : OriginalReserveSceneAux q)
    (hk : (originalReserveBlockClassKept K own other S T C D z).card = k) (j : Fin k) :
    originalReserveBlockClassSelection K own other S T C D k z j < z.2.1 ∧
      z.2.2 (originalReserveBlockClassSelection K own other S T C D k z j) ∈ D := by
  have hm : originalReserveBlockClassSelection K own other S T C D k z j ∈
      Finset.univ.map (originalReserveBlockClassSelection K own other S T C D k z) :=
    Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩
  rw [originalReserveBlockClassSelection_range K own other S T C D k z hk] at hm
  have h := Finset.mem_filter.mp hm
  exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp h.1).1).1,h.2⟩

/-- Actual Poisson inputs produce the fine-class iid law after real blockwise
deletion. No spatial law, index injection or independence is assumed as an input. -/
theorem map_originalReserveBlockClassSelection_actual_jointLaw
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsFiniteMeasure P]
    (α : Measure ℝ) [IsProbabilityMeasure α] (rate : ℝ≥0)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (own other : Fin 2)
    {S T C D : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    ((P.prod (markedPoissonLaw q ℝ α rate)).restrict
      {p | (originalReserveBlockClassKept K own other S T C D
        ((p.1.1,p.1.2),p.2.1,fun i ↦ (p.2.2 i).2)).card = k}).map
      (fun p ↦ (((p.1.1,p.1.2),p.2.1,fun i ↦ (p.2.2 i).2),
        fun j : Fin k ↦ (p.2.2 (originalReserveBlockClassSelection K own other S T C D k
          ((p.1.1,p.1.2),p.2.1,fun i ↦ (p.2.2 i).2) j)).1)) =
      ((P.prod (originalReserveCountMarkLaw α rate)).restrict
        {z | (originalReserveBlockClassKept K own other S T C D z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  exact map_originalReserveSelectedPositions_joint_restrict_aux P q α rate
    (originalReserveBlockClassSelection K own other S T C D k)
    (measurable_originalReserveBlockClassSelection_apply hK own other hS hT hC hD k)
    ((measurableSet_singleton k).preimage
      ((measurable_of_countable (fun s : Finset ℕ ↦ s.card)).comp
        (measurable_originalReserveBlockClassKept hK own other hS hT hC hD)))

end OTSelector.Reconstruction
