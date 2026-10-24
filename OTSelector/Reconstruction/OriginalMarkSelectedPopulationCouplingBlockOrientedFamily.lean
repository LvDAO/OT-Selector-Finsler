import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedFamilyPartition

/-! One RN family lives on the unchanged global original kept reserve labels. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
namespace OriginalReserveFineBlockPartition
variable {q : ℕ} {B I : Type*} [Fintype B] [Fintype I]
  (H : OriginalReserveFineBlockPartition B I)

def fineAtomLaw (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (a : Σ i, Fin (H.fineCount (originalCenteredPhysicalCubeRegion b (2*R)) own other
      (originalReserveExcessInputAux p) i)) : Measure (EuclideanSpace ℝ (Fin q)) :=
  originalReserveBlockClassOrientedAtomLaw b R own other (H.blockCell (H.blockFor a.1))
    (H.oppositeCell (H.blockFor a.1)) (H.deletionCell (H.blockFor a.1)) (H.fineCell a.1) p a.2

/-- Pull each true fine-class RN law to its unchanged original global label. -/
def atomLaw (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (a : originalReserveBlocksKeptFin (originalCenteredPhysicalCubeRegion b (2*R)) own other
      H.blockCell H.oppositeCell H.deletionCell (originalReserveExcessInputAux p)) :
    Measure (EuclideanSpace ℝ (Fin q)) :=
  H.fineAtomLaw b R own other p
    (H.indexEquiv (originalCenteredPhysicalCubeRegion b (2*R)) own other (originalReserveExcessInputAux p) a)

def atomPoint (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (a : originalReserveBlocksKeptFin (originalCenteredPhysicalCubeRegion b (2*R)) own other
      H.blockCell H.oppositeCell H.deletionCell (originalReserveExcessInputAux p)) : EuclideanSpace ℝ (Fin q) :=
  (EuclideanSpace.equiv (Fin q) ℝ).symm (originalOrientedRawCubePhysicalMap b R (p.2.2 a.val).1)

def atomEnergy (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) : ℝ :=
  ∑ a, ∫ v, dist (H.atomPoint b R own other p a) v^2 ∂H.atomLaw b R own other p a

/-- Relabeling preserves the actual endpoint energy, pointwise on every input. -/
theorem atomEnergy_eq_sum (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    H.atomEnergy b R own other p = ∑ i, originalReserveBlockClassOrientedAtomEnergy b R own other
      (H.blockCell (H.blockFor i)) (H.oppositeCell (H.blockFor i)) (H.deletionCell (H.blockFor i)) (H.fineCell i) p := by
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  let z := originalReserveExcessInputAux p
  have hh := originalIndexEquiv_sum_pullback
    (fun a : originalReserveBlocksKeptFin K own other H.blockCell H.oppositeCell H.deletionCell z ↦ a.val.val)
    (H.selectedIndex K own other z) (H.indexEquiv K own other z) (H.indexEquiv_apply K own other z)
    (fun n a ↦ ∫ v, dist ((EuclideanSpace.equiv (Fin q) ℝ).symm
      (originalOrientedRawCubePhysicalMap b R (p.2.2 n).1)) v^2 ∂H.fineAtomLaw b R own other p a)
  rw [Fintype.sum_sigma] at hh
  simpa only [atomEnergy, atomPoint, atomLaw, fineAtomLaw,
    originalReserveBlockClassOrientedAtomEnergy, originalReserveBlockClassOrientedAtomPoint,
    originalReserveBlockClassInputReadout, originalReserveBlockClassCount, selectedIndex, fineCount, K, z] using hh

/-- Every fine-class law sum is exactly the restriction of the same global
family by its unchanged original mark. -/
theorem atomLaw_class_sum (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) (i : I) :
    (∑ a, if (p.2.2 a.val).2 ∈ H.fineCell i then H.atomLaw b R own other p a else 0) =
      ∑ a, originalReserveBlockClassOrientedAtomLaw b R own other (H.blockCell (H.blockFor i))
        (H.oppositeCell (H.blockFor i)) (H.deletionCell (H.blockFor i)) (H.fineCell i) p a := by
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  let z := originalReserveExcessInputAux p
  have hh := originalIndexEquiv_sum_pullback
    (fun a : originalReserveBlocksKeptFin K own other H.blockCell H.oppositeCell H.deletionCell z ↦ a.val.val)
    (H.selectedIndex K own other z) (H.indexEquiv K own other z) (H.indexEquiv_apply K own other z)
    (fun n a ↦ if (p.2.2 n).2 ∈ H.fineCell i then H.fineAtomLaw b R own other p a else 0)
  refine hh.trans ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro a _
    have hm := (H.selectedIndex_mark K own other z ⟨i,a⟩).2
    simpa only [fineAtomLaw, selectedIndex, fineCount, z, originalReserveExcessInputAux] using
      (show (if (p.2.2 (H.selectedIndex K own other z ⟨i,a⟩)).2 ∈ H.fineCell i then
        H.fineAtomLaw b R own other p ⟨i,a⟩ else 0) = H.fineAtomLaw b R own other p ⟨i,a⟩ by
        simp [show (p.2.2 (H.selectedIndex K own other z ⟨i,a⟩)).2 ∈ H.fineCell i from hm])
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro a _
    have hm := (H.selectedIndex_mark K own other z ⟨j,a⟩).2
    have hn : (p.2.2 (H.selectedIndex K own other z ⟨j,a⟩)).2 ∉ H.fineCell i :=
      fun hi ↦ disjoint_left.mp (H.fine_disjoint hji) hm hi
    simp [hn]
  · simp

/-- The density coefficient is the literal global kept original Fin count. -/
theorem globalClassCount_eq (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) (i : I) :
    originalStageRemainingReserveClassCount p.2
      (originalReserveBlocksKeptFin K own other H.blockCell H.oppositeCell H.deletionCell
        (originalReserveExcessInputAux p)) (H.fineCell i) =
      H.fineCount K own other (originalReserveExcessInputAux p) i :=
  originalReserveBlocksKeptFin_class_count K own other H.blockCell H.oppositeCell H.deletionCell
    H.block_disjoint (originalReserveExcessInputAux p) (fun n ↦ (p.2.2 n).1)
    (H.blockFor i) (H.fine_subset_block i)

def AtomSpec (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) : Prop :=
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  (∀ a, IsProbabilityMeasure (H.atomLaw b R own other p a)) ∧
    (∀ a, Integrable (fun v ↦ dist (H.atomPoint b R own other p a) v^2) (H.atomLaw b R own other p a)) ∧
    ∀ i, (∑ a, if (p.2.2 a.val).2 ∈ H.fineCell i then H.atomLaw b R own other p a else 0) =
      ((volume.restrict K).withDensity (fun _ ↦ ENNReal.ofReal
        ((originalStageRemainingReserveClassCount p.2 (originalReserveBlocksKeptFin K own other
          H.blockCell H.oppositeCell H.deletionCell (originalReserveExcessInputAux p)) (H.fineCell i) : ℝ) /
          volume.real K))).map (EuclideanSpace.equiv (Fin q) ℝ).symm

theorem atomSpec_of_fineSpecs (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (hf : ∀ i, OriginalReserveBlockClassOrientedAtomSpec b R own other (H.blockCell (H.blockFor i))
      (H.oppositeCell (H.blockFor i)) (H.deletionCell (H.blockFor i)) (H.fineCell i) p) :
    H.AtomSpec b R own other p := by
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  let z := originalReserveExcessInputAux p
  refine ⟨fun a ↦ (hf (H.indexEquiv K own other z a).1).1 (H.indexEquiv K own other z a).2, ?_, ?_⟩
  · intro a
    have he := H.indexEquiv_apply K own other z a
    have hh := (hf (H.indexEquiv K own other z a).1).2.2.1 (H.indexEquiv K own other z a).2
    change Integrable (fun v ↦ dist ((EuclideanSpace.equiv (Fin q) ℝ).symm
      (originalOrientedRawCubePhysicalMap b R (p.2.2 a.val.val).1)) v^2) _
    rw [he]
    exact hh
  · intro i
    rw [H.atomLaw_class_sum, H.globalClassCount_eq]
    exact (hf i).2.1

end OriginalReserveFineBlockPartition
end OTSelector.Reconstruction
