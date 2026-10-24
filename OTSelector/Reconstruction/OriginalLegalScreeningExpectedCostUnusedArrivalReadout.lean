import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostReserve
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingOriginalUnusedFamilies

/-! The genuine source/target reserve partitions and unchanged unused labels read into the actual cost budget. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- An empty fine spreading class has no selected original endpoint and zero
energy, regardless of the actual opposite block and excess deletion. -/
theorem originalReserveBlockClassOrientedAtomEnergy_empty_fine {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2) (S T C : Set ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    originalReserveBlockClassOrientedAtomEnergy b R own other S T C ∅ p = 0 := by
  have hN : originalReserveBlockClassCount (originalCenteredPhysicalCubeRegion b (2*R))
      own other S T C ∅ p = 0 := by
    simp [originalReserveBlockClassCount,originalReserveBlockClassKept]
  unfold originalReserveBlockClassOrientedAtomEnergy
  apply Finset.sum_eq_zero
  intro i _
  have hi : i.val < 0 := by simpa only [hN] using i.isLt
  omega

/-- The two actual own/opposite block conventions are kept separately. The
shared endpoint budget is indexed by their disjoint sum, with the unused color's
fine class empty; no source Ico block is identified with its target Ioc block. -/
def originalScreeningPartitionReserveEndpointEnergy {q : ℕ}
    {Bs Bt Is It : Type*} [Fintype Bs] [Fintype Bt] [Fintype Is] [Fintype It]
    (Hs : OriginalReserveFineBlockPartition Bs Is) (Ht : OriginalReserveFineBlockPartition Bt It)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  originalScreeningReserveEndpointEnergy b R
    (Sum.elim (fun i ↦ Hs.blockCell (Hs.blockFor i)) (fun i ↦ Ht.blockCell (Ht.blockFor i)))
    (Sum.elim (fun i ↦ Hs.oppositeCell (Hs.blockFor i)) (fun i ↦ Ht.oppositeCell (Ht.blockFor i)))
    (Sum.elim (fun i ↦ Hs.deletionCell (Hs.blockFor i)) (fun _ ↦ ∅))
    (Sum.elim (fun _ ↦ ∅) (fun i ↦ Ht.deletionCell (Ht.blockFor i)))
    (Sum.elim Hs.fineCell (fun _ ↦ ∅))
    (Sum.elim (fun _ ↦ ∅) Ht.fineCell) p

/-- The cost-budget readout is pointwise exactly the two genuine global
original-label RN energies, with their actual opposite-block order preserved. -/
theorem originalScreeningPartitionReserveEndpointEnergy_eq {q : ℕ}
    {Bs Bt Is It : Type*} [Fintype Bs] [Fintype Bt] [Fintype Is] [Fintype It]
    (Hs : OriginalReserveFineBlockPartition Bs Is) (Ht : OriginalReserveFineBlockPartition Bt It)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :
    originalScreeningPartitionReserveEndpointEnergy Hs Ht b R p =
      Hs.atomEnergy b R 0 1 (originalSourceReserveExperimentSplice p) +
        Ht.atomEnergy b R 1 0 (originalTargetReserveExperimentSplice p) := by
  rw [Hs.atomEnergy_eq_sum,Ht.atomEnergy_eq_sum]
  simp only [originalScreeningPartitionReserveEndpointEnergy,originalScreeningReserveEndpointEnergy,
    Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    originalReserveBlockClassOrientedAtomEnergy_empty_fine,add_zero,zero_add]

/-- The two unchanged unused families pay only actual ports and the two true
reserve RN energies. Target deviation uses the same physical Euclidean metric. -/
theorem originalScreeningUnusedArrival_energy_le_ports_add_reserve {q N : ℕ}
    {Bs Bt Is It X Y : Type*} [Fintype Bs] [Fintype Bt] [Fintype Is] [Fintype It]
    [Fintype X] [Fintype Y]
    (Hs : OriginalReserveFineBlockPartition Bs Is) (Ht : OriginalReserveFineBlockPartition Bt It)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)
    (Ps Pt : Measure (LegalMarkedPhysicalPoint q))
    (x : X → LegalMarkedPhysicalPoint q) (y : Y → LegalMarkedPhysicalPoint q)
    (sourceCell targetCell : Fin N → Set ℝ)
    (sourceArrival targetDeparture : Fin N → Measure (EuclideanSpace ℝ (Fin q)))
    (κ : X → Measure (EuclideanSpace ℝ (Fin q)))
    (τ : Y → Measure (EuclideanSpace ℝ (Fin q)))
    (hs : OriginalUnusedArrivalFamilySpec x sourceCell sourceArrival
      (Ps.real univ+Hs.atomEnergy b R 0 1 (originalSourceReserveExperimentSplice p)) κ)
    (ht : OriginalUnusedArrivalFamilySpec y targetCell targetDeparture
      (Pt.real univ+Ht.atomEnergy b R 1 0 (originalTargetReserveExperimentSplice p)) τ) :
    (∑ i, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2 ∂κ i) +
      (∑ j, ∫ v, dist v ((EuclideanSpace.equiv _ ℝ).symm (y j).1)^2 ∂τ j) ≤
        (Ps.real univ+Pt.real univ)+originalScreeningPartitionReserveEndpointEnergy Hs Ht b R p := by
  have ht' : (∑ j, ∫ v, dist v ((EuclideanSpace.equiv _ ℝ).symm (y j).1)^2 ∂τ j) ≤
      Pt.real univ+Ht.atomEnergy b R 1 0 (originalTargetReserveExperimentSplice p) := by
    simpa only [dist_comm] using ht.2.2.1
  rw [originalScreeningPartitionReserveEndpointEnergy_eq]
  linarith [hs.2.2.1,ht']

/-- The literal remaining-measure identity bounds the number of unused labels
by actual port mass plus the original raw reserve count. Finiteness of the port
measure is derived from that identity, rather than assumed as an extra input. -/
theorem originalScreeningUnused_count_le_port_add_raw
    {X I : Type*} [MeasurableSpace X] [Fintype I] {N : ℕ}
    (x : I → X) (y : Fin N → X) (kept : Finset (Fin N)) (ports : Measure X)
    (hcount : (∑ i, Measure.dirac (x i)) = ports+∑ j : kept, Measure.dirac (y j.val)) :
    (Fintype.card I : ℝ) ≤ ports.real univ+N := by
  have he : (Fintype.card I : ℝ≥0∞) = ports univ+kept.card := by
    simpa [Measure.finsetSum_apply] using congrArg (fun μ : Measure X ↦ μ univ) hcount
  have hp : ports univ ≠ (⊤ : ℝ≥0∞) := by
    apply ne_top_of_le_ne_top (by simp : (Fintype.card I : ℝ≥0∞) ≠ ⊤)
    rw [he]
    exact le_add_of_nonneg_right bot_le
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add hp (by simp)] at hr
  have hcard : (Fintype.card I : ℝ) = ports.real univ+kept.card := by
    simpa only [ENNReal.toReal_natCast,measureReal_def] using hr
  rw [hcard]
  have hc : (kept.card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using Finset.card_le_univ kept)
  exact add_le_add le_rfl hc

end OTSelector.Reconstruction
