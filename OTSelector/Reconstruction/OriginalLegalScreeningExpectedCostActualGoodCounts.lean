import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostCutFailures
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorActualSignedMaximumObjects

/-! The complement of the genuine full joint exception supplies every literal screening good count. -/
open Set Function MeasureTheory Module Manifold
open scoped BigOperators ENNReal Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

omit [BorelSpace E] in
/-- Actual joint failure exclusion gives the exact reserve capacities, raw
prefix counts, summed genuine excess deletion and original full-current cut
errors used by the automatic legal matcher. No count, balance or rate is supplied. -/
theorem originalScreeningActualGoodCounts_of_not_allFailure
    (P : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    (G : OriginalStageClockGrid)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R rawRate e : ℝ)
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)
    (hp : p ∉ originalScreeningAllFailure S w μ ν P b rawRate R G e
      (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e)) :
    OriginalClockBlockGoodCounts S w G μ ν b R rawRate e p := by
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  have hncap : p ∉ originalMainReserveClockSlabCapacityFailure μ ν b R G :=
    fun h ↦ hp (Or.inr (Or.inr h))
  have hnres : p ∉ originalScreeningReserveBlockFailure μ ν b rawRate R G e :=
    fun h ↦ hp (Or.inr (Or.inl h))
  let ES := fun block : G.ClockSlabBlock μ ν ↦ originalReserveBlockExcess K 0 1
    (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
    ((p.1,p.2.2),p.2.1.1,fun i ↦ (p.2.1.2 i).2)
  let ET := fun block : G.ClockSlabBlock μ ν ↦ originalReserveBlockExcess K 1 0
    (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
    ((p.1,p.2.1),p.2.2.1,fun i ↦ (p.2.2.2 i).2)
  have hsum : (((∑ block : G.ClockSlabBlock μ ν, (ES block+ET block)) : ℕ) : ℝ) =
      originalFullClockSlabDiscrepancy (α := μ) (β := ν) G K p := by
    rw [Nat.cast_sum]
    unfold originalFullClockSlabDiscrepancy
    apply Finset.sum_congr rfl
    intro block _
    rw [Nat.cast_add]
    simpa only [ES,ET,originalReserveExcessInputAux,originalSourceReserveExperimentSplice,
      originalTargetReserveExperimentSplice] using originalReserveBlockExcess_sum_eq_fullDiscrepancy K
        (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block) p
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro block
    apply le_of_not_gt
    intro h
    exact hncap ⟨block,Or.inl h⟩
  · intro block
    apply le_of_not_gt
    intro h
    exact hncap ⟨block,Or.inr h⟩
  · intro k
    apply le_of_not_gt
    intro h
    exact hnres (Or.inl ⟨k,Or.inl h⟩)
  · intro k
    apply le_of_not_gt
    intro h
    exact hnres (Or.inl ⟨k,Or.inr h⟩)
  · change (((∑ block : G.ClockSlabBlock μ ν, (ES block+ET block)) : ℕ) : ℝ) ≤ e*volume.real K
    rw [hsum]
    apply le_of_not_gt
    intro h
    exact hnres (Or.inr h)
  · intro k
    have hcut : p.1 ∉ originalScreeningActualCutBadEnvelope S w P b R (G.cut k.val) e := by
      intro h
      exact hp (Or.inl (Set.mem_iUnion.mpr ⟨k,h⟩))
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    exact hcut ((originalScreeningActualCutBadEnvelope_spec S w P b R (G.cut k.val) e).2.1 h)

end OTSelector.Reconstruction
