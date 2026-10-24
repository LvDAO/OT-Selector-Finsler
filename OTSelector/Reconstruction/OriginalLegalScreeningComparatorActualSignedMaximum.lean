import OTSelector.Reconstruction.OriginalLegalScreeningComparatorActualSignedMaximumObjects
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorActualSignedMaximumRepairs
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedUniformOriginalCore
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockZeroAtomsJoint
import OTSelector.Finite.MatchingGlobalDeletedCounts
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockOriginalLabels
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingOriginalUnusedFamiliesExtension

/-! The actual unit matching and original raw reserves construct a signed legal maximum. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped BigOperators ENNReal Classical ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

private theorem actual_nat_dist_cast (a d : ℕ) : (Nat.dist a d : ℝ) = |(a : ℝ)-d| := by
  rcases le_total a d with h | h
  · rw [Nat.dist_eq_sub_of_le h,Nat.cast_sub h,abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h,Nat.cast_sub h,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

/-- The genuine retained core, actual global reserve deletion, original RN
families, real scalar floors and Neumann stages construct the same original
array's legal maximum. Neither a finished stage plan nor a local bijection is
assumed. The focal coefficient remains independent of the reserve intensity. -/
theorem originalActualClockBlock_signedMaximumProducer
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ} {Gbound C : ℝ} (hC : 0 ≤ C) (hGbound : 0 ≤ Gbound)
    (hphysical : ∀ (a d : ℝ) (x y : Fin (finrank ℝ S.covector.ker) → ℝ) (t : ℝ),
      D.originalFocalKinetic gap a d (y-x)-t*g a d ≤
        C*dist ((EuclideanSpace.equiv _ ℝ).symm x) ((EuclideanSpace.equiv _ ℝ).symm y)^2+|t| *Gbound)
    (tilt : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g)
    (G : OriginalStageClockGrid)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) (ht : ∀ᵐ y ∂ν, y ∈ ⋃ i, G.targetCell i)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {θ : ℝ} (hθ : 0 < θ)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _)) :
    OriginalActualClockBlockSignedMaximumProducer Q G h₀ hN b θ C (|tilt| *Gbound) tilt hj := by
  obtain ⟨e,he,ρ,hρ,hfloors⟩ := D.exists_actualClockBlock_stage_scalar_floors hF hw Q G hgap hbounds hs ht hmono hθ b
  refine ⟨e,he,ρ,hρ,?_⟩
  intro R ell hell hR
  have hRone : 1 ≤ R := by nlinarith [one_le_originalStageFrameCollarFactor b]
  have hRpos : 0 < R := by linarith
  obtain ⟨K,hK,hrepairs⟩ := D.exists_actualClockBlock_signedMaximum_of_unused_families
    hF hw (by omega) hgap hbounds Q G hs ht hmono h₀ hN b hell hR hj
  let rate := Real.toNNReal θ*(volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal
  have hc := ae_fst_of_ae (ν := twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν rate)
    (D.ae_exists_originalFullIndex_orientedPathRetainedCore_uniform_deletions hF hw Q b (by linarith) hR)
  have hp := ae_fst_of_ae (ν := twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν rate) hrepairs
  have hsigma := ae_fst_of_ae (ν := twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν rate)
    (Q.ae_originalIndex_edges_same_clockBlockLabel G hgap hbounds hs ht hmono h₀ hN)
  have hf := ae_fst_of_ae (ν := twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν rate) (hfloors R ell hell hR)
  refine ⟨K,hK,?_⟩
  filter_upwards [hc,hp,hsigma,hf,Q.ae_all_originalUnused_zeroClockBlock_filters rate G,
    D.ae_originalUnusedBlockArrivalFamilies hF hw Q b G h₀ hN hq hRone (by linarith) hR hθ.le]
    with p hcore hrepair hsame hfloor hzero hfamilies
  intro hgood m n X
  let A := originalUnusedBlockReserveData S w b R ell G h₀ hN p
  let source := A.sourceReserve
  let target := A.targetReserve
  let Cs := fun block : G.ClockSlabBlock μ ν ↦ G.sourceCell (G.firstBlockClass block)
  let Ct := fun block : G.ClockSlabBlock μ ν ↦ G.targetCell (G.lastBlockClass block)
  have hCs (block) : Cs block ⊆ G.sourceBlockCell μ ν block := by
    intro a ha
    apply (G.mem_sourceBlockCell_iff block ha).mpr
    change block.lower.val ≤ block.lower.val ∧ block.lower.val < block.upper.val
    exact ⟨le_rfl,block.consecutive.1⟩
  have hCt (block) : Ct block ⊆ G.targetBlockCell μ ν block := by
    intro a ha
    apply (G.mem_targetBlockCell_iff block ha).mpr
    change block.lower.val ≤ block.upper.val-1 ∧ block.upper.val-1 < block.upper.val
    have hh := block.consecutive.1
    omega
  have hcapS : ∀ block, originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
      (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
      ((p.1,target),source.1,fun i ↦ (source.2 i).2) ≤
        originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (Cs block) := hgood.source_capacity
  have hcapT : ∀ block, originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
      (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
      ((p.1,source),target.1,fun i ↦ (target.2 i).2) ≤
        originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (Ct block) := hgood.target_capacity
  have hscene : A.scene = p.1 := rfl
  have hsourceN : source.1 = p.2.1.1 := rfl
  have htargetN : target.1 = p.2.2.1 := rfl
  have hsourceMark : (fun i ↦ (source.2 i).2) = (fun i ↦ (p.2.1.2 i).2) := rfl
  have htargetMark : (fun i ↦ (target.2 i).2) = (fun i ↦ (p.2.2.2 i).2) := rfl
  have hExS (block : G.ClockSlabBlock μ ν) :
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
        (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
        ((p.1,target),source.1,fun i ↦ (source.2 i).2) =
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
        (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
        ((p.1,p.2.2),p.2.1.1,fun i ↦ (p.2.1.2 i).2) := rfl
  have hExT (block : G.ClockSlabBlock μ ν) :
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
        (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
        ((p.1,source),target.1,fun i ↦ (target.2 i).2) =
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
        (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
        ((p.1,p.2.1),p.2.2.1,fun i ↦ (p.2.2.2 i).2) := rfl
  have hf := hfloor source target Cs Ct hCs hCt hcapS hcapT
    (by simpa only [OriginalOrientedStageResidualDensityData.cubeVolume,
      OriginalOrientedStageResidualDensityData.cubeMeasure,measureReal_restrict_apply_univ,hsourceN,hsourceMark] using hgood.source_prefix)
    (by simpa only [OriginalOrientedStageResidualDensityData.cubeVolume,
      OriginalOrientedStageResidualDensityData.cubeMeasure,measureReal_restrict_apply_univ,htargetN,htargetMark] using hgood.target_prefix)
    (by simpa only [OriginalOrientedStageResidualDensityData.cubeVolume,
      OriginalOrientedStageResidualDensityData.cubeMeasure,measureReal_restrict_apply_univ,hExS,hExT] using hgood.deletions)
    (by simpa only [OriginalOrientedStageResidualDensityData.cubeVolume,
      OriginalOrientedStageResidualDensityData.cubeMeasure,measureReal_restrict_apply_univ] using hgood.cuts)
  let cost : Fin m → Fin n → ℝ := fun i j ↦
    originalWeightedEdgeCost (D.originalFocalKinetic gap) g tilt (X.source i,X.target j)
  obtain ⟨σ,hσ,hplan,_,hcoreCost,_,_,hdeletions⟩ := hcore m n source.1 target.1 X.source X.target
    (fun j ↦ source.2 j) (fun j ↦ target.2 j) X.sourceEmbedding X.targetEmbedding
    X.source_injective X.target_injective X.source_original X.target_original
    X.source_counting X.target_counting (originalWeightedEdgeCost (D.originalFocalKinetic gap) g tilt)
  let Ds := Finset.univ \ A.sourceKept
  let Dt := Finset.univ \ A.targetKept
  let U := σ.freeRows \ Ds.map X.sourceEmbedding
  let V := σ.freeCols \ Dt.map X.targetEmbedding
  obtain ⟨hDs,hDt,hU,hV,hcountS,hcountT⟩ := hdeletions Ds Dt
  have hcountS' : (∑ i : U,Measure.dirac (X.source i.val)) = A.sourcePortMeasure+
      ∑ j : A.sourceKept,Measure.dirac (source.2 j.val) := by
    rw [Finset.sum_coe_sort U (fun i ↦ Measure.dirac (X.source i)),
      Finset.sum_coe_sort A.sourceKept (fun j ↦ Measure.dirac (source.2 j))]
    have hr : Finset.univ \ Ds = A.sourceKept := Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
    simpa only [hr,U,OriginalOrientedStageResidualDensityData.sourcePortMeasure,hscene] using hcountS
  have hcountT' : (∑ j : V,Measure.dirac (X.target j.val)) = A.targetPortMeasure+
      ∑ j : A.targetKept,Measure.dirac (target.2 j.val) := by
    rw [Finset.sum_coe_sort V (fun j ↦ Measure.dirac (X.target j)),
      Finset.sum_coe_sort A.targetKept (fun j ↦ Measure.dirac (target.2 j))]
    have hr : Finset.univ \ Dt = A.targetKept := Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
    simpa only [hr,V,OriginalOrientedStageResidualDensityData.targetPortMeasure,hscene] using hcountT
  obtain ⟨κ,hκ⟩ := hfamilies.exists_source_fullFamily U X.source hcountS'
  obtain ⟨τ,hτ⟩ := hfamilies.exists_target_fullFamily V X.target hcountT'
  have hsameσ := hsame (originalOrientedPathLengthRetained S w b R ell) m n X.source X.target
    X.source_grid X.target_grid σ hplan
  let c := fun i ↦ G.sourceBlockLabel h₀ hN (X.source i).2 (X.source_grid i)
  let d := fun j ↦ G.targetBlockLabel h₀ hN (X.target j).2 (X.target_grid j)
  have hdcard := originalClockBlocks_mapped_global_deletion_cards G h₀ hN
    (originalCenteredPhysicalCubeRegion b (2*R)) p.1 source target Cs Ct hCs hCt hcapS hcapT
    X.source X.target X.source_grid X.target_grid X.sourceEmbedding X.targetEmbedding
    (fun j ↦ congrArg Prod.snd (X.source_original j)) (fun j ↦ congrArg Prod.snd (X.target_original j))
    X.source_blocks X.target_blocks
  have hcounts := PartialMatching.originalGlobalDeletedUnused_count_spec σ c d hsameσ
    (Ds.map X.sourceEmbedding) (Dt.map X.targetEmbedding) hDs hDt
    (fun block ↦ (hdcard block).1) (fun block ↦ (hdcard block).2)
  have hzeroσ := hzero m n X.source X.target U V (fun j ↦ source.2 j) (fun j ↦ target.2 j)
    (fun _ ↦ rfl) (fun _ ↦ rfl) A.sourceKept A.targetKept
    (originalOrientedPathLengthRetained S w b R ell) (originalCenteredPhysicalCubeRegion b (2*R))
    (by
      have hr : Finset.univ \ Ds = A.sourceKept := Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
      have hh := hcountS
      rw [hr] at hh
      convert hh using 1; congr)
    (by
      have hr : Finset.univ \ Dt = A.targetKept := Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
      have hh := hcountT
      rw [hr] at hh
      convert hh using 1; congr)
  have hρfloors (block) (hb : block ∈ G.positiveSlabBlocks μ ν) := hf block hb
  have hγ (block) (hb : block ∈ G.positiveSlabBlocks μ ν)
      (k : ℕ) (hl : block.lower.val ≤ k) (hu : k ≤ block.upper.val) : 0 ≤ A.gamma (G.cut k) := by
    have hk : k < G.count+1 := by have hh := block.upper.isLt; omega
    exact (hρfloors block hb).2.2.2.2.1 ⟨k,hk⟩ hl hu
  have hscalar (block) (hb : block ∈ G.positiveSlabBlocks μ ν)
      (k : Fin (block.upper.val-block.lower.val)) :=
    (hρfloors block hb).2.2.2.2.2
      (⟨block.lower.val+k.val,by have hh := block.upper.isLt; have hk := k.isLt; omega⟩ : Fin G.count)
      (by constructor <;> have hk := k.isLt <;> dsimp only <;> omega)
  let L := |tilt| *Gbound
  let coarse := 4*C*(finrank ℝ S.covector.ker : ℝ)*R^2+L
  have hL : 0 ≤ L := mul_nonneg (abs_nonneg _) hGbound
  have hcoarse : 0 ≤ coarse := add_nonneg (mul_nonneg (by positivity) (sq_nonneg R)) hL
  have hnew (i j) : cost i j ≤ C*dist ((EuclideanSpace.equiv _ ℝ).symm (X.source i).1)
      ((EuclideanSpace.equiv _ ℝ).symm (X.target j).1)^2+L := by
    simpa only [cost,originalWeightedEdgeCost,abs_neg,neg_mul,sub_neg_eq_add,L] using
      hphysical (X.source i).2 (X.target j).2 (X.source i).1 (X.target j).1 (-tilt)
  have hcross (i j) (_ : (c i).lower < (d j).lower) : cost i j ≤ coarse := by
    have hdiam := originalOrientedPhysicalCube_square_distance_le b hRpos.le (X.source_carrier i) (X.target_carrier j)
    have hd := mul_le_mul_of_nonneg_left hdiam hC
    dsimp only [coarse]
    nlinarith only [hnew i j,hd]
  obtain ⟨γ,hγ,hmax,hkeep,hγcost⟩ := hrepair source target Cs Ct hCs hCt hcapS hcapT ρ hρ
    (fun block hb ↦ ⟨hγ block hb,hscalar block hb⟩) m n X.source X.target
    X.source_grid X.target_grid X.monochrome σ hσ hsameσ U V hU hV
    (fun block ↦ (hcounts.2.2 block).1) hzeroσ κ τ hκ.1 hτ.1 hκ.2.1
    (fun j ↦ by simpa only [dist_comm] using hτ.2.1 j) hκ.2.2.1.2.2.2 hτ.2.2.1.2.2.2
    cost C L coarse hC hcoarse hnew hcross
  refine ⟨σ,γ,hplan,hkeep,hγ,hmax,?_⟩
  have henergy := originalScreeningUnusedArrival_energy_le_ports_add_reserve
    (G.sourceReserveFineBlockPartition h₀ hN) (G.targetReserveFineBlockPartition h₀ hN) b R p
    A.sourcePortMeasure A.targetPortMeasure (fun i : U ↦ X.source i.val) (fun j : V ↦ X.target j.val)
    G.sourceCell G.targetCell _ _ (fun i ↦ κ i.val) (fun j ↦ τ j.val) hκ.2.2.1 hτ.2.2.1
  have hcard := originalScreeningUnused_count_le_port_add_raw
    (fun i : U ↦ X.source i.val) (fun j ↦ source.2 j) A.sourceKept A.sourcePortMeasure hcountS'
  have hcard' : (U.card : ℝ) ≤ originalScreeningRepairCountBudget S w b R ell p := by
    have hpT : 0 ≤ A.targetPortMeasure.real univ := ENNReal.toReal_nonneg
    have hnT : 0 ≤ (p.2.2.1 : ℝ) := Nat.cast_nonneg _
    simp only [Fintype.card_coe] at hcard
    have hb : originalScreeningRepairCountBudget S w b R ell p =
        A.sourcePortMeasure.real univ+A.targetPortMeasure.real univ+((p.2.1.1 : ℝ)+(p.2.2.1 : ℝ)) := by
      simp only [originalScreeningRepairCountBudget,OriginalOrientedStageResidualDensityData.sourcePortMeasure,
        OriginalOrientedStageResidualDensityData.targetPortMeasure,measureReal_def,Measure.fst_univ,Measure.snd_univ]
      rfl
    rw [hb]
    change (U.card : ℝ) ≤ A.sourcePortMeasure.real univ+(p.2.1.1 : ℝ) at hcard
    linarith
  have hdiscrep : ((∑ block : G.ClockSlabBlock μ ν,
      Nat.dist (Finset.univ.filter (fun i ↦ c i = block)).card
        (Finset.univ.filter (fun j ↦ d j = block)).card : ℕ) : ℝ) =
      originalFullClockSlabDiscrepancy (α := μ) (β := ν) G (originalCenteredPhysicalCubeRegion b (2*R)) p := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro block _
    rw [G.sourceBlockLabel_filter_eq_clock_filter h₀ hN X.source X.source_grid,
      G.targetBlockLabel_filter_eq_clock_filter h₀ hN X.target X.target_grid,
      X.source_blocks block,X.target_blocks block]
    rw [actual_nat_dist_cast]
    simp only [originalFullBlockDiscrepancy,originalReserveObservedBlockCount_eq_natCount,Nat.cast_add]
  have henergy' := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 3*C by positivity)
  have hcard'' := mul_le_mul_of_nonneg_left hcard' hL
  rw [hdiscrep,← hcoreCost] at hγcost
  change γ.cost cost ≤ originalActualClockBlockSignedMaximumBudget Q G h₀ hN b K R ell ρ C L tilt hj p
  dsimp only [originalActualClockBlockSignedMaximumBudget]
  linarith only [hγcost,henergy',hcard'']

/-- The genuine focal quadratic constant is selected before the tilt,
original matching, reserve intensity and physical frame. All stage transport,
original smoothing laws and maximum matching witnesses are internal. -/
theorem exists_originalActualClockBlock_signedMaximumProducer
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (g : ℝ → ℝ → ℝ) {Gbound : ℝ} (hgb : ∀ a d, |g a d| ≤ Gbound)
    (G : OriginalStageClockGrid)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) (ht : ∀ᵐ y ∂ν, y ∈ ⋃ i, G.targetCell i)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0) :
    ∃ C ≥ 0, (∀ (a d : ℝ) (x y : Fin (finrank ℝ S.covector.ker) → ℝ) (t : ℝ),
      D.originalFocalKinetic gap a d (y-x)-t*g a d ≤
        C*dist ((EuclideanSpace.equiv _ ℝ).symm x) ((EuclideanSpace.equiv _ ℝ).symm y)^2+|t| *Gbound) ∧
      ∀ (tilt : ℝ)
      (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g)
      (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
        (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
      (θ : ℝ), 0 < θ →
      ∀ hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
        (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _),
      OriginalActualClockBlockSignedMaximumProducer Q G h₀ hN b θ C (|tilt| *Gbound) tilt hj := by
  obtain ⟨C,hC,hphysical⟩ := D.exists_originalFocalMarkedCost_physical_quadratic_bound hF hw hgap hbounds g hgb
  refine ⟨C,hC,hphysical,?_⟩
  intro tilt Q b θ hθ hj
  exact D.originalActualClockBlock_signedMaximumProducer hF hw hq hgap hbounds hC
    ((abs_nonneg (g 0 0)).trans (hgb 0 0)) hphysical tilt Q G hs ht hmono h₀ hN b hθ hj

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
