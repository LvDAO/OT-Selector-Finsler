import OTSelector.Reconstruction.OriginalLegalScreeningComparatorActualSignedMaximumStageBudget
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockUnionSignedRepairs
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockCellRestriction
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockZeroAtomsLabels
import OTSelector.Finite.PartitionFiberSums

/-! Genuine Neumann block repairs give a signed legal maximum on unchanged original labels. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped BigOperators ENNReal Classical ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Actual scalar floors and actual unused arrival laws construct local strict
bijections and then the original graph's legal maximum. Only new edges pay a
quadratic bound; the retained signed core is carried through exactly. -/
theorem exists_actualClockBlock_signedMaximum_of_unused_families
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g)
    (G : OriginalStageClockGrid)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) (ht : ∀ᵐ y ∂ν, y ∈ ⋃ i, G.targetCell i)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _)) :
    ∃ K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ),
      (∀ i, originalCenteredPhysicalCubeRegion b (2*R) ⊆ interior (K i : Set _)) ∧
      ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (source target : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (Cs Ct : G.ClockSlabBlock μ ν → Set ℝ),
      (∀ block, Cs block ⊆ G.sourceBlockCell μ ν block) →
      (∀ block, Ct block ⊆ G.targetBlockCell μ ν block) →
      (∀ block, originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
        (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
        ((scene,target),source.1,fun i ↦ (source.2 i).2) ≤
          originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (Cs block)) →
      (∀ block, originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
        (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
        ((scene,source),target.1,fun i ↦ (target.2 i).2) ≤
          originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (Ct block)) →
      let A := originalOrientedClockBlockKeptData S w G μ ν b R ell scene source target Cs Ct
      ∀ ρ : ℝ, 0 < ρ →
      (∀ block ∈ G.positiveSlabBlocks μ ν,
        (∀ k : ℕ, block.lower.val ≤ k → k ≤ block.upper.val → 0 ≤ A.gamma (G.cut k)) ∧
        ∀ k : Fin (block.upper.val-block.lower.val),
          let i : Fin G.count := ⟨block.lower.val+k.val,by have h := block.upper.isLt; have hh := k.isLt; omega⟩
          ρ ≤ A.gamma (G.cut i.val) +
            (originalStageRemainingReserveClassCount source A.sourceKept (G.sourceCell i) : ℝ)/A.cubeVolume ∧
          ρ ≤ A.gamma (G.cut (i.val+1)) +
            (originalStageRemainingReserveClassCount target A.targetKept (G.targetCell i) : ℝ)/A.cubeVolume) →
      ∀ (m n : ℕ)
        (x : Fin m → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
        (y : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
        (hx : ∀ i, G.sourceLabel (x i).2 < G.count) (hy : ∀ j, G.targetLabel (y j).2 < G.count),
      (∀ k : Fin G.count, (∀ i, (x i).2 ∉ G.sourceCell k) ∨ (∀ j, (y j).2 ∉ G.targetCell k)) →
      let c := fun i ↦ G.sourceBlockLabel h₀ hN (x i).2 (hx i)
      let d := fun j ↦ G.targetBlockLabel h₀ hN (y j).2 (hy j)
      ∀ (σ : OTSelector.PartialMatching m n),
      PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2)) σ →
      (∀ edge ∈ σ.edges, c edge.1 = d edge.2) →
      ∀ (U : Finset (Fin m)) (V : Finset (Fin n)), U ⊆ σ.freeRows → V ⊆ σ.freeCols →
      (∀ block, (σ.edges.filter (fun edge ↦ c edge.1 = block)).card + (U.filter (fun i ↦ c i = block)).card =
        min (Finset.univ.filter (fun i ↦ c i = block)).card (Finset.univ.filter (fun j ↦ d j = block)).card) →
      (∀ block, block ∉ G.positiveSlabBlocks μ ν →
        U.filter (fun i ↦ (x i).2 ∈ G.sourceBlockCell μ ν block) = ∅ ∧
        V.filter (fun j ↦ (y j).2 ∈ G.targetBlockCell μ ν block) = ∅) →
      ∀ (κ : Fin m → Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
        (τ : Fin n → Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))),
      (∀ i, IsProbabilityMeasure (κ i)) → (∀ j, IsProbabilityMeasure (τ j)) →
      (∀ i, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2) (κ i)) →
      (∀ j, Integrable (fun v ↦ dist v ((EuclideanSpace.equiv _ ℝ).symm (y j).1)^2) (τ j)) →
      (∀ i : Fin G.count, (∑ j : U, if (x j.val).2 ∈ G.sourceCell i then κ j.val else 0) =
        A.orientedSourceArrivalLaw (G.cut i.val) (G.cut (i.val+1))) →
      (∀ i : Fin G.count, (∑ j : V, if (y j.val).2 ∈ G.targetCell i then τ j.val else 0) =
        A.orientedTargetDepartureLaw (G.cut i.val) (G.cut (i.val+1))) →
      ∀ (cost : Fin m → Fin n → ℝ) (C L coarse : ℝ), 0 ≤ C → 0 ≤ coarse →
      (∀ i j, cost i j ≤ C*dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1)
        ((EuclideanSpace.equiv _ ℝ).symm (y j).1)^2+L) →
      (∀ i j, (c i).lower < (d j).lower → cost i j ≤ coarse) →
      ∃ γ : OTSelector.PartialMatching m n,
        PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2)) γ ∧
        γ.card = PartialMatching.legalMaximumCard (scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2)) ∧
        σ.edges ⊆ γ.edges ∧
        γ.cost cost ≤ σ.cost cost +
          (∑ block, C*originalClockBlockStageRepairBudget Q G b K R ell ρ hj block scene) +
          3*C*((∑ i : U, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (x i.val).1) v^2 ∂κ i.val) +
            ∑ j : V, ∫ v, dist v ((EuclideanSpace.equiv _ ℝ).symm (y j.val).1)^2 ∂τ j.val) +
          L*(U.card : ℝ) + coarse*((∑ block : G.ClockSlabBlock μ ν,
            Nat.dist (Finset.univ.filter (fun i ↦ c i = block)).card
              (Finset.univ.filter (fun j ↦ d j = block)).card : ℕ) : ℝ) := by
  obtain ⟨K,hK,hrepairs⟩ := D.exists_actualClockBlock_originalAtomRepair hF hw hq hgap hbounds Q G hs ht hmono h₀ hN b hell hR hj
  refine ⟨K,hK,?_⟩
  filter_upwards [hrepairs] with scene hp
  intro source target Cs Ct hCs hCt hsCap htCap
  dsimp only
  let A := originalOrientedClockBlockKeptData S w G μ ν b R ell scene source target Cs Ct
  intro ρ hρ hfloors m n x y hx hy hmonoXY
  let c := fun i ↦ G.sourceBlockLabel h₀ hN (x i).2 (hx i)
  let d := fun j ↦ G.targetBlockLabel h₀ hN (y j).2 (hy j)
  intro σ hσ hsame U V hU hV hcount hzero κ τ hκ hτ hκI hτI hκclass hτclass cost C L coarse hC hcoarse hnew hcross
  let : LinearOrder (G.ClockSlabBlock μ ν) := FiniteSurplusStrictBlock.linearOrder (G.clockSlabSurplus μ ν) G.count
  let Ub := fun block ↦ U.filter (fun i ↦ c i = block)
  let Vb := fun block ↦ V.filter (fun j ↦ d j = block)
  have hUb (block : G.ClockSlabBlock μ ν) : Ub block = U.filter (fun i ↦ c i = block) := by
    ext i
    simp only [Ub,Finset.mem_filter]
  have hVb (block : G.ClockSlabBlock μ ν) : Vb block = V.filter (fun j ↦ d j = block) := by
    ext j
    simp only [Vb,Finset.mem_filter]
  let Es := fun i ↦ ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2 ∂κ i
  let Et := fun j ↦ ∫ v, dist v ((EuclideanSpace.equiv _ ℝ).symm (y j).1)^2 ∂τ j
  let B := fun block ↦ originalClockBlockStageRepairBudget Q G b K R ell ρ hj block scene +
    3*(∑ i : Ub block, Es i.val) + 3*(∑ j : Vb block, Et j.val)
  have hRnonneg : 0 ≤ R := by nlinarith [one_le_originalStageFrameCollarFactor b]
  have hB (block) : 0 ≤ B block := add_nonneg
    (add_nonneg (originalClockBlockStageRepairBudget_nonneg Q G b K hRnonneg ell hρ.le hj block scene)
      (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)))))
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))))
  have hlocal (block : G.ClockSlabBlock μ ν) : ∃ e : Ub block ≃ Vb block,
      (∀ i, (i.val,(e i).val) ∈ scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2)) ∧
      (∑ i : Ub block, dist ((EuclideanSpace.equiv _ ℝ).symm (x i.val).1)
        ((EuclideanSpace.equiv _ ℝ).symm (y (e i).val).1)^2) ≤ B block := by
    by_cases hb : block ∈ G.positiveSlabBlocks μ ν
    · have hf := hfloors block hb
      obtain ⟨e,he,henergy⟩ := hp source target Cs Ct hCs hCt hsCap htCap block ρ hρ hf.1 hf.2
        (Ub block) (Vb block) (fun i ↦ x i.val) (fun j ↦ y j.val) (fun i ↦ hx i.val) (fun j ↦ hy j.val)
        (fun i ↦ (Finset.mem_filter.mp i.property).2) (fun j ↦ (Finset.mem_filter.mp j.property).2)
        (fun k ↦ (hmonoXY k).imp (fun h i ↦ h i.val) (fun h j ↦ h j.val))
        (fun i ↦ κ i.val) (fun j ↦ τ j.val) (fun i ↦ hκ i.val) (fun j ↦ hτ j.val)
        (fun i ↦ hκI i.val) (fun j ↦ hτI j.val)
        (fun i hi ↦ (G.originalSourceClockBlock_unused_cellLaw h₀ hN (fun j ↦ (x j).2) hx U block κ i hi).trans (hκclass i))
        (fun i hi ↦ (G.originalTargetClockBlock_unused_cellLaw h₀ hN (fun j ↦ (y j).2) hy V block τ i hi).trans (hτclass i))
      exact ⟨e,fun i ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,he i⟩,henergy⟩
    · have hz := hzero block hb
      obtain ⟨hUb,_,hEmpty,_,e,he⟩ := G.zeroBlock_unused_labels_empty_equiv h₀ hN x y hx hy U V block hz.1 hz.2
      have : IsEmpty (Ub block) := hEmpty
      refine ⟨e,fun i ↦ isEmptyElim i,?_⟩
      simpa only [Finset.univ_eq_empty,Finset.sum_empty] using hB block
  obtain ⟨extra,γ,hγ,hmax,hkeep,_,_,_,hcost⟩ :=
    PartialMatching.exists_legalMaximum_of_ordered_unused_block_signed_repairs
      (scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2)) c d σ hσ hsame
      (G.originalClockBlock_graph_forward_complete h₀ hN (fun i ↦ (x i).2) (fun j ↦ (y j).2) hx hy).1
      (G.originalClockBlock_graph_forward_complete h₀ hN (fun i ↦ (x i).2) (fun j ↦ (y j).2) hx hy).2
      Ub Vb (fun block ↦ (Finset.filter_subset _ U).trans hU) (fun block ↦ (Finset.filter_subset _ V).trans hV)
      (fun _ _ hi ↦ (Finset.mem_filter.mp hi).2) (fun _ _ hi ↦ (Finset.mem_filter.mp hi).2)
      (fun block ↦ by simpa only [c,d,Ub,Finset.filter_congr_decidable] using hcount block) (fun i ↦ (EuclideanSpace.equiv _ ℝ).symm (x i).1)
      (fun j ↦ (EuclideanSpace.equiv _ ℝ).symm (y j).1) B hlocal cost C L coarse hC hcoarse
      (fun _ i j ↦ hnew i.val j.val) hcross
  refine ⟨γ,hγ,hmax,hkeep,?_⟩
  have hsum : (∑ block, (C*B block+L*((Ub block).card : ℝ))) =
      (∑ block, C*originalClockBlockStageRepairBudget Q G b K R ell ρ hj block scene) +
      3*C*((∑ i : U, Es i.val)+(∑ j : V, Et j.val))+L*(U.card : ℝ) := by
    calc
      _ = (∑ block, (C*originalClockBlockStageRepairBudget Q G b K R ell ρ hj block scene +
          3*C*(∑ i : Ub block,Es i.val)+3*C*(∑ j : Vb block,Et j.val)+L*((Ub block).card : ℝ))) :=
        Finset.sum_congr rfl (fun _ _ ↦ by dsimp only [B]; ring)
      _ = _ := by
        have hs : (∑ block,∑ i : Ub block,Es i.val) = ∑ i : U,Es i.val :=
          by
            convert sum_originalUnusedBlock_restrictions U c Es using 1
            apply Finset.sum_congr rfl
            intro block _
            simp only [Finset.sum_coe_sort]
            congr 1
            ext i
            simp only [Ub,Finset.mem_filter]
        have ht : (∑ block,∑ j : Vb block,Et j.val) = ∑ j : V,Et j.val :=
          by
            convert sum_originalUnusedBlock_restrictions V d Et using 1
            apply Finset.sum_congr rfl
            intro block _
            simp only [Finset.sum_coe_sort]
            congr 1
            ext j
            simp only [Vb,Finset.mem_filter]
        have hc : (∑ block,((Ub block).card : ℝ)) = (U.card : ℝ) := by
          have hn : (∑ block,(Ub block).card) = U.card := by
            convert sum_originalUnusedBlock_cards U c using 1
            apply Finset.sum_congr rfl
            intro block _
            congr 1
            ext i
            simp only [Ub,Finset.mem_filter]
          exact_mod_cast hn
        simp only [Finset.sum_add_distrib,← Finset.mul_sum]
        rw [hs,ht,hc]
        ring

  rw [hsum] at hcost
  apply hcost.trans_eq
  dsimp only [Es,Et,c,d]
  ring_nf
  congr
  funext block
  congr

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
