import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockGridTransports
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsGlobalKept
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockStageLaws
import OTSelector.Transport.Finite.ClasswiseAtomRepairEpsilon

/-! The actual original Neumann stages repair unchanged labels in their real clock block. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff Distributions BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
namespace OriginalSeedConditionalMoments
variable {μ ν : Measure ℝ} (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Genuine original stages and actual blockwise reserve deletion construct a
strict legal bijection of unchanged endpoint labels. All background endpoints,
stage plans, RN labels and finite rounding are proved internally. The supplied
atom laws specify only actual arrival marginals and deviation integrability. -/
theorem exists_actualClockBlock_originalAtomRepair
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (G : OriginalStageClockGrid)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i)
    (ht : ∀ᵐ y ∂ν, y ∈ ⋃ i, G.targetCell i)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (frame : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*(originalStageFrameCollarFactor frame*ell) ≤ R)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2
      (Q.law : Measure _)) :
    ∃ K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ),
      (∀ i, originalCenteredPhysicalCubeRegion frame (2*R) ⊆ interior (K i : Set _)) ∧
      ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (source target : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (Cs Ct : G.ClockSlabBlock μ ν → Set ℝ),
      (∀ block, Cs block ⊆ G.sourceBlockCell μ ν block) →
      (∀ block, Ct block ⊆ G.targetBlockCell μ ν block) →
      (∀ block, originalReserveBlockExcess (originalCenteredPhysicalCubeRegion frame (2*R)) 0 1
        (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
        ((scene,target),source.1,fun i ↦ (source.2 i).2) ≤
          originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (Cs block)) →
      (∀ block, originalReserveBlockExcess (originalCenteredPhysicalCubeRegion frame (2*R)) 1 0
        (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
        ((scene,source),target.1,fun i ↦ (target.2 i).2) ≤
          originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (Ct block)) →
      let A := originalOrientedClockBlockKeptData S w G μ ν frame R ell scene source target Cs Ct
      ∀ (block : G.ClockSlabBlock μ ν) (ρ : ℝ), 0 < ρ →
      (∀ k, block.lower.val ≤ k → k ≤ block.upper.val → 0 ≤ A.gamma (G.cut k)) →
      (∀ k : Fin (block.upper.val-block.lower.val),
        let i : Fin G.count := ⟨block.lower.val+k.val,by have h := block.upper.isLt; omega⟩
        ρ ≤ A.gamma (G.cut i.val) +
          (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (G.sourceCell i) : ℝ)/A.cubeVolume ∧
        ρ ≤ A.gamma (G.cut (i.val+1)) +
          (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (G.targetCell i) : ℝ)/A.cubeVolume) →
      ∀ (I J : Type) [Fintype I] [Fintype J]
        (x : I → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
        (y : J → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
        (hx : ∀ i, G.sourceLabel (x i).2 < G.count)
        (hy : ∀ j, G.targetLabel (y j).2 < G.count),
      (∀ i, G.sourceBlockLabel h₀ hN (x i).2 (hx i) = block) →
      (∀ j, G.targetBlockLabel h₀ hN (y j).2 (hy j) = block) →
      (∀ k : Fin G.count, (∀ i, (x i).2 ∉ G.sourceCell k) ∨ (∀ j, (y j).2 ∉ G.targetCell k)) →
      ∀ (κ : I → Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
        (τ : J → Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))),
      (∀ i, IsProbabilityMeasure (κ i)) → (∀ j, IsProbabilityMeasure (τ j)) →
      (∀ i, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2) (κ i)) →
      (∀ j, Integrable (fun v ↦ dist v ((EuclideanSpace.equiv _ ℝ).symm (y j).1)^2) (τ j)) →
      (∀ i : Fin G.count, block.Contains i →
        (∑ j, if (x j).2 ∈ G.sourceCell i then κ j else 0) =
          A.orientedSourceArrivalLaw (G.cut i.val) (G.cut (i.val+1))) →
      (∀ i : Fin G.count, block.Contains i →
        (∑ j, if (y j).2 ∈ G.targetCell i then τ j else 0) =
          A.orientedTargetDepartureLaw (G.cut i.val) (G.cut (i.val+1))) →
      ∃ e : I ≃ J, (∀ i, (x i).2 < (y (e i)).2) ∧
        (∑ i, dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1)
          ((EuclideanSpace.equiv _ ℝ).symm (y (e i)).1)^2) ≤
          3*((block.upper.val-block.lower.val : ℕ) : ℝ)*
            (∑ k : Fin (block.upper.val-block.lower.val),
              let i : Fin G.count := ⟨block.lower.val+k.val,by have h := block.upper.isLt; omega⟩
              ρ⁻¹ * originalOrientedStageCurrentInputNeumannBudget S w Q frame (K i) R ell
                (G.cut i.val) (G.cut (i.val+1)) (hj i) scene) +
          3*(∑ i, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2 ∂κ i) +
          3*(∑ j, ∫ v, dist v ((EuclideanSpace.equiv _ ℝ).symm (y j).1)^2 ∂τ j) := by
  obtain ⟨K,hK,hplans⟩ := D.exists_originalClockGrid_stageTransports hF hw hq hbounds Q G frame hell hR hj
  refine ⟨K,hK,?_⟩
  filter_upwards [hplans,D.ae_all_originalOrientedClockBlockKeptEndpoints_zero hF hw Q G hgap hbounds
    hs ht hmono frame hell hR] with scene hp hz
  intro source target Cs Ct hCs hCt hsCap htCap A block ρ hρ hgamma hfloor
    I J _ _ x y hx hy hxb hyb hmonoXY κ τ hκ hτ hκI hτI hκclass hτclass
  let N := block.upper.val-block.lower.val
  let index : Fin N → Fin G.count := fun k ↦ ⟨block.lower.val+k.val,by have h := block.upper.isLt; omega⟩
  let bg : ℕ → Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))) :=
    fun k ↦ if k < N then A.orientedBackgroundLaw (G.cut (block.lower.val+k)) else 0
  let Bfin : Fin N → ℝ := fun k ↦ ρ⁻¹ * originalOrientedStageCurrentInputNeumannBudget S w Q frame
    (K (index k)) R ell (G.cut (index k).val) (G.cut ((index k).val+1)) (hj (index k)) scene
  let B : ℕ → ℝ := fun k ↦ if hk : k < N then Bfin ⟨k,hk⟩ else 0
  have hends := (hz source target Cs Ct hCs hCt hsCap htCap).2 block
  have hbg (k : ℕ) (hk : k < N) : bg k = A.orientedBackgroundLaw (G.cut (block.lower.val+k)) := by
    simp only [bg,hk,ite_true]
  have hnext (k : ℕ) (hk : k < N) :
      bg (k+1) = A.orientedBackgroundLaw (G.cut ((index ⟨k,hk⟩).val+1)) := by
    by_cases hk' : k+1 < N
    · simp only [hbg _ hk',index]
      congr 2
    · have he : block.lower.val+k+1 = block.upper.val := by dsimp [N] at hk hk'; omega
      simp only [bg,hk',ite_false,index,he]
      exact hends.2.symm
  have hgamma0 (k : ℕ) (hk : block.lower.val ≤ k) (hk' : k ≤ block.upper.val) := hgamma k hk hk'
  have hpf (k : Fin N) := hp (index k) A rfl
    (hgamma0 _ (by dsimp [index]; omega) (by dsimp [index,N] at *; omega))
    (hgamma0 _ (by dsimp [index]; omega) (by dsimp [index,N] at *; omega))
  have hfinite (k : ℕ) : IsFiniteMeasure (bg k) := by
    by_cases hk : k < N
    · rw [hbg k hk]
      exact (hpf ⟨k,hk⟩).1
    · simp only [bg,hk,ite_false]
      infer_instance
  have : ∀ k, IsFiniteMeasure (bg k) := hfinite
  have : ∀ i, IsProbabilityMeasure (κ i) := hκ
  have : ∀ j, IsProbabilityMeasure (τ j) := hτ
  have hbg0 : bg 0 = 0 := by
    have hpos : 0 < N := by dsimp [N]; have h := block.consecutive.1; omega
    rw [hbg 0 hpos,Nat.add_zero]
    exact hends.1
  have hbgN : bg N = 0 := by simp only [bg,lt_self_iff_false,ite_false]
  have hstage (k : ℕ) (hk : k < N) (ε : ℝ) (hε : 0 < ε) : ∃ π,
      IsFiniteMeasure π ∧
      π.fst = bg k + originalAtomSmoothingClassLaw κ (fun i ↦ G.sourceClockInBlock h₀ hN (x i).2 (hx i)) k ∧
      π.snd = bg (k+1) + originalAtomSmoothingClassLaw τ (fun j ↦ G.targetClockInBlock h₀ hN (y j).2 (hy j)) k ∧
      Integrable (fun p ↦ dist p.1 p.2^2) π ∧ (∫ p, dist p.1 p.2^2 ∂π) ≤ B k+ε := by
    obtain ⟨π,hπ,hsrc,htgt,hI,hcost⟩ := (hpf ⟨k,hk⟩).2.2 ρ hρ
      (hfloor ⟨k,hk⟩).1 (hfloor ⟨k,hk⟩).2 ε hε
    have hcontains : block.Contains (index ⟨k,hk⟩) := by dsimp [FiniteSurplusStrictBlock.Contains,index,N] at *; omega
    refine ⟨π,hπ,?_,?_,hI,?_⟩
    · rw [hbg k hk,G.originalSourceClockBlock_stageLaw h₀ hN (fun i ↦ (x i).2) hx block hxb κ k hk,
        hκclass (index ⟨k,hk⟩) hcontains]
      exact hsrc
    · rw [hnext k hk,G.originalTargetClockBlock_stageLaw h₀ hN (fun j ↦ (y j).2) hy block hyb τ k hk,
        hτclass (index ⟨k,hk⟩) hcontains]
      exact htgt
    · simpa only [B,dite_eq_left hk,Bfin] using hcost
  obtain ⟨e,he,henergy⟩ := exists_originalAtoms_strictClassRepair_of_epsilonStages_deviationEnergy κ τ
    (fun i ↦ G.sourceClockInBlock h₀ hN (x i).2 (hx i))
    (fun j ↦ G.targetClockInBlock h₀ hN (y j).2 (hy j))
    (fun i ↦ (EuclideanSpace.equiv _ ℝ).symm (x i).1) (fun j ↦ (EuclideanSpace.equiv _ ℝ).symm (y j).1)
    hκI hτI N (fun i ↦ by simpa only [hxb i,N] using G.sourceClockInBlock_lt h₀ hN (x i).2 (hx i))
    (fun j ↦ by simpa only [hyb j,N] using G.targetClockInBlock_lt h₀ hN (y j).2 (hy j))
    bg hbg0 hbgN B hstage (G.originalClockBlock_local_monochrome h₀ hN _ _ hx hy block hxb hyb hmonoXY)
  have hsum : (∑ k ∈ Finset.range N, B k) = ∑ k : Fin N, Bfin k := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simp only [B,dite_eq_left k.isLt]
  refine ⟨e,fun i ↦ G.original_clock_lt_of_local_block_order h₀ hN (hx i) (hy (e i))
    ((hxb i).trans (hyb (e i)).symm) (he i),?_⟩
  simpa only [hsum,N,Bfin,index] using henergy

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
