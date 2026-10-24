import OTSelector.Reconstruction.OriginalLegalScreeningComparatorActualSignedMaximumData
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorActualSignedMaximumStageBudget
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostUnusedArrivalReadout
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostPortReserve
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockExcessBudgetLimit
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedCubeCost

/-! Actual original-array signed comparator and its literal physical screening budget. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped BigOperators ENNReal Classical ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The literal good-event budget pays the true signed retained core, actual
Neumann stages, physical ports, global original reserve RN energy and actual
FULL block imbalance. Only ports and raw reserve labels pay the bounded tilt. -/
def originalActualClockBlockSignedMaximumBudget
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) (R ell ρ C L tilt : ℝ)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) : ℝ :=
  let A := originalUnusedBlockReserveData S w b R ell G h₀ hN p
  (∫ edge, originalWeightedEdgeCost kin g tilt edge ∂(originalStageRestrictedPathPlan
    (originalOrientedPathLengthRetained S w b R ell) p.1 :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) +
  (∑ block, C*originalClockBlockStageRepairBudget Q G b K R ell ρ hj block p.1) +
  3*C*((A.sourcePortMeasure.real univ+A.targetPortMeasure.real univ)+
    originalScreeningPartitionReserveEndpointEnergy (G.sourceReserveFineBlockPartition h₀ hN)
      (G.targetReserveFineBlockPartition h₀ hN) b R p) +
  L*originalScreeningRepairCountBudget S w b R ell p +
  (4*C*(finrank ℝ S.covector.ker : ℝ)*R^2+L)*
    originalFullClockSlabDiscrepancy (α := μ) (β := ν) G (originalCenteredPhysicalCubeRegion b (2*R)) p

/-- A genuine original-label maximum and the same retained core realize the
literal signed budget. No stage plan or already constructed repair is an input. -/
def OriginalActualClockBlockSignedMaximum
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) (R ell ρ C L tilt : ℝ)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) : Prop :=
  ∀ m n (X : OriginalClockBlockFullArrayData (μ := μ) (ν := ν) G b R p m n),
    ∃ σ γ : OTSelector.PartialMatching m n,
      (originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) p.1 :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) =
          ∑ edge ∈ σ.edges, Measure.dirac (X.source edge.1,X.target edge.2) ∧
      σ.edges ⊆ γ.edges ∧
      PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (X.source i).2) (fun j ↦ (X.target j).2)) γ ∧
      γ.card = PartialMatching.legalMaximumCard
        (scalarClockLegalGraph (fun i ↦ (X.source i).2) (fun j ↦ (X.target j).2)) ∧
      γ.cost (fun i j ↦ originalWeightedEdgeCost kin g tilt (X.source i,X.target j)) ≤
        originalActualClockBlockSignedMaximumBudget Q G h₀ hN b K R ell ρ C L tilt hj p


/-- One fixed tolerance and floor work for every large physical cube. The only
pointwise premises are the literal good counts and unchanged FULL observations. -/
def OriginalActualClockBlockSignedMaximumProducer
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (θ C L tilt : ℝ)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _)) : Prop :=
  ∃ e : ℝ, 0 < e ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ R ell : ℝ,
    1 ≤ ell → 2*(originalStageFrameCollarFactor b*ell) ≤ R →
    ∃ K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ),
      (∀ i, originalCenteredPhysicalCubeRegion b (2*R) ⊆ interior (K i : Set _)) ∧
      ∀ᵐ p ∂originalMainReserveExperimentLaw Q
        (Real.toNNReal θ*(volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal),
        OriginalClockBlockGoodCounts S w G μ ν b R θ e p →
          OriginalActualClockBlockSignedMaximum Q G h₀ hN b K R ell ρ C L tilt hj p

end OTSelector.Reconstruction
