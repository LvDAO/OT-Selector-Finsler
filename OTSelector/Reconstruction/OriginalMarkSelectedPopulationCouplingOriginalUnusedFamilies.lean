import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingOriginalUnusedFamiliesExperiment
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairActualArrivalFamilies

/-! Actual ports and the true global kept reserve family smooth unchanged unused labels. -/
open Set Function MeasureTheory Module Manifold
open scoped BigOperators ENNReal Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Probability, individual true deviation integrability, actual energy and
every original clock-cell arrival for one unchanged finite label family. -/
def OriginalUnusedArrivalFamilySpec {q N : ℕ} {I : Type*} [Fintype I]
    (x : I → LegalMarkedPhysicalPoint q) (cell : Fin N → Set ℝ)
    (arrival : Fin N → Measure (EuclideanSpace ℝ (Fin q))) (budget : ℝ)
    (κ : I → Measure (EuclideanSpace ℝ (Fin q))) : Prop :=
  (∀ i, IsProbabilityMeasure (κ i)) ∧
    (∀ i, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2) (κ i)) ∧
    (∑ i, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2 ∂κ i) ≤ budget ∧
    ∀ i, (∑ j, if (x j).2 ∈ cell i then κ j else 0) = arrival i

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual original scene, physically mapped original reserve words,
and literal global original kept Fin sets form one residual-density datum. -/
def originalUnusedBlockReserveData (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ)
    (G : OriginalStageClockGrid) {μ ν : Measure ℝ}
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) :
    OriginalOrientedStageResidualDensityData S w b R ell :=
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  let Hs := G.sourceReserveFineBlockPartition h₀ hN
  let Ht := G.targetReserveFineBlockPartition h₀ hN
  { scene := p.1
    sourceReserve := originalMappedReserveCloud _ (originalOrientedRawCubePhysicalMap b R) p.2.1
    targetReserve := originalMappedReserveCloud _ (originalOrientedRawCubePhysicalMap b R) p.2.2
    sourceKept := originalReserveBlocksKeptFin K 0 1 Hs.blockCell Hs.oppositeCell Hs.deletionCell
      (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p))
    targetKept := originalReserveBlocksKeptFin K 1 0 Ht.blockCell Ht.oppositeCell Ht.deletionCell
      (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) }

variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
    (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {R ell : ℝ}
  {G : OriginalStageClockGrid} {μ ν : Measure ℝ}
  {h₀ : G.clockSlabSurplus μ ν 0 = 0} {hN : G.clockSlabSurplus μ ν G.count = 0}

/-- Actual source ports and internally produced global reserve RN laws
construct every unchanged unused source label, including repeated values. -/
theorem exists_originalUnusedBlockSourceFamily
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) (hR : 1 ≤ R)
    (hp : (G.sourceReserveFineBlockPartition h₀ hN).AtomSpec b R 0 1
      (originalSourceReserveExperimentSplice p))
    (hport : Nonempty (OriginalOrientedPortAtomFamily b R
      (originalUnusedBlockReserveData S w b R ell G h₀ hN p).sourcePortMeasure))
    {I : Type*} [Fintype I] (x : I → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
    (hcount : (∑ i, Measure.dirac (x i)) =
      (originalUnusedBlockReserveData S w b R ell G h₀ hN p).sourcePortMeasure +
        ∑ j : (originalUnusedBlockReserveData S w b R ell G h₀ hN p).sourceKept,
          Measure.dirac ((originalUnusedBlockReserveData S w b R ell G h₀ hN p).sourceReserve.2 j.val)) :
    let A := originalUnusedBlockReserveData S w b R ell G h₀ hN p
    ∃ κ, OriginalUnusedArrivalFamilySpec x G.sourceCell
      (fun i ↦ A.orientedSourceArrivalLaw (G.cut i.val) (G.cut (i.val+1)))
      (A.sourcePortMeasure.real univ + (G.sourceReserveFineBlockPartition h₀ hN).atomEnergy b R 0 1
        (originalSourceReserveExperimentSplice p)) κ := by
  let A := originalUnusedBlockReserveData S w b R ell G h₀ hN p
  let H := G.sourceReserveFineBlockPartition h₀ hN
  let ps := originalSourceReserveExperimentSplice p
  obtain ⟨P⟩ := hport
  have hi (j : A.sourceKept) : Integrable
      (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (A.sourceReserve.2 j.val).1) v^2)
      (H.atomLaw b R 0 1 ps j) := hp.2.1 j
  have hc (i : Fin G.count) := H.atomSpec_class_sum_smul b R 0 1 ps hp i
  obtain ⟨κ,hκ,hκI,henergy,hclass⟩ := A.exists_originalUnused_sourceArrivalFamily hR P G x hcount
    (H.atomLaw b R 0 1 ps) hp.1 hi hc
  exact ⟨κ,hκ,hκI,henergy,hclass⟩

/-- Targets use the actual Ioc arrival and opposite-block ordering throughout. -/
theorem exists_originalUnusedBlockTargetFamily
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) (hR : 1 ≤ R)
    (hp : (G.targetReserveFineBlockPartition h₀ hN).AtomSpec b R 1 0
      (originalTargetReserveExperimentSplice p))
    (hport : Nonempty (OriginalOrientedPortAtomFamily b R
      (originalUnusedBlockReserveData S w b R ell G h₀ hN p).targetPortMeasure))
    {I : Type*} [Fintype I] (x : I → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
    (hcount : (∑ i, Measure.dirac (x i)) =
      (originalUnusedBlockReserveData S w b R ell G h₀ hN p).targetPortMeasure +
        ∑ j : (originalUnusedBlockReserveData S w b R ell G h₀ hN p).targetKept,
          Measure.dirac ((originalUnusedBlockReserveData S w b R ell G h₀ hN p).targetReserve.2 j.val)) :
    let A := originalUnusedBlockReserveData S w b R ell G h₀ hN p
    ∃ κ, OriginalUnusedArrivalFamilySpec x G.targetCell
      (fun i ↦ A.orientedTargetDepartureLaw (G.cut i.val) (G.cut (i.val+1)))
      (A.targetPortMeasure.real univ + (G.targetReserveFineBlockPartition h₀ hN).atomEnergy b R 1 0
        (originalTargetReserveExperimentSplice p)) κ := by
  let A := originalUnusedBlockReserveData S w b R ell G h₀ hN p
  let H := G.targetReserveFineBlockPartition h₀ hN
  let ps := originalTargetReserveExperimentSplice p
  obtain ⟨P⟩ := hport
  have hi (j : A.targetKept) : Integrable
      (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (A.targetReserve.2 j.val).1) v^2)
      (H.atomLaw b R 1 0 ps j) := hp.2.1 j
  have hc (i : Fin G.count) := H.atomSpec_class_sum_smul b R 1 0 ps hp i
  obtain ⟨κ,hκ,hκI,henergy,hclass⟩ := A.exists_originalUnused_targetArrivalFamily hR P G x hcount
    (H.atomLaw b R 1 0 ps) hp.1 hi hc
  exact ⟨κ,hκ,hκI,henergy,hclass⟩

end OTSelector.Reconstruction
