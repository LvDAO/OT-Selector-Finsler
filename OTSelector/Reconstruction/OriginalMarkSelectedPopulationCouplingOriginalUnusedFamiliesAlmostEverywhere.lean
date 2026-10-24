import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingOriginalUnusedFamilies

/-! One real original-scene/raw-reserve AE event supplies every unused arrival family. -/
open Set Function MeasureTheory Module Manifold
open scoped BigOperators ENNReal NNReal Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Every genuine unused counting array gets its own internally constructed
probability family, with literal per-cell arrivals and actual port/reserve cost. -/
def OriginalUnusedBlockArrivalFamilies (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ)
    (G : OriginalStageClockGrid) {μ ν : Measure ℝ}
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) : Prop :=
  let A := originalUnusedBlockReserveData S w b R ell G h₀ hN p
  (∀ (I : Type*) [Fintype I] (x : I → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)),
    (∑ i, Measure.dirac (x i)) = A.sourcePortMeasure +
      ∑ j : A.sourceKept, Measure.dirac (A.sourceReserve.2 j.val) →
    ∃ κ, OriginalUnusedArrivalFamilySpec x G.sourceCell
      (fun i ↦ A.orientedSourceArrivalLaw (G.cut i.val) (G.cut (i.val+1)))
      (A.sourcePortMeasure.real univ + (G.sourceReserveFineBlockPartition h₀ hN).atomEnergy b R 0 1
        (originalSourceReserveExperimentSplice p)) κ) ∧
  (∀ (I : Type*) [Fintype I] (x : I → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)),
    (∑ i, Measure.dirac (x i)) = A.targetPortMeasure +
      ∑ j : A.targetKept, Measure.dirac (A.targetReserve.2 j.val) →
    ∃ κ, OriginalUnusedArrivalFamilySpec x G.targetCell
      (fun i ↦ A.orientedTargetDepartureLaw (G.cut i.val) (G.cut (i.val+1)))
      (A.targetPortMeasure.real univ + (G.targetReserveFineBlockPartition h₀ hN).atomEnergy b R 1 0
        (originalTargetReserveExperimentSplice p)) κ)

namespace OriginalSeedConditionalMoments
variable [BorelSpace E] {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The real original port-array producer and actual global Poisson RN
producer give a single AE event for all unchanged finite unused arrays.
No unused family, port-family witness or selected iid law is an input. -/
theorem ae_originalUnusedBlockArrivalFamilies
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (hq : 4 < finrank ℝ S.covector.ker)
    {R ell ρ : ℝ} (hR : 1 ≤ R) (hell : 0 ≤ ell)
    (hcollar : 2*(originalStageFrameCollarFactor b*ell) ≤ R) (hρ : 0 ≤ ρ) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∀ᵐ p ∂originalMainReserveExperimentLaw Q (Real.toNNReal ρ*
      (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal),
      OriginalUnusedBlockArrivalFamilies S w b R ell G h₀ hN p := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let rate := Real.toNNReal ρ*(volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal
  let J := originalMainReserveExperimentLaw Q rate
  have hrn := Q.originalGlobalReserveAtomLaws G h₀ hN b (lt_of_lt_of_le zero_lt_one hR) hρ hq
  have hports := D.ae_exists_originalPhysicalOrientedStagePortFamilies hF hw Q b hell hcollar
  have hp : MeasurePreserving Prod.fst J (Q.law : Measure (LegalMarkedOptimalInputScene _)) :=
    measurePreserving_fst
  filter_upwards [hrn.1, hp.quasiMeasurePreserving.ae hports] with p hrn hport
  constructor
  · intro I _ x hcount
    exact exists_originalUnusedBlockSourceFamily p hR hrn.1 hport.1 x hcount
  · intro I _ x hcount
    exact exists_originalUnusedBlockTargetFamily p hR hrn.2 hport.2 x hcount

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
