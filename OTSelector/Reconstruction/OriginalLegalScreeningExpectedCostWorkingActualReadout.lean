import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostActualBudgetReadout
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostActualGoodCounts
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostActualMaximumReadout
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorActualSignedMaximumWorkingData

/-! Actual original signed maxima read into the literal FULL scalar on the same experiment. -/
open Set Function MeasureTheory Module Manifold TopologicalSpace
open scoped BigOperators ENNReal Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

omit [BorelSpace E] in
/-- The genuine original-array signed maximum controls the actual FULL finite
scalar on the same good observation. Every FULL-array record, original index,
clock, count and carrier property is supplied by the actual working experiment.
The only incoming comparison is the separately constructed actual signed maximum. -/
theorem OriginalSeedConditionalMoments.ae_original_screening_fullValue_le_actualGridBudget_on_good
    (D : OriginalSeedConditionalMoments S w μ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q Reserve : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    {R ell rawRate floor C L tilt e δ diameter : ℝ}
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (hq : 0 < finrank ℝ S.covector.ker) (hR : 0 < R)
    (hlo : G.cut 0 = D.lo+(S.level : ℝ)) (hhi : G.cut G.count = D.hi+(S.level : ℝ))
    (hsep : ConditionalClockSupportBounds μ ν δ diameter)
    (hwidth : ∀ k : Fin G.count, G.cut (k+1)-G.cut k < δ)
    (X : OriginalReserveFullWorkingInputExperiment Q Reserve b rawRate R)
    (hmatching : ∀ᵐ p ∂originalMainReserveExperimentLaw Q
      (Real.toNNReal rawRate*(volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal),
      OriginalClockBlockGoodCounts S w G μ ν b R rawRate e p →
        OriginalActualClockBlockSignedMaximum Q G h₀ hN b K R ell floor C L tilt hj p) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
    (p.1.1,p.1.2.2) ∉ originalScreeningAllFailure S w μ ν (Q.law : Measure _) b rawRate R G e
      (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e) →
      originalScreeningFullValue b R kin g tilt p.2 ≤
        originalScreeningClockGridCompleteCostBudget Q G h₀ hN b K R ell rawRate floor C L tilt e
          (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e) hj (p.1.1,p.1.2.2) := by
  have hm := X.ae_of_main_sampler hmatching
  have hd := D.ae_originalClockBlockFullArrayData hq hR G hlo hhi hsep hwidth X
  filter_upwards [hm,hd] with p hmatch hdata
  intro hp
  have hgood := originalScreeningActualGoodCounts_of_not_allFailure (S := S) (w := w)
    (μ := μ) (ν := ν) (Q.law : Measure _) G b R rawRate e (p.1.1,p.1.2.2) hp
  have hmax := hmatch hgood
  obtain ⟨A,hsource,htarget⟩ := hdata
  obtain ⟨σ,γ,_hcore,_hkeep,hlegal,hcard,hcost⟩ := hmax _ _ A
  have hlegal' : PartialMatching.IsLegal
      (scalarClockLegalGraph (fun i : Fin p.2.1.1 ↦ (p.2.1.2 i).2)
        (fun j : Fin p.2.2.1 ↦ (p.2.2.2 j).2)) γ := by
    simpa only [hsource,htarget,originalMappedReserveCloudArrays,originalPhysicalReserveCloudArrays,
      originalMappedReserveTwoCloud,originalMappedReserveCloud,cloudEncode] using hlegal
  have hcard' : γ.card = PartialMatching.legalMaximumCard
      (scalarClockLegalGraph (fun i : Fin p.2.1.1 ↦ (p.2.1.2 i).2)
        (fun j : Fin p.2.2.1 ↦ (p.2.2.2 j).2)) := by
    simpa only [hsource,htarget,originalMappedReserveCloudArrays,originalPhysicalReserveCloudArrays,
      originalMappedReserveTwoCloud,originalMappedReserveCloud,cloudEncode] using hcard
  have hv := originalScreeningFullValue_le_actualMaximum_cost b R kin g tilt p.2 γ hlegal' hcard'
  have hcosteq : γ.cost (fun i j ↦ originalWeightedEdgeCost kin g tilt
      ((originalMappedReserveCloudArrays _ (originalOrientedRawCubePhysicalMap b R) p.2).1.2 i,
        (originalMappedReserveCloudArrays _ (originalOrientedRawCubePhysicalMap b R) p.2).2.2 j)) =
      γ.cost (fun i j ↦ originalWeightedEdgeCost kin g tilt (A.source i,A.target j)) := by
    apply congrArg (fun cost ↦ γ.cost cost)
    funext i j
    rw [hsource,htarget]
  have hbudget := originalScreeningClockGridCompleteCostBudget_eq_signed_add_exception Q G h₀ hN b K
    R ell rawRate floor C L tilt e (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e) hj (p.1.1,p.1.2.2)
  have hz : (originalScreeningAllFailure S w μ ν (Q.law : Measure _) b rawRate R G e
      (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e)).indicator
        (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R)))
          (p.1.1,p.1.2.2) = 0 := indicator_of_notMem hp _
  have heq : originalScreeningClockGridCompleteCostBudget Q G h₀ hN b K R ell rawRate floor C L tilt e
      (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e) hj (p.1.1,p.1.2.2) =
      originalActualClockBlockSignedMaximumBudget Q G h₀ hN b K R ell floor C L tilt hj (p.1.1,p.1.2.2) :=
    hbudget.trans ((congrArg (fun z : ℝ ↦ originalActualClockBlockSignedMaximumBudget Q G h₀ hN b K
      R ell floor C L tilt hj (p.1.1,p.1.2.2)+(4*C*(finrank ℝ S.covector.ker : ℝ)*R^2+2*L)*z) hz).trans
        (by simp only [mul_zero,add_zero]))
  exact (hv.trans_eq hcosteq).trans (hcost.trans_eq heq.symm)

end OTSelector.Reconstruction
