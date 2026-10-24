import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostWorkingActualReadout

/-! Same-experiment actual finite scalar means, including the genuine bad observations. -/
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

/-- The actual original-label maximum and the unchanged complete budget imply
an inequality of literal sampler means. The bad-event finite-value bound,
signed-core lower bound, actual array record and both exact marginals are
internal. The budget's L1 property is supplied by its separately proved bound. -/
theorem OriginalSeedConditionalMoments.integral_original_screening_fullValue_le_actualGridBudget
    (D : OriginalSeedConditionalMoments S w μ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q Reserve : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    {R ell rawRate floor C tilt e δ diameter Gbound : ℝ}
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 0 < finrank ℝ S.covector.ker) (hR : 0 < R)
    (hell : 0 ≤ ell) (hcollar : 2*(originalStageFrameCollarFactor b*ell) ≤ R)
    (hC : 0 ≤ C) (hfloor : 0 ≤ floor)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hk0 : ∀ a d v, 0 ≤ kin a d v) (hkb : ∀ a d v, |kin a d v| ≤ C*∑ i, v i^2)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a d, |g a d| ≤ Gbound)
    (hlo : G.cut 0 = D.lo+(S.level : ℝ)) (hhi : G.cut G.count = D.hi+(S.level : ℝ))
    (hsep : ConditionalClockSupportBounds μ ν δ diameter)
    (hwidth : ∀ k : Fin G.count, G.cut (k+1)-G.cut k < δ)
    (X : OriginalReserveFullWorkingInputExperiment Q Reserve b rawRate R)
    (hmatching : ∀ᵐ p ∂originalMainReserveExperimentLaw Q
      (Real.toNNReal rawRate*(volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal),
      OriginalClockBlockGoodCounts S w G μ ν b R rawRate e p →
        OriginalActualClockBlockSignedMaximum Q G h₀ hN b K R ell floor C (|tilt| *Gbound) tilt hj p)
    (hbudgetI : Integrable (originalScreeningClockGridCompleteCostBudget Q G h₀ hN b K R ell
      rawRate floor C (|tilt| *Gbound) tilt e (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e) hj)
      (originalMainReserveExperimentLaw Q (Real.toNNReal rawRate*
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal))) :
    (∫ cloud, originalScreeningFullValue b R kin g tilt cloud
      ∂twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν
        (Real.toNNReal (1+rawRate)*(volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) ≤
    ∫ p, originalScreeningClockGridCompleteCostBudget Q G h₀ hN b K R ell rawRate floor C
      (|tilt| *Gbound) tilt e (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e) hj p
      ∂originalMainReserveExperimentLaw Q (Real.toNNReal rawRate*
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal) := by
  let Hs := G.sourceReserveFineBlockPartition h₀ hN
  let Ht := G.targetReserveFineBlockPartition h₀ hN
  let RS := Sum.elim (fun i ↦ Hs.blockCell (Hs.blockFor i)) (fun i ↦ Ht.blockCell (Ht.blockFor i))
  let RT := Sum.elim (fun i ↦ Hs.oppositeCell (Hs.blockFor i)) (fun i ↦ Ht.oppositeCell (Ht.blockFor i))
  let RCs := Sum.elim (fun i ↦ Hs.deletionCell (Hs.blockFor i)) (fun _ : Fin G.count ↦ (∅ : Set ℝ))
  let RCt := Sum.elim (fun _ : Fin G.count ↦ (∅ : Set ℝ)) (fun i ↦ Ht.deletionCell (Ht.blockFor i))
  let RDs := Sum.elim Hs.fineCell (fun _ : Fin G.count ↦ (∅ : Set ℝ))
  let RDt := Sum.elim (fun _ : Fin G.count ↦ (∅ : Set ℝ)) Ht.fineCell
  have hgood := D.ae_original_screening_fullValue_le_actualGridBudget_on_good Q Reserve G h₀ hN b K
    hj hq hR hlo hhi hsep hwidth X hmatching
  have hdom := D.ae_original_screening_fullValue_le_budget_of_actualGood S w Q b K R ell
    (fun i ↦ G.cut i.val) (fun i ↦ G.cut (i.val+1))
    (originalScreeningBlockStageWeight G h₀ hN floor C) hj rawRate G e
    (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e) C (|tilt| *Gbound)
    RS RT RCs RCt RDs RDt tilt hF hw hR.le hell hcollar hC rfl
    (originalScreeningBlockStageWeight_nonneg G h₀ hN hfloor hC) hk hk0 hkb hg hgb Reserve X hgood
  let view := fun p : OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
    TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ ↦ (p.1.1,p.1.2.2)
  have hp : MeasurePreserving view (X.fullLaw : Measure _)
      (originalMainReserveExperimentLaw Q (Real.toNNReal rawRate*
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) :=
    ⟨by fun_prop,X.fullLaw_main_sampler⟩
  have hB : Integrable (fun p ↦ originalScreeningClockGridCompleteCostBudget Q G h₀ hN b K R ell
      rawRate floor C (|tilt| *Gbound) tilt e (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e) hj (view p))
      (X.fullLaw : Measure _) := hp.integrable_comp_of_integrable hbudgetI
  have hV := (X.original_screening_fullValue_integrable_and_ae_bound hR.le hC hk hkb hg hgb tilt).1
  have hle := integral_mono_ae hV hB hdom
  rw [X.integral_original_screening_fullValue hk hg tilt] at hle
  exact hle.trans_eq (hp.hasLaw.integral_comp hbudgetI.aestronglyMeasurable)

end OTSelector.Reconstruction
