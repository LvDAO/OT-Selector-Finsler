import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficCurrent
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedOmittedCut
import OTSelector.Reconstruction.OriginalRetainedSlabResidualReadouts
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetGaussGreen

/-! Actual oriented omitted-current divergence is the genuine positive-cut slab balance. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}

/-- Actual omitted source endpoint smoothing in the same selected frame, retaining [s,t). -/
def originalOrientedOmittedRawSlabSourceDensity (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell s t : ℝ)
    (z : Fin (finrank ℝ S.covector.ker) → ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ∫ x, originalEuclideanMollifier _ (x-z) ∂originalRestrictedSceneSlabSourceMeasure
    (originalOrientedPathLengthRetained S w b R ell)ᶜ s t scene

/-- Actual omitted target endpoint smoothing retains the original target convention (s,t]. -/
def originalOrientedOmittedRawSlabTargetDensity (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell s t : ℝ)
    (z : Fin (finrank ℝ S.covector.ker) → ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ∫ x, originalEuclideanMollifier _ (x-z) ∂originalRestrictedSceneSlabTargetMeasure
    (originalOrientedPathLengthRetained S w b R ell)ᶜ s t scene

/-- On the unchanged original scene, true full-minus-retained current is C1 and its actual
divergence is the omitted positive-cut/source/target balance. Local traffic, actual Fubini,
differentiation and clock FTC are internal, with no completed field identity as an input. -/
theorem OriginalSeedConditionalMoments.ae_originalOrientedOmittedCurrent_C1_divergence_balance
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ)
    {s t : ℝ} (hst : s ≤ t) :
    let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ContDiff ℝ 1 (fun z ↦ originalOrientedOmittedSeedPathClockSetCurrent S w b R ell
        (fun x ↦ η (x-z)) (Ioc s t) scene) ∧
      ∀ z, originalStageCurrentDivergence (fun z ↦ originalOrientedOmittedSeedPathClockSetCurrent S w b R ell
          (fun x ↦ η (x-z)) (Ioc s t) scene) z =
        originalOrientedOmittedRawSlabSourceDensity S w b R ell s t z scene -
        originalOrientedOmittedRawSlabTargetDensity S w b R ell s t z scene +
        originalOrientedOmittedCutDensity S w b R ell s scene z -
        originalOrientedOmittedCutDensity S w b R ell t scene z := by
  let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
  let B := originalOrientedPathLengthRetained S w b R ell
  have hB : MeasurableSet B := measurableSet_originalOrientedPathLengthRetained S hF hw b R ell
  have hη : ContDiff ℝ 1 η := (contDiff_originalEuclideanMollifier _).of_le (by norm_num)
  have hcη : HasCompactSupport η := hasCompactSupport_originalEuclideanMollifier _
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q,
    D.ae_all_originalRestrictedWeakSlab_integrable_balance hF hw Q Bᶜ hst,
    D.ae_all_originalRestrictedClockSlab_testDerivative_eq_weakSlab Q] with scene htraffic hb hd
  have hfun : (fun z ↦ originalOrientedOmittedSeedPathClockSetCurrent S w b R ell
      (fun x ↦ η (x-z)) (Ioc s t) scene) =
      fun z ↦ originalPairRestrictedSeedPathClockSetCurrent S w Bᶜ (fun x ↦ η (x-z)) (Ioc s t) scene := by
    funext z
    exact originalFull_sub_pairRestrictedCurrent_eq_compl S hF hw hη.continuous hcη B hB
      (Ioc s t) scene (htraffic (Ioc s t)) z
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (originalPairRestrictedCurrent_spatially_contDiff_derivative S hF hw hη hcη Bᶜ
      (Ioc s t) scene (htraffic (Ioc s t))).1
  · intro z
    let ψ := fun x ↦ η (x-z)
    have hψ : ContDiff ℝ 1 ψ := hη.comp (contDiff_id.sub contDiff_const)
    have hcψ : HasCompactSupport ψ := by
      simpa only [ψ, Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
        hcη.comp_homeomorph (Homeomorph.addRight (-z))
    have h := (hb ψ hψ hcψ).2
    rw [← hd Bᶜ ψ s t hst] at h
    rw [originalStageCurrentDivergence, hfun, divergence_originalPairRestrictedCurrent_spatial
      S hF hw hη hcη Bᶜ (Ioc s t) scene (htraffic (Ioc s t)) z]
    exact h

end OTSelector.Reconstruction
