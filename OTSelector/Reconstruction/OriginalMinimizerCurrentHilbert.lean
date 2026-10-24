import OTSelector.Probability.StationaryL2Foundation
import OTSelector.Reconstruction.OriginalMinimizerPrefixCurrentCentering
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalJointSceneReroot

/-! Hilbert-space readouts of the same original minimizing current. Actual
stationarity produces covariance positivity, and the attained-minimum
conditional centering removes the current's whole invariant L² component.
This module constructs no spectral measure or boundary asymptotic. -/

open Set Function Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology ComplexOrder
noncomputable section

namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm Module Manifold
open scoped ContDiff

/-- The SAME original stationary matching law directly produces positive
semidefinite covariance blocks of any finite L² readouts. No spectral law,
second-moment replacement matching, or resampled scene is used. -/
theorem LegalWeightedStationaryPoissonMatching.posSemidef_sceneL2CrossCovariance
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {W 𝕜 n : Type*} [RCLike 𝕜] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [Fintype n]
    (f : n → Lp W 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (x : n → Fin q → ℝ) :
    Matrix.PosSemidef (fun i j ↦ ⟪f i,
      Lp.compMeasurePreserving (legalMarkedInputSceneReroot q (x j - x i))
        (Q.stationary (x j - x i)) (f j)⟫_𝕜 : Matrix n n 𝕜) := by
  exact posSemidef_stationaryL2CrossCovariance (𝕜 := 𝕜) (Q.law : Measure _)
    (legalMarkedInputSceneReroot q) Q.stationary (legalMarkedInputSceneReroot_add q) f x

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Every scalar L² readout of the actual minimizing clock-set current has
zero invariant Hilbert component. The actual conditional centering is produced
internally from its attained minimum and complete-path first moment. Prefixes
and slabs are the special choices A=Iic t and A=Ioc s t. -/
theorem OriginalSeedConditionalMoments.inner_pathClockSetCurrent_invariant_eq_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 0 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (τ : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ R.value τ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηI : Integrable η volume) (A : Set ℝ)
    (C : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ] ℝ)
    (hL2 : MemLp (C ∘ originalSeedPathClockSetCurrent S w η A) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (v : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker))))
    (hv : ∀ z, Lp.compMeasurePreserving
      (legalMarkedInputSceneReroot (finrank ℝ S.covector.ker) z) (Q.stationary z) v = v) :
    ⟪hL2.toLp (C ∘ originalSeedPathClockSetCurrent S w η A), v⟫_ℝ = 0 := by
  have hcenter := D.condExp_original_pathClockSetCurrent_eq_zero_of_minimal_value
    hF hw hq hgap hbounds Q τ hmin hη hηI A
  have hcomm := C.comp_condExp_comm (m := Q.invariantSigma)
    (D.integrable_original_pathClockSetCurrent hF hw hbounds Q hη hηI A)
  have hzero : (Q.law : Measure (LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker)))[C ∘ originalSeedPathClockSetCurrent S w η A |
        Q.invariantSigma] =ᵐ[(Q.law : Measure _)] fun _ ↦ 0 := by
    refine hcomm.symm.trans ?_
    filter_upwards [hcenter] with scene hscene
    simp only [Function.comp_apply, hscene, _root_.map_zero]
  exact inner_eq_zero_of_condExp_aeInvariantEventSigma_eq_zero
    (V := ℝ) (Q.law : Measure _) (legalMarkedInputSceneReroot _) Q.stationary
    (hL2.toLp (C ∘ originalSeedPathClockSetCurrent S w η A)) v
    ((condExp_congr_ae hL2.coeFn_toLp).trans hzero) hv

end OTSelector.Reconstruction
