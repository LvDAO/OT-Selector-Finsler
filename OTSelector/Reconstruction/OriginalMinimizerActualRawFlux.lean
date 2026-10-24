import OTSelector.Reconstruction.OriginalMinimizerPathClockCurrentLtwo
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessMinimizerRawFlux

/-! Actual original density inputs produce coordinate L², one common normal frame and vanishing
surface-order raw flux variance for the same countable family of original clock-set currents. -/

open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology BigOperators InnerProductSpace ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The original two population densities and same attained minimizer produce the coordinate
L² evidence internally. One common frame then annihilates every scalar current face projection
and gives vanishing normalized raw physical cube-flux variance for the whole countable family. -/
theorem OriginalSeedConditionalMoments.exists_actual_coordinateLtwo_common_frame_rawFlux_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {densityμ densityν : M → ℝ} {v : M → E → ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀ x, 0 ≤ densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀ x, 0 ≤ densityν x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensityμ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ ↦ x - S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {gBound : ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ P.value τ)
    {K : Type*} [Countable K]
    (ψ ξ : K → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (hψ : ∀ a, Measurable (ψ a)) (hξ : ∀ a, Measurable (ξ a))
    (hξI : ∀ a, Integrable (ξ a) volume) (hξ0 : ∀ a x, 0 ≤ ξ a x)
    (physicalRadius M₀ : K → ℝ) (hRadius : ∀ a, 0 ≤ physicalRadius a)
    (hM : ∀ a, 0 ≤ M₀ a) (hξM : ∀ a x, ξ a x ≤ M₀ a)
    (hξR : ∀ a x, physicalRadius a < ‖x‖ → ξ a x = 0)
    (hdom : ∀ a x, |ψ a x| ≤ ξ a x) (A : K → Set ℝ) :
    ∃ hL2 : ∀ a k,
        MemLp (fun s ↦ originalSeedPathClockSetCurrent S w (ψ a) (A a) s k) 2
          (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∃ b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
          (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
        (∀ i a C,
          (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
            (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
              (originalSeedPathClockSetCurrent S w (ψ a) (A a)) (hL2 a) C) = 0) ∧
        ∀ a, Tendsto (fun R : ℝ ↦ ∫ s,
          ((R^((finrank ℝ S.covector.ker)-1))⁻¹ * Q.sceneRawCenteredCubeFlux b
            (fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _)
              (originalSeedPathClockSetCurrent S w (ψ a) (A a)) (hL2 a)
              (originalEuclideanNormalReadout (b i))) R s)^2
            ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
          atTop (𝓝 0) := by
  let hL2 : ∀ a k,
      MemLp (fun s ↦ originalSeedPathClockSetCurrent S w (ψ a) (A a) s k) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
    intro a k
    have h := D.original_minimizer_pathClockSetCurrent_memLp_two
      hF hw (by omega) cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
      hg hgb τ Q hmin (hξ a) (hξI a) (hξ0 a) (hRadius a) (hM a) (hξM a) (hξR a)
      (hψ a) (hdom a) (A a)
      (ContinuousLinearMap.proj k : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ] ℝ)
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using h.2.1
  have hψI (a : K) : Integrable (ψ a) volume :=
    (hξI a).mono' (hψ a).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hdom a x)
  obtain ⟨b, hb⟩ := D.exists_basis_projection_all_pathClockSetCurrent_readouts_zero
    hF hw hq hgap hbounds Q τ hmin ψ hψ hψI A hL2
  refine ⟨hL2, b, hb, ?_⟩
  intro a
  apply Q.tendsto_integral_sq_normalized_sceneRawCenteredCubeFlux_zero b
    (fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _)
      (originalSeedPathClockSetCurrent S w (ψ a) (A a)) (hL2 a)
      (originalEuclideanNormalReadout (b i)))
  intro i
  exact hb i a (originalEuclideanNormalReadout (b i))

end OTSelector.Reconstruction
