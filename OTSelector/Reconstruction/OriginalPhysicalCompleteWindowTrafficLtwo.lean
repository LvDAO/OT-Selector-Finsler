import OTSelector.Reconstruction.OriginalMinimizerCompleteWindowTrafficLtwo
import OTSelector.Reconstruction.FinslerFocalLiteralEdgeOccupation
import OTSelector.Reconstruction.OriginalCompactClockWeightedOccupation
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! Physical endpoint windows provide the literal one-edge constant and every
Palm integrability input in the original current-scale large-traffic L2 estimate. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}


private theorem finite_spatial_smoothing_mass {q : ℕ}
    {η : (Fin q → ℝ) → ℝ}
    {R M : ℝ} (hηM : ∀ x, η x ≤ M)
    (hηR : ∀ x, R < ‖x‖ → η x = 0) :
    (∫⁻ x, ENNReal.ofReal (η x) ∂(volume : Measure (Fin q → ℝ))) ≠ (⊤ : ℝ≥0∞) := by
  have hpoint : ∀ x, ENNReal.ofReal (η x) ≤
      (Metric.closedBall (0 : Fin q → ℝ) R).indicator (fun _ ↦ ENNReal.ofReal M) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Fin q → ℝ) R
    · rw [indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (hηM x)
    · have hnorm : R < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
      rw [hηR x hnorm, ENNReal.ofReal_zero]
      positivity
  have hbound := lintegral_mono (μ := (volume : Measure (Fin q → ℝ))) hpoint
  rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet, lintegral_const,
    Measure.restrict_apply_univ] at hbound
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (isCompact_closedBall (0 : Fin q → ℝ) R).measure_lt_top.ne) hbound

/-- Original kinetic energy internally supplies all Palm moments needed for
complete physical-window L2 traffic. The physical kernel, original two clocks,
actual canonical field and unchanged original minimizer are retained. -/
theorem OriginalSeedConditionalMoments.original_minimizer_physicalWindowTraffic_memLp_two
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h ell a : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h) (ha : 0 ≤ a)
    (hclockRange : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ *
        Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ))
    {ρ A : ℝ} (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r -
        originalNormalizedClockMobility S w T (cut + S.level) ell r'‖ ≤ A * |r - r'|)
    {R₀ M₀ : ℝ} (hR₀ : 0 ≤ R₀) (hM₀ : 0 ≤ M₀)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηM : ∀ x, η x ≤ M₀)
    (hηR : ∀ x, R₀ < ‖x‖ → η x = 0)
    (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (hmaskM : Measurable mask) (hmaskOne : ∀ z, mask z ≤ 1)
    (hclock : ∀ m c, mask (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (heligible : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      ENNReal.ofReal ‖originalSeedClockOccupation S w c (physicalPairAnchor e).2‖ *
          mask ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    {J : Set ℝ} (hJ : IsCompact J)
    (hclockJ : ∀ c ∈ J, c - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hzero : ∀ m c, c ∉ J → mask (m, c) = 0)
    (hsingle : ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))) ≤
          ENNReal.ofReal (4 * M₀ * (R₀ + 1))) :
    MemLp (fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x))
      (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) s).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
  let f := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
  have hf : Measurable f :=
    (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hmaskM
  have hηfinite := finite_spatial_smoothing_mass hηM hηR
  have hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞) := by
    apply ne_top_of_le_ne_top (b := ∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
    · rw [D.lintegral_original_clockOccupation_norm_eq_pathLength hF hw hbounds Q]
      exact ENNReal.ofReal_ne_top
    · apply lintegral_mono
      intro m
      apply lintegral_mono
      intro c
      exact mul_le_of_le_one_right (by positivity) (hmaskOne (m, c))
  have hpfinite : (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞) := by
    simpa only [originalNormalizedMomentumMarkNorm, f] using
      (D.lintegral_original_compactClock_maskedWeightedOccupation_lt_top hF hw hgap
        hbounds Q (Tᵀ)⁻¹ hJ hclockJ mask hmaskOne hzero).ne
  apply D.original_minimizer_completeWindowTraffic_memLp_two (B := 4 * M₀ * (R₀ + 1))
    hF hw hgap hbounds T
    hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
  · intro m c hc
    exact hclock m c (right_ne_zero_of_mul hc)
  · intro x hx
    apply hηwindow x
    intro hn
    rw [hn, ENNReal.ofReal_zero] at hx
    exact hx rfl
  · exact heligible
  · exact hη.ennreal_ofReal
  · exact hf
  · exact hηfinite
  · exact hffinite
  · positivity
  · exact hsingle
  · exact hpfinite

end OTSelector.Reconstruction