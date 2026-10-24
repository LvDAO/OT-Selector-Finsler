import OTSelector.Reconstruction.FinslerOriginalBirthContributorClockBands
import OTSelector.Reconstruction.BirthTrafficSpatialWindowMembership
import OTSelector.Reconstruction.BirthNormalizerCoarseSpatialBound
import OTSelector.Reconstruction.FinslerOriginalBoundedPhaseContributorBounds
import OTSelector.Reconstruction.OriginalOccupiedTrafficInputCounts
import OTSelector.Reconstruction.OriginalNormalizedEndpointConfinement
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! The actual weighted minimizer's bounded birth phase confines every
occupied target contributor and bounds its count by the unchanged original input. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Every bounded canonical right-birth phase has one fixed-radius physical
target window at every actual dyadic scale. The same occupied contributors
retain their original narrow clock band and original target-count domination. -/
theorem OriginalSeedConditionalMoments.exists_original_right_birth_bounded_contributors_sameResidue
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ P.value τ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞} (hηmeas : Measurable η)
    {physicalRadius basecap : ℝ} (hphysicalRadius : 0 ≤ physicalRadius)
    (hbasecap : 0 < basecap) (hηsupport : ∀ x, η x ≠ 0 → ‖x‖ ≤ physicalRadius) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ h : ℝ, 0 < h ∧ ∃ cap : ℝ, 0 < cap ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ H : ℝ, 0 ≤ H → ∃ radius : ℝ, 0 ≤ radius ∧
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      ∀ n j i ell : ℕ, i < dyadicBirthBandCount j → ell < birthPhysicalClockWindowCount cap →
      let t := birthDyadicShellScale ε n
      let s := birthDyadicElapsedScale ε n j
      let δ := birthTrafficCoarseScale (finrank ℝ S.covector.ker) t s
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      let cut := D.originalRightBirthPhysicalClockReference ε cap n j i ell - S.level
      let width := -(birthPhysicalClockWindowWidth cap s)
      let R := originalNormalizedClockMobility S w T (cut + S.level) width
      let f := D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell
      let V := occupiedPairTrafficContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f
      let W := birthTrafficSpatialWindow G t s radius
      let J := D.originalRightBirthNarrowClockBand ε n j i
      IsUnit T.det ∧ cut ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0 : ℝ) 1, cut + width * r ∈ Ioo D.lo D.hi) ∧
        R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ ρ) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ‖R r - R v‖ ≤ ρ * |r - v|) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) ∧
        (∀ e clock, f ((physicalPairAnchor e).2, clock) ≠ 0 →
          e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h) ∧
      ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ →
        (∀ a ∈ V scene, a.1 + a.2.2 ∈ W ∧ a.2.1.2 ∈ J) ∧
          physicalScenePairKernel scene.1 (V scene) ≤
            (scene.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
              ((W ×ˢ J) ×ˢ {(1 : Fin 2)}) := by
  let ηsmall := min poleη 1
  have hηsmall : 0 < ηsmall := lt_min hη zero_lt_one
  have hηsmallη : ηsmall ≤ poleη := min_le_left _ _
  have hRemSmall : ContinuousOn Rem (Ioo (-ηsmall) ηsmall) :=
    hRem.mono (fun r hr ↦ ⟨lt_of_le_of_lt (neg_le_neg hηsmallη) hr.1,
      lt_of_lt_of_le hr.2 hηsmallη⟩)
  obtain ⟨ε, hε, hεη, h, hh, B, hB, U, hU, hwindows⟩ :=
    D.exists_original_right_supported_contractive_birthWindows_sameResidue hF hw hbounds hgap
      hηsmall (hηsmallη.trans_lt hηspan) hG hRemSmall
        (fun r hr ↦ hpole r ⟨hr.1, hr.2.trans_le hηsmallη⟩)
  have hεone : ε ≤ 1 := hεη.le.trans (min_le_right _ _)
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let cap := commonPhysicalNormalizedWindowFraction basecap B (L : ℝ)
  have hcap : 0 < cap := (commonPhysicalNormalizedWindowFraction_spec hbasecap hB L.coe_nonneg).1
  obtain ⟨C, hC, hCbound⟩ := exists_norm_bound_of_posSemidef_scalar_upper
    (ι := Fin (finrank ℝ S.covector.ker)) U
  let A := Real.sqrt (finrank ℝ S.covector.ker : ℝ) * physicalRadius
  let b := Real.sqrt (8 * |τ| * gBound / h)
  let ρ := cap * B
  have hA : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) hphysicalRadius
  have hρ : 0 ≤ ρ := mul_nonneg hcap.le hB
  refine ⟨ε, hε, hεone, h, hh, cap, hcap, ρ, hρ, ?_⟩
  intro H hH
  let radius := A + (ρ + C) * (2 * H + 2 * ((L : ℝ) * A + b))
  have hradius : 0 ≤ radius := by dsimp [radius, b]; positivity
  refine ⟨radius, hradius, ?_⟩
  dsimp only
  intro n j i ell hi hell
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let δ := birthTrafficCoarseScale (finrank ℝ S.covector.ker) t s
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
  let cut := ref - S.level
  let width := -(birthPhysicalClockWindowWidth cap s)
  let f := D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hs : 0 < s := (birthDyadicClockBand_base_bounds hε n j i hi).1
  have hst : s ≤ t := (birthDyadicClockBand_base_bounds hε n j i hi).2.1
  have htε : 2 * t ≤ ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have htone : t ≤ 1 := by linarith
  have hδ : 1 ≤ δ := one_le_birthTrafficCoarseScale _ ht htone hs hst
  have hδpos : 0 < δ := birthTrafficCoarseScale_pos _ ht hs
  rcases hwindows L basecap hbasecap n j i ell hi hell with
    ⟨hT, hcut, hclockRange, hRzero, hR, hRLip, hsmall, helig⟩
  let _ := Matrix.invertibleOfIsUnitDet T hT
  have hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + width * r := by
    intro m c hf
    let e := (physicalPairAnchorHomeomorph (finrank ℝ S.covector.ker)).symm (0, m)
    have heq : (physicalPairAnchor e).2 = m :=
      congrArg Prod.snd ((physicalPairAnchorHomeomorph _).apply_symm_apply (0, m))
    have hhf : f ((physicalPairAnchor e).2, c) ≠ 0 := by rwa [heq]
    obtain ⟨r, hr, hcr⟩ := (helig e c hhf).2.2
    exact ⟨r, hr, by simpa only [cut, sub_add_cancel] using hcr⟩
  have hwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ A * δ := by
    intro x hx
    simpa only [Fintype.card_fin] using
      birthNormalizer_mulVec_norm_le_coarseScale_of_norm_le hG ht htone hs (hηsupport x hx)
  have hclockRange' : ∀ r ∈ Icc (0 : ℝ) 1, cut + width * r ∈ Ioo D.lo D.hi := by
    intro r hr
    have heq : cut + width * r = ref + width * r - S.level := by
      dsimp [cut]
      ring
    rw [heq]
    exact hclockRange r hr
  have hR' : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) width r‖ ≤ ρ := by
    simpa only [cut, sub_add_cancel] using hR
  have hsmall' : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) width r‖ *
        Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ) := by
    change ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) width r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)
    simpa only [cut, sub_add_cancel] using hsmall
  have hnodes := D.ae_original_minimizer_boundedPhase_contributor_bounds hF hw hgap hbounds
    T hg hgb τ Q hmin hcut hh hclockRange' hsmall' hR' hclock hwindow
    (fun e c hf ↦ (helig e c hf).1) (mul_nonneg hA hδpos.le) (mul_nonneg hH hδpos.le)
  refine ⟨hT, hcut, hclockRange', ?_, hR', ?_, ?_, (fun e c hf ↦ (helig e c hf).1), ?_⟩
  · simpa only [cut, sub_add_cancel] using hRzero
  · simpa only [cut, sub_add_cancel] using hRLip
  · exact hsmall'
  filter_upwards [Q.full_matching, hnodes] with scene hfull hnodes
  intro hamp
  have htarget : ∀ e ∈ occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker)
      d η f scene, e.2 ∈ birthTrafficSpatialWindow G t s radius ×ˢ
        D.originalRightBirthNarrowClockBand ε n j i := by
    intro e he
    obtain ⟨clock, _, hfc⟩ := legalMarkedCompletePathEdgeTraffic_ne_zero_exists_clock d η f e he.2
    have hnode := hnodes hamp e he
    have hleg := hCbound _ (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut e.2.2)
      (helig e clock hfc).2.1
    have hendpoint := D.normalizedMomentumNode_target_norm_le hF hw T hcut e hnode.1 hnode.2.1 hC
      hnode.2.2.2.1 hnode.2.2.1 hleg
    have hscaled : ‖T *ᵥ e.2.1‖ ≤ δ * radius := by
      calc
        _ ≤ (A * δ + ρ * (2 * (H * δ) + 2 * ((L : ℝ) * (A * δ) + b))) +
            C * (2 * (H * δ) + 2 * ((L : ℝ) * (A * δ) + b)) := hendpoint
        _ = A * δ + (ρ + C) * (2 * (H * δ) + 2 * ((L : ℝ) * (A * δ) + b)) := by ring
        _ ≤ δ * radius := bounded_phase_endpoint_radius_le_coarseScale hδ (Real.sqrt_nonneg _) hρ hC
    refine ⟨mem_birthTrafficSpatialWindow_of_normalized_norm hG ht hs e.2.1
      (by simpa only [Fintype.card_fin] using hscaled), ?_⟩
    simpa only [physicalPairAnchor] using
      D.originalSupportedRightBirthPhysicalClockWeight_target_mem_band ε cap n j i ell _ hfc
  refine ⟨?_, ?_⟩
  · intro a ha
    have h := htarget ((physicalPairAnchorHomeomorph _).symm a) ha
    exact ⟨h.1, h.2⟩
  · exact occupiedPairTrafficContributors_target_count_le d
      (measurable_originalSeedPathOffset_joint S hF hw) hηmeas
      (D.measurable_originalSupportedRightBirthPhysicalClockWeight hF hw ε cap n j i ell)
      scene hfull ((isCompact_birthTrafficSpatialWindow G t s radius).measurableSet.prod
        (D.measurableSet_originalRightBirthNarrowClockBand ε n j i)) htarget

end OTSelector.Reconstruction
