import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthContraction
import OTSelector.Reconstruction.OriginalMinimizerFullTrafficAssembly

/-! Bounded actual regular birth phases retain original source confinement and count domination. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker
local notation "MarkClock" => PhysicalPairPalmMark (Fin qdim) × ℝ

/-- Actual occupied weight in a literal regular birth or death window. -/
def originalRegularBirthWindowWeight (H ε cap : ℝ) (side : Fin 2) (n j i ell : ℕ)
    (z : MarkClock) : ℝ≥0∞ :=
  ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
    D.originalRegularBirthWindowMask H ε cap side n j i ell z

theorem measurable_originalRegularBirthWindowWeight
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (H ε cap : ℝ) (side : Fin 2) (n j i ell : ℕ) :
    Measurable (D.originalRegularBirthWindowWeight H ε cap side n j i ell) :=
  (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul
    (D.measurable_originalRegularBirthWindowMask H ε cap side n j i ell)

theorem originalRegularBirthWindowWeight_left_supported_ne_zero
    (H ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalRegularBirthWindowWeight H ε cap 0 n j i ell z ≠ 0) :
    D.originalSupportedLeftBirthPhysicalClockWeight H cap n j i ell z ≠ 0 := by
  exact mul_ne_zero (left_ne_zero_of_mul hz) (right_ne_zero_of_mul (right_ne_zero_of_mul hz))

/-- One phase choice retains geometry at all scales and actual bounded-phase
confinement at scales at most one. -/
theorem exists_original_regularBirth_left_bounded_contributors_allScales
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {H ε gap diameter : ℝ} (hH : 0 < H) (hε : 0 < ε) (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y,|g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching qdim μ ν
      (D.originalFocalKinetic gap) g,Q.value τ ≤ P.value τ)
    {η : (Fin qdim → ℝ) → ℝ≥0∞} (hη : Measurable η)
    {physicalRadius basecap : ℝ} (hRadius : 0 ≤ physicalRadius) (hbasecap : 0 < basecap)
    (hηsupport : ∀ x,η x ≠ 0 → ‖x‖ ≤ physicalRadius) :
    ∃ h cap ρ U₀ : ℝ,0 < h ∧ 0 < cap ∧ cap ≤ basecap ∧ 0 ≤ ρ ∧ 0 < U₀ ∧
      (∀ n j i ell : ℕ,ell < birthPhysicalClockWindowCount cap →
        (∃ z : MarkClock,D.originalRegularBirthWindowMask H ε cap 0 n j i ell z ≠ 0) →
        let s := birthDyadicElapsedScale H n j
        let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
        let ref := D.originalLeftBirthPhysicalClockReference H cap n j i ell
        let cut := ref-S.level
        let width := birthPhysicalClockWindowWidth cap s
        let L : ℝ≥0 := ⟨Real.sqrt ((qdim:ℝ)/h^2),Real.sqrt_nonneg _⟩
        let R := originalNormalizedClockMobility S w T ref width
        let f := D.originalRegularBirthWindowWeight H ε cap 0 n j i ell
        IsUnit T.det ∧ cut ∈ Ioo D.lo D.hi ∧
          (∀ r ∈ Icc (0:ℝ) 1,cut+width*r ∈ Ioo D.lo D.hi) ∧ R 0 = 0 ∧
          (∀ r ∈ Icc (0:ℝ) 1,‖R r‖ ≤ ρ) ∧
          (∀ r ∈ Icc (0:ℝ) 1,∀ v ∈ Icc (0:ℝ) 1,‖R r-R v‖ ≤ ρ*|r-v|) ∧
          (∀ r ∈ Icc (0:ℝ) 1,‖R r‖*(L:ℝ) ≤ (1/2:ℝ)) ∧
          (∀ e clock,f ((physicalPairAnchor e).2,clock) ≠ 0 →
            e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h ∧
              (U₀ • 1-T*D.sourcePhaseLeg cut e.1.2*Tᵀ).PosSemidef)) ∧
      ∀ Amp : ℝ,0 ≤ Amp → ∃ radius : ℝ,0 ≤ radius ∧
      ∀ n j i ell : ℕ,ell < birthPhysicalClockWindowCount cap →
      birthDyadicElapsedScale H n j ≤ 1 →
      (∃ z : MarkClock,D.originalRegularBirthWindowMask H ε cap 0 n j i ell z ≠ 0) →
      let s := birthDyadicElapsedScale H n j
      let δ := (Real.sqrt s)⁻¹
      let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
      let ref := D.originalLeftBirthPhysicalClockReference H cap n j i ell
      let cut := ref-S.level
      let width := birthPhysicalClockWindowWidth cap s
      let L : ℝ≥0 := ⟨Real.sqrt ((qdim:ℝ)/h^2),Real.sqrt_nonneg _⟩
      let R := originalNormalizedClockMobility S w T ref width
      let f := D.originalRegularBirthWindowWeight H ε cap 0 n j i ell
      let V := occupiedPairTrafficContributors qdim (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f
      let W := birthTrafficSpatialWindow (0:Matrix (Fin qdim) (Fin qdim) ℝ) 1 s radius
      let J := D.originalLeftBirthNarrowClockBand H n j i
      IsUnit T.det ∧ cut ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0:ℝ) 1,cut+width*r ∈ Ioo D.lo D.hi) ∧ R 0 = 0 ∧
        (∀ r ∈ Icc (0:ℝ) 1,‖R r‖ ≤ ρ) ∧
        (∀ r ∈ Icc (0:ℝ) 1,∀ v ∈ Icc (0:ℝ) 1,‖R r-R v‖ ≤ ρ*|r-v|) ∧
        (∀ r ∈ Icc (0:ℝ) 1,‖R r‖*(L:ℝ) ≤ (1/2:ℝ)) ∧
        (∀ e clock,f ((physicalPairAnchor e).2,clock) ≠ 0 →
          e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h ∧
            (U₀ • 1-T*D.sourcePhaseLeg cut e.1.2*Tᵀ).PosSemidef) ∧
      ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ Amp*δ →
        (∀ p ∈ V scene,p.1 ∈ W ∧ p.2.1.1 ∈ J) ∧
        physicalScenePairKernel scene.1 (V scene) ≤
          (scene.2 : Measure (LegalColoredInputPoint qdim)) ((W ×ˢ J) ×ˢ {(0:Fin 2)}) := by
  obtain ⟨h,U₀,hh,hU₀,helig⟩ :=
    D.exists_original_regularBirth_left_phaseEligibility_shortLegUpper hF hw hH hε hgap hbounds
  obtain ⟨cap,ρ,hcap,hcapbase,hρ,hgeom⟩ :=
    D.exists_original_regularBirth_left_contractive_windows hF hw hH hε hgap hbounds hbasecap hh
  obtain ⟨C,hC,hCbound⟩ := exists_norm_bound_of_posSemidef_scalar_upper (ι := Fin qdim) U₀
  let L : ℝ≥0 := ⟨Real.sqrt ((qdim:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let a := Real.sqrt (qdim:ℝ)*physicalRadius
  let b := Real.sqrt (8*|τ| *gBound/h)
  have ha : 0 ≤ a := by dsimp [a];positivity
  refine ⟨h,cap,ρ,U₀,hh,hcap,hcapbase,hρ,hU₀,?_,?_⟩
  · intro n j i ell hell hnonzero
    dsimp only
    obtain ⟨hT,hcut,hclockRange,hR0,hR,hRLip,hsmall⟩ := hgeom n j i ell hnonzero
    refine ⟨hT,hcut,?_,hR0,hR,hRLip,hsmall,?_⟩
    · intro r hr
      simpa only [sub_add_eq_add_sub] using hclockRange r hr
    · intro e clock hf
      exact helig hcap n j i ell hell e clock (right_ne_zero_of_mul hf)
  intro Amp hAmp
  let radius := a+(ρ+C)*(2*Amp+2*((L:ℝ)*a+b))
  have hradius : 0 ≤ radius := by dsimp [radius,b];positivity
  refine ⟨radius,hradius,?_⟩
  intro n j i ell hell hs1 hnonzero
  dsimp only
  let s := birthDyadicElapsedScale H n j
  let δ := (Real.sqrt s)⁻¹
  let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
  let ref := D.originalLeftBirthPhysicalClockReference H cap n j i ell
  let cut := ref-S.level
  let width := birthPhysicalClockWindowWidth cap s
  let f := D.originalRegularBirthWindowWeight H ε cap 0 n j i ell
  let d := fun z : MarkClock ↦ originalSeedPathOffset S w z.2 z.1
  have hs : 0 < s := div_pos (birthDyadicShellScale_pos hH n) (by positivity)
  have hδpos : 0 < δ := by dsimp [δ];positivity
  have hδ : 1 ≤ δ := by
    apply (one_le_inv₀ (Real.sqrt_pos.mpr hs)).mpr
    exact (Real.sqrt_le_one).mpr hs1
  rcases hgeom n j i ell hnonzero with ⟨hT,hcut,hclockRange,hR0,hR,hRLip,hsmall⟩
  let _ := Matrix.invertibleOfIsUnitDet T hT
  have helig' : ∀ e clock,f ((physicalPairAnchor e).2,clock) ≠ 0 →
      e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h ∧
        (U₀ • 1-T*D.sourcePhaseLeg cut e.1.2*Tᵀ).PosSemidef := by
    intro e clock hf
    exact helig hcap n j i ell hell e clock (right_ne_zero_of_mul hf)
  have hclock : ∀ m clock,f (m,clock) ≠ 0 →
      ∃ r ∈ Icc (0:ℝ) 1,clock = cut+S.level+width*r := by
    intro m clock hf
    obtain ⟨r,hr,heq⟩ := D.originalSupportedLeftBirthPhysicalClockWeight_clock_witness hH hcap n j i ell
      (m,clock) (D.originalRegularBirthWindowWeight_left_supported_ne_zero H ε cap n j i ell _ hf)
    exact ⟨r,hr,by simpa only [cut,sub_add_cancel] using heq⟩
  have hwindow : ∀ x,η x ≠ 0 → ‖T*ᵥx‖ ≤ a*δ := by
    intro x hx
    have hb := birthNormalizer_mulVec_norm_le_coarseScale_of_norm_le
      (Matrix.PosSemidef.zero (n := Fin qdim)) zero_lt_one le_rfl hs (hηsupport x hx)
    simpa only [birthResidueScale,smul_zero,add_zero,birthTrafficCoarseScale,Real.one_rpow,
      mul_one,Fintype.card_fin] using hb
  have hclockRange' : ∀ r ∈ Icc (0:ℝ) 1,cut+width*r ∈ Ioo D.lo D.hi := by
    intro r hr
    simpa only [cut,sub_add_eq_add_sub] using hclockRange r hr
  have hR' : ∀ r ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) width r‖ ≤ ρ := by
    simpa only [cut,sub_add_cancel] using hR
  have hsmall' : ∀ r ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) width r‖*Real.sqrt ((qdim:ℝ)/h^2) ≤ (1/2:ℝ) := by
    simpa only [cut,sub_add_cancel] using hsmall
  have hnodes := D.ae_original_minimizer_boundedPhase_contributor_bounds hF hw hgap hbounds T
    hg hgb τ Q hmin hcut hh hclockRange' hsmall' hR' hclock hwindow
    (fun e c hf ↦ (helig' e c hf).1) (mul_nonneg ha hδpos.le) (mul_nonneg hAmp hδpos.le)
  refine ⟨hT,hcut,hclockRange',hR0,hR,hRLip,hsmall,helig',?_⟩
  filter_upwards [Q.full_matching,hnodes] with scene hfull hnodes
  intro hamp
  have hsource : ∀ e ∈ occupiedCompletePathTrafficContributors qdim d η f scene,
      e.1 ∈ birthTrafficSpatialWindow (0:Matrix (Fin qdim) (Fin qdim) ℝ) 1 s radius ×ˢ
        D.originalLeftBirthNarrowClockBand H n j i := by
    intro e he
    obtain ⟨clock,_,hf⟩ := legalMarkedCompletePathEdgeTraffic_ne_zero_exists_clock d η f e he.2
    have hnode := hnodes hamp e he
    have hleg := hCbound _ (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut e.1.2)
      (helig' e clock hf).2
    have hendpoint := D.normalizedMomentumNode_source_norm_le T e hnode.1 hC
      hnode.2.2.2.1 hnode.2.2.1 hleg
    have hscaled : ‖T*ᵥe.1.1‖ ≤ δ*radius := by
      apply hendpoint.trans
      calc
        _ = a*δ+(ρ+C)*(2*(Amp*δ)+2*((L:ℝ)*(a*δ)+b)) := by ring
        _ ≤ δ*radius := bounded_phase_endpoint_radius_le_coarseScale hδ (Real.sqrt_nonneg _) hρ hC
    refine ⟨?_,?_⟩
    · apply mem_birthTrafficSpatialWindow_of_normalized_norm (Matrix.PosSemidef.zero (n := Fin qdim))
        zero_lt_one hs e.1.1
      simpa only [birthResidueScale,smul_zero,add_zero,birthTrafficCoarseScale,
        Real.one_rpow,mul_one,Fintype.card_fin] using hscaled
    · simpa only [physicalPairAnchor] using D.originalSupportedLeftBirthPhysicalClockWeight_source_mem_band
        H cap n j i ell _ (D.originalRegularBirthWindowWeight_left_supported_ne_zero H ε cap n j i ell _ hf)
  refine ⟨?_,?_⟩
  · intro p hp
    exact hsource ((physicalPairAnchorHomeomorph _).symm p) hp
  · exact occupiedPairTrafficContributors_source_count_le d
      (measurable_originalSeedPathOffset_joint S hF hw) hη
      (D.measurable_originalRegularBirthWindowWeight hF hw H ε cap 0 n j i ell) scene hfull
      ((isCompact_birthTrafficSpatialWindow (0:Matrix (Fin qdim) (Fin qdim) ℝ) 1 s radius).measurableSet.prod
        (D.measurableSet_originalLeftBirthNarrowClockBand H n j i)) hsource

/-- The actual original minimizer confines bounded regular source births to
one physical source window and bounds their count by the same original input PPP. -/
theorem exists_original_regularBirth_left_bounded_contributors
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {H ε gap diameter : ℝ} (hH : 0 < H) (hε : 0 < ε) (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y,|g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching qdim μ ν
      (D.originalFocalKinetic gap) g,Q.value τ ≤ P.value τ)
    {η : (Fin qdim → ℝ) → ℝ≥0∞} (hη : Measurable η)
    {physicalRadius basecap : ℝ} (hRadius : 0 ≤ physicalRadius) (hbasecap : 0 < basecap)
    (hηsupport : ∀ x,η x ≠ 0 → ‖x‖ ≤ physicalRadius) :
    ∃ h cap ρ U₀ : ℝ,0 < h ∧ 0 < cap ∧ cap ≤ basecap ∧ 0 ≤ ρ ∧ 0 < U₀ ∧
      ∀ Amp : ℝ,0 ≤ Amp → ∃ radius : ℝ,0 ≤ radius ∧
      ∀ n j i ell : ℕ,ell < birthPhysicalClockWindowCount cap →
      birthDyadicElapsedScale H n j ≤ 1 →
      (∃ z : MarkClock,D.originalRegularBirthWindowMask H ε cap 0 n j i ell z ≠ 0) →
      let s := birthDyadicElapsedScale H n j
      let δ := (Real.sqrt s)⁻¹
      let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
      let ref := D.originalLeftBirthPhysicalClockReference H cap n j i ell
      let cut := ref-S.level
      let width := birthPhysicalClockWindowWidth cap s
      let L : ℝ≥0 := ⟨Real.sqrt ((qdim:ℝ)/h^2),Real.sqrt_nonneg _⟩
      let R := originalNormalizedClockMobility S w T ref width
      let f := D.originalRegularBirthWindowWeight H ε cap 0 n j i ell
      let V := occupiedPairTrafficContributors qdim (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f
      let W := birthTrafficSpatialWindow (0:Matrix (Fin qdim) (Fin qdim) ℝ) 1 s radius
      let J := D.originalLeftBirthNarrowClockBand H n j i
      IsUnit T.det ∧ cut ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0:ℝ) 1,cut+width*r ∈ Ioo D.lo D.hi) ∧ R 0 = 0 ∧
        (∀ r ∈ Icc (0:ℝ) 1,‖R r‖ ≤ ρ) ∧
        (∀ r ∈ Icc (0:ℝ) 1,∀ v ∈ Icc (0:ℝ) 1,‖R r-R v‖ ≤ ρ*|r-v|) ∧
        (∀ r ∈ Icc (0:ℝ) 1,‖R r‖*(L:ℝ) ≤ (1/2:ℝ)) ∧
        (∀ e clock,f ((physicalPairAnchor e).2,clock) ≠ 0 →
          e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h ∧
            (U₀ • 1-T*D.sourcePhaseLeg cut e.1.2*Tᵀ).PosSemidef) ∧
      ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ Amp*δ →
        (∀ p ∈ V scene,p.1 ∈ W ∧ p.2.1.1 ∈ J) ∧
        physicalScenePairKernel scene.1 (V scene) ≤
          (scene.2 : Measure (LegalColoredInputPoint qdim)) ((W ×ˢ J) ×ˢ {(0:Fin 2)}) := by
  obtain ⟨h,cap,ρ,U₀,hh,hcap,hcapbase,hρ,hU₀,_hgeom,hbounded⟩ :=
    D.exists_original_regularBirth_left_bounded_contributors_allScales
      hF hw hH hε hgap hbounds hg hgb τ Q hmin hη hRadius hbasecap hηsupport
  exact ⟨h,cap,ρ,U₀,hh,hcap,hcapbase,hρ,hU₀,hbounded⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
