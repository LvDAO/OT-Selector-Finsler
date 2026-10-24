import OTSelector.MeasureTheory.Lp.ThreeEventCover
import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthPalm
import OTSelector.Reconstruction.OriginalMinimizerRightRegularHeadLtwo

/-! The actual endpoint-confined regular birth count event has its K s² band
moment and original-input exponential count tail. No selected-cloud law is used. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
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
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker
local notation "MarkClock" => PhysicalPairPalmMark (Fin qdim) × ℝ

/-- One original h/cap and the actual two amplitude branches give the sharp
same-band regular birth norm at every nonempty physical window. -/
theorem exists_original_regularBirth_left_window_norm
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < qdim)
    {H ε gap diameter : ℝ} (hH : 0 < H) (hε : 0 < ε) (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y,|g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching qdim μ ν
      (D.originalFocalKinetic gap) g,Q.value τ ≤ P.value τ)
    {η : (Fin qdim → ℝ) → ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (hη0 : ∀ x,0 ≤ η x) {physicalRadius M₀ basecap : ℝ}
    (hRadius : 0 ≤ physicalRadius) (hM : 0 ≤ M₀) (hbasecap : 0 < basecap)
    (hηM : ∀ x,η x ≤ M₀) (hηR : ∀ x,physicalRadius < ‖x‖ → η x = 0) :
    ∃ h cap A Btail K₀ : ℝ,0 < h ∧ 0 < cap ∧ cap ≤ basecap ∧
      0 ≤ A ∧ 0 ≤ Btail ∧ 0 ≤ K₀ ∧
    (∀ n j i ell : ℕ,ell < birthPhysicalClockWindowCount cap →
      (∃ z : MarkClock,D.originalRegularBirthWindowMask H ε cap 0 n j i ell z ≠ 0) →
      MemLp (fun scene : LegalMarkedOptimalInputScene qdim ↦
        (legalMarkedCompletePathTraffic qdim (fun z ↦ originalSeedPathOffset S w z.2 z.1)
          (fun x ↦ ENNReal.ofReal (η x)) (D.originalRegularBirthWindowWeight H ε cap 0 n j i ell) scene).toReal)
        2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim))) ∧
    ∀ n j i ell : ℕ,ell < birthPhysicalClockWindowCount cap →
      birthDyadicElapsedScale H n j ≤ 1 →
      (∃ z : MarkClock,D.originalRegularBirthWindowMask H ε cap 0 n j i ell z ≠ 0) →
    ∀ {K : ℝ},K₀ ≤ K →
    let s := birthDyadicElapsedScale H n j
    let traffic := fun scene : LegalMarkedOptimalInputScene qdim ↦
      (legalMarkedCompletePathTraffic qdim (fun z ↦ originalSeedPathOffset S w z.2 z.1)
        (fun x ↦ ENNReal.ofReal (η x)) (D.originalRegularBirthWindowWeight H ε cap 0 n j i ell) scene).toReal
    let V := (∫⁻ m in {m : PhysicalPairPalmMark (Fin qdim) |
        m.1.1 ∈ D.originalLeftBirthNarrowClockBand H n j i},
        ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2) ∂legalMarkedJointPalm qdim Q.law).toReal
    MemLp traffic 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
      eLpNorm traffic 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ≤
        ENNReal.ofReal (A*Real.sqrt K*s*Real.sqrt V+Btail*Real.exp (-K/4)) := by
  obtain ⟨capedge,Cedge,hcapedge,hCedge,hsingle⟩ :=
    D.exists_original_regularBirth_left_window_min_bound hF hw hH hε hgap hbounds
  obtain ⟨cappalm,Cweighted,hcappalm,hCweighted,hweighted⟩ :=
    D.exists_original_regularBirth_left_window_weightedPalm_rate hF hw hH hε hgap hbounds
  let rawcap := min basecap (min capedge cappalm)
  have hrawcap : 0 < rawcap := lt_min hbasecap (lt_min hcapedge hcappalm)
  have hηsupport : ∀ x,ENNReal.ofReal (η x) ≠ 0 → ‖x‖ ≤ physicalRadius := by
    intro x hx
    by_contra hn
    exact hx (by rw [hηR x (lt_of_not_ge hn),ENNReal.ofReal_zero])
  obtain ⟨h,cap,ρ,U₀,hh,hcap,hcapraw,hρ,hU₀,hgeomall,hbounded⟩ :=
    D.exists_original_regularBirth_left_bounded_contributors_allScales
      hF hw hH hε hgap hbounds hg hgb τ Q hmin hη.ennreal_ofReal hRadius hrawcap hηsupport
  have hcapbase : cap ≤ basecap := hcapraw.trans (min_le_left _ _)
  have hcapedge' : cap ≤ capedge := hcapraw.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcappalm' : cap ≤ cappalm := hcapraw.trans ((min_le_right _ _).trans (min_le_right _ _))
  let L : ℝ≥0 := ⟨Real.sqrt ((qdim:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let a := Real.sqrt (qdim:ℝ)*physicalRadius
  let b := Real.sqrt (8*|τ| *gBound/h)
  let Amp := 1+2*((L:ℝ)*a+b)
  have ha : 0 ≤ a := by dsimp [a];positivity
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hAmp : 0 ≤ Amp := by dsimp [Amp];positivity
  obtain ⟨radius,hradius,hwindows⟩ := hbounded Amp hAmp
  let Bedge := 4*M₀*(physicalRadius+1)
  have hBedge : 0 ≤ Bedge := by dsimp [Bedge];positivity
  obtain ⟨Cgood,Bsmall,hCgood,hBsmall,hsmallMoments⟩ :=
    D.exists_original_regularBirth_confined_goodBad_smallMoments hF hw hq hgap hbounds Q 0
      hBedge hCedge (radius := radius)
  obtain ⟨Ddet,hDdet,hdet⟩ := exists_det_bound_of_posSemidef_scalar_upper (ι := Fin qdim) U₀
  obtain ⟨Ccell,hCcell,hcell⟩ := D.exists_original_regularBirth_sourcePhaseCell_intensity hF hw hq 1
  let Λ := Ccell*Ddet
  let phaseRadius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let Ccurve := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ ρ
  let space := (∫⁻ x,ENNReal.ofReal (η x) ∂(volume:Measure (Fin qdim → ℝ))).toReal
  let Clarge := 3*Bedge*(Ccurve+1)*space*cap*Cweighted
  let Rlarge := Bedge^2*commonScaleSourceEnvelopeBudget qdim Λ phaseRadius
  let K₀ := commonScaleSourceCountThreshold qdim Λ phaseRadius
  let A := Real.sqrt Cgood+Real.sqrt Clarge
  let Btail := Bsmall+Real.sqrt Rlarge*Real.exp (K₀/4)
  have hΛ : 0 ≤ Λ := by dsimp [Λ];positivity
  have hCcurve : 1 ≤ Ccurve := (canonicalPhaseCurveScaleCoefficient_bounds (L:ℝ) ρ ρ).1
  have hClarge : 0 ≤ Clarge := by dsimp [Clarge,space];positivity
  have hRlarge : 0 ≤ Rlarge := by
    apply mul_nonneg (sq_nonneg _)
    apply tsum_nonneg
    intro k
    positivity
  have hexp1 : 0 ≤ Real.exp 1-1 := sub_nonneg.mpr (Real.one_le_exp zero_le_one)
  have hphaseRadius : 0 ≤ phaseRadius := by dsimp [phaseRadius];positivity
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀,commonScaleSourceCountThreshold];positivity
  refine ⟨h,cap,A,Btail,K₀,hh,hcap,hcapbase,by dsimp [A];positivity,
    by dsimp [Btail];positivity,hK₀,?_,?_⟩
  · intro n j i ell hell hnonzero
    let s := birthDyadicElapsedScale H n j
    let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
    let ref := D.originalLeftBirthPhysicalClockReference H cap n j i ell
    let cut := ref-S.level
    let width := birthPhysicalClockWindowWidth cap s
    let mask := D.originalRegularBirthWindowMask H ε cap 0 n j i ell
    let f := D.originalRegularBirthWindowWeight H ε cap 0 n j i ell
    have hs : 0 < s := div_pos (birthDyadicShellScale_pos hH n) (by positivity)
    have hwidth : 0 < width := (birthPhysicalClockWindow_spec hcap hs).2.1
    obtain ⟨hT,hcut,hclockRange,_hR0,hR,hRLip,hsmall,helig⟩ := hgeomall n j i ell hell hnonzero
    let _ := Matrix.invertibleOfIsUnitDet T hT
    have hwin : ∀ clock ∈ Icc ref (ref+width),clock-S.level ∈ Ioo D.lo D.hi := by
      intro clock hc
      have hr : (clock-ref)/width ∈ Icc (0:ℝ) 1 :=
        ⟨div_nonneg (sub_nonneg.mpr hc.1) hwidth.le,(div_le_one hwidth).mpr (by linarith [hc.2])⟩
      have heq : cut+width*((clock-ref)/width) = clock-S.level := by
        dsimp only [cut]
        field_simp [ne_of_gt hwidth]
        ring
      have hci := hclockRange _ hr
      change cut+width*((clock-ref)/width) ∈ Ioo D.lo D.hi at hci
      rwa [heq] at hci
    have hclockMask (z : MarkClock) (hz : mask z ≠ 0) : z.2 ∈ Ioc ref (ref+width) := by
      have hm : D.originalSupportedLeftBirthPhysicalClockMask H cap n j i ell z ≠ 0 := right_ne_zero_of_mul hz
      exact D.originalLeftBirthPhysicalClockMask_clock_mem H cap n j i ell z
        ((D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff H cap n j i ell z).mp hm).2.2
    have hz : ∀ m clock,clock ∉ Icc ref (ref+width) → mask (m,clock) = 0 := by
      intro m clock hout
      by_contra hn
      exact hout ⟨(hclockMask (m,clock) hn).1.le,(hclockMask (m,clock) hn).2⟩
    have hclock : ∀ m clock,f (m,clock) ≠ 0 →
        ∃ r ∈ Icc (0:ℝ) 1,clock = cut+S.level+width*r := by
      intro m clock hf
      obtain ⟨r,hr,heq⟩ := D.originalSupportedLeftBirthPhysicalClockWeight_clock_witness hH hcap n j i ell (m,clock)
        (D.originalRegularBirthWindowWeight_left_supported_ne_zero H ε cap n j i ell (m,clock) hf)
      exact ⟨r,hr,by simpa only [cut,sub_add_cancel] using heq⟩
    have hR' : ∀ r ∈ Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T (cut+S.level) width r‖ ≤ ρ := by
      simpa only [cut,sub_add_cancel] using hR
    have hRLip' : ∀ r ∈ Icc (0:ℝ) 1,∀ v ∈ Icc (0:ℝ) 1,
        ‖originalNormalizedClockMobility S w T (cut+S.level) width r-
          originalNormalizedClockMobility S w T (cut+S.level) width v‖ ≤ ρ*|r-v| := by
      simpa only [cut,sub_add_cancel] using hRLip
    have hsmall' : ∀ r ∈ Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T (cut+S.level) width r‖*
        Real.sqrt ((qdim:ℝ)/h^2) ≤ (1/2:ℝ) := by
      intro r hr
      have hm := hsmall r hr
      change ‖originalNormalizedClockMobility S w T ref width r‖*Real.sqrt ((qdim:ℝ)/h^2) ≤ (1/2:ℝ) at hm
      simpa only [cut,sub_add_cancel] using hm
    exact D.original_regular_compactWindow_traffic_memLp_two_of_phase_geometry
      hF hw hgap hbounds hg hgb τ Q hmin 0 T hcut hh hρ hclockRange hR' hRLip' hsmall'
      isCompact_Icc hwin mask (D.measurable_originalRegularBirthWindowMask H ε cap 0 n j i ell)
      (D.originalRegularBirthWindowMask_le_one H ε cap 0 n j i ell) hz hclock
      (by intro e clock hf;exact helig e clock hf) hη hηI hRadius hBedge hηsupport (by
        intro x m
        exact (hsingle hcap hcapedge' n j i ell hRadius hM η hη0 hηM hηR x m).trans
          (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hBedge (min_le_left _ _))))
  intro n j i ell hell hs1 hnonzero K hK
  dsimp only
  let s := birthDyadicElapsedScale H n j
  let δ := (Real.sqrt s)⁻¹
  let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
  let ref := D.originalLeftBirthPhysicalClockReference H cap n j i ell
  let cut := ref-S.level
  let width := birthPhysicalClockWindowWidth cap s
  let f := D.originalRegularBirthWindowWeight H ε cap 0 n j i ell
  let mask := D.originalRegularBirthWindowMask H ε cap 0 n j i ell
  let d := fun z : MarkClock ↦ originalSeedPathOffset S w z.2 z.1
  let traffic := fun scene : LegalMarkedOptimalInputScene qdim ↦
    (legalMarkedCompletePathTraffic qdim d (fun x ↦ ENNReal.ofReal (η x)) f scene).toReal
  let J := D.originalLeftBirthNarrowClockBand H n j i
  let Carrier := D.originalBirthSourceDetCarrier T cut J Ddet
  let W := birthTrafficSpatialWindow (0:Matrix (Fin qdim) (Fin qdim) ℝ) 1 s radius
  let N := fun scene : LegalMarkedOptimalInputScene qdim ↦
    ((scene.2 : Measure (LegalColoredInputPoint qdim)) ((W ×ˢ J) ×ˢ {(0:Fin 2)})).toReal
  let Small := {scene : LegalMarkedOptimalInputScene qdim |
    ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ Amp*δ}
  let Good := {scene : LegalMarkedOptimalInputScene qdim | scene ∈ Small ∧ N scene ≤ K}
  let Bad := {scene : LegalMarkedOptimalInputScene qdim | K < N scene}
  let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ ρ δ
  let Big := {scene : LegalMarkedOptimalInputScene qdim |
    1 ≤ k scene ∧ δ ≤ ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ∧
      2*((L:ℝ)*(a*δ)+b) ≤ ‖D.normalizedMomentumPhaseField T cut h L scene 0‖}
  let energy := (∫⁻ m in {m : PhysicalPairPalmMark (Fin qdim) | m.1.1 ∈ J},
    ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2) ∂legalMarkedJointPalm qdim Q.law).toReal
  have hs : 0 < s := div_pos (birthDyadicShellScale_pos hH n) (by positivity)
  have hδ : 1 ≤ δ := (one_le_inv₀ (Real.sqrt_pos.mpr hs)).mpr (Real.sqrt_le_one.mpr hs1)
  have hk : 0 ≤ K := hK₀.trans hK
  rcases hwindows n j i ell hell hs1 hnonzero with
    ⟨hT,hcut,hclockRange,hR0,hR,hRLip,hsmall,helig,hconf⟩
  let _ := Matrix.invertibleOfIsUnitDet T hT
  have hηENN := hη.ennreal_ofReal
  have hf := D.measurable_originalRegularBirthWindowWeight hF hw H ε cap 0 n j i ell
  have hmask := D.measurable_originalRegularBirthWindowMask H ε cap 0 n j i ell
  have hd := measurable_originalSeedPathOffset_joint S hF hw
  have htraffic : Measurable traffic := (measurable_legalMarkedCompletePathTraffic d hd hηENN hf).ennreal_toReal
  have hJ := D.measurableSet_originalLeftBirthNarrowClockBand H n j i
  have hSmall : MeasurableSet Small :=
    measurableSet_le ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm measurable_const
  have hsingle' := hsingle hcap hcapedge' n j i ell hRadius hM η hη0 hηM hηR
  have hgood := hsmallMoments hs hηENN hJ mask hmask hSmall hsingle' (by
    filter_upwards [hconf] with scene hscene
    intro hsceneSmall
    obtain ⟨hsource,hcount⟩ := hscene hsceneSmall
    refine ⟨?_,hcount⟩
    intro p hp
    simpa only [ite_true,add_zero] using hsource p hp) hk
  have hηfinite : (∫⁻ x,ENNReal.ofReal (η x) ∂(volume:Measure (Fin qdim → ℝ))) ≠ (∞:ℝ≥0∞) :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hηI.2).ne
  have hffinite : (∫⁻ m,∫⁻ clock : ℝ,f (m,clock) ∂volume ∂legalMarkedJointPalm qdim Q.law) ≠ (∞:ℝ≥0∞) := by
    apply ne_top_of_le_ne_top (D.original_left_supportedBirthWindow_palm_lt_top hF hw hbounds Q H cap n j i ell).ne
    apply lintegral_mono
    intro m
    apply lintegral_mono
    intro clock
    change ENNReal.ofReal _ * (originalClockTrafficRegionMask _ _ ε 1 (m,clock) * _) ≤ ENNReal.ofReal _ * _
    exact mul_le_mul' le_rfl (mul_le_of_le_one_left zero_le
      (originalClockTrafficRegionMask_le_one _ _ ε 1 (m,clock)))
  have hclock : ∀ m clock,f (m,clock) ≠ 0 → ∃ r ∈ Icc (0:ℝ) 1,clock = cut+S.level+width*r := by
    intro m clock hfc
    obtain ⟨r,hr,heq⟩ := D.originalSupportedLeftBirthPhysicalClockWeight_clock_witness hH hcap n j i ell (m,clock)
      (D.originalRegularBirthWindowWeight_left_supported_ne_zero H ε cap n j i ell (m,clock) hfc)
    exact ⟨r,hr,by simpa only [cut,sub_add_cancel] using heq⟩
  have hηwindow : ∀ x,ENNReal.ofReal (η x) ≠ 0 → ‖T*ᵥx‖ ≤ a*δ := by
    intro x hx
    have hb' := birthNormalizer_mulVec_norm_le_coarseScale_of_norm_le
      (Matrix.PosSemidef.zero (n := Fin qdim)) zero_lt_one le_rfl hs (hηsupport x hx)
    simpa only [birthResidueScale,smul_zero,add_zero,birthTrafficCoarseScale,Real.one_rpow,
      mul_one,Fintype.card_fin] using hb'
  have hCarrier : MeasurableSet Carrier := D.measurableSet_originalBirthSourceDetCarrier hF hw T hcut hJ Ddet
  have hunit : ((volume:Measure (Fin qdim → ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ Carrier 0 0 1) ≤ ENNReal.ofReal Λ :=
    hcell hs hDdet.le hcut hJ 0 0
  have hmaskCarrier : ∀ (e : LegalMarkedPhysicalEdge qdim) clock,f ((physicalPairAnchor e).2,clock) ≠ 0 →
      e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h ∧ e.1.2 ∈ Carrier := by
    intro e clock hfc
    refine ⟨(helig e clock hfc).1,?_,?_⟩
    · simpa only [physicalPairAnchor] using D.originalSupportedLeftBirthPhysicalClockWeight_source_mem_band
        H cap n j i ell _ (D.originalRegularBirthWindowWeight_left_supported_ne_zero H ε cap n j i ell _ hfc)
    · exact hdet _ (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut e.1.2) (helig e clock hfc).2
  have hbound : ∀ e ∈ legalMarkedCompletePathContributors qdim d (fun x ↦ ENNReal.ofReal (η x)) f,
      (legalMarkedCompletePathEdgeTraffic qdim d (fun x ↦ ENNReal.ofReal (η x)) f e).toReal ≤ Bedge := by
    intro e _
    have hsingleOne := (hsingle' e.1.1 (physicalPairAnchor e).2).trans
      (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hBedge (min_le_left _ _)))
    change _ ≤ ENNReal.ofReal Bedge at hsingleOne
    have htoreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsingleOne
    simpa only [legalMarkedCompletePathEdgeTraffic,physicalPairAnchor,d,f,ENNReal.toReal_ofReal hBedge] using htoreal
  have hp := hweighted Q hcap hcappalm' n j i ell hnonzero
  have hR' : ∀ r ∈ Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T (cut+S.level) width r‖ ≤ ρ := by
    simpa only [cut,sub_add_cancel] using hR
  have hRLip' : ∀ r ∈ Icc (0:ℝ) 1,∀ v ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) width r-
        originalNormalizedClockMobility S w T (cut+S.level) width v‖ ≤ ρ*|r-v| := by
    simpa only [cut,sub_add_cancel] using hRLip
  have hsmall' : ∀ r ∈ Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T (cut+S.level) width r‖*
      Real.sqrt ((qdim:ℝ)/h^2) ≤ (1/2:ℝ) := by
    intro r hr
    have hm := hsmall r hr
    change ‖originalNormalizedClockMobility S w T ref width r‖*Real.sqrt ((qdim:ℝ)/h^2) ≤ (1/2:ℝ) at hm
    simpa only [cut,sub_add_cancel] using hm
  have hlarge := D.original_minimizer_commonScale_large_traffic_memLp_two_le
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall' hρ hR' hRLip'
    hηENN hf hclock hηwindow hCarrier hmaskCarrier hηfinite hffinite hBedge hΛ hbound hunit hK hp.1
  let weighted := ∫⁻ m,∫⁻ clock : ℝ,ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,clock)
    ∂volume ∂legalMarkedJointPalm qdim Q.law
  have hwprate : Real.sqrt s*weighted.toReal ≤ cap*Cweighted*s^2*energy := hp.2
  have hlmain : (3*Bedge*(K*(Ccurve+1)/δ))*
      ((∫⁻ x,ENNReal.ofReal (η x) ∂(volume:Measure (Fin qdim → ℝ)))*weighted).toReal ≤
      Clarge*K*s^2*energy := by
    rw [ENNReal.toReal_mul]
    calc
      _ = (3*Bedge*(Ccurve+1)*space*K)*(Real.sqrt s*weighted.toReal) := by
        dsimp only [δ,space]
        rw [div_eq_mul_inv,inv_inv]
        ring
      _ ≤ (3*Bedge*(Ccurve+1)*space*K)*(cap*Cweighted*s^2*energy) :=
        mul_le_mul_of_nonneg_left hwprate (by dsimp [space];positivity)
      _ = _ := by dsimp [Clarge];ring
  have hlargeNorm : eLpNorm (Big.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ≤
      ENNReal.ofReal (Real.sqrt Clarge*Real.sqrt K*s*Real.sqrt energy+
        Real.sqrt Rlarge*Real.exp (K₀/4)*Real.exp (-K/4)) := by
    apply hlarge.2.2.trans
    apply ENNReal.ofReal_le_ofReal
    exact (Real.sqrt_le_sqrt (add_le_add hlmain le_rfl)).trans
      (regularBirth_sqrt_square_tail hClarge hk hs ENNReal.toReal_nonneg hRlarge)
  have hgoodNorm : eLpNorm (Good.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ≤
      ENNReal.ofReal (Real.sqrt Cgood*Real.sqrt K*s*Real.sqrt energy) := by
    apply (eLpNorm_two_le_sqrt_of_integral_sq_le hgood.1 hgood.2.1).trans
    apply ENNReal.ofReal_le_ofReal
    apply le_of_eq
    rw [Real.sqrt_mul (by positivity : 0 ≤ Cgood*K*s^2),Real.sqrt_mul (by positivity : 0 ≤ Cgood*K),
      Real.sqrt_mul hCgood,Real.sqrt_sq_eq_abs,abs_of_pos hs]
    simp only [ite_true,energy,J]
  have hcover : ∀scene:LegalMarkedOptimalInputScene qdim,scene∈Good∨scene∈Bad∩Small∨scene∈Big := by
    intro scene
    by_cases hsm : scene∈Small
    · by_cases hcount : N scene≤K
      · exact Or.inl ⟨hsm,hcount⟩
      · exact Or.inr (Or.inl ⟨lt_of_not_ge hcount,hsm⟩)
    · have hamp : Amp*δ < ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ := lt_of_not_ge hsm
      have hAmp1 : 1 ≤ Amp := by dsimp [Amp];nlinarith only [mul_nonneg L.coe_nonneg ha,hb]
      have hδpos : 0 < δ := by linarith
      have hampδ : δ ≤ ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ :=
        (le_mul_of_one_le_left hδpos.le hAmp1).trans hamp.le
      have hscale := D.commonScaleNormalizedCanonicalCurveIntegerScale_spec T cut h L ρ ρ δ
        (N := 1) le_rfl scene (by simpa only [Nat.cast_one] using (one_le_div hδpos).mpr hampδ)
      have hbig : scene ∈ Big := by
        refine ⟨hscale.1,hampδ,?_⟩
        have hbδ : b ≤ b*δ := le_mul_of_one_le_right hb hδ
        dsimp only [Amp] at hamp
        nlinarith only [hamp,hbδ,hδpos]
      exact Or.inr (Or.inr hbig)
  have hbadEq : (Bad∩Small).indicator traffic=Bad.indicator (Small.indicator traffic) := by
    funext scene
    by_cases hb : scene∈Bad <;> by_cases hs : scene∈Small <;> simp [hb,hs]
  have hbLp : MemLp ((Bad∩Small).indicator traffic) 2 (Q.law:Measure (LegalMarkedOptimalInputScene qdim)) := by
    rw [hbadEq]
    exact hgood.2.2.1
  have hbNorm : eLpNorm ((Bad∩Small).indicator traffic) 2 (Q.law:Measure (LegalMarkedOptimalInputScene qdim))≤
      ENNReal.ofReal (Bsmall*Real.exp (-K/4)) := by
    rw [hbadEq]
    exact hgood.2.2.2
  have hout := nonnegative_traffic_memLp_two_of_three_event_cover
    (Q.law:Measure (LegalMarkedOptimalInputScene qdim)) htraffic.aestronglyMeasurable
    (fun _↦ENNReal.toReal_nonneg) Good (Bad∩Small) Big hcover hgood.1 hbLp hlarge.1
    (by positivity) (by positivity) (by positivity) hgoodNorm hbNorm hlargeNorm
  refine ⟨hout.1,hout.2.trans_eq ?_⟩
  apply congrArg ENNReal.ofReal
  dsimp only [A,Btail]
  ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
