import OTSelector.Reconstruction.OriginalMinimizerBirthSourceCarrier

/-! The actual large canonical-phase birth contribution consumes the same
geometric window certificate, original-input count carrier and true weighted
Palm mean. Its physical s² energy rate is proved before summing birth bands. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "q" => finrank ℝ S.covector.ker

/-- At every actual original birth subwindow, the same concrete canonical
mobility/eligibility certificate gives the full large-phase square estimate.
The only remaining input is that geometric certificate: original counts, the
per-edge bound and true Palm moments are produced here from the original law. -/
theorem exists_original_left_birth_largePhase_real_square_rate
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 0<q)
    {density : M→ℝ} {v : M→E→ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀x,0≤density x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x:ℝ↦x-S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0<gap)
    {poleη : ℝ} (hη : 0<poleη) (hηspan : poleη<D.hi-D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ→Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀r∈Ioo 0 poleη,originalSeedKernel S w (D.lo+r)=(r^2)⁻¹•G+Rem r)
    {g:ℝ→ℝ→ℝ} {gBound:ℝ} (hg:Measurable (Function.uncurry g))
    (hgb:∀x y,|g x y|≤gBound) (τ:ℝ)
    (Q:LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin:∀P:LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {η:(Fin q→ℝ)→ℝ} (hηmeas:Measurable η) (hη0:∀x,0≤η x)
    {physicalRadius M₀:ℝ} (hphysicalRadius:0≤physicalRadius)
    (hηR:∀x,physicalRadius<‖x‖→η x=0) (hM:0≤M₀) (hηM:∀x,η x≤M₀) :
    ∃σ:ℝ,0<σ∧∀{h ρ cap:ℝ},0<h→0≤ρ→0<cap→cap≤σ→
    ∃ ε₀ A B K₀ : ℝ,0<ε₀∧ε₀≤1∧0≤A∧0≤B∧0≤K₀∧
    ∀{ε:ℝ},0<ε→ε<ε₀→∀n j i ell:ℕ,
      i<dyadicBirthBandCount j→ell<birthPhysicalClockWindowCount cap→
      let t:=birthDyadicShellScale ε n
      let s:=birthDyadicElapsedScale ε n j
      let δ:=birthTrafficCoarseScale q t s
      let T:=positiveMatrixNormalizer (birthResidueScale G t s)
      let cut:=D.originalLeftBirthPhysicalClockReference ε cap n j i ell-S.level
      let width:=birthPhysicalClockWindowWidth cap s
      let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
      let R:=originalNormalizedClockMobility S w T (cut+S.level) width
      let f:=D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
      IsUnit T.det→cut∈Ioo D.lo D.hi→
      (∀r∈Icc (0:ℝ) 1,cut+width*r∈Ioo D.lo D.hi)→
      (∀r∈Icc (0:ℝ) 1,‖R r‖≤ρ)→
      (∀r∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,‖R r-R v‖≤ρ*|r-v|)→
      (∀r∈Icc (0:ℝ) 1,‖R r‖*(L:ℝ)≤(1/2:ℝ))→
      (∀(e:LegalMarkedPhysicalEdge q) clock,f ((physicalPairAnchor e).2,clock)≠0→
        e∈D.normalizedMomentumPhaseEligibleEdges T cut h)→
      ∀{K:ℝ},K₀≤K→
      let a:=Real.sqrt (q:ℝ)*physicalRadius
      let b:=Real.sqrt (8*|τ| *gBound/h)
      let k:=D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ ρ δ
      let Big:={scene:LegalMarkedOptimalInputScene q|1≤k scene∧
        δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖∧
        2*((L:ℝ)*(a*δ)+b)≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖}
      let traffic:=Big.indicator (fun scene:LegalMarkedOptimalInputScene q↦
        (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
          (fun x↦ENNReal.ofReal (η x)) f scene).toReal)
      let Band:={m:PhysicalPairPalmMark (Fin q)|m.1.1∈D.originalLeftBirthNarrowClockBand ε n j i}
      let budget:=A*K*s^2*
        (t^(-2+1/(q:ℝ))*(∫⁻m in Band,ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
            ∂legalMarkedJointPalm q Q.law).toReal+
          t^(-1+1/(q:ℝ))*(∫⁻m in Band,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
            ∂legalMarkedJointPalm q Q.law).toReal)+B*Real.exp (-(K-K₀)/2)
      MemLp traffic 2 (Q.law:Measure (LegalMarkedOptimalInputScene q))∧
        (∫scene,traffic scene^2∂(Q.law:Measure (LegalMarkedOptimalInputScene q)))≤budget∧
        eLpNorm traffic 2 (Q.law:Measure (LegalMarkedOptimalInputScene q))≤
          ENNReal.ofReal (Real.sqrt budget) := by
  obtain ⟨εs,σ,hεs,hσ,hsingle⟩:=D.exists_original_left_birthWindow_single_bound hF hw
  obtain ⟨εc,Ddet,hεc,hεc1,hDdet,hcarrier⟩:=
    D.exists_original_left_birth_sourceDetCarrier_all_caps hF hw hq hbounds hgap
      c hdensityCont hdensity0 hv hv0 hdensity hη hηspan hG hRem hpole
  obtain ⟨εp,Cp,hεp,hCp,hpalm⟩:=
    D.exists_original_left_birth_coarseWeightedPalm_real_rate hF hw hη hηspan hG hRem hpole
  obtain ⟨Λ,hΛ,hcarrier⟩:=hcarrier 1
  refine ⟨σ,hσ,?_⟩
  intro h ρ cap hh hρ hcap hcapσ
  let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let a:=Real.sqrt (q:ℝ)*physicalRadius
  let b:=Real.sqrt (8*|τ| *gBound/h)
  let radius:=max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let Ccurve:=canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ ρ
  let Bedge:=4*M₀*(physicalRadius+1)
  let space:=(∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin q→ℝ))).toReal
  let A:=3*Bedge*(Ccurve+1)*space*(cap*Cp)
  let B:=Bedge^2*commonScaleSourceEnvelopeBudget q Λ radius
  let K₀:=commonScaleSourceCountThreshold q Λ radius
  let ε₀:=min εs (min εc εp)
  have ha:0≤a:=by dsimp only [a];positivity
  have hb:0≤b:=Real.sqrt_nonneg _
  have hradius:0≤radius:=by dsimp only [radius];positivity
  have hcurve:1≤Ccurve:=(canonicalPhaseCurveScaleCoefficient_bounds (L:ℝ) ρ ρ).1
  have hBedge:0≤Bedge:=by dsimp only [Bedge];positivity
  have hcurve0:0≤Ccurve:=by linarith
  have hA:0≤A:=by dsimp only [A,space];positivity
  have hbudget:0≤commonScaleSourceEnvelopeBudget q Λ radius:=by
    apply tsum_nonneg
    intro n
    positivity
  have hB:0≤B:=mul_nonneg (sq_nonneg _) hbudget
  have he1:0≤Real.exp 1-1:=sub_nonneg.mpr (Real.one_le_exp zero_le_one)
  have hK₀:0≤K₀:=by
    dsimp only [K₀,commonScaleSourceCountThreshold]
    positivity
  have hε₀:0<ε₀:=lt_min hεs (lt_min hεc hεp)
  have hε₀s:ε₀≤εs:=min_le_left _ _
  have hε₀c:ε₀≤εc:=(min_le_right _ _).trans (min_le_left _ _)
  have hε₀p:ε₀≤εp:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε₀,A,B,K₀,hε₀,hε₀c.trans hεc1,hA,hB,hK₀,?_⟩
  intro ε hε hεsmall n j i ell hi hell
  dsimp only
  let t:=birthDyadicShellScale ε n
  let s:=birthDyadicElapsedScale ε n j
  let δ:=birthTrafficCoarseScale q t s
  let T:=positiveMatrixNormalizer (birthResidueScale G t s)
  let cut:=D.originalLeftBirthPhysicalClockReference ε cap n j i ell-S.level
  let width:=birthPhysicalClockWindowWidth cap s
  let f:=D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
  let J:=D.originalLeftBirthNarrowClockBand ε n j i
  let Carrier:=D.originalBirthSourceDetCarrier T cut J Ddet
  let d:=fun z:PhysicalPairPalmMark (Fin q)×ℝ↦originalSeedPathOffset S w z.2 z.1
  intro hT hcut hclockRange hR hRLip hsmall helig K hK
  have hK0:0≤K:=hK₀.trans hK
  let _:=Matrix.invertibleOfIsUnitDet T hT
  have ht:0<t:=birthDyadicShellScale_pos hε n
  have hband:=birthDyadicClockBand_base_bounds hε n j i hi
  have hs:0<s:=hband.1
  have ht1:t≤1:=by
    have htε:2*t≤ε:=by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    linarith [hεsmall.le.trans (hε₀c.trans hεc1)]
  have hδ:1≤δ:=one_le_birthTrafficCoarseScale q ht ht1 hs hband.2.1
  have hηENN:Measurable (fun x↦ENNReal.ofReal (η x)):=hηmeas.ennreal_ofReal
  have hηsupport:∀x,ENNReal.ofReal (η x)≠0→‖x‖≤physicalRadius:=by
    intro x hx
    by_contra hn
    exact hx (by rw [hηR x (lt_of_not_ge hn),ENNReal.ofReal_zero])
  have hηwindow:∀x,ENNReal.ofReal (η x)≠0→‖T*ᵥx‖≤a*δ:=by
    intro x hx
    simpa only [Fintype.card_fin] using
      birthNormalizer_mulVec_norm_le_coarseScale_of_norm_le hG ht ht1 hs (hηsupport x hx)
  have hηfinite:(∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin q→ℝ)))≠(∞:ℝ≥0∞):=by
    have hsupport:Function.support (fun x↦ENNReal.ofReal (η x))⊆
        Metric.closedBall (0:Fin q→ℝ) physicalRadius:=by
      intro x hx
      simpa only [Metric.mem_closedBall,dist_zero_right] using hηsupport x hx
    rw [←setLIntegral_eq_of_support_subset hsupport]
    apply ne_top_of_le_ne_top (b:=ENNReal.ofReal M₀*volume (Metric.closedBall (0:Fin q→ℝ) physicalRadius))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (isCompact_closedBall _ _).measure_ne_top
    · calc
        _≤∫⁻_x in Metric.closedBall (0:Fin q→ℝ) physicalRadius,ENNReal.ofReal M₀:=
          lintegral_mono (fun x↦ENNReal.ofReal_le_ofReal (hηM x))
        _=_:=by simp
  have hffinite:=D.original_left_supportedBirthWindow_palm_lt_top hF hw hbounds Q ε cap n j i ell
  have hcarrier':=hcarrier hε (hεsmall.trans_le hε₀c) hcap n j i ell hi hell
  have hCarrier:MeasurableSet Carrier:=D.measurableSet_originalBirthSourceDetCarrier hF hw T hcut
    (D.measurableSet_originalLeftBirthNarrowClockBand ε n j i) Ddet
  have hunit:((volume:Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ Carrier 0 0 1)≤ENNReal.ofReal Λ:=by
    apply (hcarrier'.2.2.2 0 0).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hΛ.le ((div_le_one ht).mpr hband.2.1))
  have hclock:∀m clock,f (m,clock)≠0→∃r∈Icc (0:ℝ) 1,clock=cut+S.level+width*r:=by
    intro m clock hf
    obtain ⟨r,hr,heq⟩:=D.originalSupportedLeftBirthPhysicalClockWeight_clock_witness
      hε hcap n j i ell (m,clock) hf
    exact ⟨r,hr,by simpa only [cut,sub_add_cancel] using heq⟩
  have hmask:∀(e:LegalMarkedPhysicalEdge q) clock,f ((physicalPairAnchor e).2,clock)≠0→
      e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.1.2∈Carrier:=by
    intro e clock hf
    exact ⟨helig e clock hf,hcarrier'.2.2.1 e clock hf⟩
  have hsingle':=hsingle hε (hεsmall.trans_le hε₀s) hcap hcapσ n j i ell hi hell
    hphysicalRadius hM hη0 hηM hηR
  have hbound:∀e∈legalMarkedCompletePathContributors q d (fun x↦ENNReal.ofReal (η x)) f,
      (legalMarkedCompletePathEdgeTraffic q d (fun x↦ENNReal.ofReal (η x)) f e).toReal≤Bedge:=by
    intro e _
    have hb:=ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsingle' e.1.1 (physicalPairAnchor e).2)
    simpa only [legalMarkedCompletePathEdgeTraffic,physicalPairAnchor,d,f,Bedge,
      ENNReal.toReal_ofReal (show 0≤4*M₀*(physicalRadius+1) by positivity)] using hb
  have hp:=hpalm hε (hεsmall.trans_le hε₀p) hcap hgap hbounds Q n j i ell hi hell
  have hpfinite:(∫⁻m,∫⁻clock:ℝ,ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,clock)
      ∂volume∂legalMarkedJointPalm q Q.law)≠(∞:ℝ≥0∞):=hp.1
  have hlarge:=D.original_minimizer_commonScale_large_traffic_memLp_two_le hF hw hgap hbounds
    T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hρ hR hRLip
    hηENN (D.measurable_originalSupportedLeftBirthPhysicalClockWeight hF hw ε cap n j i ell)
    hclock hηwindow hCarrier hmask hηfinite hffinite.ne hBedge hΛ.le hbound hunit hK hpfinite
  let Band:={m:PhysicalPairPalmMark (Fin q)|m.1.1∈J}
  let e:=(∫⁻m in Band,ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
    ∂legalMarkedJointPalm q Q.law).toReal
  let v:=(∫⁻m in Band,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
    ∂legalMarkedJointPalm q Q.law).toReal
  let weightedPalm:=(∫⁻m,∫⁻clock:ℝ,ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,clock)
    ∂volume∂legalMarkedJointPalm q Q.law).toReal
  have hmain:(3*Bedge*(K*(Ccurve+1)/δ))*
      ((∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin q→ℝ)))*
        (∫⁻m,∫⁻clock:ℝ,ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,clock)
          ∂volume∂legalMarkedJointPalm q Q.law)).toReal≤
      A*K*s^2*(t^(-2+1/(q:ℝ))*e+t^(-1+1/(q:ℝ))*v):=by
    rw [ENNReal.toReal_mul]
    calc
      _=(3*Bedge*(Ccurve+1)*space*K)*(δ⁻¹*weightedPalm):=by
        dsimp only [space,weightedPalm]
        rw [div_eq_mul_inv]
        ring
      _≤(3*Bedge*(Ccurve+1)*space*K)*((cap*Cp)*
          (s^2*t^(-2+1/(q:ℝ))*e+s^2*t^(-1+1/(q:ℝ))*v)):=
        mul_le_mul_of_nonneg_left hp.2 (by dsimp only [space];positivity)
      _=_:=by dsimp only [A];ring
  have hmean:=hlarge.2.1
  have hnewmean:=hmean.trans (add_le_add hmain
    (le_refl (B*Real.exp (-(K-K₀)/2))))
  exact ⟨hlarge.1,hnewmean,eLpNorm_two_le_sqrt_of_integral_sq_le hlarge.1 hnewmean⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
