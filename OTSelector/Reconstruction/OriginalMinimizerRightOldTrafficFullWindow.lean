import OTSelector.Reconstruction.OriginalMinimizerRightOldTrafficPalmRates
import OTSelector.Reconstruction.OriginalMinimizerRightOldTrafficIntensity
import OTSelector.Reconstruction.OriginalMinimizerCompleteTraffic
import OTSelector.Reconstruction.OriginalMinimizerTargetCommonScaleWindow
import OTSelector.Reconstruction.OriginalMinimizerRightBirthWindowBasic
import OTSelector.Probability.OriginalMinimizerOldRegularTrafficNorm

/-! Actual full right old-focal window norms from one original geometric choice.
Both amplitude branches and all original count events are assembled internally. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- One original h/cap selection gives the genuine full old-window norm rate
on every smaller collar, with both amplitude branches and original count tails. -/
theorem exists_original_right_old_fullWindow_level_norm
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 2≤qdim)
    {density : M→ℝ} {v : M→E→ℝ} (c : ℝ≥0∞)
    (hρ : Continuous density) (hρ0 : ∀x,0≤density x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensity : PopulationSeedClockDensity S w
      (ν.map (fun x:ℝ↦x-S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0<gap)
    {poleη : ℝ} (hη : 0<poleη) (hηspan : poleη<D.hi-D.lo)
    {G : Matrix (Fin qdim) (Fin qdim) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ→Matrix (Fin qdim) (Fin qdim) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀a∈Ioo 0 poleη,originalSeedKernel S w (D.hi-a)=(a^2)⁻¹•G+Rem a)
    {g:ℝ→ℝ→ℝ} {gBound:ℝ} (hg:Measurable (Function.uncurry g))
    (hgb:∀x y,|g x y|≤gBound) (τ:ℝ)
    (Q:LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin:∀P:LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {η:(Fin qdim→ℝ)→ℝ} (hηmeas:Measurable η) (hηI:Integrable η volume)
    (hη0:∀x,0≤η x) {physicalRadius basecap M₀:ℝ}
    (hphysicalRadius:0≤physicalRadius) (hbasecap:0<basecap)
    (hηR:∀x,physicalRadius<‖x‖→η x=0) (hM:0≤M₀) (hηM:∀x,η x≤M₀) :
    ∃ h cap ε₀ A Btail K₀ E₀ : ℝ,0<h∧0<cap∧cap≤basecap∧
      0<ε₀∧ε₀≤1∧0≤A∧0≤Btail∧0≤K₀∧1≤E₀∧
      ∀{ε:ℝ},0<ε→ε<ε₀→∀n ell:ℕ,ell<birthPhysicalClockWindowCount cap→
      ∀{K:ℝ},K₀≤K→
      let traffic:=fun scene:LegalMarkedOptimalInputScene qdim↦
        (legalMarkedCompletePathTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
          (fun x↦ENNReal.ofReal (η x)) (D.originalSupportedOldPhysicalClockWeight ε cap 1 n ell) scene).toReal
      MemLp traffic 2 (Q.law:Measure (LegalMarkedOptimalInputScene qdim))∧
        eLpNorm traffic 2 (Q.law:Measure (LegalMarkedOptimalInputScene qdim))≤
          ENNReal.ofReal (A*Real.sqrt (K*E₀)*(birthDyadicShellScale ε n)^(1/(2*(qdim:ℝ)))+
            Btail*Real.exp (-K/4)) := by
  obtain ⟨εp,Cfirst,Cweighted,E₀,hεp,hεp1,hCfirst,hCweighted,hE₀,hpalms⟩:=
    D.exists_original_right_oldWindow_Palm_real_rates hF hw c hρ hρ0 hv hv0 hdensity
      hη hηspan hG hRem hpole hgap hbounds Q
  obtain ⟨εc,hεc,hεc1,_hεcspan,hcell⟩:=
    D.exists_original_right_old_commonScale_phaseCell_uniform_intensity hF hw
      (by omega) c hρ hρ0 hv hv0 hdensity hη hηspan hG hRem hpole
  obtain ⟨Λ,hΛ,hcell⟩:=hcell 1
  obtain ⟨εs,hεs,_hεsspan,σ,hσ,hsingle⟩:=D.exists_original_right_oldWindow_single_bound hF hw
  obtain ⟨εg,hεg,_hεgη,h,hh,Bmob,hBmob,hgeo⟩:=
    D.exists_original_right_shrinkable_supported_contractive_oldWindows_sameResidue
      hF hw hbounds hgap hη hηspan hG hRem hpole
  let L:ℝ≥0:=⟨Real.sqrt ((qdim:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let rawcap:=min basecap σ
  have hrawcap:0<rawcap:=lt_min hbasecap hσ
  let cap:=commonPhysicalNormalizedWindowFraction (min rawcap (1/4)) Bmob (L:ℝ)
  have hbase:0<min rawcap (1/4:ℝ):=lt_min hrawcap (by norm_num)
  have hcap:0<cap:=(commonPhysicalNormalizedWindowFraction_spec hbase hBmob L.coe_nonneg).1
  have hcapraw:cap≤rawcap:=(commonPhysicalNormalizedWindowFraction_le_cap _ _ _).trans (min_le_left _ _)
  have hcapbase:cap≤basecap:=hcapraw.trans (min_le_left _ _)
  have hcapσ:cap≤σ:=hcapraw.trans (min_le_right _ _)
  let ρ:=cap*Bmob
  let a:=Real.sqrt (qdim:ℝ)*physicalRadius
  let b:=Real.sqrt (8*|τ| *gBound/h)
  let radius:=max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let Ccurve:=canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ ρ
  let H:=1+2*((L:ℝ)*a+b)
  let m:=Nat.ceil (Ccurve*H)
  let Λsmall:=(2*(m:ℝ)+radius)^qdim*Λ
  let Bedge:=4*M₀*(physicalRadius+1)
  let space:=(∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin qdim→ℝ))).toReal
  let Csmall:=Bedge*space*cap*Cfirst
  let Clarge:=3*Bedge*(Ccurve+1)*space*cap*Cweighted
  let Rsmall:=8*Bedge^2*Real.exp (Λsmall*(Real.exp 1-1))
  let Rlarge:=Bedge^2*commonScaleSourceEnvelopeBudget qdim Λ radius
  let K₀:=commonScaleSourceCountThreshold qdim Λ radius
  let A:=Real.sqrt (2*Csmall)+Real.sqrt (2*Clarge)
  let Btail:=Real.sqrt Rsmall+Real.sqrt Rlarge*Real.exp (K₀/4)
  let ε₀:=min εp (min εc (min εs εg))
  have hε₀:0<ε₀:=lt_min hεp (lt_min hεc (lt_min hεs hεg))
  have hε₀p:ε₀≤εp:=min_le_left _ _
  have hε₀c:ε₀≤εc:=(min_le_right _ _).trans (min_le_left _ _)
  have hε₀s:ε₀≤εs:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₀g:ε₀≤εg:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρ:0≤ρ:=mul_nonneg hcap.le hBmob
  have ha:0≤a:=by dsimp [a];positivity
  have hb:0≤b:=Real.sqrt_nonneg _
  have hBedge:0≤Bedge:=by dsimp [Bedge];positivity
  have hspace:0≤space:=ENNReal.toReal_nonneg
  have hCcurve:1≤Ccurve:=(canonicalPhaseCurveScaleCoefficient_bounds (L:ℝ) ρ ρ).1
  have hCs:0≤Csmall:=by dsimp [Csmall];positivity
  have hCl:0≤Clarge:=by dsimp [Clarge];positivity
  have hRs:0≤Rsmall:=by dsimp [Rsmall];positivity
  have hRl:0≤Rlarge:=by
    apply mul_nonneg (sq_nonneg _)
    apply tsum_nonneg
    intro n
    positivity
  have hexp1:0≤Real.exp 1-1:=sub_nonneg.mpr (Real.one_le_exp zero_le_one)
  have hK₀:0≤K₀:=by
    dsimp [K₀,commonScaleSourceCountThreshold]
    positivity
  refine ⟨h,cap,ε₀,A,Btail,K₀,E₀,hh,hcap,hcapbase,hε₀,hε₀p.trans hεp1,
    by dsimp [A];positivity,by dsimp [Btail];positivity,hK₀,hE₀,?_⟩
  intro ε hε hεsmall n ell hell K hK
  dsimp only
  let t:=birthDyadicShellScale ε n
  let T:=positiveMatrixNormalizer (focalResidueScale G t)
  let δ:=birthTrafficCoarseScale qdim t t
  let ref:=D.originalOldPhysicalClockReference ε cap 1 n ell
  let cut:=ref-S.level
  let width:=oldPhysicalClockWindowWidth cap t
  let f:=D.originalSupportedOldPhysicalClockWeight ε cap 1 n ell
  have ht:0<t:=birthDyadicShellScale_pos hε n
  have htε:2*t≤ε:=by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num:(1:ℝ)≤2))
  have ht1:t≤1:=by linarith [hεsmall.le.trans (hε₀p.trans hεp1)]
  have hδ:1≤δ:=one_le_birthTrafficCoarseScale qdim ht ht1 ht le_rfl
  have hp:=hgeo hε (hεsmall.trans_le hε₀g) L rawcap hrawcap n ell hell
  have hT:IsUnit T.det:=hp.1
  have hcut:cut∈Ioo D.lo D.hi:=hp.2.1
  let _:=Matrix.invertibleOfIsUnitDet T hT
  have hclockRange:∀r∈Icc (0:ℝ) 1,cut+(-width)*r∈Ioo D.lo D.hi:=by
    intro r hr
    simpa only [cut,sub_add_eq_add_sub] using hp.2.2.1 r hr
  have hR:∀r∈Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T (cut+S.level) (-width) r‖≤ρ:=by
    simpa only [cut,sub_add_cancel] using hp.2.2.2.2.1
  have hRLip:∀r∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) (-width) r-
        originalNormalizedClockMobility S w T (cut+S.level) (-width) v‖≤ρ*|r-v|:=by
    simpa only [cut,sub_add_cancel] using hp.2.2.2.2.2.1
  have hsmall:∀r∈Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) (-width) r‖*Real.sqrt ((qdim:ℝ)/h^2)≤(1/2:ℝ):=by
    intro r hr
    have hs:=hp.2.2.2.2.2.2.1 r hr
    change ‖originalNormalizedClockMobility S w T ref (-width) r‖*(L:ℝ)≤(1/2:ℝ) at hs
    change ‖originalNormalizedClockMobility S w T (cut+S.level) (-width) r‖*(L:ℝ)≤(1/2:ℝ)
    simpa only [cut,sub_add_cancel] using hs
  have helig:=hp.2.2.2.2.2.2.2
  have hclock:∀m clock,f (m,clock)≠0→∃r∈Icc (0:ℝ) 1,clock=cut+S.level+(-width)*r:=by
    intro m clock hf
    obtain ⟨r,hr,heq⟩:=D.originalSupportedRightOldPhysicalClockWeight_clock_witness hε hcap n ell _ hf
    exact ⟨r,hr,by simpa only [cut,sub_add_cancel] using heq⟩
  have hmask:∀(e:LegalMarkedPhysicalEdge qdim) clock,f ((physicalPairAnchor e).2,clock)≠0→
      e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.2.2∈D.targetPhaseClocks cut:=by
    intro e clock hf
    have he:=(helig e clock hf).1
    exact ⟨he,he.2.1⟩
  have hηfinite:(∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin qdim→ℝ)))≠(∞:ℝ≥0∞):=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hηI.2).ne
  have hηwindow:∀x,ENNReal.ofReal (η x)≠0→‖T*ᵥx‖≤a*δ:=by
    intro x hx
    have hxR:‖x‖≤physicalRadius:=by
      by_contra hn
      exact hx (by rw [hηR x (lt_of_not_ge hn),ENNReal.ofReal_zero])
    have hb:=birthNormalizer_mulVec_norm_le_coarseScale_of_norm_le hG ht ht1 ht hxR
    rw [birthResidueScale_same_time_eq_focal G ht] at hb
    simpa only [Fintype.card_fin] using hb
  have hrefI:=D.originalOldPhysicalClockWindow_right_inward hε hcap n ell hell
    (show ref∈Icc (ref-width) ref from ⟨sub_le_self _
      (oldPhysicalClockWindow_spec hcap ht).2.1.le,le_rfl⟩)
  have hunit:((volume:Measure (Fin qdim→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ (D.targetPhaseClocks cut) 0 0 1)≤ENNReal.ofReal Λ:=by
    have hc:=hcell ht (htε.trans_lt (hεsmall.trans_le hε₀c)) hrefI 0 0
    have hceq:D.hi-(D.hi-(ref-S.level))=cut:=by dsimp [cut];ring
    rw [hceq] at hc
    exact hc
  rcases hpalms hε (hεsmall.trans_le hε₀p) hcap n ell hell with
    ⟨he,hv',heE,hvE,hpfinite,hprate,hwpfinite,hwprate⟩
  have hsingle':=hsingle hε (hεsmall.trans_le hε₀s) hcap hcapσ n ell hell
    hphysicalRadius hM hη0 hηM hηR
  have hbound:∀e∈legalMarkedCompletePathContributors qdim
      (fun z↦originalSeedPathOffset S w z.2 z.1) (fun x↦ENNReal.ofReal (η x)) f,
      (legalMarkedCompletePathEdgeTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
        (fun x↦ENNReal.ofReal (η x)) f e).toReal≤Bedge:=by
    intro e _
    have hh:=ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsingle' e.1.1 (physicalPairAnchor e).2)
    simpa only [legalMarkedCompletePathEdgeTraffic,physicalPairAnchor,f,Bedge,
      ENNReal.toReal_ofReal (show 0≤4*M₀*(physicalRadius+1) by positivity)] using hh
  have hfull:=D.original_minimizer_commonScale_target_fullWindow_traffic_memLp_two_le hF hw hgap hbounds
    T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hρ hR hRLip
    hηmeas.ennreal_ofReal (D.measurable_originalSupportedOldPhysicalClockWeight hF hw ε cap 1 n ell)
    hclock hηwindow (D.measurableSet_targetPhaseClocks cut) hmask hηfinite hpfinite
    hBedge hΛ.le hbound hunit hK hwpfinite
  let Band:={m:PhysicalPairPalmMark (Fin qdim)|D.hi-(m.1.2-S.level)∈Ioc 0 (2*t)}
  let e:=(∫⁻m in Band,ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
    ∂legalMarkedJointPalm qdim Q.law).toReal
  let v:=(∫⁻m in Band,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
    ∂legalMarkedJointPalm qdim Q.law).toReal
  let palm:=∫⁻m,∫⁻clock:ℝ,f (m,clock)∂volume∂legalMarkedJointPalm qdim Q.law
  let weighted:=∫⁻m,∫⁻clock:ℝ,
    ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,clock)
      ∂volume∂legalMarkedJointPalm qdim Q.law
  let smallProfile:=t^((G.rank:ℝ)/2)*Real.sqrt e+t^(((G.rank:ℝ)+3)/2)*Real.sqrt v
  let largeProfile:=t^(1/(qdim:ℝ))*e+t^(1+1/(qdim:ℝ))*v
  change e≤E₀ at heE
  change v≤E₀ at hvE
  change palm.toReal≤cap*Cfirst*smallProfile at hprate
  change δ⁻¹*weighted.toReal≤cap*Cweighted*largeProfile at hwprate
  have hk:0≤K:=hK₀.trans hK
  have hezero:G.rank=0→e=0:=by
    intro hz
    have hpoint:=D.original_right_poleEnergy_eq_zero_of_rank_zero hz
    simp only [e,hpoint,ENNReal.ofReal_zero,lintegral_zero,ENNReal.toReal_zero]
  have hqreal:2≤(qdim:ℝ):=by exact_mod_cast hq
  have hsp:smallProfile≤2*E₀*t^(1/(qdim:ℝ)):=
    oldFocal_small_firstMoment_le_common_power ht ht1 hqreal hE₀ heE hvE G.rank hezero
  have hlp:largeProfile≤2*E₀*t^(1/(qdim:ℝ)):=
    oldFocal_large_energy_le_common_power ht ht1 heE hvE ENNReal.toReal_nonneg
  have hsmain:Bedge*K*((∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin qdim→ℝ)))*palm).toReal≤
      Csmall*K*smallProfile:=by
    rw [ENNReal.toReal_mul]
    calc
      _=(Bedge*space*K)*palm.toReal:=by dsimp [space];ring
      _≤(Bedge*space*K)*(cap*Cfirst*smallProfile):=
        mul_le_mul_of_nonneg_left hprate (by positivity)
      _=_:=by dsimp [Csmall];ring
  have hlmain:(3*Bedge*(K*(Ccurve+1)/δ))*
      ((∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin qdim→ℝ)))*weighted).toReal≤
      Clarge*K*largeProfile:=by
    rw [ENNReal.toReal_mul]
    calc
      _=(3*Bedge*(Ccurve+1)*space*K)*(δ⁻¹*weighted.toReal):=by
        dsimp [space];rw [div_eq_mul_inv];ring
      _≤(3*Bedge*(Ccurve+1)*space*K)*(cap*Cweighted*largeProfile):=
        mul_le_mul_of_nonneg_left hwprate (by positivity)
      _=_:=by dsimp [Clarge];ring
  have hsroot:=oldFocal_sqrt_budget_le_common_power (K₀:=0) ht (show 0≤E₀ by linarith) hk hCs hRs hsp
  have hlroot:=oldFocal_sqrt_budget_le_common_power (K₀:=K₀) ht (show 0≤E₀ by linarith) hk hCl hRl hlp
  simp only [sub_zero,zero_div,Real.exp_zero,mul_one] at hsroot
  refine ⟨hfull.1,hfull.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  change Real.sqrt (Bedge*K*((∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin qdim→ℝ)))*palm).toReal+
      Rsmall*Real.exp (-K/2))+
    Real.sqrt ((3*Bedge*(K*(Ccurve+1)/δ))*
      ((∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin qdim→ℝ)))*weighted).toReal+
        Rlarge*Real.exp (-(K-K₀)/2))≤_
  calc
    _≤(Real.sqrt (2*Csmall)*Real.sqrt (K*E₀)*t^(1/(2*(qdim:ℝ)))+
        Real.sqrt Rsmall*Real.exp (-K/4))+
      (Real.sqrt (2*Clarge)*Real.sqrt (K*E₀)*t^(1/(2*(qdim:ℝ)))+
        Real.sqrt Rlarge*Real.exp (K₀/4)*Real.exp (-K/4)):=
      add_le_add ((Real.sqrt_le_sqrt (add_le_add hsmain le_rfl)).trans hsroot)
        ((Real.sqrt_le_sqrt (add_le_add hlmain le_rfl)).trans hlroot)
    _=_:=by dsimp [A,Btail];ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
