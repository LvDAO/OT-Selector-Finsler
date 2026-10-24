import OTSelector.Probability.BirthBandUnifiedInterpolatedNorm
import OTSelector.Reconstruction.OriginalMinimizerRightFullBirthTrafficLargePhase
import OTSelector.Probability.FiniteBandTrafficRemainderLtwo
import OTSelector.MeasureTheory.Lp.FiniteGoodBadSum

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

/-- Every original right-birth band, including BOTH canonical amplitude
branches and every original count event, has the summable physical level
profile. One geometric h/cap choice is shared by all branches internally. -/
theorem exists_original_right_full_birth_level_norm
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g,
      Q.value τ ≤ P.value τ)
    {η : (Fin q → ℝ) → ℝ} (hηmeas : Measurable η)
    (hη0 : ∀ x, 0 ≤ η x)
    {physicalRadius basecap M₀ : ℝ} (hphysicalRadius : 0 ≤ physicalRadius)
    (hbasecap : 0 < basecap) (hηR : ∀ x, physicalRadius < ‖x‖ → η x = 0)
    (hM : 0 ≤ M₀) (hηM : ∀ x, η x ≤ M₀) :
    ∃ cap ε₀ A B K₀ E₀ : ℝ,0<cap∧cap≤basecap∧0<ε₀∧ε₀≤1∧
      0≤A∧0≤B∧0≤K₀∧1≤E₀∧
      ∀{ε:ℝ},0<ε→ε<ε₀→∀n j ell:ℕ,ell<birthPhysicalClockWindowCount cap→
      ∀{K:ℝ},K₀≤K→
      let t:=birthDyadicShellScale ε n
      let s:=birthDyadicElapsedScale ε n j
      let level:=fun scene:LegalMarkedOptimalInputScene q↦
        ∑i∈Finset.range (dyadicBirthBandCount j),
          (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
            (fun x↦ENNReal.ofReal (η x))
            (D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell) scene).toReal
      MemLp level 2 (Q.law:Measure (LegalMarkedOptimalInputScene q))∧
        eLpNorm level 2 (Q.law:Measure (LegalMarkedOptimalInputScene q))≤
        ENNReal.ofReal (A*Real.sqrt (K*E₀)*
          (t^(1/(2*(q:ℝ)))*Real.sqrt (s/t)+
            t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
              (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4))))+
          B*(2:ℝ)^j*Real.exp (-K/4)) := by
  obtain ⟨σ,hσ,hlarge⟩:=D.exists_original_right_birth_largePhase_real_square_rate
    hF hw hq c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
    hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hηR hM hηM
  obtain ⟨h,cap,ρ,hh,hcap,hcapbase,hρ,hsmallgeom⟩:=
    D.exists_original_right_bounded_birth_geometric_goodBad_smallMoments hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius (lt_min hbasecap hσ) hηR hM hηM
  have hcapσ:cap≤σ:=hcapbase.trans (min_le_right _ _)
  let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let a:=Real.sqrt (q:ℝ)*physicalRadius
  let b:=Real.sqrt (8*|τ| *gBound/h)
  let H:=1+2*((L:ℝ)*a+b)
  have ha:0≤a:=by dsimp only [a];positivity
  have hphaseb:0≤b:=Real.sqrt_nonneg _
  have hH:0≤H:=by dsimp only [H];positivity
  obtain ⟨εs,radius,C₁,C₂,Btail,hεs,hεs1,hradius,hC₁,hC₂,hBtail,hsmallgeom⟩:=hsmallgeom H hH
  obtain ⟨εl,Al,Bl,K₀,hεl,hεl1,hAl,hBl,hK₀,hlarge⟩:=hlarge hh hρ hcap hcapσ
  obtain ⟨E₀,hE₀,henergy⟩:=D.exists_original_right_narrowBirthBands_energy_budget
    hF hw hη hηspan hG hRem hpole hgap hbounds Q
  let ε₀:=min εs εl
  have hε₀:0<ε₀:=lt_min hεs hεl
  have hε₀s:ε₀≤εs:=min_le_left _ _
  have hε₀l:ε₀≤εl:=min_le_right _ _
  have hε₀1:ε₀≤1:=hε₀s.trans hεs1
  let p₁:=4*M₀*(physicalRadius+1)*
    (∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin q→ℝ))).toReal*cap*C₁
  let p₂:=(M₀*cap)^2*C₂
  let C:=max p₁ p₂+1
  have hp₁:p₁≤C:=(le_max_left _ _).trans (by dsimp only [C];linarith)
  have hp₂:p₂≤C:=(le_max_right _ _).trans (by dsimp only [C];linarith)
  have hp₁0:0≤p₁:=by dsimp only [p₁];positivity
  have hC:0<C:=by dsimp only [C];linarith [le_max_left p₁ p₂]
  let As:=(2*(8:ℝ)^(3/4:ℝ)+2*Real.sqrt 8)*Real.sqrt C
  let Abig:=2*Real.sqrt 8*Real.sqrt Al
  let Atotal:=As+Abig
  let Btotal:=8*(Btail+Real.sqrt Bl*Real.exp (K₀/4))
  have hAs:0<As:=by dsimp only [As];positivity
  have hAbig:0≤Abig:=by dsimp only [Abig];positivity
  have hAtotal:0≤Atotal:=add_nonneg hAs.le hAbig
  have hBtotal:0≤Btotal:=by dsimp only [Btotal];positivity
  refine ⟨cap,ε₀,Atotal,Btotal,K₀,E₀,hcap,hcapbase.trans (min_le_left _ _),
    hε₀,hε₀1,hAtotal,hBtotal,hK₀,hE₀,?_⟩
  intro ε hε hεsmall n j ell hell K hKbound
  have hK:0≤K:=hK₀.trans hKbound
  dsimp only
  let t:=birthDyadicShellScale ε n
  let s:=birthDyadicElapsedScale ε n j
  let δ:=birthTrafficCoarseScale q t s
  let T:=positiveMatrixNormalizer (birthResidueScale G t s)
  let W:=birthTrafficSpatialWindow G t s radius
  let J:=D.originalRightBirthNarrowClockBand ε n j
  let cut:=fun i↦D.originalRightBirthPhysicalClockReference ε cap n j i ell-S.level
  let Good:=fun i↦{scene:LegalMarkedOptimalInputScene q |
    ‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖≤H*δ∧
      (scene.2:Measure (LegalColoredInputPoint q)) ((W×ˢJ i)×ˢ{1})≤ENNReal.ofReal K}
  let traffic:=fun i↦(Good i).indicator (fun scene:LegalMarkedOptimalInputScene q↦
    (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
      (fun x↦ENNReal.ofReal (η x))
      (D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell) scene).toReal)
  let B : ℕ → Set (PhysicalPairPalmMark (Fin q)) := fun i ↦ {m | m.1.2 ∈ J i}
  let e:=fun i↦(∫⁻ m in B i,ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
    ∂legalMarkedJointPalm q Q.law).toReal
  let v:=fun i↦(∫⁻ m in B i,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
    ∂legalMarkedJointPalm q Q.law).toReal
  let bands:=Finset.range (dyadicBirthBandCount j)
  let P:Measure (LegalMarkedOptimalInputScene q):=Q.law
  have ht : 0<t := birthDyadicShellScale_pos hε n
  have hs : 0<s := div_pos ht (by positivity)
  have ht1 : t≤1 := by
    have htε : 2*t≤ε := by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    linarith [hεsmall.le.trans hε₀1]
  have hNs : (bands.card:ℝ)*s=8*t := by
    dsimp only [bands,birthDyadicElapsedScale,s,t]
    simp only [Finset.card_range,dyadicBirthBandCount,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  have hb:=henergy hε n j (dyadicBirthBandCount j)
  dsimp only at hb
  have he : ∀ i,0≤e i := fun _↦ENNReal.toReal_nonneg
  have hv : ∀ i,0≤v i := fun _↦ENNReal.toReal_nonneg
  have hE : (∑ i∈bands,e i)≤E₀ := hb.2.1
  have hV : (∑ i∈bands,v i)≤E₀ := hb.2.2
  have hLp : ∀ i∈bands,MemLp (traffic i) 2 P := by
    intro i hi
    exact (hsmallgeom hε (hεsmall.trans_le hε₀s) n j i ell (Finset.mem_range.mp hi) hell hK).1.1
  have hfirst : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤
      (K*C)*s^(3/2:ℝ)*(t^(((G.rank:ℝ)-3)/2)*Real.sqrt (e i)+t^((G.rank:ℝ)/2)*Real.sqrt (v i)) := by
    intro i hi
    have hr:=(hsmallgeom hε (hεsmall.trans_le hε₀s) n j i ell (Finset.mem_range.mp hi) hell hK).1.2.1
    have hr:=hr.trans (min_le_left _ _)
    calc
      _ ≤ (K*p₁)*s^(3/2:ℝ)*(t^(((G.rank:ℝ)-3)/2)*Real.sqrt (e i)+t^((G.rank:ℝ)/2)*Real.sqrt (v i)) := by
        convert hr using 1
        all_goals first | rfl | (dsimp only [p₁,t,s,e,v,B,J]; ring)
      _ ≤ _ := by gcongr
  have hsecond : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤
      (K*C)*s^2*(t^(-((G.rank:ℝ)+4))*e i+t^(-((G.rank:ℝ)+3))*v i) := by
    intro i hi
    have hr:=(hsmallgeom hε (hεsmall.trans_le hε₀s) n j i ell (Finset.mem_range.mp hi) hell hK).1.2.1
    have hr:=hr.trans (min_le_right _ _)
    calc
      _ ≤ (K*p₂)*s^2*(t^(-((G.rank:ℝ)+4))*e i+t^(-((G.rank:ℝ)+3))*v i) := by
        convert hr using 1
        all_goals first | rfl | (dsimp only [p₂,t,s,e,v,B,J]; ring)
      _ ≤ _ := by gcongr
  have hgood : MemLp (fun scene↦∑ i∈bands,traffic i scene) 2 P ∧
      eLpNorm (fun scene↦∑ i∈bands,traffic i scene) 2 P ≤
        ENNReal.ofReal ((As*Real.sqrt K*Real.sqrt E₀)*
          (t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
            (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4))))) := by
    have hezero : G.rank=0 → ∀ i,e i=0 := by
      intro hrank i
      simp only [e,D.original_right_poleEnergy_eq_zero_of_rank_zero hrank,
        ENNReal.ofReal_zero,lintegral_zero,ENNReal.toReal_zero]
    have hout := birthBand_unified_traffic_interpolated_level_norm
      P bands traffic hLp e v he hv ht ht1 hs (mul_nonneg hK hC.le)
      hE₀ hNs hE hV hfirst hsecond hezero
    refine ⟨hout.1,hout.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [Real.sqrt_mul hK]
    dsimp only [As]
    exact le_of_eq (by ring)
  
  let Small:=fun i↦{scene:LegalMarkedOptimalInputScene q |
    ‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖≤H*δ}
  let Bad:=fun i↦{scene:LegalMarkedOptimalInputScene q |
    ENNReal.ofReal K < (scene.2:Measure (LegalColoredInputPoint q)) ((W×ˢJ i)×ˢ{1})}
  let raw:=fun i (scene:LegalMarkedOptimalInputScene q)↦
    (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
      (fun x↦ENNReal.ofReal (η x))
      (D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell) scene).toReal
  have hGoodEq : ∀ i,Good i=((Small i)ᶜ∪Bad i)ᶜ := by
    intro i
    ext scene
    simp only [Good,Small,Bad,mem_ofPred_eq,mem_compl_iff,mem_union,not_or,not_not,not_lt]
  have hgood' : MemLp (fun scene↦∑ i∈bands,((Small i)ᶜ∪Bad i)ᶜ.indicator (raw i) scene) 2 P ∧
      eLpNorm (fun scene↦∑ i∈bands,((Small i)ᶜ∪Bad i)ᶜ.indicator (raw i) scene) 2 P ≤
        ENNReal.ofReal ((As*Real.sqrt K*Real.sqrt E₀)*
          (t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
            (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4))))) := by
    simpa only [traffic,hGoodEq] using hgood
  have hbad : ∀ i∈bands,MemLp ((Bad i).indicator ((Small i).indicator (raw i))) 2 P := by
    intro i hi
    exact (hsmallgeom hε (hεsmall.trans_le hε₀s) n j i ell (Finset.mem_range.mp hi) hell hK).2.1
  have hbadNorm : ∀ i∈bands,eLpNorm ((Bad i).indicator ((Small i).indicator (raw i))) 2 P ≤
      ENNReal.ofReal (Btail*Real.exp (-K/4)) := by
    intro i hi
    exact (hsmallgeom hε (hεsmall.trans_le hε₀s) n j i ell (Finset.mem_range.mp hi) hell hK).2.2.1
  have hfullSmall:=finite_sceneEvent_traffic_memLp_two_of_good_bad_norm_bounds P bands Small Bad raw
    hgood'.1 hbad (by positivity) (by positivity) hgood'.2 hbadNorm
  let k:=fun i↦D.commonScaleNormalizedCanonicalCurveIntegerScale T (cut i) h L ρ ρ δ
  let Big:=fun i↦{scene:LegalMarkedOptimalInputScene q|1≤k i scene∧
    δ≤‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖∧
      2*((L:ℝ)*(a*δ)+b)≤‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖}
  let bigTraffic:=fun i↦(Big i).indicator (raw i)
  have hlargeBand:∀i∈bands,MemLp (bigTraffic i) 2 P∧
      (∫scene,(bigTraffic i scene)^2∂P)≤
        (Al*K)*s^2*(t^(-2+1/(q:ℝ))*e i+t^(-1+1/(q:ℝ))*v i)+
          Bl*Real.exp (-(K-K₀)/2):=by
    intro i hi
    have hp:=(hsmallgeom hε (hεsmall.trans_le hε₀s) n j i ell
      (Finset.mem_range.mp hi) hell (K:=0) (by norm_num)).2.2.2
    have hr:=hlarge hε (hεsmall.trans_le hε₀l) n j i ell (Finset.mem_range.mp hi) hell
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2 hKbound
    exact ⟨hr.1,hr.2.1⟩
  have hbig:=birthBand_large_traffic_level_norm_remainder P bands bigTraffic
    (fun i hi↦(hlargeBand i hi).1) e v he hv ht ht1 hs
    (mul_nonneg hAl hK) (mul_nonneg hBl (Real.exp_nonneg _)) hNs hE hV
    (fun i hi↦(hlargeBand i hi).2)
  have hrawMeas:∀i,Measurable (raw i):=by
    intro i
    exact (measurable_legalMarkedCompletePathTraffic
      (fun z↦originalSeedPathOffset S w z.2 z.1)
      (measurable_originalSeedPathOffset_joint S hF hw) hηmeas.ennreal_ofReal
      (D.measurable_originalSupportedRightBirthPhysicalClockWeight hF hw ε cap n j i ell)).ennreal_toReal
  have hδ:1≤δ:=one_le_birthTrafficCoarseScale q ht ht1 hs
    ((birthDyadicClockBand_base_bounds hε n j 0 (by
      dsimp only [dyadicBirthBandCount];positivity)).2.1)
  have hrawle:∀i scene,raw i scene≤(Small i).indicator (raw i) scene+bigTraffic i scene:=by
    intro i scene
    by_cases hsm:scene∈Small i
    · rw [indicator_of_mem hsm]
      exact le_add_of_nonneg_right (indicator_nonneg (fun _ _↦ENNReal.toReal_nonneg) scene)
    · have hamp:H*δ<‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖:=lt_of_not_ge hsm
      have hH1:1≤H:=by dsimp only [H];nlinarith [mul_nonneg L.coe_nonneg ha]
      have hδpos:0<δ:=by linarith
      have hampδ:δ≤‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖:=
        (le_mul_of_one_le_left hδpos.le hH1).trans hamp.le
      have hscale:=D.commonScaleNormalizedCanonicalCurveIntegerScale_spec T (cut i) h L ρ ρ δ
        (N:=1) le_rfl scene (by simpa only [Nat.cast_one] using (one_le_div hδpos).mpr hampδ)
      have hlargeAmp:2*((L:ℝ)*(a*δ)+b)≤‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖:=by
        have hbδ:b≤b*δ:=le_mul_of_one_le_right hphaseb hδ
        dsimp only [H] at hamp
        nlinarith only [hamp,hbδ,hδpos]
      have hbigmem:scene∈Big i:=⟨hscale.1,hampδ,hlargeAmp⟩
      simpa only [bigTraffic,indicator_of_notMem hsm,indicator_of_mem hbigmem,zero_add]
        using (le_refl (raw i scene))
  have hdom:∀ᵐscene∂P,‖∑i∈bands,raw i scene‖≤
      (∑i∈bands,(Small i).indicator (raw i) scene)+(∑i∈bands,bigTraffic i scene):=by
    filter_upwards [] with scene
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun i _↦ENNReal.toReal_nonneg)),
      ←Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _↦hrawle i scene)
  have hmem:MemLp (fun scene↦∑i∈bands,raw i scene) 2 P:=
    (hfullSmall.1.add hbig.1).mono'
      (Finset.measurable_sum bands (fun i _↦hrawMeas i)).aestronglyMeasurable hdom
  refine ⟨hmem,?_⟩
  have hbound:eLpNorm (fun scene↦∑i∈bands,raw i scene) 2 P≤
      ENNReal.ofReal (((As*Real.sqrt K*Real.sqrt E₀)*
        (t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
          (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4)))))+
        (bands.card:ℝ)*(Btail*Real.exp (-K/4))+
        (2*Real.sqrt 8*Real.sqrt (Al*K)*Real.sqrt E₀*t^(1/(2*(q:ℝ)))*Real.sqrt (s/t)+
          (bands.card:ℝ)*Real.sqrt (Bl*Real.exp (-(K-K₀)/2)))):=by
    calc
      _≤eLpNorm (fun scene↦(∑i∈bands,(Small i).indicator (raw i) scene)+
          (∑i∈bands,bigTraffic i scene)) 2 P:=eLpNorm_mono_ae_real hdom
      _≤eLpNorm (fun scene↦∑i∈bands,(Small i).indicator (raw i) scene) 2 P+
          eLpNorm (fun scene↦∑i∈bands,bigTraffic i scene) 2 P:=
        eLpNorm_add_le hfullSmall.1.aestronglyMeasurable hbig.1.aestronglyMeasurable (by norm_num)
      _≤_:=by
        exact (add_le_add hfullSmall.2 hbig.2).trans_eq (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  apply hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsqrtExp:∀x:ℝ,Real.sqrt (Real.exp x)=Real.exp (x/2):=by
    intro x
    have heq:Real.exp x=(Real.exp (x/2))^2:=by rw [pow_two,←Real.exp_add];congr 1;ring
    rw [heq,Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.exp_nonneg _)]
  have herror:Real.sqrt (Bl*Real.exp (-(K-K₀)/2))=
      Real.sqrt Bl*Real.exp (K₀/4)*Real.exp (-K/4):=by
    rw [Real.sqrt_mul hBl,hsqrtExp]
    rw [show (-(K-K₀)/2)/2=K₀/4+(-K/4) by ring,Real.exp_add]
    ring
  rw [herror,Real.sqrt_mul hAl,Real.sqrt_mul hK]
  simp only [bands,Finset.card_range,dyadicBirthBandCount,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  dsimp only [Atotal,Btotal,Abig]
  have hcross:0≤As*(Real.sqrt K*Real.sqrt E₀)*
      (t^(1/(2*(q:ℝ)))*Real.sqrt (s/t))+
      (2*Real.sqrt 8*Real.sqrt Al)*(Real.sqrt K*Real.sqrt E₀)*
        (t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
          (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4)))):=by
    positivity
  nlinarith only [hcross]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
