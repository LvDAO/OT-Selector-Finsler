import OTSelector.Probability.BirthBandUnifiedInterpolatedNorm
import OTSelector.Reconstruction.OriginalMinimizerFullTrafficAssembly
import OTSelector.Reconstruction.OriginalMinimizerRightCommonScaleTraffic
import OTSelector.Reconstruction.OriginalMinimizerRightBirthWindowBasic
import OTSelector.MeasureTheory.Lp.FiniteGoodBadSum
import OTSelector.Reconstruction.OriginalBirthTrafficDoubleSummation

/-! Actual target/right bounded-birth traffic. Target input counts use the
unchanged nu law and color one; target phase centers keep the positive leg.
The physical h/cap choice precedes every amplitude cutoff H. -/
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

/-- The same actual right geometric choice retains concrete inward-clock
mobility and eligible-edge certificates with both true target small moments
and its original count-tail norm. No second h/cap choice is needed. -/
theorem exists_original_right_bounded_birth_geometric_goodBad_smallMoments
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
    ∃ h cap ρ : ℝ, 0 < h ∧ 0 < cap ∧ cap ≤ basecap ∧ 0 ≤ ρ ∧ ∀ H : ℝ, 0 ≤ H →
    ∃ ε₀ radius C₁ C₂ Btail : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      0 ≤ radius ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 ≤ Btail ∧ ∀ {ε : ℝ}, 0 < ε → ε < ε₀ →
      ∀ n j i ell : ℕ, i < dyadicBirthBandCount j → ell < birthPhysicalClockWindowCount cap →
      ∀ {K : ℝ}, 0 ≤ K →
      let t := birthDyadicShellScale ε n
      let s := birthDyadicElapsedScale ε n j
      let δ := birthTrafficCoarseScale q t s
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      let cut := D.originalRightBirthPhysicalClockReference ε cap n j i ell - S.level
      let L : ℝ≥0 := ⟨Real.sqrt ((q : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let J := D.originalRightBirthNarrowClockBand ε n j i
      let B := {m : PhysicalPairPalmMark (Fin q) | m.1.2 ∈ J}
      let W := birthTrafficSpatialWindow G t s radius
      let Good := {scene : LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ ∧
          (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {1}) ≤ ENNReal.ofReal K}
      let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
        (legalMarkedCompletePathTraffic q (fun z ↦ originalSeedPathOffset S w z.2 z.1)
          (fun x ↦ ENNReal.ofReal (η x)) (D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell) scene).toReal
      let firstBudget :=
        (4*M₀*(physicalRadius+1)*K*
          (∫⁻ x, ENNReal.ofReal (η x) ∂(volume : Measure (Fin q → ℝ))).toReal *cap*C₁) *
          s ^ (3/2 : ℝ) *
          (t ^ (((G.rank : ℝ)-3)/2) * Real.sqrt
            (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
              ∂legalMarkedJointPalm q Q.law).toReal +
            t ^ ((G.rank : ℝ)/2) * Real.sqrt
              (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
                ∂legalMarkedJointPalm q Q.law).toReal)
      let secondBudget := (K*(M₀*cap)^2*C₂)*s^2 *
        (t ^ (-(G.rank : ℝ)-4)*
          (∫⁻ m in B,ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm q Q.law).toReal +
          t ^ (-(G.rank : ℝ)-3)*
            (∫⁻ m in B,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
              ∂legalMarkedJointPalm q Q.law).toReal)
      (MemLp (Good.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ scene,(Good.indicator traffic scene)^2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤ min firstBudget secondBudget ∧
      eLpNorm (Good.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt (min firstBudget secondBudget))) ∧
      let Small := {scene : LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ}
      let Bad := {scene : LegalMarkedOptimalInputScene q |
        ENNReal.ofReal K < (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {1})}
      MemLp (Bad.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      eLpNorm (Bad.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≤
          ENNReal.ofReal (Btail * Real.exp (-K / 4)) ∧
      let width := -(birthPhysicalClockWindowWidth cap s)
      let R := originalNormalizedClockMobility S w T (cut+S.level) width
      IsUnit T.det ∧ cut∈Ioo D.lo D.hi ∧
        (∀ r∈Icc (0:ℝ) 1, cut+width*r∈Ioo D.lo D.hi) ∧ R 0=0 ∧
        (∀ r∈Icc (0:ℝ) 1, ‖R r‖≤ρ) ∧
        (∀ r∈Icc (0:ℝ) 1, ∀ v∈Icc (0:ℝ) 1, ‖R r-R v‖≤ρ*|r-v|) ∧
        (∀ r∈Icc (0:ℝ) 1, ‖R r‖*(L:ℝ)≤(1/2:ℝ)) ∧
        ∀ (e:LegalMarkedPhysicalEdge q) clock,
          D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell
            ((physicalPairAnchor e).2,clock)≠0 →
          e∈D.normalizedMomentumPhaseEligibleEdges T cut h := by
  have hηENN : Measurable (fun x ↦ ENNReal.ofReal (η x)) := hηmeas.ennreal_ofReal
  have hηsupport : ∀ x, ENNReal.ofReal (η x) ≠ 0 → ‖x‖ ≤ physicalRadius := by
    intro x hx
    by_contra hn
    exact hx (by rw [hηR x (lt_of_not_ge hn),ENNReal.ofReal_zero])
  obtain ⟨εs,σ,hεs,hσ,hsingle⟩ := D.exists_original_right_birthWindow_single_bound hF hw
  obtain ⟨εg,hεg,hεg1,h,hh,cap,hcap,hcapbase,ρ,hρ,hgeom⟩ :=
    D.exists_original_right_shrinkable_birth_bounded_contributors_sameResidue
      hF hw hbounds hgap hη hηspan hG hRem hpole hg hgb τ Q hmin
      hηENN hphysicalRadius (lt_min hbasecap hσ) hηsupport
  have hcapσ : cap ≤ σ := hcapbase.trans (min_le_right _ _)
  refine ⟨h,cap,ρ,hh,hcap,hcapbase.trans (min_le_left _ _),hρ,?_⟩
  intro H hH
  obtain ⟨radius,hradius,hgeom⟩ := hgeom H hH
  obtain ⟨εb,Cb,hεb,_hεbη,hCb,hsecond⟩ :=
    D.exists_original_right_birthBand_smallSecondMoment_bound_ae hF hw hq radius
      hη hηspan hG hRem hpole
  obtain ⟨εa,C,hεa,_hεaη,hC,hfirst⟩ :=
    D.exists_original_right_birthBand_smallFirstSquare_bound_ae hF hw
      hη hηspan hG hRem hpole
  obtain ⟨εm,Cm,hεm,_hspan,hCm,hmass⟩ := D.exists_original_right_birth_narrowBand_mass_bound
    hF hw c hdensityCont hdensity0 hv hv0 hdensity hη
    (hRem.continuousAt (Ioo_mem_nhds (by linarith) hη)) hpole
  let ε₀ := min εg (min (εa/4) (min (εb/4) (min εm εs)))
  have hε₀g : ε₀ ≤ εg := min_le_left _ _
  have hε₀a : ε₀ ≤ εa/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀b : ε₀ ≤ εb/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₀m : ε₀ ≤ εm := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hε₀s : ε₀ ≤ εs := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨Ct,hCt,hint⟩ := exists_birthSpatialClockWindow_intensity_bound hG
    (by simpa only [Fintype.card_fin] using hq) radius
  let Btail := Real.sqrt 8 * (4*M₀*(physicalRadius+1)) *
    Real.exp ((Ct*Cm)*(Real.exp 1-1)/2)
  refine ⟨ε₀,radius,C*Real.sqrt Cm,Cb,Btail,
    lt_min hεg (lt_min (by positivity) (lt_min (by positivity) (lt_min hεm hεs))),hε₀g.trans hεg1,
    hradius,mul_pos hC (Real.sqrt_pos.mpr hCm),hCb,(by dsimp only [Btail]; positivity),?_⟩
  intro ε hε hεsmall n j i ell hi hell K hK
  dsimp only
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let δ := birthTrafficCoarseScale q t s
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
  let cut := ref - S.level
  let L : ℝ≥0 := ⟨Real.sqrt ((q : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let J := D.originalRightBirthNarrowClockBand ε n j i
  let B := {m : PhysicalPairPalmMark (Fin q) | m.1.2 ∈ J}
  let W := birthTrafficSpatialWindow G t s radius
  let width := birthPhysicalClockWindowWidth cap s
  let I := Ico (ref - width) ref
  let d := fun z : PhysicalPairPalmMark (Fin q) × ℝ ↦ originalSeedPathOffset S w z.2 z.1
  let f := D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell
  let mask := D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell
  let V := occupiedPairTrafficContributors q d (fun x ↦ ENNReal.ofReal (η x)) f
  let Good := {scene : LegalMarkedOptimalInputScene q |
    ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ ∧
      (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {1}) ≤ ENNReal.ofReal K}
  have hεg' : ε < εg := hεsmall.trans_le hε₀g
  have hp := hgeom hε hεg' n j i ell hi hell
  have hcut : cut ∈ Ioo D.lo D.hi := hp.2.1
  have hJ : MeasurableSet J := D.measurableSet_originalRightBirthNarrowClockBand ε n j i
  have hB : MeasurableSet B := hJ.preimage measurable_fst.snd
  have hW : MeasurableSet W := (isCompact_birthTrafficSpatialWindow G t s radius).measurableSet
  have hcount : Measurable (fun scene : LegalMarkedOptimalInputScene q ↦
      (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {1})) :=
    (Measure.measurable_coe ((hW.prod hJ).prod (measurableSet_singleton 1))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)
  have hGood : MeasurableSet Good :=
    (measurableSet_le (((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm) measurable_const).inter
      (measurableSet_le hcount measurable_const)
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hb := birthDyadicClockBand_base_bounds hε n j i hi
  have hs : 0 < s := hb.1
  have htε : 2 * t ≤ ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have ht1 : t ≤ 1 := by
    have hε1 := hεsmall.le.trans (hε₀g.trans hεg1)
    linarith
  have htεa : 4 * t < εa := by
    have hεa' : ε < εa / 4 := hεsmall.trans_le hε₀a
    linarith
  have hvol : volume I ≤ ENNReal.ofReal (cap * s) := by
    have hw := (birthPhysicalClockWindow_spec hcap hs).2.2.1
    simpa only [I,Real.volume_Ico,sub_sub_cancel] using ENNReal.ofReal_le_ofReal hw
  have hIclock : ∀ c ∈ I, D.hi - (c - S.level) ∈ Icc t (4*t) := by
    intro c hc
    have hmem := D.originalRightBirthPhysicalClockWindow_inward_bounds hε hcap
      n j i ell hi hell ⟨hc.1,hc.2.le⟩
    exact hmem
  have hBclock : ∀ m ∈ B, D.hi - (m.1.2 - S.level) ∈ Icc t (2*t) := by
    intro m hm
    change D.hi-(t+((i:ℝ)+1)*(s/8))≤m.1.2-S.level ∧
      m.1.2-S.level<D.hi-(t+(i:ℝ)*(s/8)) at hm
    constructor <;> linarith [hm.1,hm.2,hb.2.2.1,hb.2.2.2]
  have hmaskzero : ∀ m c, m ∉ B ∨ c ∉ I → mask (m,c)=0 := by
    intro m c hc
    by_contra hn
    have hm := (D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff ε cap n j i ell (m,c)).mp hn
    rcases hc with hc | hc
    · exact hc (D.originalRightBirthClockMask_target_mem_reflectedClockBand ε n j i (m,c)
        (D.originalSupportedRightBirthPhysicalClockMask_birth ε cap n j i ell (m,c) hn).1)
    · exact hc (D.originalRightBirthPhysicalClockMask_clock_mem ε cap n j i ell (m,c) hm.2.2)
  have hspace : (∫⁻ x, ENNReal.ofReal (η x) ∂(volume : Measure (Fin q → ℝ))) ≠ (∞ : ℝ≥0∞) := by
    have hsupport : Function.support (fun x ↦ ENNReal.ofReal (η x)) ⊆
        Metric.closedBall (0 : Fin q → ℝ) physicalRadius := by
      intro x hx
      simpa only [Metric.mem_closedBall,dist_zero_right] using hηsupport x hx
    rw [←setLIntegral_eq_of_support_subset hsupport]
    apply ne_top_of_le_ne_top (b:=ENNReal.ofReal M₀ * volume (Metric.closedBall (0:Fin q→ℝ) physicalRadius))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (isCompact_closedBall _ _).measure_ne_top
    · calc
        _ ≤ ∫⁻ _x in Metric.closedBall (0:Fin q→ℝ) physicalRadius, ENNReal.ofReal M₀ :=
          lintegral_mono (fun x ↦ ENNReal.ofReal_le_ofReal (hηM x))
        _ = _ := by simp
  let shiftedJ := Ico (D.hi-(t+((i:ℝ)+1)*(s/8))) (D.hi-(t+(i:ℝ)*(s/8)))
  have hmass' : (ν.map (fun a:ℝ ↦a-S.level)) shiftedJ ≤ ENNReal.ofReal (Cm*t^G.rank*s) := by
    have hshift : Measurable (fun a:ℝ ↦a-(S.level:ℝ)) := measurable_id.sub_const _
    rw [Measure.map_apply hshift measurableSet_Ico]
    simpa only [originalRightBirthNarrowClockBand,shiftedJ,t,s,Set.preimage] using
      hmass hε (hεsmall.trans_le hε₀m) n j i hi
  have hsingle' := hsingle hε (hεsmall.trans_le hε₀s) hcap hcapσ
    n j i ell hi hell hphysicalRadius hM hη0 hηM hηR
  have hdata : ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)), scene ∉ Goodᶜ →
      (∀ᵐ a ∂physicalScenePairKernel scene.1, a ∉ V scene →
        (∫⁻ r : ℝ, ENNReal.ofReal (η (a.1 + d (a.2,r))) * f (a.2,r) ∂volume)=0) ∧
      (∀ᵐ a ∂(physicalScenePairKernel scene.1).restrict (V scene),
        (∫⁻ r : ℝ, ENNReal.ofReal (η (a.1 + d (a.2,r))) * f (a.2,r) ∂volume)≤
          ENNReal.ofReal (4*M₀*(physicalRadius+1))) ∧
      physicalScenePairKernel scene.1 (V scene) ≤ ENNReal.ofReal K := by
    filter_upwards [hp.2.2.2.2.2.2.2.2] with scene hscene
    intro hn
    have hsGood : scene ∈ Good := not_not.mp hn
    exact ⟨ae_occupiedPairTrafficContributors_outside_zero d (fun x ↦ ENNReal.ofReal (η x)) f scene,
      ae_of_all _ (fun a ↦ hsingle' a.1 a.2),(hscene hsGood.1).2.trans hsGood.2⟩
  have hres := hfirst hgap hbounds Q ht hs htεa hB hBclock
    measurableSet_Ico hIclock hcap.le hCm.le hvol (show MeasurableSet shiftedJ from measurableSet_Ico)
    (fun m hm ↦hm) hmass' mask
    (D.measurable_originalSupportedRightBirthPhysicalClockMask ε cap n j i ell)
    (D.originalSupportedRightBirthPhysicalClockMask_le_one ε cap n j i ell)
    hmaskzero hηENN hspace hGood.compl V
    (fun scene ↦measurableSet_occupiedPairTrafficContributors d
      (measurable_originalSeedPathOffset_joint S hF hw) hηENN
      (D.measurable_originalSupportedRightBirthPhysicalClockWeight hF hw ε cap n j i ell) scene)
    (show 0≤4*M₀*(physicalRadius+1) by positivity) hK hdata
  have hdata₂ : ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)), scene ∉ Goodᶜ →
      (∀ a ∈ V scene,a.1+a.2.2∈W∧a.2∈B) ∧
      physicalScenePairKernel scene.1 (V scene) ≤ ENNReal.ofReal K ∧
      (∀ᵐ a ∂physicalScenePairKernel scene.1,a∉V scene→
        (∫⁻ r:ℝ,ENNReal.ofReal (η (a.1+d (a.2,r)))*f (a.2,r) ∂volume)=0) := by
    filter_upwards [hp.2.2.2.2.2.2.2.2] with scene hscene
    intro hn
    have hsGood : scene∈Good := not_not.mp hn
    exact ⟨(hscene hsGood.1).1,(hscene hsGood.1).2.trans hsGood.2,
      ae_occupiedPairTrafficContributors_outside_zero d (fun x ↦ ENNReal.ofReal (η x)) f scene⟩
  have htεb : 4*t<εb := by
    have hεb' := hεsmall.trans_le hε₀b
    linarith
  have hres₂ := hsecond hgap hbounds Q ht ht1 hs htεb hcap.le hM hK
    measurableSet_Ico hvol (fun c hc ↦⟨(by linarith [(hIclock c hc).1]),(hIclock c hc).2⟩)
    hηENN (fun x ↦ ENNReal.ofReal_le_ofReal (hηM x)) mask
    (D.measurable_originalSupportedRightBirthPhysicalClockMask ε cap n j i ell)
    (D.originalSupportedRightBirthPhysicalClockMask_le_one ε cap n j i ell)
    (fun m c hc ↦hmaskzero m c (Or.inr hc)) hGood.compl hB hBclock V
    (fun scene ↦measurableSet_occupiedPairTrafficContributors d
      (measurable_originalSeedPathOffset_joint S hF hw) hηENN
      (D.measurable_originalSupportedRightBirthPhysicalClockWeight hF hw ε cap n j i ell) scene)
    hdata₂
  have hfEq : (fun z : PhysicalPairPalmMark (Fin q) × ℝ ↦
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) =
      D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell := by
    funext z
    rfl
  rw [hfEq] at hres hres₂
  simp only [compl_compl] at hres hres₂
  have hmean₁ : (∫ scene,(Good.indicator (fun scene ↦
      (legalMarkedCompletePathTraffic q d (fun x ↦ENNReal.ofReal (η x)) f scene).toReal) scene)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      (4*M₀*(physicalRadius+1)*K*
        (∫⁻ x,ENNReal.ofReal (η x) ∂(volume : Measure (Fin q→ℝ))).toReal*cap*(C*Real.sqrt Cm))*
      s^(3/2:ℝ)*
        (t^(((G.rank:ℝ)-3)/2)*Real.sqrt
          (∫⁻ m in B,ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm q Q.law).toReal +
          t^((G.rank:ℝ)/2)*Real.sqrt
            (∫⁻ m in B,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
              ∂legalMarkedJointPalm q Q.law).toReal) := by
    convert hres.2 using 1
    ring
  have hmean := le_min hmean₁ hres₂.2
  refine ⟨⟨hres.1,hmean,eLpNorm_two_le_sqrt_of_integral_sq_le hres.1 hmean⟩,?_⟩
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  let Small := {scene : LegalMarkedOptimalInputScene q |
    ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ}
  let Bad := {scene : LegalMarkedOptimalInputScene q |
    ENNReal.ofReal K < (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {1})}
  let N := fun scene : LegalMarkedOptimalInputScene q ↦
    ((scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {1})).toReal
  let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
    (legalMarkedCompletePathTraffic q d (fun x ↦ ENNReal.ofReal (η x)) f scene).toReal
  have hSmall : MeasurableSet Small := measurableSet_le
    (((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm) measurable_const
  have hmassRaw : ν J ≤ ENNReal.ofReal (Cm*t^G.rank*s) :=
    hmass hε (hεsmall.trans_le hε₀m) n j i hi
  have hintensity : ((volume : Measure (Fin q → ℝ)).prod ν) (W ×ˢ J) ≤
      ENNReal.ofReal (Ct*Cm) := by
    have hh := hint ν ht ht1 hs hCm.le hJ hmassRaw
    apply hh.trans
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right
      (mul_nonneg hCt.le hCm.le) ((div_le_one ht).mpr hb.2.1))
  have htail := Q.original_target_countTail_completePath_ltwo_ae_on d
    (measurable_originalSeedPathOffset_joint S hF hw) hηENN
    (D.measurable_originalSupportedRightBirthPhysicalClockWeight hF hw ε cap n j i ell)
    (hW.prod hJ) (mul_nonneg hCt.le hCm.le) hintensity hSmall V
    (fun scene ↦ measurableSet_occupiedPairTrafficContributors d
      (measurable_originalSeedPathOffset_joint S hF hw) hηENN
      (D.measurable_originalSupportedRightBirthPhysicalClockWeight hF hw ε cap n j i ell) scene)
    (K:=K) (show 0≤4*M₀*(physicalRadius+1) by positivity) (by
      filter_upwards [hp.2.2.2.2.2.2.2.2] with scene hscene
      intro hsSmall _
      exact ⟨ae_occupiedPairTrafficContributors_outside_zero d
        (fun x ↦ ENNReal.ofReal (η x)) f scene,
        ae_of_all _ (fun a ↦ hsingle' a.1 a.2), (hscene hsSmall).2⟩)
  have hNfinite := (Q.original_target_exp_moment_of_finite_intensity
    (hW.prod hJ) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hintensity)
    (t:=0) (by norm_num)).1
  have heq : Bad.indicator (Small.indicator traffic) =ᵐ[(Q.law : Measure (LegalMarkedOptimalInputScene q))]
      {scene | K < N scene}.indicator (Small.indicator traffic) := by
    filter_upwards [hNfinite] with scene hfinite
    have hevent : scene ∈ Bad ↔ K < N scene := by
      change ENNReal.ofReal K < _ ↔ _
      rw [← ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfinite.ne,
        ENNReal.toReal_ofReal hK]
    simp only [indicator_apply,hevent,mem_ofPred_eq]
  exact ⟨htail.1.ae_eq heq.symm,
    (eLpNorm_congr_ae heq).trans_le htail.2.2,
    hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,
    hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1,hp.2.2.2.2.2.2.2.1⟩




/-- One right-side geometric choice gives both genuine target count-good
moments and the count-bad exponential remainder. -/
theorem exists_original_right_bounded_birth_goodBad_smallMoments
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
    ∃ h cap : ℝ, 0 < h ∧ 0 < cap ∧ cap ≤ basecap ∧ ∀ H : ℝ, 0 ≤ H →
    ∃ ε₀ radius C₁ C₂ Btail : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      0 ≤ radius ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 ≤ Btail ∧ ∀ {ε : ℝ}, 0 < ε → ε < ε₀ →
      ∀ n j i ell : ℕ, i < dyadicBirthBandCount j → ell < birthPhysicalClockWindowCount cap →
      ∀ {K : ℝ}, 0 ≤ K →
      let t := birthDyadicShellScale ε n
      let s := birthDyadicElapsedScale ε n j
      let δ := birthTrafficCoarseScale q t s
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      let cut := D.originalRightBirthPhysicalClockReference ε cap n j i ell - S.level
      let L : ℝ≥0 := ⟨Real.sqrt ((q : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let J := D.originalRightBirthNarrowClockBand ε n j i
      let B := {m : PhysicalPairPalmMark (Fin q) | m.1.2 ∈ J}
      let W := birthTrafficSpatialWindow G t s radius
      let Good := {scene : LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ ∧
          (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {1}) ≤ ENNReal.ofReal K}
      let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
        (legalMarkedCompletePathTraffic q (fun z ↦ originalSeedPathOffset S w z.2 z.1)
          (fun x ↦ ENNReal.ofReal (η x)) (D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell) scene).toReal
      let firstBudget :=
        (4*M₀*(physicalRadius+1)*K*
          (∫⁻ x, ENNReal.ofReal (η x) ∂(volume : Measure (Fin q → ℝ))).toReal *cap*C₁) *
          s ^ (3/2 : ℝ) *
          (t ^ (((G.rank : ℝ)-3)/2) * Real.sqrt
            (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
              ∂legalMarkedJointPalm q Q.law).toReal +
            t ^ ((G.rank : ℝ)/2) * Real.sqrt
              (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
                ∂legalMarkedJointPalm q Q.law).toReal)
      let secondBudget := (K*(M₀*cap)^2*C₂)*s^2 *
        (t ^ (-(G.rank : ℝ)-4)*
          (∫⁻ m in B,ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm q Q.law).toReal +
          t ^ (-(G.rank : ℝ)-3)*
            (∫⁻ m in B,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
              ∂legalMarkedJointPalm q Q.law).toReal)
      (MemLp (Good.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ scene,(Good.indicator traffic scene)^2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤ min firstBudget secondBudget ∧
      eLpNorm (Good.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt (min firstBudget secondBudget))) ∧
      let Small := {scene : LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ}
      let Bad := {scene : LegalMarkedOptimalInputScene q |
        ENNReal.ofReal K < (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {1})}
      MemLp (Bad.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      eLpNorm (Bad.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≤
          ENNReal.ofReal (Btail * Real.exp (-K / 4)) := by
  obtain ⟨h,cap,ρ,hh,hcap,hcapbase,hρ,hall⟩ :=
    D.exists_original_right_bounded_birth_geometric_goodBad_smallMoments hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨h,cap,hh,hcap,hcapbase,?_⟩
  intro H hH
  obtain ⟨ε₀,radius,C₁,C₂,Btail,hε₀,hε₀1,hradius,hC₁,hC₂,hBtail,hall⟩ := hall H hH
  refine ⟨ε₀,radius,C₁,C₂,Btail,hε₀,hε₀1,hradius,hC₁,hC₂,hBtail,?_⟩
  intro ε hε hεsmall n j i ell hi hell K hK
  have hh := hall hε hεsmall n j i ell hi hell hK
  exact ⟨hh.1,hh.2.1,hh.2.2.1⟩

/-- Full actual bounded-birth levels retain the interpolated energy saving
and the same original count-tail remainder, for the same geometric choice. -/
theorem exists_original_right_bounded_birth_level_norm
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
    ∃ h cap E₀ : ℝ,0<h∧0<cap∧1≤E₀∧∀ H:ℝ,0≤H→
    ∃ ε₀ radius A Btail : ℝ,0<ε₀∧ε₀≤1∧0≤radius∧0<A∧0≤Btail∧
      ∀ {ε:ℝ},0<ε→ε<ε₀→∀ n j ell:ℕ,ell<birthPhysicalClockWindowCount cap→∀ {K:ℝ},0≤K→
      let t:=birthDyadicShellScale ε n
      let s:=birthDyadicElapsedScale ε n j
      let δ:=birthTrafficCoarseScale q t s
      let T:=positiveMatrixNormalizer (birthResidueScale G t s)
      let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
      let cut:=fun i↦D.originalRightBirthPhysicalClockReference ε cap n j i ell-S.level
      let Small:=fun i↦{scene:LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖≤H*δ}
      let traffic:=fun i scene↦(Small i).indicator (fun scene:LegalMarkedOptimalInputScene q↦
        (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
          (fun x↦ENNReal.ofReal (η x))
          (D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell) scene).toReal) scene
      MemLp (fun scene↦∑ i∈Finset.range (dyadicBirthBandCount j),traffic i scene)
        2 (Q.law:Measure (LegalMarkedOptimalInputScene q)) ∧
      eLpNorm (fun scene↦∑ i∈Finset.range (dyadicBirthBandCount j),traffic i scene)
        2 (Q.law:Measure (LegalMarkedOptimalInputScene q))≤
      ENNReal.ofReal ((A*Real.sqrt K*Real.sqrt E₀)*
        (t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
          (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4)))) + (dyadicBirthBandCount j : ℝ)*(Btail*Real.exp (-K/4))) := by
  obtain ⟨h,cap,hh,hcap,_hcapbase,hsmall⟩ :=
    D.exists_original_right_bounded_birth_goodBad_smallMoments hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  obtain ⟨E₀,hE₀,henergy⟩ := D.exists_original_right_narrowBirthBands_energy_budget
    hF hw hη hηspan hG hRem hpole hgap hbounds Q
  refine ⟨h,cap,E₀,hh,hcap,hE₀,?_⟩
  intro H hH
  obtain ⟨ε₀,radius,C₁,C₂,Btail,hε₀,hε₀1,hradius,hC₁,hC₂,hBtail,hsmall⟩ := hsmall H hH
  let p₁:=4*M₀*(physicalRadius+1)*
    (∫⁻ x,ENNReal.ofReal (η x) ∂(volume:Measure (Fin q→ℝ))).toReal*cap*C₁
  let p₂:=(M₀*cap)^2*C₂
  let C:=max p₁ p₂+1
  have hp₁ : p₁≤C := (le_max_left _ _).trans (by dsimp only [C]; linarith)
  have hp₂ : p₂≤C := (le_max_right _ _).trans (by dsimp only [C]; linarith)
  have hp₁0 : 0≤p₁ := by dsimp only [p₁]; positivity
  have hC : 0<C := by dsimp only [C]; linarith [le_max_left p₁ p₂]
  let A:=(2*(8:ℝ)^(3/4:ℝ)+2*Real.sqrt 8)*Real.sqrt C
  have hA : 0<A := by dsimp only [A]; positivity
  refine ⟨ε₀,radius,A,Btail,hε₀,hε₀1,hradius,hA,hBtail,?_⟩
  intro ε hε hεsmall n j ell hell K hK
  dsimp only
  let t:=birthDyadicShellScale ε n
  let s:=birthDyadicElapsedScale ε n j
  let δ:=birthTrafficCoarseScale q t s
  let T:=positiveMatrixNormalizer (birthResidueScale G t s)
  let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
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
    exact (hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).1.1
  have hfirst : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤
      (K*C)*s^(3/2:ℝ)*(t^(((G.rank:ℝ)-3)/2)*Real.sqrt (e i)+t^((G.rank:ℝ)/2)*Real.sqrt (v i)) := by
    intro i hi
    have hr:=(hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).1.2.1
    have hr:=hr.trans (min_le_left _ _)
    calc
      _ ≤ (K*p₁)*s^(3/2:ℝ)*(t^(((G.rank:ℝ)-3)/2)*Real.sqrt (e i)+t^((G.rank:ℝ)/2)*Real.sqrt (v i)) := by
        convert hr using 1
        all_goals first | rfl | (dsimp only [p₁,t,s,e,v,B,J]; ring)
      _ ≤ _ := by gcongr
  have hsecond : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤
      (K*C)*s^2*(t^(-((G.rank:ℝ)+4))*e i+t^(-((G.rank:ℝ)+3))*v i) := by
    intro i hi
    have hr:=(hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).1.2.1
    have hr:=hr.trans (min_le_right _ _)
    calc
      _ ≤ (K*p₂)*s^2*(t^(-((G.rank:ℝ)+4))*e i+t^(-((G.rank:ℝ)+3))*v i) := by
        convert hr using 1
        all_goals first | rfl | (dsimp only [p₂,t,s,e,v,B,J]; ring)
      _ ≤ _ := by gcongr
  have hgood : MemLp (fun scene↦∑ i∈bands,traffic i scene) 2 P ∧
      eLpNorm (fun scene↦∑ i∈bands,traffic i scene) 2 P ≤
        ENNReal.ofReal ((A*Real.sqrt K*Real.sqrt E₀)*
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
    dsimp only [A]
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
        ENNReal.ofReal ((A*Real.sqrt K*Real.sqrt E₀)*
          (t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
            (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4))))) := by
    simpa only [traffic,hGoodEq] using hgood
  have hbad : ∀ i∈bands,MemLp ((Bad i).indicator ((Small i).indicator (raw i))) 2 P := by
    intro i hi
    exact (hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).2.1
  have hbadNorm : ∀ i∈bands,eLpNorm ((Bad i).indicator ((Small i).indicator (raw i))) 2 P ≤
      ENNReal.ofReal (Btail*Real.exp (-K/4)) := by
    intro i hi
    exact (hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).2.2
  have hfull:=finite_sceneEvent_traffic_memLp_two_of_good_bad_norm_bounds P bands Small Bad raw
    hgood'.1 hbad (by positivity) (by positivity) hgood'.2 hbadNorm
  simpa only [bands,Finset.card_range] using hfull



/-- Every bounded canonical phase of the actual original right-birth traffic
is L2 over the entire double dyadic family. The original count-good and
count-bad pieces are assembled internally on the same Q and same h/cap. -/
theorem exists_original_right_bounded_birth_dyadic_traffic_memLp_two
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
    ∃ h cap : ℝ,0<h∧0<cap∧∀ H:ℝ,0≤H→
    ∃ ε : ℝ,0<ε∧
      ∀ ell:ℕ,ell<birthPhysicalClockWindowCount cap→
      let level := fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q) ↦
        let t:=birthDyadicShellScale ε z.1
        let s:=birthDyadicElapsedScale ε z.1 z.2
        let δ:=birthTrafficCoarseScale q t s
        let T:=positiveMatrixNormalizer (birthResidueScale G t s)
        let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
        ∑ i∈Finset.range (dyadicBirthBandCount z.2),
          {scene:LegalMarkedOptimalInputScene q |
            ‖D.normalizedMomentumPhaseField T
              (D.originalRightBirthPhysicalClockReference ε cap z.1 z.2 i ell-S.level) h L scene 0‖≤H*δ}.indicator
            (fun scene:LegalMarkedOptimalInputScene q ↦
              (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
                (fun x↦ENNReal.ofReal (η x))
                (D.originalSupportedRightBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene).toReal) scene
      MemLp (fun scene↦∑' z:ℕ×ℕ,level z scene) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q)) ∧
      Summable (fun z:ℕ×ℕ ↦(eLpNorm (level z) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q))).toReal) ∧
      ∀ᵐ scene∂(Q.law:Measure (LegalMarkedOptimalInputScene q)),
        Summable (fun z:ℕ×ℕ ↦‖level z scene‖) := by
  obtain ⟨h,cap,E₀,hh,hcap,hE₀,hlevel⟩ :=
    D.exists_original_right_bounded_birth_level_norm hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨h,cap,hh,hcap,?_⟩
  intro H hH
  obtain ⟨ε₀,radius,A,Btail,hε₀,_hε₀1,hradius,hA,hBtail,hlevel⟩ := hlevel H hH
  let ε:=ε₀/2
  have hε : 0<ε := by dsimp only [ε]; positivity
  have hεsmall : ε<ε₀ := by dsimp only [ε]; linarith
  refine ⟨ε,hε,?_⟩
  intro ell hell
  dsimp only
  let level := fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q) ↦
    let t:=birthDyadicShellScale ε z.1
    let s:=birthDyadicElapsedScale ε z.1 z.2
    let δ:=birthTrafficCoarseScale q t s
    let T:=positiveMatrixNormalizer (birthResidueScale G t s)
    let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    ∑ i∈Finset.range (dyadicBirthBandCount z.2),
      {scene:LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T
      (D.originalRightBirthPhysicalClockReference ε cap z.1 z.2 i ell-S.level) h L scene 0‖≤H*δ}.indicator
        (fun scene:LegalMarkedOptimalInputScene q ↦
      (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
        (fun x↦ENNReal.ofReal (η x))
        (D.originalSupportedRightBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene).toReal) scene
  let P:Measure (LegalMarkedOptimalInputScene q):=Q.law
  have hLp : ∀ z,MemLp (level z) 2 P := by
    intro z
    exact (hlevel hε hεsmall z.1 z.2 ell hell (by norm_num : (0:ℝ)≤0)).1
  -- The count thresholds are chosen by the common analytic summation lemma.
  exact memLp_original_birth_double_tsum_of_level_norm_bounds
    («q» := (q : ℝ)) (ε := ε) (E := E₀) (A := A) (Btail := Btail)
    P (by exact_mod_cast hq) hε hE₀ hA.le hBtail G.rank level hLp
    (by
      intro z K hK
      exact (hlevel hε hεsmall z.1 z.2 ell hell hK).2)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
