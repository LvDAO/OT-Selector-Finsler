import OTSelector.Reconstruction.CountDominatedWindowLtwo
import OTSelector.Reconstruction.OriginalMinimizerDyadicTrafficNorm
import OTSelector.Reconstruction.OriginalFinslerPoleLoewnerComparison
import OTSelector.Reconstruction.OriginalSameResidueClockBandEnergyBudget
import OTSelector.Reconstruction.OriginalInputCountTailTrafficLtwo
import OTSelector.Reconstruction.OriginalBirthSpatialWindowCountTailLtwo
import OTSelector.Reconstruction.OriginalCompletePathGoodEventLtwo
import OTSelector.Reconstruction.FinslerOriginalCompletePathClockPieces
import OTSelector.Reconstruction.FinslerOriginalLeftBirthBoundedContributors
import OTSelector.Reconstruction.FinslerOriginalRightBirthBoundedContributors
import OTSelector.Reconstruction.FinslerOriginalBirthSmallSecondMomentAE
import OTSelector.Reconstruction.FinslerOriginalBirthSmallFirstSquareAE
import OTSelector.Probability.BirthSmallTrafficInterpolatedNorm
import OTSelector.Probability.BirthRankZeroInterpolatedNorm
import OTSelector.Probability.BirthActualProfileSummability
import OTSelector.MeasureTheory.Lp.SummableSeries
import OTSelector.Reconstruction.FinslerFocalLiteralEdgeOccupation

/-! Actual complete-traffic assembly with coherent original pole certificates
and genuine common-scale original-input counts. -/
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

/-- Both actual endpoints retain their exact original pole certificates on
one common interior radius. Every later smaller collar uses these same residues. -/
theorem exists_original_both_poles_common_radius
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ radius : ℝ,0<radius∧radius<D.hi-D.lo∧
    ∃ Gleft Gright : Matrix (Fin q) (Fin q) ℝ,
    ∃ Remleft Remright : ℝ→Matrix (Fin q) (Fin q) ℝ,
      Gleft.PosSemidef∧Gright.PosSemidef∧
      ContDiffOn ℝ ∞ Remleft (Ioo (-radius) radius)∧
      ContDiffOn ℝ ∞ Remright (Ioo (-radius) radius)∧
      (∀r∈Ioo 0 radius,originalSeedKernel S w (D.lo+r)=(r^2)⁻¹•Gleft+Remleft r)∧
      (∀r∈Ioo 0 radius,originalSeedKernel S w (D.hi-r)=(r^2)⁻¹•Gright+Remright r)∧
    ∃ cleft Cleft cright Cright : ℝ,
      0<cleft∧0<Cleft∧0<cright∧0<Cright∧
      (∀r∈Ioo 0 radius,
        (originalSeedKernel S w (D.lo+r)-cleft•((r^2)⁻¹•Gleft+1)).PosSemidef∧
        (Cleft•((r^2)⁻¹•Gleft+1)-originalSeedKernel S w (D.lo+r)).PosSemidef)∧
      (∀r∈Ioo 0 radius,
        (originalSeedKernel S w (D.hi-r)-cright•((r^2)⁻¹•Gright+1)).PosSemidef∧
        (Cright•((r^2)⁻¹•Gright+1)-originalSeedKernel S w (D.hi-r)).PosSemidef) := by
  obtain ⟨leftRadius,hlpos,hlspan,Gleft,Remleft,hGl,hRl,hpoleL,cleft,hcl,Cleft,hCl,hcompL⟩ :=
    D.exists_original_kernel_left_pole_loewner_comparison hF hw
  obtain ⟨rightRadius,hrpos,_hrspan,Gright,Remright,hGr,hRr,hpoleR,cright,hcr,Cright,hCr,hcompR⟩ :=
    D.exists_original_kernel_right_pole_loewner_comparison hF hw
  let radius := min leftRadius rightRadius
  have hpos : 0<radius := lt_min hlpos hrpos
  have hleft : radius≤leftRadius := min_le_left _ _
  have hright : radius≤rightRadius := min_le_right _ _
  refine ⟨radius,hpos,hleft.trans_lt hlspan,Gleft,Gright,Remleft,Remright,hGl,hGr,
    hRl.mono (Ioo_subset_Ioo (neg_le_neg hleft) hleft),
    hRr.mono (Ioo_subset_Ioo (neg_le_neg hright) hright),
    fun r hr ↦hpoleL r ⟨hr.1,hr.2.trans_le hleft⟩,
    fun r hr ↦hpoleR r ⟨hr.1,hr.2.trans_le hright⟩,
    cleft,Cleft,cright,Cright,hcl,hCl,hcr,hCr,
    fun r hr ↦hcompL r ⟨hr.1,hr.2.trans_le hleft⟩,
    fun r hr ↦hcompR r ⟨hr.1,hr.2.trans_le hright⟩⟩

/-- Every smaller actual common-scale radius gives a subset of the SAME
original input cell, keeping its deterministic clock carrier fixed. -/
theorem commonScaleOriginalSourcePhaseCell_mono_radius
    (T : Matrix (Fin q) (Fin q) ℝ) (cut δ : ℝ) (Band : Set ℝ)
    (z₀ p₀ : Fin q→ℝ) {R₁ R₂ : ℝ} (hR : R₁≤R₂) :
    D.commonScaleOriginalSourcePhaseCell T cut δ Band z₀ p₀ R₁⊆
      D.commonScaleOriginalSourcePhaseCell T cut δ Band z₀ p₀ R₂ := by
  intro x hx
  refine ⟨hx.1,hx.2.trans ?_⟩
  dsimp only [phaseSourceCellRadius]
  gcongr


/-- A bounded genuinely divided amplitude is controlled by one fixed original
source count. The same frame, source clock carrier and actual occupied edges are
retained; no selected-cloud count hypothesis is introduced. -/
theorem ae_original_minimizer_commonScale_bounded_traffic_le_fixedCount
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hgap : 0<gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T] {δ : ℝ} (hδ : 1≤δ)
    {G : ℝ} {g : ℝ→ℝ→ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀a b,|g a b|≤G) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀P : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {cut h ell a : ℝ} (hcut : cut∈Ioo D.lo D.hi) (hh : 0<h) (ha : 0≤a)
    (hclockRange : ∀r∈Icc (0:ℝ) 1,cut+ell*r∈Ioo D.lo D.hi)
    (hsmall : ∀r∈Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) ell r‖*
        Real.sqrt ((q:ℝ)/h^2)≤(1/2:ℝ))
    {ρ A : ℝ} (hA : 0≤A)
    (hR : ∀r∈Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T (cut+S.level) ell r‖≤ρ)
    (hRLip : ∀r∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) ell r-
        originalNormalizedClockMobility S w T (cut+S.level) ell v‖≤A*|r-v|)
    {η : (Fin q→ℝ)→ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q)×ℝ→ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (hclock : ∀m c,f (m,c)≠0→∃r∈Icc (0:ℝ) 1,c=cut+S.level+ell*r)
    (hηwindow : ∀x,η x≠0→‖T*ᵥx‖≤a*δ)
    {Band : Set ℝ} (hBand : MeasurableSet Band)
    (hmask : ∀(e : LegalMarkedPhysicalEdge q) c,
      f ((physicalPairAnchor e).2,c)≠0→e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.1.2∈Band)
    (hηfinite : (∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))≠(⊤:ℝ≥0∞))
    (hffinite : (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)≠(⊤:ℝ≥0∞))
    {Bedge Λ : ℝ} (hBedge : 0≤Bedge) (hΛ : 0≤Λ)
    (hbound : ∀e∈legalMarkedCompletePathContributors q
      (fun z ↦originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic q
        (fun z ↦originalSeedPathOffset S w z.2 z.1) η f e).toReal≤Bedge)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
    (H : ℝ) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
    let m := Nat.ceil (C*H)
    ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ‖D.normalizedMomentumPhaseField T cut h L scene 0‖≤H*δ→
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f scene).toReal≤
        Bedge*D.commonScaleOriginalSourceGlobalCount T cut δ Band m radius scene := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|τ| *G/h)
  let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
  let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
  let m := Nat.ceil (C*H)
  have hδpos : 0<δ := by linarith
  have hC : 1≤C := (canonicalPhaseCurveScaleCoefficient_bounds (L:ℝ) ρ A).1
  have hρ : 0≤ρ := (norm_nonneg
    (originalNormalizedClockMobility S w T (cut+S.level) ell 0)).trans (hR 0 (by norm_num))
  have hradius : 0≤radius := by dsimp only [radius,b]; positivity
  have hdom := D.ae_original_minimizer_commonScale_traffic_le_globalCount
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hBand hmask hηfinite hffinite hBedge hΛ hbound hunit
  have hN := (D.commonScaleOriginalSourceGlobalCount_fourth_moment
    hF hw T hcut hδpos hBand hΛ hradius hunit Q m).1
  filter_upwards [hdom,hN] with scene hs hsN
  intro hamp
  have hkm : k scene≤m := by
    apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hδpos).mpr hamp) (by linarith)
  have hsub : D.commonScaleOriginalSourceGlobalEnvelope T cut δ Band (k scene) radius⊆
      D.commonScaleOriginalSourceGlobalEnvelope T cut δ Band m radius := by
    apply D.commonScaleOriginalSourcePhaseCell_mono_radius
    have hkm' : (k scene:ℝ)≤m := by exact_mod_cast hkm
    linarith
  have hc : D.commonScaleOriginalSourceGlobalCount T cut δ Band (k scene) radius scene≤
      D.commonScaleOriginalSourceGlobalCount T cut δ Band m radius scene := by
    exact ENNReal.toReal_mono hsN.ne (measure_mono (Set.prod_mono hsub subset_rfl))
  exact hs.trans (mul_le_mul_of_nonneg_left hc hBedge)


/-- The bounded common-scale branch has a quantitative norm bound from the
SAME fixed original input count and actual original first Palm occupation. -/
theorem original_minimizer_commonScale_bounded_traffic_memLp_two_le
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hgap : 0<gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T] {δ : ℝ} (hδ : 1≤δ)
    {G : ℝ} {g : ℝ→ℝ→ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀a b,|g a b|≤G) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀P : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {cut h ell a : ℝ} (hcut : cut∈Ioo D.lo D.hi) (hh : 0<h) (ha : 0≤a)
    (hclockRange : ∀r∈Icc (0:ℝ) 1,cut+ell*r∈Ioo D.lo D.hi)
    (hsmall : ∀r∈Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) ell r‖*
        Real.sqrt ((q:ℝ)/h^2)≤(1/2:ℝ))
    {ρ A : ℝ} (hA : 0≤A)
    (hR : ∀r∈Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T (cut+S.level) ell r‖≤ρ)
    (hRLip : ∀r∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) ell r-
        originalNormalizedClockMobility S w T (cut+S.level) ell v‖≤A*|r-v|)
    {η : (Fin q→ℝ)→ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q)×ℝ→ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (hclock : ∀m c,f (m,c)≠0→∃r∈Icc (0:ℝ) 1,c=cut+S.level+ell*r)
    (hηwindow : ∀x,η x≠0→‖T*ᵥx‖≤a*δ)
    {Band : Set ℝ} (hBand : MeasurableSet Band)
    (hmask : ∀(e : LegalMarkedPhysicalEdge q) c,
      f ((physicalPairAnchor e).2,c)≠0→e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.1.2∈Band)
    (hηfinite : (∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))≠(⊤:ℝ≥0∞))
    (hffinite : (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)≠(⊤:ℝ≥0∞))
    {Bedge Λ : ℝ} (hBedge : 0≤Bedge) (hΛ : 0≤Λ)
    (hbound : ∀e∈legalMarkedCompletePathContributors q
      (fun z ↦originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic q
        (fun z ↦originalSeedPathOffset S w z.2 z.1) η f e).toReal≤Bedge)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
    (H : ℝ)
    {K : ℝ} (hK : 0≤K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
    let m := Nat.ceil (C*H)
    let Λsmall := (2*(m:ℝ)+radius)^q*Λ
    let traffic := fun scene ↦
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f scene).toReal
    let Small := {scene |‖D.normalizedMomentumPhaseField T cut h L scene 0‖≤H*δ}
    let palm := ((∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))*
      (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)).toReal
    let budget := Bedge*K*palm+8*Bedge^2*Real.exp (Λsmall*(Real.exp 1-1))*Real.exp (-K/2)
    MemLp (Small.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫scene,(Small.indicator traffic scene)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤budget ∧
    eLpNorm (Small.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))≤
      ENNReal.ofReal (Real.sqrt budget) := by
  dsimp only
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|τ| *G/h)
  let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
  let m := Nat.ceil (C*H)
  let W := D.commonScaleOriginalSourceGlobalEnvelope T cut δ Band m radius
  let N := fun scene : LegalMarkedOptimalInputScene q ↦
    ((scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{0})).toReal
  let Λsmall := (2*(m:ℝ)+radius)^q*Λ
  let d := fun z : PhysicalPairPalmMark (Fin q)×ℝ ↦originalSeedPathOffset S w z.2 z.1
  let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
    (legalMarkedCompletePathTraffic q d η f scene).toReal
  let Small := {scene |‖D.normalizedMomentumPhaseField T cut h L scene 0‖≤H*δ}
  have hd := measurable_originalSeedPathOffset_joint S hF hw
  have htraffic : Measurable traffic :=
    (measurable_legalMarkedCompletePathTraffic d hd hη hf).ennreal_toReal
  have hSmall : MeasurableSet Small := measurableSet_le
    (((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm) measurable_const
  have hW := D.measurableSet_commonScaleOriginalSourceGlobalEnvelope hF hw T hcut δ hBand m radius
  have hN : Measurable N := D.measurable_commonScaleOriginalSourceGlobalCount hF hw T hcut δ hBand m radius
  have hρ : 0≤ρ := (norm_nonneg
    (originalNormalizedClockMobility S w T (cut+S.level) ell 0)).trans (hR 0 (by norm_num))
  have hradius : 0≤radius := by dsimp only [radius,b]; positivity
  have hδpos : 0<δ := by linarith
  have hΛsmall : 0≤Λsmall := mul_nonneg (pow_nonneg (by positivity) _) hΛ
  have hmass : ((volume : Measure (Fin q→ℝ)).prod μ) W≤ENNReal.ofReal Λsmall :=
    D.commonScaleOriginalSourcePhaseCell_intensity_le_of_unit hF hw T hcut hδpos hBand hΛ
      (by positivity) hunit 0 0
  have hdom := D.ae_original_minimizer_commonScale_bounded_traffic_le_fixedCount
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hBand hmask hηfinite hffinite hBedge hΛ hbound hunit H
  have hfinite : (∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))*
      (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)≠(⊤:ℝ≥0∞) :=
    ENNReal.mul_ne_top hηfinite hffinite
  have hm := measurable_legalMarkedCompletePathTraffic d hd hη hf
  have hmeanFinite : (∫⁻scene,legalMarkedCompletePathTraffic q d η f scene
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≠(⊤:ℝ≥0∞) := by
    rwa [Q.lintegral_completePathTraffic d hd hη hf]
  have hInt := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hmeanFinite
  have hmean : (∫scene,traffic scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))=
      ((∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))*
        (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)).toReal := by
    rw [show traffic=(fun scene↦(legalMarkedCompletePathTraffic q d η f scene).toReal) from rfl,
      integral_toReal hm.aemeasurable (ae_lt_top hm hmeanFinite),
      Q.lintegral_completePathTraffic d hd hη hf]
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hreal : (((volume : Measure (Fin q→ℝ)).prod μ) W).toReal≤Λsmall := by
    simpa only [ENNReal.toReal_ofReal hΛsmall] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  obtain ⟨_,hExp,hExpBound⟩ :=
    Q.original_source_exp_moment_of_finite_intensity hW hfin (t:=1) (by norm_num)
  simp only [one_mul] at hExp hExpBound
  have hexp : (∫scene,Real.exp (N scene)
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤Real.exp (Λsmall*(Real.exp 1-1)) := by
    apply hExpBound.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hreal
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ)≤1)))
  have hout := bounded_count_traffic_memLp_two_le
    (Q.law : Measure (LegalMarkedOptimalInputScene q)) htraffic
    (fun _↦ENNReal.toReal_nonneg) hInt hSmall hN (fun _↦ENNReal.toReal_nonneg)
    hExp hexp hBedge hK hdom
  rwa [hmean] at hout


/-- Bounded and large genuinely common-scale phases cover the SAME complete
window traffic. Both norm budgets use the true original delta-frame counts. -/
theorem original_minimizer_commonScale_fullWindow_traffic_memLp_two_le
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hgap : 0<gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T] {δ : ℝ} (hδ : 1≤δ)
    {G : ℝ} {g : ℝ→ℝ→ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀a b,|g a b|≤G) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀P : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {cut h ell a : ℝ} (hcut : cut∈Ioo D.lo D.hi) (hh : 0<h) (ha : 0≤a)
    (hclockRange : ∀r∈Icc (0:ℝ) 1,cut+ell*r∈Ioo D.lo D.hi)
    (hsmall : ∀r∈Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) ell r‖*
        Real.sqrt ((q:ℝ)/h^2)≤(1/2:ℝ))
    {ρ A : ℝ} (hA : 0≤A)
    (hR : ∀r∈Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T (cut+S.level) ell r‖≤ρ)
    (hRLip : ∀r∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) ell r-
        originalNormalizedClockMobility S w T (cut+S.level) ell v‖≤A*|r-v|)
    {η : (Fin q→ℝ)→ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q)×ℝ→ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (hclock : ∀m c,f (m,c)≠0→∃r∈Icc (0:ℝ) 1,c=cut+S.level+ell*r)
    (hηwindow : ∀x,η x≠0→‖T*ᵥx‖≤a*δ)
    {Band : Set ℝ} (hBand : MeasurableSet Band)
    (hmask : ∀(e : LegalMarkedPhysicalEdge q) c,
      f ((physicalPairAnchor e).2,c)≠0→e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.1.2∈Band)
    (hηfinite : (∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))≠(⊤:ℝ≥0∞))
    (hffinite : (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)≠(⊤:ℝ≥0∞))
    {Bedge Λ : ℝ} (hBedge : 0≤Bedge) (hΛ : 0≤Λ)
    (hbound : ∀e∈legalMarkedCompletePathContributors q
      (fun z ↦originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic q
        (fun z ↦originalSeedPathOffset S w z.2 z.1) η f e).toReal≤Bedge)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
    {K : ℝ} (hK :
      let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8*|τ| *G/h)
      let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
      commonScaleSourceCountThreshold q Λ radius≤K)
    (hpfinite : (∫⁻m,∫⁻c : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,c)
      ∂volume ∂legalMarkedJointPalm q Q.law)≠(⊤:ℝ≥0∞)) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
    let H := 1+2*((L:ℝ)*a+b)
    let m := Nat.ceil (C*H)
    let Λsmall := (2*(m:ℝ)+radius)^q*Λ
    let firstPalm := ((∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))*
      (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)).toReal
    let weightedPalm := ((∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))*
      (∫⁻m,∫⁻c : ℝ,ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,c)
        ∂volume ∂legalMarkedJointPalm q Q.law)).toReal
    let smallBudget := Bedge*K*firstPalm+
      8*Bedge^2*Real.exp (Λsmall*(Real.exp 1-1))*Real.exp (-K/2)
    let largeBudget := (3*Bedge*(K*(C+1)/δ))*weightedPalm+
      Bedge^2*commonScaleSourceEnvelopeBudget q Λ radius*
        Real.exp (-(K-commonScaleSourceCountThreshold q Λ radius)/2)
    MemLp (fun scene ↦
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f scene).toReal)
      2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    eLpNorm (fun scene ↦
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f scene).toReal)
      2 (Q.law : Measure (LegalMarkedOptimalInputScene q))≤
      ENNReal.ofReal (Real.sqrt smallBudget+Real.sqrt largeBudget) := by
  dsimp only at hK ⊢
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|τ| *G/h)
  let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
  let H := 1+2*((L:ℝ)*a+b)
  let m := Nat.ceil (C*H)
  let Λsmall := (2*(m:ℝ)+radius)^q*Λ
  let d := fun z : PhysicalPairPalmMark (Fin q)×ℝ ↦originalSeedPathOffset S w z.2 z.1
  let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
    (legalMarkedCompletePathTraffic q d η f scene).toReal
  let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
  let Small := {scene |‖D.normalizedMomentumPhaseField T cut h L scene 0‖≤H*δ}
  let Big := {scene |1≤k scene∧δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖∧
    2*((L:ℝ)*(a*δ)+b)≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖}
  have hd := measurable_originalSeedPathOffset_joint S hF hw
  have htraffic : Measurable traffic :=
    (measurable_legalMarkedCompletePathTraffic d hd hη hf).ennreal_toReal
  have hρ : 0≤ρ := (norm_nonneg
    (originalNormalizedClockMobility S w T (cut+S.level) ell 0)).trans (hR 0 (by norm_num))
  have hradius : 0≤radius := by dsimp only [radius,b]; positivity
  have he1 : 0≤Real.exp 1-1 := sub_nonneg.mpr (Real.one_le_exp zero_le_one)
  have hK0 : 0≤K := (show 0≤commonScaleSourceCountThreshold q Λ radius by
    unfold commonScaleSourceCountThreshold
    positivity).trans hK
  have hs := D.original_minimizer_commonScale_bounded_traffic_memLp_two_le
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hBand hmask hηfinite hffinite hBedge hΛ hbound hunit H hK0
  have hb := D.original_minimizer_commonScale_large_traffic_memLp_two_le
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hBand hmask hηfinite hffinite hBedge hΛ hbound hunit hK hpfinite
  have hdom : ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ‖traffic scene‖≤Small.indicator traffic scene+Big.indicator traffic scene := by
    filter_upwards [] with scene
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    by_cases hsm : scene∈Small
    · rw [indicator_of_mem hsm]
      exact le_add_of_nonneg_right (indicator_nonneg (fun _ _ ↦ENNReal.toReal_nonneg) scene)
    · have hamp : H*δ<‖D.normalizedMomentumPhaseField T cut h L scene 0‖ := lt_of_not_ge hsm
      have hb0 : 0≤b := Real.sqrt_nonneg _
      have hL0 : 0≤(L:ℝ) := L.coe_nonneg
      have hH : 1≤H := by dsimp only [H]; nlinarith [mul_nonneg hL0 ha]
      have hδpos : 0<δ := by linarith
      have hampδ : δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖ :=
        (le_mul_of_one_le_left hδpos.le hH).trans hamp.le
      have hscale := D.commonScaleNormalizedCanonicalCurveIntegerScale_spec
        T cut h L ρ A δ (N:=1) le_rfl scene
        (by simpa only [Nat.cast_one] using (one_le_div hδpos).mpr hampδ)
      have hlarge : 2*((L:ℝ)*(a*δ)+b)≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖ := by
        have hbδ : b≤b*δ := le_mul_of_one_le_right hb0 hδ
        dsimp only [H] at hamp
        nlinarith
      have hbig : scene∈Big := ⟨hscale.1,hampδ,hlarge⟩
      rw [indicator_of_notMem hsm,indicator_of_mem hbig,zero_add]
  refine ⟨(hs.1.add hb.1).mono' htraffic.aestronglyMeasurable hdom,?_⟩
  calc
    _ ≤ eLpNorm (fun scene ↦Small.indicator traffic scene+Big.indicator traffic scene) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) := eLpNorm_mono_ae_real hdom
    _ ≤ eLpNorm (Small.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))+
        eLpNorm (Big.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
      eLpNorm_add_le hs.1.aestronglyMeasurable hb.1.aestronglyMeasurable (by norm_num)
    _ ≤ _ := by
      exact (add_le_add hs.2.2 hb.2.2).trans_eq
        (ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).symm


/-- A SAME-residue comparison gives actual left birth windows for EVERY
sufficiently small collar. All geometric proofs are consumed from the original
of-comparison APIs, so later common-collar selection does not reselect G. -/
theorem exists_original_left_shrinkable_birthWindows_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {geoε lower upper : ℝ} (_hgeoε : 0<geoε) (hgeospan : geoε<D.hi-D.lo)
    (hlower : 0<lower) (hupper : 0<upper)
    (hcomp : ∀r∈Ioo 0 geoε,
      (originalSeedKernel S w (D.lo+r)-lower•((r^2)⁻¹•G+1)).PosSemidef∧
      (upper•((r^2)⁻¹•G+1)-originalSeedKernel S w (D.lo+r)).PosSemidef) :
    ∃ Bmob : ℝ,0≤Bmob∧∀{ε : ℝ},0<ε→8*ε<geoε→8*ε≤gap→
      ∀(L : ℝ≥0)(basecap : ℝ),0<basecap→
      let cap := commonPhysicalNormalizedWindowFraction basecap Bmob (L:ℝ)
      ∀n j i ell : ℕ,i<dyadicBirthBandCount j→ell<birthPhysicalClockWindowCount cap→
      let T := positiveMatrixNormalizer
        (birthResidueScale G (birthDyadicShellScale ε n) (birthDyadicElapsedScale ε n j))
      let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
      let width := birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)
      let R := originalNormalizedClockMobility S w T ref width
      IsUnit T.det∧ref-S.level∈Ioo D.lo D.hi∧
      (∀r∈Icc (0:ℝ) 1,ref+width*r-S.level∈Ioo D.lo D.hi)∧
      R 0=0∧(∀r∈Icc (0:ℝ) 1,‖R r‖≤cap*Bmob)∧
      (∀r∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,‖R r-R v‖≤(cap*Bmob)*|r-v|)∧
      (∀r∈Icc (0:ℝ) 1,‖R r‖*(L:ℝ)≤(1/2:ℝ))∧
      ∀(e : LegalMarkedPhysicalEdge q) clock,
        D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
          ((physicalPairAnchor e).2,clock)≠0→
        e∈D.normalizedMomentumPhaseEligibleEdges T (ref-S.level) (lower/128)∧
        ((16*upper)•1-T*D.sourcePhaseLeg (ref-S.level) e.1.2*Tᵀ).PosSemidef∧
        ∃r∈Icc (0:ℝ) 1,clock=ref+width*r := by
  obtain ⟨Bmob,hBmob,hmob⟩ := D.original_left_birth_mobility_bound_of_comparison
    hF hw hG hgeospan hupper.le (fun r hr ↦(hcomp r hr).2)
  refine ⟨Bmob,hBmob,?_⟩
  intro ε hε hεgeo hεgap L basecap hbasecap
  let cap := commonPhysicalNormalizedWindowFraction basecap Bmob (L:ℝ)
  have hcap : 0<cap :=
    (commonPhysicalNormalizedWindowFraction_spec hbasecap hBmob L.coe_nonneg).1
  dsimp only
  intro n j i ell hi hell
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  have ht : 0<t := birthDyadicShellScale_pos hε n
  have hs : 0<s := (birthDyadicClockBand_base_bounds hε n j i hi).1
  have htε : 2*t≤ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hscale : 8*t<geoε := by nlinarith
  have hm := D.originalLeftBirthPhysicalWindow_mobility_bounds_of_band_bound
    hF hw hε hcap hgeospan hBmob n j i ell hi hell (by linarith)
    (G:=G) (fun r hr ↦hmob ht hs (by linarith) hr)
  have hT := (positiveMatrixNormalizer_spec (birthResidueScale_posDef (t:=t) hG hs)).1
  have hc := commonPhysicalNormalizedWindowFraction_contractive hbasecap hBmob L.coe_nonneg hm.2.2.2.1
  refine ⟨hT,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2,hc,?_⟩
  intro e clock hf
  have hmask := D.originalSupportedLeftBirthPhysicalClockWeight_mask_ne_zero
    ε cap n j i ell _ hf
  exact ⟨(D.originalSupportedLeftBirthPhysicalClockMask_eligible_of_comparison hF hw hG
    hε hcap hbounds hεgap hgeospan hlower.le hupper.le hcomp n j i ell hscale hell e clock hmask).2.2,
    D.originalSupportedLeftBirthPhysicalClockMask_shortLeg_upper_of_comparison hF hw hG
      hε hcap hbounds hεgap hgeospan hlower.le hupper.le hcomp n j i ell hscale hell e clock hmask,
    D.originalSupportedLeftBirthPhysicalClockWeight_clock_witness hε hcap n j i ell _ hf⟩


/-- A SAME-residue comparison gives actual right birth windows for EVERY
sufficiently small collar. All geometric proofs are consumed from the original
of-comparison APIs, so later common-collar selection does not reselect G. -/
theorem exists_original_right_shrinkable_birthWindows_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {geoε lower upper : ℝ} (_hgeoε : 0<geoε) (hgeospan : geoε<D.hi-D.lo)
    (hlower : 0<lower) (hupper : 0<upper)
    (hcomp : ∀r∈Ioo 0 geoε,
      (originalSeedKernel S w (D.hi-r)-lower•((r^2)⁻¹•G+1)).PosSemidef∧
      (upper•((r^2)⁻¹•G+1)-originalSeedKernel S w (D.hi-r)).PosSemidef) :
    ∃ Bmob : ℝ,0≤Bmob∧∀{ε : ℝ},0<ε→8*ε<geoε→8*ε≤gap→
      ∀(L : ℝ≥0)(basecap : ℝ),0<basecap→
      let cap := commonPhysicalNormalizedWindowFraction basecap Bmob (L:ℝ)
      ∀n j i ell : ℕ,i<dyadicBirthBandCount j→ell<birthPhysicalClockWindowCount cap→
      let T := positiveMatrixNormalizer
        (birthResidueScale G (birthDyadicShellScale ε n) (birthDyadicElapsedScale ε n j))
      let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
      let width := birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)
      let R := originalNormalizedClockMobility S w T ref (-width)
      IsUnit T.det∧ref-S.level∈Ioo D.lo D.hi∧
      (∀r∈Icc (0:ℝ) 1,ref+(-width)*r-S.level∈Ioo D.lo D.hi)∧
      R 0=0∧(∀r∈Icc (0:ℝ) 1,‖R r‖≤cap*Bmob)∧
      (∀r∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,‖R r-R v‖≤(cap*Bmob)*|r-v|)∧
      (∀r∈Icc (0:ℝ) 1,‖R r‖*(L:ℝ)≤(1/2:ℝ))∧
      ∀(e : LegalMarkedPhysicalEdge q) clock,
        D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell
          ((physicalPairAnchor e).2,clock)≠0→
        e∈D.normalizedMomentumPhaseEligibleEdges T (ref-S.level) (lower/128)∧
        ((16*upper)•1-T*D.targetPhaseLeg (ref-S.level) e.2.2*Tᵀ).PosSemidef∧
        ∃r∈Icc (0:ℝ) 1,clock=ref+(-width)*r := by
  obtain ⟨Bmob,hBmob,hmob⟩ := D.original_right_birth_mobility_bound_of_comparison
    hF hw hG hgeospan hupper.le (fun r hr ↦(hcomp r hr).2)
  refine ⟨Bmob,hBmob,?_⟩
  intro ε hε hεgeo hεgap L basecap hbasecap
  let cap := commonPhysicalNormalizedWindowFraction basecap Bmob (L:ℝ)
  have hcap : 0<cap :=
    (commonPhysicalNormalizedWindowFraction_spec hbasecap hBmob L.coe_nonneg).1
  dsimp only
  intro n j i ell hi hell
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  have ht : 0<t := birthDyadicShellScale_pos hε n
  have hs : 0<s := (birthDyadicClockBand_base_bounds hε n j i hi).1
  have htε : 2*t≤ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hscale : 8*t<geoε := by nlinarith
  have hm := D.originalRightBirthPhysicalWindow_mobility_bounds_of_band_bound
    hF hw hε hcap hgeospan hBmob n j i ell hi hell (by linarith)
    (G:=G) (fun r hr ↦hmob ht hs (by linarith) hr)
  have hT := (positiveMatrixNormalizer_spec (birthResidueScale_posDef (t:=t) hG hs)).1
  have hc := commonPhysicalNormalizedWindowFraction_contractive hbasecap hBmob L.coe_nonneg hm.2.2.2.1
  refine ⟨hT,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2,hc,?_⟩
  intro e clock hf
  have hmask := D.originalSupportedRightBirthPhysicalClockWeight_mask_ne_zero
    ε cap n j i ell _ hf
  exact ⟨(D.originalSupportedRightBirthPhysicalClockMask_eligible_of_comparison hF hw hG
    hε hcap hbounds hεgap hgeospan hlower.le hupper.le hcomp n j i ell hscale hell e clock hmask).2.2,
    D.originalSupportedRightBirthPhysicalClockMask_shortLeg_upper_of_comparison hF hw hG
      hε hcap hbounds hεgap hgeospan hlower.le hupper.le hcomp n j i ell hscale hell e clock hmask,
    D.originalSupportedRightBirthPhysicalClockWeight_clock_witness hε hcap n j i ell _ hf⟩


/-- The SAME explicit original pole and density generate uniform true source
cell intensities for every later smaller collar and every interior common cut.
The determinant certificate is returned with the constant, so actual supported
contributors can consume the same short-leg bound without reselecting data. -/
theorem exists_original_left_samePole_shrinkable_commonScale_intensity
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 0<q)
    {poleRadius : ℝ} (hpoleRadius : 0<poleRadius)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ→Matrix (Fin q) (Fin q) ℝ} (hRem : ContinuousAt Rem 0)
    (hpole : ∀r∈Ioo 0 poleRadius,
      originalSeedKernel S w (D.lo+r)=(r^2)⁻¹•G+Rem r)
    {ρden : M→ℝ} {v : M→E→ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρden) (hρ0 : ∀x,0≤ρden x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦x-S.level)) ρden v c.toReal)
    (U₀ : ℝ) :
    ∃ ε₀ Ddet : ℝ,0<ε₀∧ε₀≤1∧0<Ddet∧
      (∀A : Matrix (Fin q) (Fin q) ℝ,
        A.PosSemidef→(U₀•1-A).PosSemidef→(1+A).det≤Ddet)∧
      ∀Rcell : ℝ,∃Λ : ℝ,0<Λ∧∀{ε : ℝ},0<ε→ε<ε₀→
      ∀n j i : ℕ,i<dyadicBirthBandCount j→
      let t := birthDyadicShellScale ε n
      let s := birthDyadicElapsedScale ε n j
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      let δ := birthTrafficCoarseScale q t s
      ∀cut∈Ioo D.lo D.hi,∀z₀ p₀,
      ((volume : Measure (Fin q→ℝ)).prod μ)
        (D.commonScaleOriginalSourcePhaseCell T cut δ
          (D.originalBirthSourceDetCarrier T cut
            (D.originalLeftBirthNarrowClockBand ε n j i) Ddet) z₀ p₀ Rcell)≤
        ENNReal.ofReal (Λ*(s/t)) := by
  obtain ⟨εmass,Cmass,hεmass,_hεspan,hCmass,hmass⟩ :=
    D.exists_original_left_birth_narrowBand_mass_bound hF hw c hρ hρ0 hv hv0 hdensity
      hpoleRadius hRem hpole
  obtain ⟨Ddet,hDdet,hdet⟩ :=
    exists_det_bound_of_posSemidef_scalar_upper (ι:=Fin q) U₀
  let ε₀ := min εmass 1
  refine ⟨ε₀,Ddet,lt_min hεmass zero_lt_one,min_le_right _ _,hDdet,hdet,?_⟩
  intro Rcell
  obtain ⟨Ccell,hCcell,hcell⟩ :=
    D.exists_commonScaleOriginalSourcePhaseCell_birth_intensity hF hw hG hq Rcell
  let Λ := Ccell*Ddet*Cmass
  refine ⟨Λ,by dsimp only [Λ]; positivity,?_⟩
  intro ε hε hεsmall n j i hi
  dsimp only
  intro cut hcut z₀ p₀
  have hεmasslt : ε<εmass := hεsmall.trans_le (min_le_left _ _)
  have hεone : ε≤1 := hεsmall.le.trans (min_le_right _ _)
  have ht : 0<birthDyadicShellScale ε n := birthDyadicShellScale_pos hε n
  have hs : 0<birthDyadicElapsedScale ε n j := (birthDyadicClockBand_base_bounds hε n j i hi).1
  have htε : 2*birthDyadicShellScale ε n≤ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have htone : birthDyadicShellScale ε n≤1 := by linarith
  exact hcell ht htone hs hDdet.le hCmass.le hcut
    (D.measurableSet_originalLeftBirthNarrowClockBand ε n j i)
    (hmass hε hεmasslt n j i hi) z₀ p₀


/-- The same original pole gives bounded-phase source confinement and exact
original-input count domination for EVERY smaller collar. This stronger
quantifier permits actual left/right, density and energy collars to be unified. -/
theorem exists_original_left_shrinkable_birth_bounded_contributors_sameResidue
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ P.value τ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞} (hηmeas : Measurable η)
    {physicalRadius basecap : ℝ} (hphysicalRadius : 0 ≤ physicalRadius)
    (hbasecap : 0 < basecap) (hηsupport : ∀ x, η x ≠ 0 → ‖x‖ ≤ physicalRadius) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∃ h : ℝ, 0 < h ∧ ∃ cap : ℝ, 0 < cap ∧ cap ≤ basecap ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ H : ℝ, 0 ≤ H →
      ∃ radius : ℝ, 0 ≤ radius ∧ ∀ {ε : ℝ}, 0 < ε → ε < ε₀ →
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      ∀ n j i ell : ℕ, i < dyadicBirthBandCount j → ell < birthPhysicalClockWindowCount cap →
      let t := birthDyadicShellScale ε n
      let s := birthDyadicElapsedScale ε n j
      let δ := birthTrafficCoarseScale (finrank ℝ S.covector.ker) t s
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      let cut := D.originalLeftBirthPhysicalClockReference ε cap n j i ell - S.level
      let width := birthPhysicalClockWindowWidth cap s
      let R := originalNormalizedClockMobility S w T (cut + S.level) width
      let f := D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
      let V := occupiedPairTrafficContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f
      let W := birthTrafficSpatialWindow G t s radius
      let J := D.originalLeftBirthNarrowClockBand ε n j i
      IsUnit T.det ∧ cut ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0 : ℝ) 1, cut + width * r ∈ Ioo D.lo D.hi) ∧
        R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ ρ) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ‖R r - R v‖ ≤ ρ * |r - v|) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) ∧
        (∀ e clock, f ((physicalPairAnchor e).2, clock) ≠ 0 →
          e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h) ∧
      ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ →
        (∀ a ∈ V scene, a.1 ∈ W ∧ a.2.1.1 ∈ J) ∧
          physicalScenePairKernel scene.1 (V scene) ≤
            (scene.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
              ((W ×ˢ J) ×ˢ {(0 : Fin 2)}) := by
  let ηsmall := min poleη 1
  have hηsmall : 0 < ηsmall := lt_min hη zero_lt_one
  have hηsmallη : ηsmall ≤ poleη := min_le_left _ _
  have hRemSmall : ContinuousOn Rem (Ioo (-ηsmall) ηsmall) :=
    hRem.mono (fun r hr ↦ ⟨lt_of_le_of_lt (neg_le_neg hηsmallη) hr.1,
      lt_of_lt_of_le hr.2 hηsmallη⟩)
  obtain ⟨geoε,hgeoε,_hgeoη,hgeospan,lower,upper,hlower,hupper,hcomp⟩ :=
    D.exists_original_left_birth_comparison_sameResidue hF hw hηsmall
      (hηsmallη.trans_lt hηspan) hG hRemSmall
      (fun r hr ↦hpole r ⟨hr.1,hr.2.trans_le hηsmallη⟩)
  obtain ⟨B,hB,hwindows⟩ := D.exists_original_left_shrinkable_birthWindows_of_comparison
    hF hw hbounds hG hgeoε hgeospan hlower hupper hcomp
  let ε₀ := min (geoε/16) (min (gap/16) 1)
  have hε₀ : 0<ε₀ := lt_min (by positivity) (lt_min (by positivity) zero_lt_one)
  have hε₀one : ε₀≤1 := (min_le_right _ _).trans (min_le_right _ _)
  have hε₀geo : ε₀≤geoε/16 := min_le_left _ _
  have hε₀gap : ε₀≤gap/16 := (min_le_right _ _).trans (min_le_left _ _)
  let h := lower/128
  have hh : 0<h := by dsimp only [h]; positivity
  let U := 16*upper
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
  refine ⟨ε₀,hε₀,hε₀one,h,hh,cap,hcap,commonPhysicalNormalizedWindowFraction_le_cap _ _ _,ρ,hρ,?_⟩
  intro H hH
  let radius := A + (ρ + C) * (2 * H + 2 * ((L : ℝ) * A + b))
  have hradius : 0 ≤ radius := by dsimp [radius, b]; positivity
  refine ⟨radius, hradius, ?_⟩
  intro ε hε hεsmall
  have hεone : ε≤1 := hεsmall.le.trans hε₀one
  have hεgeo8 : 8*ε<geoε := by linarith
  have hεgap8 : 8*ε≤gap := by linarith
  dsimp only
  intro n j i ell hi hell
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let δ := birthTrafficCoarseScale (finrank ℝ S.covector.ker) t s
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
  let cut := ref - S.level
  let width := birthPhysicalClockWindowWidth cap s
  let f := D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
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
  rcases hwindows hε hεgeo8 hεgap8 L basecap hbasecap n j i ell hi hell with
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
  have hsource : ∀ e ∈ occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker)
      d η f scene, e.1 ∈ birthTrafficSpatialWindow G t s radius ×ˢ
        D.originalLeftBirthNarrowClockBand ε n j i := by
    intro e he
    obtain ⟨clock, _, hfc⟩ := legalMarkedCompletePathEdgeTraffic_ne_zero_exists_clock d η f e he.2
    have hnode := hnodes hamp e he
    have hleg := hCbound _ (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut e.1.2)
      (helig e clock hfc).2.1
    have hendpoint := D.normalizedMomentumNode_source_norm_le T e hnode.1 hC
      hnode.2.2.2.1 hnode.2.2.1 hleg
    have hscaled : ‖T *ᵥ e.1.1‖ ≤ δ * radius := by
      calc
        _ ≤ (A * δ + ρ * (2 * (H * δ) + 2 * ((L : ℝ) * (A * δ) + b))) +
            C * (2 * (H * δ) + 2 * ((L : ℝ) * (A * δ) + b)) := hendpoint
        _ = A * δ + (ρ + C) * (2 * (H * δ) + 2 * ((L : ℝ) * (A * δ) + b)) := by ring
        _ ≤ δ * radius := bounded_phase_endpoint_radius_le_coarseScale hδ (Real.sqrt_nonneg _) hρ hC
    refine ⟨mem_birthTrafficSpatialWindow_of_normalized_norm hG ht hs e.1.1
      (by simpa only [Fintype.card_fin] using hscaled), ?_⟩
    simpa only [physicalPairAnchor] using
      D.originalSupportedLeftBirthPhysicalClockWeight_source_mem_band ε cap n j i ell _ hfc
  refine ⟨?_, ?_⟩
  · intro a ha
    have h := hsource ((physicalPairAnchorHomeomorph _).symm a) ha
    exact ⟨h.1, h.2⟩
  · exact occupiedPairTrafficContributors_source_count_le d
      (measurable_originalSeedPathOffset_joint S hF hw) hηmeas
      (D.measurable_originalSupportedLeftBirthPhysicalClockWeight hF hw ε cap n j i ell)
      scene hfull ((isCompact_birthTrafficSpatialWindow G t s radius).measurableSet.prod
        (D.measurableSet_originalLeftBirthNarrowClockBand ε n j i)) hsource


/-- The SAME original right pole gives confinement for every smaller collar.
Every bounded canonical right-birth phase has one fixed-radius physical
target window at every actual dyadic scale. The same occupied contributors
retain their original narrow clock band and original target-count domination. -/
theorem exists_original_right_shrinkable_birth_bounded_contributors_sameResidue
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
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∃ h : ℝ, 0 < h ∧ ∃ cap : ℝ, 0 < cap ∧ cap ≤ basecap ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ H : ℝ, 0 ≤ H →
      ∃ radius : ℝ, 0 ≤ radius ∧ ∀ {ε : ℝ}, 0 < ε → ε < ε₀ →
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
  obtain ⟨geoε,hgeoε,_hgeoη,hgeospan,lower,upper,hlower,hupper,hcomp⟩ :=
    D.exists_original_right_birth_comparison_sameResidue hF hw hηsmall
      (hηsmallη.trans_lt hηspan) hG hRemSmall
      (fun r hr ↦hpole r ⟨hr.1,hr.2.trans_le hηsmallη⟩)
  obtain ⟨B,hB,hwindows⟩ := D.exists_original_right_shrinkable_birthWindows_of_comparison
    hF hw hbounds hG hgeoε hgeospan hlower hupper hcomp
  let ε₀ := min (geoε/16) (min (gap/16) 1)
  have hε₀ : 0<ε₀ := lt_min (by positivity) (lt_min (by positivity) zero_lt_one)
  have hε₀one : ε₀≤1 := (min_le_right _ _).trans (min_le_right _ _)
  have hε₀geo : ε₀≤geoε/16 := min_le_left _ _
  have hε₀gap : ε₀≤gap/16 := (min_le_right _ _).trans (min_le_left _ _)
  let h := lower/128
  have hh : 0<h := by dsimp only [h]; positivity
  let U := 16*upper
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
  refine ⟨ε₀,hε₀,hε₀one,h,hh,cap,hcap,commonPhysicalNormalizedWindowFraction_le_cap _ _ _,ρ,hρ,?_⟩
  intro H hH
  let radius := A + (ρ + C) * (2 * H + 2 * ((L : ℝ) * A + b))
  have hradius : 0 ≤ radius := by dsimp [radius, b]; positivity
  refine ⟨radius, hradius, ?_⟩
  intro ε hε hεsmall
  have hεone : ε≤1 := hεsmall.le.trans hε₀one
  have hεgeo8 : 8*ε<geoε := by linarith
  have hεgap8 : 8*ε≤gap := by linarith
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
  rcases hwindows hε hεgeo8 hεgap8 L basecap hbasecap n j i ell hi hell with
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


/-- The physical bounded-birth window and the literal original narrow clock
band have uniformly bounded original Poisson intensity. The rank Jacobian and
original clock-density power cancel to the TRUE elapsed/inward ratio `s/t`. -/
theorem exists_original_left_bounded_birthWindow_intensity
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {ρ : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) ρ v c.toReal)
    {poleη : ℝ} (hη : 0 < poleη)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ} (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo+r)=(r ^ 2)⁻¹ • G+Rem r)
    (radius : ℝ) :
    ∃ ε₀ Λ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < Λ ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ε₀ → ∀ n j i : ℕ, i < dyadicBirthBandCount j →
      let t := birthDyadicShellScale ε n
      let s := birthDyadicElapsedScale ε n j
      let W := birthTrafficSpatialWindow G t s radius ×ˢ D.originalLeftBirthNarrowClockBand ε n j i
      ((volume : Measure (Fin q → ℝ)).prod μ) W ≤ ENNReal.ofReal (Λ*(s/t)) ∧
        ((volume : Measure (Fin q → ℝ)).prod μ) W ≤ ENNReal.ofReal Λ := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  obtain ⟨εm,Cm,hεm,_hspan,hCm,hmass⟩ :=
    D.exists_original_left_birth_narrowBand_mass_bound hF hw c hρ hρ0 hv hv0 hdensity hη hRem hpole
  obtain ⟨Cv,hCv,hvol⟩ := exists_birthTrafficSpatialWindow_volume_bound hG
    (by simpa only [Fintype.card_fin] using hq) radius
  refine ⟨min εm 1,Cv*Cm,lt_min hεm zero_lt_one,min_le_right _ _,mul_pos hCv hCm,?_⟩
  intro ε hε hεsmall n j i hi
  dsimp only
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hb := birthDyadicClockBand_base_bounds hε n j i hi
  have hs : 0 < s := hb.1
  have hst : s ≤ t := hb.2.1
  have ht1 : t ≤ 1 := by
    have hε1 : ε ≤ 1 := hεsmall.le.trans (min_le_right _ _)
    have htε : 2*t ≤ ε := by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    linarith
  have hmass := hmass hε (hεsmall.trans_le (min_le_left _ _)) n j i hi
  have hbound : ((volume : Measure (Fin q → ℝ)).prod μ)
      (birthTrafficSpatialWindow G t s radius ×ˢ D.originalLeftBirthNarrowClockBand ε n j i) ≤
      ENNReal.ofReal ((Cv*(t^(G.rank+1))⁻¹)*(Cm*t^G.rank*s)) := by
    rw [Measure.prod_prod]
    exact (mul_le_mul' (hvol ht ht1 hs) hmass).trans_eq
      (ENNReal.ofReal_mul (by positivity)).symm
  have hid : (Cv*(t^(G.rank+1))⁻¹)*(Cm*t^G.rank*s)=Cv*Cm*(s/t) := by
    rw [pow_succ]
    field_simp
  rw [hid] at hbound
  exact ⟨hbound,hbound.trans (ENNReal.ofReal_le_ofReal
    (mul_le_of_le_one_right (mul_nonneg hCv.le hCm.le) ((div_le_one ht).mpr hst)))⟩


/-- The literal actual left birth subdivision has the SAME uniform physical
one-edge constant on all inward and elapsed scales. The original endpoint
geometry supplies the constant before any input count or selected edge occurs. -/
theorem exists_original_left_birthWindow_single_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ ε₀ σ : ℝ, 0 < ε₀ ∧ 0 < σ ∧ ∀ {ε cap : ℝ},
      0 < ε → ε < ε₀ → 0 < cap → cap ≤ σ →
      ∀ (n j i ell : ℕ), i < dyadicBirthBandCount j → ell < birthPhysicalClockWindowCount cap →
      ∀ {R₀ M₀ : ℝ}, 0 ≤ R₀ → 0 ≤ M₀ →
      ∀ {η : (Fin q → ℝ) → ℝ}, (∀ x, 0 ≤ η x) → (∀ x, η x ≤ M₀) →
        (∀ x, R₀ < ‖x‖ → η x = 0) →
      ∀ (x : Fin q → ℝ) (m : PhysicalPairPalmMark (Fin q)),
        (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
          D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell (m,c)) ≤
          ENNReal.ofReal (4*M₀*(R₀+1)) := by
  obtain ⟨δ,hδ,_hδspan,σ,hσ,_hσhalf,hterminal⟩ :=
    D.exists_original_left_focal_maskedCompletePathEdgeTraffic hF hw
  refine ⟨δ/4,σ,by positivity,hσ,?_⟩
  intro ε cap hε hεδ hcap hcapσ n j i ell hi hell R₀ M₀ hR₀ hM₀ η hη0 hηM hηR x m
  let mask := D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell
  by_cases hz : ∀ c, mask (m,c)=0
  · simp only [originalSupportedLeftBirthPhysicalClockWeight,←show mask=
        D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell from rfl,
        hz,mul_zero,lintegral_zero]
    exact bot_le
  push Not at hz
  obtain ⟨c,hc⟩ := hz
  let e := (physicalPairAnchorHomeomorph q).symm (x,m)
  have he : physicalPairAnchor e=(x,m) := (physicalPairAnchorHomeomorph q).apply_symm_apply (x,m)
  have hclock : e.1.2-S.level∈Ioo D.lo D.hi := by
    have hm := D.originalSupportedLeftBirthPhysicalClockMask_support ε cap n j i ell (m,c) hc
    change (physicalPairAnchor e).2.1.1-S.level∈Ioo D.lo D.hi
    rw [he]
    exact ⟨by linarith [hm.2.2.1],by linarith [hm.2.2.2.1,hm.2.2.2.2.1,hm.2.2.2.2.2]⟩
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
  let width := birthPhysicalClockWindowWidth cap s
  let a := ref-S.level-D.lo
  have ht : 0<t := birthDyadicShellScale_pos hε n
  have hb := birthDyadicClockBand_base_bounds hε n j i hi
  have hs : 0<s := hb.1
  have hwidth := birthPhysicalClockWindow_spec hcap hs
  have ha := D.originalLeftBirthPhysicalClockWindow_inward_bounds hε hcap n j i ell hi hell
    (show ref∈Icc ref (ref+width) from ⟨le_rfl,by linarith [hwidth.2.1]⟩)
  have htε : 2*t≤ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have haI : a∈Ioo (0:ℝ) δ := ⟨ht.trans_le ha.1,by dsimp only [a]; linarith [ha.2]⟩
  have hband : ∀ c∈Icc ref (ref+width),|c-S.level-D.lo-a|≤σ*a := by
    intro c hc
    rw [abs_of_nonneg (by dsimp only [a]; linarith [hc.1])]
    have hcs : width≤cap*s := hwidth.2.2.1
    have hst : s≤t := hb.2.1
    have hsA : s≤a := hst.trans ha.1
    calc
      _ ≤ width := by dsimp only [a]; linarith [hc.2]
      _ ≤ cap*s := hcs
      _ ≤ σ*a := mul_le_mul hcapσ hsA hs.le hσ.le
  have hz : ∀ c∉Icc ref (ref+width),mask ((physicalPairAnchor e).2,c)=0 := by
    intro c hc
    by_contra hn
    have hh := (D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff
      ε cap n j i ell ((physicalPairAnchor e).2,c)).mp hn
    have hh := D.originalLeftBirthPhysicalClockMask_clock_mem ε cap n j i ell _ hh.2.2
    exact hc ⟨hh.1.le,hh.2⟩
  have hedge := (hterminal a haI ref (ref+width) (by linarith [hwidth.2.1]) hband e hclock
    R₀ M₀ hR₀ hM₀ η hη0 hηM hηR mask
    (fun c _ ↦D.originalSupportedLeftBirthPhysicalClockMask_le_one ε cap n j i ell _) hz).1
  have hb : originalMaskedCompletePathEdgeTraffic S w η mask e≤ENNReal.ofReal (4*M₀*(R₀+1)) :=
    hedge.trans (ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right (by positivity) (min_le_left _ _)))
  change legalMarkedCompletePathEdgeTraffic q _ _ _ e≤_ at hb
  simpa only [legalMarkedCompletePathEdgeTraffic,he,Prod.fst,Prod.snd,
    originalSupportedLeftBirthPhysicalClockWeight,mask] using hb
/-- One same geometric h/cap choice retains the mobility and eligible-edge
certificates together with both actual small-phase moment estimates and the
original count-tail norm. The mobility certificate can therefore be consumed
by the large branch without a second existential choice. -/
theorem exists_original_left_bounded_birth_geometric_goodBad_smallMoments
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
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
      let cut := D.originalLeftBirthPhysicalClockReference ε cap n j i ell - S.level
      let L : ℝ≥0 := ⟨Real.sqrt ((q : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let J := D.originalLeftBirthNarrowClockBand ε n j i
      let B := {m : PhysicalPairPalmMark (Fin q) | m.1.1 ∈ J}
      let W := birthTrafficSpatialWindow G t s radius
      let Good := {scene : LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ ∧
          (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {0}) ≤ ENNReal.ofReal K}
      let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
        (legalMarkedCompletePathTraffic q (fun z ↦ originalSeedPathOffset S w z.2 z.1)
          (fun x ↦ ENNReal.ofReal (η x)) (D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell) scene).toReal
      let firstBudget :=
        (4*M₀*(physicalRadius+1)*K*
          (∫⁻ x, ENNReal.ofReal (η x) ∂(volume : Measure (Fin q → ℝ))).toReal *cap*C₁) *
          s ^ (3/2 : ℝ) *
          (t ^ (((G.rank : ℝ)-3)/2) * Real.sqrt
            (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
              ∂legalMarkedJointPalm q Q.law).toReal +
            t ^ ((G.rank : ℝ)/2) * Real.sqrt
              (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
                ∂legalMarkedJointPalm q Q.law).toReal)
      let secondBudget := (K*(M₀*cap)^2*C₂)*s^2 *
        (t ^ (-(G.rank : ℝ)-4)*
          (∫⁻ m in B,ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
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
        ENNReal.ofReal K < (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {0})}
      MemLp (Bad.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      eLpNorm (Bad.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≤
          ENNReal.ofReal (Btail * Real.exp (-K / 4)) ∧
      let width:=birthPhysicalClockWindowWidth cap s
      let R:=originalNormalizedClockMobility S w T (cut+S.level) width
      IsUnit T.det ∧ cut∈Ioo D.lo D.hi ∧
        (∀r∈Icc (0:ℝ) 1,cut+width*r∈Ioo D.lo D.hi) ∧ R 0=0 ∧
        (∀r∈Icc (0:ℝ) 1,‖R r‖≤ρ) ∧
        (∀r∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,‖R r-R v‖≤ρ*|r-v|) ∧
        (∀r∈Icc (0:ℝ) 1,‖R r‖*(L:ℝ)≤(1/2:ℝ)) ∧
        ∀(e:LegalMarkedPhysicalEdge q) clock,
          D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
            ((physicalPairAnchor e).2,clock)≠0→
          e∈D.normalizedMomentumPhaseEligibleEdges T cut h := by
  have hηENN : Measurable (fun x ↦ ENNReal.ofReal (η x)) := hηmeas.ennreal_ofReal
  have hηsupport : ∀ x, ENNReal.ofReal (η x) ≠ 0 → ‖x‖ ≤ physicalRadius := by
    intro x hx
    by_contra hn
    exact hx (by rw [hηR x (lt_of_not_ge hn),ENNReal.ofReal_zero])
  obtain ⟨εs,σ,hεs,hσ,hsingle⟩ := D.exists_original_left_birthWindow_single_bound hF hw
  obtain ⟨εg,hεg,hεg1,h,hh,cap,hcap,hcapbase,ρ,hρ,hgeom⟩ :=
    D.exists_original_left_shrinkable_birth_bounded_contributors_sameResidue
      hF hw hbounds hgap hη hηspan hG hRem hpole hg hgb τ Q hmin
      hηENN hphysicalRadius (lt_min hbasecap hσ) hηsupport
  have hcapσ : cap ≤ σ := hcapbase.trans (min_le_right _ _)
  refine ⟨h,cap,ρ,hh,hcap,hcapbase.trans (min_le_left _ _),hρ,?_⟩
  intro H hH
  obtain ⟨radius,hradius,hgeom⟩ := hgeom H hH
  obtain ⟨εb,Cb,hεb,_hεbη,hCb,hsecond⟩ :=
    D.exists_original_left_birthBand_smallSecondMoment_bound_ae hF hw hq radius
      hη hηspan hG hRem hpole
  obtain ⟨εa,C,hεa,_hεaη,hC,hfirst⟩ :=
    D.exists_original_left_birthBand_smallFirstSquare_bound_ae hF hw
      hη hηspan hG hRem hpole
  obtain ⟨εm,Cm,hεm,_hspan,hCm,hmass⟩ := D.exists_original_left_birth_narrowBand_mass_bound
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
  let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
  let cut := ref - S.level
  let L : ℝ≥0 := ⟨Real.sqrt ((q : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let J := D.originalLeftBirthNarrowClockBand ε n j i
  let B := {m : PhysicalPairPalmMark (Fin q) | m.1.1 ∈ J}
  let W := birthTrafficSpatialWindow G t s radius
  let width := birthPhysicalClockWindowWidth cap s
  let I := Ioc ref (ref + width)
  let d := fun z : PhysicalPairPalmMark (Fin q) × ℝ ↦ originalSeedPathOffset S w z.2 z.1
  let f := D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
  let mask := D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell
  let V := occupiedPairTrafficContributors q d (fun x ↦ ENNReal.ofReal (η x)) f
  let Good := {scene : LegalMarkedOptimalInputScene q |
    ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ ∧
      (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {0}) ≤ ENNReal.ofReal K}
  have hεg' : ε < εg := hεsmall.trans_le hε₀g
  have hp := hgeom hε hεg' n j i ell hi hell
  have hcut : cut ∈ Ioo D.lo D.hi := hp.2.1
  have hJ : MeasurableSet J := D.measurableSet_originalLeftBirthNarrowClockBand ε n j i
  have hB : MeasurableSet B := hJ.preimage measurable_fst.fst
  have hW : MeasurableSet W := (isCompact_birthTrafficSpatialWindow G t s radius).measurableSet
  have hcount : Measurable (fun scene : LegalMarkedOptimalInputScene q ↦
      (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {0})) :=
    (Measure.measurable_coe ((hW.prod hJ).prod (measurableSet_singleton 0))).comp
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
    simpa only [I,Real.volume_Ioc,add_sub_cancel_left] using ENNReal.ofReal_le_ofReal hw
  have hIclock : ∀ c ∈ I, c - S.level - D.lo ∈ Icc t (4*t) := by
    intro c hc
    have hmem := D.originalLeftBirthPhysicalClockWindow_inward_bounds hε hcap
      n j i ell hi hell ⟨hc.1.le,hc.2⟩
    exact hmem
  have hBclock : ∀ m ∈ B, m.1.1 - S.level - D.lo ∈ Icc t (2*t) := by
    intro m hm
    change D.lo+t+(i:ℝ)*(s/8)<m.1.1-S.level ∧
      m.1.1-S.level≤D.lo+t+((i:ℝ)+1)*(s/8) at hm
    constructor <;> linarith [hm.1,hm.2,hb.2.2.1,hb.2.2.2]
  have hmaskzero : ∀ m c, m ∉ B ∨ c ∉ I → mask (m,c)=0 := by
    intro m c hc
    by_contra hn
    have hm := (D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff ε cap n j i ell (m,c)).mp hn
    rcases hc with hc | hc
    · exact hc (D.originalLeftBirthClockMask_source_mem_clockGridBand ε n j i (m,c)
        (D.originalSupportedLeftBirthPhysicalClockMask_birth ε cap n j i ell (m,c) hn).1)
    · exact hc (D.originalLeftBirthPhysicalClockMask_clock_mem ε cap n j i ell (m,c) hm.2.2)
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
  have hmass' : (μ.map (fun a:ℝ ↦a-S.level))
      (clockGridBand (D.lo+t) (s/8) i) ≤ ENNReal.ofReal (Cm*t^G.rank*s) := by
    have hshift : Measurable (fun a:ℝ ↦a-(S.level:ℝ)) := measurable_id.sub_const _
    rw [clockGridBand,Measure.map_apply hshift measurableSet_Ioc]
    simpa only [originalLeftBirthNarrowClockBand,clockGridBand,t,s,Set.preimage] using
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
    measurableSet_Ioc hIclock hcap.le hCm.le hvol measurableSet_Ioc
    (fun m hm ↦hm) hmass' mask
    (D.measurable_originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell)
    (D.originalSupportedLeftBirthPhysicalClockMask_le_one ε cap n j i ell)
    hmaskzero hηENN hspace hGood.compl V
    (fun scene ↦measurableSet_occupiedPairTrafficContributors d
      (measurable_originalSeedPathOffset_joint S hF hw) hηENN
      (D.measurable_originalSupportedLeftBirthPhysicalClockWeight hF hw ε cap n j i ell) scene)
    (show 0≤4*M₀*(physicalRadius+1) by positivity) hK hdata
  have hdata₂ : ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)), scene ∉ Goodᶜ →
      (∀ a ∈ V scene,a.1∈W∧a.2∈B) ∧
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
    measurableSet_Ioc hvol (fun c hc ↦⟨(by linarith [(hIclock c hc).1]),(hIclock c hc).2⟩)
    hηENN (fun x ↦ ENNReal.ofReal_le_ofReal (hηM x)) mask
    (D.measurable_originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell)
    (D.originalSupportedLeftBirthPhysicalClockMask_le_one ε cap n j i ell)
    (fun m c hc ↦hmaskzero m c (Or.inr hc)) hGood.compl hB hBclock V
    (fun scene ↦measurableSet_occupiedPairTrafficContributors d
      (measurable_originalSeedPathOffset_joint S hF hw) hηENN
      (D.measurable_originalSupportedLeftBirthPhysicalClockWeight hF hw ε cap n j i ell) scene)
    hdata₂
  have hfEq : (fun z : PhysicalPairPalmMark (Fin q) × ℝ ↦
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) =
      D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell := by
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
          (∫⁻ m in B,ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
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
    ENNReal.ofReal K < (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {0})}
  let N := fun scene : LegalMarkedOptimalInputScene q ↦
    ((scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {0})).toReal
  let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
    (legalMarkedCompletePathTraffic q d (fun x ↦ ENNReal.ofReal (η x)) f scene).toReal
  have hSmall : MeasurableSet Small := measurableSet_le
    (((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm) measurable_const
  have hmassRaw : μ J ≤ ENNReal.ofReal (Cm*t^G.rank*s) :=
    hmass hε (hεsmall.trans_le hε₀m) n j i hi
  have hintensity : ((volume : Measure (Fin q → ℝ)).prod μ) (W ×ˢ J) ≤
      ENNReal.ofReal (Ct*Cm) := by
    have hh := hint μ ht ht1 hs hCm.le hJ hmassRaw
    apply hh.trans
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right
      (mul_nonneg hCt.le hCm.le) ((div_le_one ht).mpr hb.2.1))
  have htail := Q.original_source_countTail_completePath_ltwo_ae_on d
    (measurable_originalSeedPathOffset_joint S hF hw) hηENN
    (D.measurable_originalSupportedLeftBirthPhysicalClockWeight hF hw ε cap n j i ell)
    (hW.prod hJ) (mul_nonneg hCt.le hCm.le) hintensity hSmall V
    (fun scene ↦ measurableSet_occupiedPairTrafficContributors d
      (measurable_originalSeedPathOffset_joint S hF hw) hηENN
      (D.measurable_originalSupportedLeftBirthPhysicalClockWeight hF hw ε cap n j i ell) scene)
    (K:=K) (show 0≤4*M₀*(physicalRadius+1) by positivity) (by
      filter_upwards [hp.2.2.2.2.2.2.2.2] with scene hscene
      intro hsSmall _
      exact ⟨ae_occupiedPairTrafficContributors_outside_zero d
        (fun x ↦ ENNReal.ofReal (η x)) f scene,
        ae_of_all _ (fun a ↦ hsingle' a.1 a.2), (hscene hsSmall).2⟩)
  have hNfinite := (Q.original_source_exp_moment_of_finite_intensity
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




/-- The same original geometric choice gives both actual count-good
energy estimates and the count-bad exponential norm bound, on the same Q. -/
theorem exists_original_left_bounded_birth_goodBad_smallMoments
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
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
      let cut := D.originalLeftBirthPhysicalClockReference ε cap n j i ell - S.level
      let L : ℝ≥0 := ⟨Real.sqrt ((q : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let J := D.originalLeftBirthNarrowClockBand ε n j i
      let B := {m : PhysicalPairPalmMark (Fin q) | m.1.1 ∈ J}
      let W := birthTrafficSpatialWindow G t s radius
      let Good := {scene : LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ ∧
          (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {0}) ≤ ENNReal.ofReal K}
      let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
        (legalMarkedCompletePathTraffic q (fun z ↦ originalSeedPathOffset S w z.2 z.1)
          (fun x ↦ ENNReal.ofReal (η x)) (D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell) scene).toReal
      let firstBudget :=
        (4*M₀*(physicalRadius+1)*K*
          (∫⁻ x, ENNReal.ofReal (η x) ∂(volume : Measure (Fin q → ℝ))).toReal *cap*C₁) *
          s ^ (3/2 : ℝ) *
          (t ^ (((G.rank : ℝ)-3)/2) * Real.sqrt
            (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
              ∂legalMarkedJointPalm q Q.law).toReal +
            t ^ ((G.rank : ℝ)/2) * Real.sqrt
              (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
                ∂legalMarkedJointPalm q Q.law).toReal)
      let secondBudget := (K*(M₀*cap)^2*C₂)*s^2 *
        (t ^ (-(G.rank : ℝ)-4)*
          (∫⁻ m in B,ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
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
        ENNReal.ofReal K < (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {0})}
      MemLp (Bad.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      eLpNorm (Bad.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≤
          ENNReal.ofReal (Btail * Real.exp (-K / 4)) := by
  obtain ⟨h,cap,ρ,hh,hcap,hcapbase,hρ,hall⟩ :=
    D.exists_original_left_bounded_birth_geometric_goodBad_smallMoments hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨h,cap,hh,hcap,hcapbase,?_⟩
  intro H hH
  obtain ⟨ε₀,radius,C₁,C₂,Btail,hε₀,hε₀1,hradius,hC₁,hC₂,hBtail,hall⟩ := hall H hH
  refine ⟨ε₀,radius,C₁,C₂,Btail,hε₀,hε₀1,hradius,hC₁,hC₂,hBtail,?_⟩
  intro ε hε hεsmall n j i ell hi hell K hK
  have hh:=hall hε hεsmall n j i ell hi hell hK
  exact ⟨hh.1,hh.2.1,hh.2.2.1⟩


/-- The bounded canonical phase and the SAME original source-count good event
have both actual small-birth square estimates. The phase confinement,
occupied support and count domination are derived internally from the attained
original minimizer. One radius and one collar work at every literal scale. -/
theorem exists_original_left_bounded_birth_countGood_smallMoments
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
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
    ∃ ε₀ radius C₁ C₂ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      0 ≤ radius ∧ 0 < C₁ ∧ 0 < C₂ ∧ ∀ {ε : ℝ}, 0 < ε → ε < ε₀ →
      ∀ n j i ell : ℕ, i < dyadicBirthBandCount j → ell < birthPhysicalClockWindowCount cap →
      ∀ {K : ℝ}, 0 ≤ K →
      let t := birthDyadicShellScale ε n
      let s := birthDyadicElapsedScale ε n j
      let δ := birthTrafficCoarseScale q t s
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      let cut := D.originalLeftBirthPhysicalClockReference ε cap n j i ell - S.level
      let L : ℝ≥0 := ⟨Real.sqrt ((q : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let J := D.originalLeftBirthNarrowClockBand ε n j i
      let B := {m : PhysicalPairPalmMark (Fin q) | m.1.1 ∈ J}
      let W := birthTrafficSpatialWindow G t s radius
      let Good := {scene : LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T cut h L scene 0‖ ≤ H * δ ∧
          (scene.2 : Measure (LegalColoredInputPoint q)) ((W ×ˢ J) ×ˢ {0}) ≤ ENNReal.ofReal K}
      let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
        (legalMarkedCompletePathTraffic q (fun z ↦ originalSeedPathOffset S w z.2 z.1)
          (fun x ↦ ENNReal.ofReal (η x)) (D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell) scene).toReal
      let firstBudget :=
        (4*M₀*(physicalRadius+1)*K*
          (∫⁻ x, ENNReal.ofReal (η x) ∂(volume : Measure (Fin q → ℝ))).toReal *cap*C₁) *
          s ^ (3/2 : ℝ) *
          (t ^ (((G.rank : ℝ)-3)/2) * Real.sqrt
            (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
              ∂legalMarkedJointPalm q Q.law).toReal +
            t ^ ((G.rank : ℝ)/2) * Real.sqrt
              (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
                ∂legalMarkedJointPalm q Q.law).toReal)
      let secondBudget := (K*(M₀*cap)^2*C₂)*s^2 *
        (t ^ (-(G.rank : ℝ)-4)*
          (∫⁻ m in B,ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
            ∂legalMarkedJointPalm q Q.law).toReal +
          t ^ (-(G.rank : ℝ)-3)*
            (∫⁻ m in B,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
              ∂legalMarkedJointPalm q Q.law).toReal)
      MemLp (Good.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ scene,(Good.indicator traffic scene)^2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤ min firstBudget secondBudget ∧
      eLpNorm (Good.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt (min firstBudget secondBudget)) := by
  obtain ⟨h,cap,hh,hcap,hcapbase,hall⟩ :=
    D.exists_original_left_bounded_birth_goodBad_smallMoments hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨h,cap,hh,hcap,hcapbase,?_⟩
  intro H hH
  obtain ⟨ε₀,radius,C₁,C₂,Btail,hε₀,hε₀1,hradius,hC₁,hC₂,hBtail,hall⟩ := hall H hH
  refine ⟨ε₀,radius,C₁,C₂,hε₀,hε₀1,hradius,hC₁,hC₂,?_⟩
  intro ε hε hεsmall n j i ell hi hell K hK
  exact (hall hε hεsmall n j i ell hi hell hK).1


/-- The literal physical narrow source bands carry ONE genuine original Palm
energy budget at every shell and elapsed level. The true clock translation is
proved exactly; the selected cloud receives no new distribution. -/
theorem exists_original_left_narrowBirthBands_energy_budget
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi-D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r∈Ioo 0 poleη, originalSeedKernel S w (D.lo+r)=(r ^ 2)⁻¹ • G+Rem r)
    {gap diameter : ℝ} (hgap : 0<gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g) :
    ∃ E₀ : ℝ, 1≤E₀ ∧ ∀ {ε : ℝ},0<ε→∀ n j N : ℕ,
      let B := fun i ↦{m : PhysicalPairPalmMark (Fin q) |
        m.1.1∈D.originalLeftBirthNarrowClockBand ε n j i}
      (∀ i : ℕ,
        (∫⁻ m in B i,ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
          ∂legalMarkedJointPalm q Q.law)≠(∞:ℝ≥0∞) ∧
        (∫⁻ m in B i,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
          ∂legalMarkedJointPalm q Q.law)≠(∞:ℝ≥0∞)) ∧
      (∑ i∈Finset.range N,(∫⁻ m in B i,ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
        ∂legalMarkedJointPalm q Q.law).toReal)≤E₀ ∧
      (∑ i∈Finset.range N,(∫⁻ m in B i,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
        ∂legalMarkedJointPalm q Q.law).toReal)≤E₀ := by
  obtain ⟨E₀,hE₀,hbudget⟩ := D.exists_original_left_sameResidue_clockBand_energy_budget
    hF hw hη hηspan hG hRem hpole hgap hbounds Q
  refine ⟨E₀,hE₀,?_⟩
  intro ε hε n j N
  let t:=birthDyadicShellScale ε n
  let s:=birthDyadicElapsedScale ε n j
  have hs : 0<s := div_pos (birthDyadicShellScale_pos hε n) (by positivity)
  have hset : ∀ i : ℕ,{m : PhysicalPairPalmMark (Fin q) |
      m.1.1∈D.originalLeftBirthNarrowClockBand ε n j i} =
      (fun m : PhysicalPairPalmMark (Fin q) ↦m.1.1-S.level-D.lo) ⁻¹' clockGridBand t (s/8) i := by
    intro i
    ext m
    simp only [mem_ofPred_eq,originalLeftBirthNarrowClockBand,clockGridBand,
      mem_preimage,mem_Ioc]
    constructor
    · intro hm
      constructor <;> dsimp only [t,s] <;> linarith [hm.1,hm.2]
    · intro hm
      constructor <;> dsimp only [t,s] at hm <;> linarith [hm.1,hm.2]
  have hb := hbudget t (div_nonneg hs.le (by norm_num : (0:ℝ)≤8)) N
  dsimp only at hb ⊢
  simpa only [←hset] using hb


/-- Rank zero leaves no pole energy for the SAME original residue. -/
theorem original_left_poleEnergy_eq_zero_of_rank_zero
    {G : Matrix (Fin q) (Fin q) ℝ} (hGzero : G.rank=0)
    (m : PhysicalPairPalmMark (Fin q)) : originalSeedLeftPoleEnergy S w D.lo G m=0 := by
  have hlin : G.mulVecLin=0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hGzero)
  have hzero : G=0 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    change G.mulVecLin (Pi.single i 1)=(0:Matrix (Fin q) (Fin q) ℝ).mulVecLin (Pi.single i 1)
    rw [hlin,Matrix.mulVecLin_zero]
  simp only [originalSeedLeftPoleEnergy,hzero,Matrix.zero_mulVec,dotProduct_zero,zero_div]

/-- The SAME attained minimizer, original band energies and SAME count-good
birth contributions have the genuine finite-band interpolated decay. Rank zero
retains its momentum-only gain. The original energy sum budget is internal. -/
theorem exists_original_left_bounded_birth_countGood_level_norm
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
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
    ∃ ε₀ radius A : ℝ,0<ε₀∧ε₀≤1∧0≤radius∧0<A∧
      ∀ {ε:ℝ},0<ε→ε<ε₀→∀ n j ell:ℕ,ell<birthPhysicalClockWindowCount cap→∀ {K:ℝ},0≤K→
      let t:=birthDyadicShellScale ε n
      let s:=birthDyadicElapsedScale ε n j
      let δ:=birthTrafficCoarseScale q t s
      let T:=positiveMatrixNormalizer (birthResidueScale G t s)
      let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
      let W:=birthTrafficSpatialWindow G t s radius
      let J:=D.originalLeftBirthNarrowClockBand ε n j
      let cut:=fun i↦D.originalLeftBirthPhysicalClockReference ε cap n j i ell-S.level
      let Good:=fun i↦{scene:LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖≤H*δ∧
          (scene.2:Measure (LegalColoredInputPoint q)) ((W×ˢJ i)×ˢ{0})≤ENNReal.ofReal K}
      let traffic:=fun i scene↦(Good i).indicator (fun scene:LegalMarkedOptimalInputScene q↦
        (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
          (fun x↦ENNReal.ofReal (η x))
          (D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell) scene).toReal) scene
      MemLp (fun scene↦∑ i∈Finset.range (dyadicBirthBandCount j),traffic i scene)
        2 (Q.law:Measure (LegalMarkedOptimalInputScene q)) ∧
      eLpNorm (fun scene↦∑ i∈Finset.range (dyadicBirthBandCount j),traffic i scene)
        2 (Q.law:Measure (LegalMarkedOptimalInputScene q))≤
      ENNReal.ofReal ((A*Real.sqrt K*Real.sqrt E₀)*
        (t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
          (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4))))) := by
  obtain ⟨h,cap,hh,hcap,_hcapbase,hsmall⟩ :=
    D.exists_original_left_bounded_birth_countGood_smallMoments hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  obtain ⟨E₀,hE₀,henergy⟩ := D.exists_original_left_narrowBirthBands_energy_budget
    hF hw hη hηspan hG hRem hpole hgap hbounds Q
  refine ⟨h,cap,E₀,hh,hcap,hE₀,?_⟩
  intro H hH
  obtain ⟨ε₀,radius,C₁,C₂,hε₀,hε₀1,hradius,hC₁,hC₂,hsmall⟩ := hsmall H hH
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
  refine ⟨ε₀,radius,A,hε₀,hε₀1,hradius,hA,?_⟩
  intro ε hε hεsmall n j ell hell K hK
  dsimp only
  let t:=birthDyadicShellScale ε n
  let s:=birthDyadicElapsedScale ε n j
  let δ:=birthTrafficCoarseScale q t s
  let T:=positiveMatrixNormalizer (birthResidueScale G t s)
  let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let W:=birthTrafficSpatialWindow G t s radius
  let J:=D.originalLeftBirthNarrowClockBand ε n j
  let cut:=fun i↦D.originalLeftBirthPhysicalClockReference ε cap n j i ell-S.level
  let Good:=fun i↦{scene:LegalMarkedOptimalInputScene q |
    ‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖≤H*δ∧
      (scene.2:Measure (LegalColoredInputPoint q)) ((W×ˢJ i)×ˢ{0})≤ENNReal.ofReal K}
  let traffic:=fun i↦(Good i).indicator (fun scene:LegalMarkedOptimalInputScene q↦
    (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
      (fun x↦ENNReal.ofReal (η x))
      (D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell) scene).toReal)
  let B : ℕ → Set (PhysicalPairPalmMark (Fin q)) := fun i ↦ {m | m.1.1 ∈ J i}
  let e:=fun i↦(∫⁻ m in B i,ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
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
    exact (hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).1
  have hfirst : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤
      (K*C)*s^(3/2:ℝ)*(t^(((G.rank:ℝ)-3)/2)*Real.sqrt (e i)+t^((G.rank:ℝ)/2)*Real.sqrt (v i)) := by
    intro i hi
    have hr:=(hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).2.1
    have hr:=hr.trans (min_le_left _ _)
    calc
      _ ≤ (K*p₁)*s^(3/2:ℝ)*(t^(((G.rank:ℝ)-3)/2)*Real.sqrt (e i)+t^((G.rank:ℝ)/2)*Real.sqrt (v i)) := by
        convert hr using 1
        all_goals first | rfl | (dsimp only [p₁,t,s,e,v,B,J]; ring)
      _ ≤ _ := by gcongr
  have hsecond : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤
      (K*C)*s^2*(t^(-((G.rank:ℝ)+4))*e i+t^(-((G.rank:ℝ)+3))*v i) := by
    intro i hi
    have hr:=(hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).2.1
    have hr:=hr.trans (min_le_right _ _)
    calc
      _ ≤ (K*p₂)*s^2*(t^(-((G.rank:ℝ)+4))*e i+t^(-((G.rank:ℝ)+3))*v i) := by
        convert hr using 1
        all_goals first | rfl | (dsimp only [p₂,t,s,e,v,B,J]; ring)
      _ ≤ _ := by gcongr
  by_cases hrank : G.rank=0
  · have hezero : ∀ i,e i=0 := by
      intro i
      simp only [e,D.original_left_poleEnergy_eq_zero_of_rank_zero hrank,ENNReal.ofReal_zero,
        lintegral_zero,ENNReal.toReal_zero]
    have hf : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤(K*C)*s^(3/2:ℝ)*Real.sqrt (v i) := by
      simpa only [hrank,Nat.cast_zero,hezero,Real.sqrt_zero,mul_zero,zero_add,
        zero_div,Real.rpow_zero,one_mul] using hfirst
    have hs' : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤(K*C)*s^2*(t^(-3:ℝ)*v i) := by
      simpa only [hrank,Nat.cast_zero,hezero,mul_zero,zero_add] using hsecond
    have hout:=birthBand_rankZero_traffic_interpolated_level_norm P bands traffic hLp v hv
      ht ht1 hs (mul_nonneg hK hC.le) hE₀ hNs hV hf hs'
    refine ⟨hout.1,hout.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    simp only [hrank,ite_true,Real.sqrt_mul hK,t,s]
    dsimp only [A]
    nlinarith [mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤8) (3/4:ℝ))
      (mul_nonneg (Real.sqrt_nonneg K) (Real.sqrt_nonneg C)))
      (mul_nonneg (Real.sqrt_nonneg E₀) (mul_nonneg (Real.rpow_nonneg ht.le (3/8:ℝ))
        (Real.rpow_nonneg (div_nonneg hs.le ht.le) (3/28:ℝ))))]
  · have hk : 0<(G.rank:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hrank
    have hout:=birthBand_small_traffic_interpolated_level_norm P bands traffic hLp e v he hv
      ht ht1 hs (mul_nonneg hK hC.le) hE₀ hk hNs hE hV hfirst hsecond
    refine ⟨hout.1,hout.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    simp only [hrank,ite_false,Real.sqrt_mul hK,t,s]
    dsimp only [A]
    exact le_of_eq (by ring)


/-- One deterministic increasing threshold is internally chosen so that the
actual bounded/count-good birth traffic is L2 over ALL inward/elapsed levels.
Both original matrix ranks are covered; no summability hypothesis is supplied.
This is the count-good component of full traffic, retaining the same scene. -/
theorem exists_original_left_bounded_birth_countGood_dyadic_traffic_memLp_two
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
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
    ∃ ε radius C : ℝ,0<ε∧0≤radius∧0<C∧
      ∀ ell:ℕ,ell<birthPhysicalClockWindowCount cap→
      let level := fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q) ↦
        let t:=birthDyadicShellScale ε z.1
        let s:=birthDyadicElapsedScale ε z.1 z.2
        let δ:=birthTrafficCoarseScale q t s
        let T:=positiveMatrixNormalizer (birthResidueScale G t s)
        let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
        let W:=birthTrafficSpatialWindow G t s radius
        let K:=interleavedLevelThreshold 0 C z.1 z.2
        ∑ i∈Finset.range (dyadicBirthBandCount z.2),
          {scene:LegalMarkedOptimalInputScene q |
            ‖D.normalizedMomentumPhaseField T
              (D.originalLeftBirthPhysicalClockReference ε cap z.1 z.2 i ell-S.level) h L scene 0‖≤H*δ∧
              (scene.2:Measure (LegalColoredInputPoint q))
                ((W×ˢD.originalLeftBirthNarrowClockBand ε z.1 z.2 i)×ˢ{0})≤ENNReal.ofReal K}.indicator
            (fun scene:LegalMarkedOptimalInputScene q ↦
              (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
                (fun x↦ENNReal.ofReal (η x))
                (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene).toReal) scene
      MemLp (fun scene↦∑' z:ℕ×ℕ,level z scene) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q)) ∧
      Summable (fun z:ℕ×ℕ ↦(eLpNorm (level z) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q))).toReal) ∧
      ∀ᵐ scene∂(Q.law:Measure (LegalMarkedOptimalInputScene q)),
        Summable (fun z:ℕ×ℕ ↦‖level z scene‖) := by
  obtain ⟨h,cap,E₀,hh,hcap,hE₀,hlevel⟩ :=
    D.exists_original_left_bounded_birth_countGood_level_norm hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨h,cap,hh,hcap,?_⟩
  intro H hH
  obtain ⟨ε₀,radius,A,hε₀,_hε₀1,hradius,hA,hlevel⟩ := hlevel H hH
  let ε:=ε₀/2
  have hε : 0<ε := by dsimp only [ε]; positivity
  have hεsmall : ε<ε₀ := by dsimp only [ε]; linarith
  obtain ⟨C,hC,hsum⟩ := exists_summable_original_birth_profile_with_constants
    (K₀:=0) (E:=E₀) (t:=ε/2) («q» := (q : ℝ)) (c:=1) (A:=A) (B:=0)
    (by norm_num) (by linarith) (by positivity) (by exact_mod_cast hq)
    (by norm_num) hA.le (by norm_num) G.rank
  refine ⟨ε,radius,C,hε,hradius,hC,?_⟩
  intro ell hell
  dsimp only
  let level := fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q) ↦
    let t:=birthDyadicShellScale ε z.1
    let s:=birthDyadicElapsedScale ε z.1 z.2
    let δ:=birthTrafficCoarseScale q t s
    let T:=positiveMatrixNormalizer (birthResidueScale G t s)
    let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let W:=birthTrafficSpatialWindow G t s radius
    let K:=interleavedLevelThreshold 0 C z.1 z.2
    ∑ i∈Finset.range (dyadicBirthBandCount z.2),
      {scene:LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T
      (D.originalLeftBirthPhysicalClockReference ε cap z.1 z.2 i ell-S.level) h L scene 0‖≤H*δ∧
      (scene.2:Measure (LegalColoredInputPoint q))
        ((W×ˢD.originalLeftBirthNarrowClockBand ε z.1 z.2 i)×ˢ{0})≤ENNReal.ofReal K}.indicator
        (fun scene:LegalMarkedOptimalInputScene q ↦
      (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
        (fun x↦ENNReal.ofReal (η x))
        (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene).toReal) scene
  let P:Measure (LegalMarkedOptimalInputScene q):=Q.law
  let K:=fun z:ℕ×ℕ↦interleavedLevelThreshold 0 C z.1 z.2
  let β:=if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8
  let γ:=if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4))
  let B:=fun z:ℕ×ℕ ↦
    A*(Real.sqrt (K z*E₀)*
      (((ε/2)/(2:ℝ)^z.1)^(1/(2*(q:ℝ)))*(1/(2:ℝ)^z.2)^(1/2:ℝ)+
        ((ε/2)/(2:ℝ)^z.1)^β*(1/(2:ℝ)^z.2)^γ))+
      0*((2:ℝ)^z.2*Real.exp (-1*K z))
  have hB : Summable B := hsum
  have hB0 : ∀ z,0≤B z := by intro z; dsimp only [B]; positivity
  have hK : ∀ z,0≤K z := by intro z; dsimp only [K,interleavedLevelThreshold]; positivity
  have hLp : ∀ z,MemLp (level z) 2 P := by
    intro z
    exact (hlevel hε hεsmall z.1 z.2 ell hell (hK z)).1
  have hbound : ∀ z,eLpNorm (level z) 2 P≤ENNReal.ofReal (B z) := by
    intro z
    have hn:=(hlevel hε hεsmall z.1 z.2 ell hell (hK z)).2
    change eLpNorm (level z) 2 P≤ENNReal.ofReal
      ((A*Real.sqrt (K z)*Real.sqrt E₀)*
        ((birthDyadicShellScale ε z.1)^β*
          ((birthDyadicElapsedScale ε z.1 z.2)/(birthDyadicShellScale ε z.1))^γ)) at hn
    have ht : 0<birthDyadicShellScale ε z.1 := birthDyadicShellScale_pos hε z.1
    have hscale : birthDyadicShellScale ε z.1=(ε/2)/(2:ℝ)^z.1 := by
      dsimp only [birthDyadicShellScale]
      rw [pow_succ]
      field_simp
    have hratio : birthDyadicElapsedScale ε z.1 z.2/birthDyadicShellScale ε z.1=
        1/(2:ℝ)^z.2 := by
      dsimp only [birthDyadicElapsedScale]
      field_simp
    rw [hratio,hscale] at hn
    apply hn.trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp only [B]
    rw [Real.sqrt_mul (hK z)]
    have hpos : 0≤A*Real.sqrt (K z)*Real.sqrt E₀*
        (((ε/2)/(2:ℝ)^z.1)^(1/(2*(q:ℝ)))*(1/(2:ℝ)^z.2)^(1/2:ℝ)) := by positivity
    nlinarith
  have hnorm : Summable (fun z↦(eLpNorm (level z) 2 P).toReal) :=
    hB.of_nonneg_of_le (fun _↦ENNReal.toReal_nonneg)
      (fun z↦ENNReal.toReal_le_of_le_ofReal (hB0 z) (hbound z))
  have hout:=memLp_tsum_of_summable_level_bound P level hLp B hB hB0 hbound
  exact ⟨hout.1,hnorm,hout.2.2⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
