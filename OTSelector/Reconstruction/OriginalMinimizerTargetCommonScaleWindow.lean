import OTSelector.Reconstruction.OriginalMinimizerRightCommonScaleTraffic
import OTSelector.Reconstruction.CountDominatedWindowLtwo
import OTSelector.Reconstruction.OriginalMinimizerFullTrafficAssembly

/-! Complete common-scale traffic uses the unchanged original target law.
The same target clocks, positive target phase center and color-one Poisson counts
provide both bounded and large canonical-amplitude branches. -/
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

/-- Every smaller actual common-scale radius gives a subset of the SAME
original input cell, keeping its deterministic clock carrier fixed. -/
theorem commonScaleOriginalTargetPhaseCell_mono_radius
    (T : Matrix (Fin q) (Fin q) ℝ) (cut δ : ℝ) (Band : Set ℝ)
    (z₀ p₀ : Fin q→ℝ) {R₁ R₂ : ℝ} (hR : R₁≤R₂) :
    D.commonScaleOriginalTargetPhaseCell T cut δ Band z₀ p₀ R₁⊆
      D.commonScaleOriginalTargetPhaseCell T cut δ Band z₀ p₀ R₂ := by
  intro x hx
  refine ⟨hx.1,hx.2.trans ?_⟩
  dsimp only [phaseSourceCellRadius]
  gcongr


/-- A bounded genuinely divided amplitude is controlled by one fixed original
target count. The same frame, target clock carrier and actual occupied edges are
retained; no selected-cloud count hypothesis is introduced. -/
theorem ae_original_minimizer_commonScale_target_bounded_traffic_le_fixedCount
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
      f ((physicalPairAnchor e).2,c)≠0→e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.2.2∈Band)
    (hηfinite : (∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))≠(⊤:ℝ≥0∞))
    (hffinite : (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)≠(⊤:ℝ≥0∞))
    {Bedge Λ : ℝ} (hBedge : 0≤Bedge) (hΛ : 0≤Λ)
    (hbound : ∀e∈legalMarkedCompletePathContributors q
      (fun z ↦originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic q
        (fun z ↦originalSeedPathOffset S w z.2 z.1) η f e).toReal≤Bedge)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
    (H : ℝ) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
    let m := Nat.ceil (C*H)
    ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ‖D.normalizedMomentumPhaseField T cut h L scene 0‖≤H*δ→
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f scene).toReal≤
        Bedge*D.commonScaleOriginalTargetGlobalCount T cut δ Band m radius scene := by
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
  have hdom := D.ae_original_minimizer_commonScale_traffic_le_targetGlobalCount
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hBand hmask hηfinite hffinite hBedge hΛ hbound hunit
  have hN := (D.commonScaleOriginalTargetGlobalCount_fourth_moment
    hF hw T hcut hδpos hBand hΛ hradius hunit Q m).1
  filter_upwards [hdom,hN] with scene hs hsN
  intro hamp
  have hkm : k scene≤m := by
    apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hδpos).mpr hamp) (by linarith)
  have hsub : D.commonScaleOriginalTargetGlobalEnvelope T cut δ Band (k scene) radius⊆
      D.commonScaleOriginalTargetGlobalEnvelope T cut δ Band m radius := by
    apply D.commonScaleOriginalTargetPhaseCell_mono_radius
    have hkm' : (k scene:ℝ)≤m := by exact_mod_cast hkm
    linarith
  have hc : D.commonScaleOriginalTargetGlobalCount T cut δ Band (k scene) radius scene≤
      D.commonScaleOriginalTargetGlobalCount T cut δ Band m radius scene := by
    exact ENNReal.toReal_mono hsN.ne (measure_mono (Set.prod_mono hsub subset_rfl))
  exact hs.trans (mul_le_mul_of_nonneg_left hc hBedge)


/-- The bounded common-scale branch has a quantitative norm bound from the
SAME fixed original input count and actual original first Palm occupation. -/
theorem original_minimizer_commonScale_target_bounded_traffic_memLp_two_le
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
      f ((physicalPairAnchor e).2,c)≠0→e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.2.2∈Band)
    (hηfinite : (∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))≠(⊤:ℝ≥0∞))
    (hffinite : (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)≠(⊤:ℝ≥0∞))
    {Bedge Λ : ℝ} (hBedge : 0≤Bedge) (hΛ : 0≤Λ)
    (hbound : ∀e∈legalMarkedCompletePathContributors q
      (fun z ↦originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic q
        (fun z ↦originalSeedPathOffset S w z.2 z.1) η f e).toReal≤Bedge)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
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
  let W := D.commonScaleOriginalTargetGlobalEnvelope T cut δ Band m radius
  let N := fun scene : LegalMarkedOptimalInputScene q ↦
    ((scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{1})).toReal
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
  have hW := D.measurableSet_commonScaleOriginalTargetGlobalEnvelope hF hw T hcut δ hBand m radius
  have hN : Measurable N := D.measurable_commonScaleOriginalTargetGlobalCount hF hw T hcut δ hBand m radius
  have hρ : 0≤ρ := (norm_nonneg
    (originalNormalizedClockMobility S w T (cut+S.level) ell 0)).trans (hR 0 (by norm_num))
  have hradius : 0≤radius := by dsimp only [radius,b]; positivity
  have hδpos : 0<δ := by linarith
  have hΛsmall : 0≤Λsmall := mul_nonneg (pow_nonneg (by positivity) _) hΛ
  have hmass : ((volume : Measure (Fin q→ℝ)).prod ν) W≤ENNReal.ofReal Λsmall :=
    D.commonScaleOriginalTargetPhaseCell_intensity_le_of_unit hF hw T hcut hδpos hBand hΛ
      (by positivity) hunit 0 0
  have hdom := D.ae_original_minimizer_commonScale_target_bounded_traffic_le_fixedCount
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
  have hreal : (((volume : Measure (Fin q→ℝ)).prod ν) W).toReal≤Λsmall := by
    simpa only [ENNReal.toReal_ofReal hΛsmall] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  obtain ⟨_,hExp,hExpBound⟩ :=
    Q.original_target_exp_moment_of_finite_intensity hW hfin (t:=1) (by norm_num)
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
theorem original_minimizer_commonScale_target_fullWindow_traffic_memLp_two_le
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
      f ((physicalPairAnchor e).2,c)≠0→e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.2.2∈Band)
    (hηfinite : (∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))≠(⊤:ℝ≥0∞))
    (hffinite : (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)≠(⊤:ℝ≥0∞))
    {Bedge Λ : ℝ} (hBedge : 0≤Bedge) (hΛ : 0≤Λ)
    (hbound : ∀e∈legalMarkedCompletePathContributors q
      (fun z ↦originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic q
        (fun z ↦originalSeedPathOffset S w z.2 z.1) η f e).toReal≤Bedge)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
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
  have hs := D.original_minimizer_commonScale_target_bounded_traffic_memLp_two_le
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hBand hmask hηfinite hffinite hBedge hΛ hbound hunit H hK0
  have hb := D.original_minimizer_commonScale_target_large_traffic_memLp_two_le
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



end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
