import OTSelector.Reconstruction.OriginalMinimizerDyadicTrafficBudget
import OTSelector.Reconstruction.FinslerNormalizedAdaptiveGlobalEnvelope
import OTSelector.Reconstruction.OriginalInputBadEventSecondMoment
import OTSelector.Analysis.PolynomialFourthRootExponentialSummability
import OTSelector.Probability.SelectedIntegerBadEventSecondMoment
import OTSelector.MeasureTheory.Lp.SecondMomentNorm
import OTSelector.Reconstruction.FinslerOriginalCommonScaleWholePathAssembly
import OTSelector.Reconstruction.OriginalOccupiedTrafficInputCounts
import OTSelector.Reconstruction.OriginalCountTrafficGoodEventAELtwo
import OTSelector.Reconstruction.CompletePathTrafficCountUpper
import OTSelector.Reconstruction.OriginalBirthBandLargePhaseMoment
import OTSelector.Reconstruction.FinslerOriginalMinimizerContractiveTrafficSquare
import OTSelector.Reconstruction.OriginalCompactClockWeightedOccupation
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! Quantitative original-input envelope moments and actual minimizer traffic
in the true common-divided phase coordinates, retaining the frame δ T inverse. -/
open Set Function Filter MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator ENNReal NNReal Classical BigOperators
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
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "q" => finrank ℝ S.covector.ker

/-- Deterministic phase centers preserve the unchanged original input intensity. -/
theorem commonScaleOriginalSourcePhaseCell_intensity_eq_zeroCenter
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {δ : ℝ} (hδ : 0 < δ)
    {B : Set ℝ} (hB : MeasurableSet B) (z₀ p₀ : Fin q → ℝ) (R : ℝ) :
    ((volume : Measure (Fin q → ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B z₀ p₀ R) =
      ((volume : Measure (Fin q → ℝ)).prod μ)
        (D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 R) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  have hL : IsUnit (δ • T⁻¹).det := by
    rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hδ.ne')).mul
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
  unfold commonScaleOriginalSourcePhaseCell
  rw [prod_volume_markedPhaseSourceCell hL
    (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
    (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_commonScaleOriginalSourcePhaseCenter hF hw T hcut δ z₀ p₀) hB μ R,
    prod_volume_markedPhaseSourceCell hL
    (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
    (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_commonScaleOriginalSourcePhaseCenter hF hw T hcut δ 0 0) hB μ R]

/-- At fixed actual frame and clock carrier, original intensity is homogeneous
of degree q in the radius. -/
theorem commonScaleOriginalSourcePhaseCell_intensity_scale
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {δ : ℝ} (hδ : 0 < δ)
    {B : Set ℝ} (hB : MeasurableSet B) {R : ℝ} (hR : 0 ≤ R) :
    ((volume : Measure (Fin q → ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 R) =
      ENNReal.ofReal R ^ q * ((volume : Measure (Fin q → ℝ)).prod μ)
        (D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 1) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  have hL : IsUnit (δ • T⁻¹).det := by
    rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hδ.ne')).mul
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
  simpa only [commonScaleOriginalSourcePhaseCell, Fintype.card_fin] using
    prod_volume_markedPhaseSourceCell_radius_scale hL
      (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
      (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
      (D.measurable_commonScaleOriginalSourcePhaseCenter hF hw T hcut δ 0 0) hB μ hR

/-- The actual global radius has exact polynomial original intensity in real form. -/
theorem commonScaleOriginalSourceGlobalEnvelope_intensity_real
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {δ : ℝ} (hδ : 0 < δ)
    {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (((volume : Measure (Fin q → ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 (2 * (m : ℝ) + r))).toReal =
      (2 * (m : ℝ) + r) ^ q *
        (((volume : Measure (Fin q → ℝ)).prod μ)
          (D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 1)).toReal := by
  rw [D.commonScaleOriginalSourcePhaseCell_intensity_scale hF hw T hcut hδ hB (by positivity),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]


/-- The same true unit-cell intensity controls every radius and center. -/
theorem commonScaleOriginalSourcePhaseCell_intensity_le_of_unit
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (hB : MeasurableSet B) {Λ R : ℝ} (_hΛ : 0≤Λ) (hR : 0≤R)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 1)≤ENNReal.ofReal Λ)
    (z₀ p₀ : Fin q→ℝ) :
    ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B z₀ p₀ R)≤ENNReal.ofReal (R^q*Λ) := by
  rw [D.commonScaleOriginalSourcePhaseCell_intensity_eq_zeroCenter hF hw T hcut hδ hB,
    D.commonScaleOriginalSourcePhaseCell_intensity_scale hF hw T hcut hδ hB hR]
  calc
    _ ≤ ENNReal.ofReal R^q*ENNReal.ofReal Λ := by simpa only [mul_comm] using mul_le_mul_left hunit (ENNReal.ofReal R^q)
    _ = _ := by rw [←ENNReal.ofReal_pow hR,←ENNReal.ofReal_mul (pow_nonneg hR _)]

/-- The all-code event is fixed before any actual adaptive current is selected. -/
def commonScaleOriginalSourcePhaseBadEvent
    (T : Matrix (Fin q) (Fin q) ℝ) (cut δ : ℝ) (B : Set ℝ)
    (m : ℕ) (r K : ℝ) : Set (LegalMarkedOptimalInputScene q) :=
  ⋃code : PhaseWalkCode (2*q) m,{scene | K*(m:ℝ)≤
    ((scene.2 : Measure (LegalColoredInputPoint q))
      (D.commonScaleOriginalSourceCandidate T cut δ B code (r+2) ×ˢ {0})).toReal}

def commonScaleOriginalSourceGlobalEnvelope
    (T : Matrix (Fin q) (Fin q) ℝ) (cut δ : ℝ) (B : Set ℝ)
    (m : ℕ) (r : ℝ) : Set (LegalMarkedPhysicalPoint q) :=
  D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 (2*(m:ℝ)+r)

def commonScaleOriginalSourceGlobalCount
    (T : Matrix (Fin q) (Fin q) ℝ) (cut δ : ℝ) (B : Set ℝ)
    (m : ℕ) (r : ℝ) (scene : LegalMarkedOptimalInputScene q) : ℝ :=
  ((scene.2 : Measure (LegalColoredInputPoint q))
    (D.commonScaleOriginalSourceGlobalEnvelope T cut δ B m r ×ˢ {0})).toReal

def commonScaleSourceCountThreshold (qdim : ℕ) (Λ r : ℝ) : ℝ :=
  (3*(2*qdim:ℝ)+(3:ℝ)^(2*qdim))+2*((r+2)^qdim*Λ)*(Real.exp 1-1)+1

def commonScaleSourceEnvelopeBudget (qdim : ℕ) (Λ r : ℝ) : ℝ :=
  ∑'n : ℕ,(192*Real.exp (Real.exp 1-1)*
    (1+((2*((n+1:ℕ):ℝ)+r)^qdim*Λ)^4))^(1/2:ℝ)*Real.exp (-((n+1:ℕ):ℝ)/2)

theorem measurableSet_commonScaleOriginalSourcePhaseBadEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) (r K : ℝ) :
    MeasurableSet (D.commonScaleOriginalSourcePhaseBadEvent T cut δ B m r K) := by
  apply MeasurableSet.iUnion
  intro code
  exact measurableSet_le measurable_const
    (((Measure.measurable_coe
      ((D.measurableSet_commonScaleOriginalSourceCandidate hF hw T hcut δ hB code (r+2)).prod
        (measurableSet_singleton 0))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal)

theorem measurableSet_commonScaleOriginalSourceGlobalEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) (r : ℝ) :
    MeasurableSet (D.commonScaleOriginalSourceGlobalEnvelope T cut δ B m r) :=
  D.measurableSet_commonScaleOriginalSourcePhaseCell hF hw T hcut δ hB 0 0 _

theorem measurable_commonScaleOriginalSourceGlobalCount
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) (r : ℝ) :
    Measurable (D.commonScaleOriginalSourceGlobalCount T cut δ B m r) :=
  ((Measure.measurable_coe
    ((D.measurableSet_commonScaleOriginalSourceGlobalEnvelope hF hw T hcut δ hB m r).prod
      (measurableSet_singleton 0))).comp
    (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal

/-- The unchanged original Poisson envelope has a uniform polynomial fourth
moment in the genuine divided frame and deterministic original clock carrier. -/
theorem commonScaleOriginalSourceGlobalCount_fourth_moment
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (hB : MeasurableSet B) {Λ r : ℝ} (hΛ : 0≤Λ) (hr : 0≤r)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 1)≤ENNReal.ofReal Λ)
    {kin : ℝ→ℝ→(Fin q→ℝ)→ℝ} {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) (m : ℕ) :
    (∀ᵐ (scene : LegalMarkedOptimalInputScene q) ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      (scene.2 : Measure (LegalColoredInputPoint q))
        (D.commonScaleOriginalSourceGlobalEnvelope T cut δ B m r ×ˢ {0})<(∞:ℝ≥0∞)) ∧
    Integrable (fun scene ↦ (D.commonScaleOriginalSourceGlobalCount T cut δ B m r scene)^4)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫scene,(D.commonScaleOriginalSourceGlobalCount T cut δ B m r scene)^4
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤
      192*Real.exp (Real.exp 1-1)*(1+((2*(m:ℝ)+r)^q*Λ)^4) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have hi := D.commonScaleOriginalSourcePhaseCell_intensity_le_of_unit hF hw T hcut hδ hB
    hΛ (show 0≤2*(m:ℝ)+r by positivity) hunit 0 0
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi
  have h4 := Q.original_source_fourth_moment
    (D.measurableSet_commonScaleOriginalSourceGlobalEnvelope hF hw T hcut δ hB m r) hfin
  refine ⟨h4.1,h4.2.1,h4.2.2.trans ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
  rw [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (by positivity) _) hΛ)] at hreal
  gcongr
  exact hreal

/-- Original all-code probability and original fourth moments remain valid on
the same dependent bad event. The common divided frame is retained literally. -/
theorem commonScaleOriginalSource_bad_globalCount_second_moment
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (hB : MeasurableSet B) {Λ r : ℝ} (hΛ : 0≤Λ) (hr : 0≤r)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 1)≤ENNReal.ofReal Λ)
    {kin : ℝ→ℝ→(Fin q→ℝ)→ℝ} {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) {m : ℕ} (hm : 1≤m) (K : ℝ) :
    Integrable (fun scene ↦
      ((D.commonScaleOriginalSourcePhaseBadEvent T cut δ B m r K).indicator
        (D.commonScaleOriginalSourceGlobalCount T cut δ B m r) scene)^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫scene,((D.commonScaleOriginalSourcePhaseBadEvent T cut δ B m r K).indicator
      (D.commonScaleOriginalSourceGlobalCount T cut δ B m r) scene)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤
      (192*Real.exp (Real.exp 1-1)*(1+((2*(m:ℝ)+r)^q*Λ)^4))^(1/2:ℝ)*
        Real.exp ((-(K-(3*(2*q:ℝ)+(3:ℝ)^(2*q))-2*((r+2)^q*Λ)*(Real.exp 1-1))*(m:ℝ))*(1/2:ℝ)) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have hi := D.commonScaleOriginalSourcePhaseCell_intensity_le_of_unit hF hw T hcut hδ hB
    hΛ (show 0≤2*(m:ℝ)+r by positivity) hunit 0 0
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi
  have hbad := D.measurableSet_commonScaleOriginalSourcePhaseBadEvent hF hw T hcut δ hB m r K
  have hb := Q.original_source_badEvent_second_moment
    (D.measurableSet_commonScaleOriginalSourceGlobalEnvelope hF hw T hcut δ hB m r) hfin hbad
  have hp := D.commonScaleOriginalSourceCandidates_count_le_exp hF hw T hcut δ hB (r+2)
    (mul_nonneg (pow_nonneg (by positivity) _) hΛ)
    (fun z₀ p₀ ↦ D.commonScaleOriginalSourcePhaseCell_intensity_le_of_unit hF hw T hcut hδ hB
      hΛ (by positivity) hunit z₀ p₀) Q hm K
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
  rw [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (by positivity) _) hΛ)] at hreal
  calc
    _ ≤ (192*Real.exp (Real.exp 1-1)*(1+((2*(m:ℝ)+r)^q*Λ)^4))^(1/2:ℝ)*
        ((Q.law : Measure (LegalMarkedOptimalInputScene q)).real
          (D.commonScaleOriginalSourcePhaseBadEvent T cut δ B m r K))^(1/2:ℝ) := by
      gcongr
      exact hreal
    _ ≤ _ := by
      rw [Real.exp_mul]
      gcongr
      exact hp


/-- The fixed uniform original-input threshold makes the common-scale bad
count squares summable, with an explicit exponentially decreasing budget. -/
theorem commonScaleOriginalSource_bad_globalCount_summable_le_exp
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (hB : MeasurableSet B) {Λ r : ℝ} (hΛ : 0≤Λ) (hr : 0≤r)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 1)≤ENNReal.ofReal Λ)
    {kin : ℝ→ℝ→(Fin q→ℝ)→ℝ} {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) {K : ℝ}
    (hK : commonScaleSourceCountThreshold q Λ r≤K) :
    (∀m : ℕ,1≤m→Integrable (fun scene ↦
      ((D.commonScaleOriginalSourcePhaseBadEvent T cut δ B m r K).indicator
        (D.commonScaleOriginalSourceGlobalCount T cut δ B m r) scene)^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene q))) ∧
    Summable (fun m : ℕ ↦∫scene,
      ((D.commonScaleOriginalSourcePhaseBadEvent T cut δ B m r K).indicator
        (D.commonScaleOriginalSourceGlobalCount T cut δ B m r) scene)^2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ∧
    (∑'n : ℕ,∫scene,
      ((D.commonScaleOriginalSourcePhaseBadEvent T cut δ B (n+1) r K).indicator
        (D.commonScaleOriginalSourceGlobalCount T cut δ B (n+1) r) scene)^2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤
      commonScaleSourceEnvelopeBudget q Λ r * 
        Real.exp (-(K-commonScaleSourceCountThreshold q Λ r)/2) := by
  let a : ℕ→ℝ := fun m ↦
    (192*Real.exp (Real.exp 1-1)*(1+((2*(m:ℝ)+r)^q*Λ)^4))^(1/2:ℝ)*
      Real.exp (-(m:ℝ)/2)
  let J : ℕ→ℝ := fun m ↦∫scene,
    ((D.commonScaleOriginalSourcePhaseBadEvent T cut δ B m r K).indicator
      (D.commonScaleOriginalSourceGlobalCount T cut δ B m r) scene)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))
  let Δ := K-commonScaleSourceCountThreshold q Λ r
  have hΔ : 0≤Δ := sub_nonneg.mpr hK
  have ha : Summable a := summable_polynomialFourthRoot_exp_neg_half_nat q (by positivity) hr
  have hbound (m : ℕ) (hm : 1≤m) : J m≤a m*Real.exp (-Δ/2) := by
    have hb := (D.commonScaleOriginalSource_bad_globalCount_second_moment
      hF hw T hcut hδ hB hΛ hr hunit Q hm K).2
    apply hb.trans
    dsimp only [a]
    simp only [mul_assoc]
    rw [←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
    apply Real.exp_le_exp.mpr
    have hm' : (1:ℝ)≤m := by exact_mod_cast hm
    have hΔm := mul_nonneg hΔ (sub_nonneg.mpr hm')
    dsimp only [Δ,commonScaleSourceCountThreshold] at hΔm ⊢
    nlinarith
  have hJ : Summable J := by
    apply (ha.mul_right (Real.exp (-Δ/2))).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦sq_nonneg _))]
    exact hbound m hm
  refine ⟨fun m hm ↦(D.commonScaleOriginalSource_bad_globalCount_second_moment
    hF hw T hcut hδ hB hΛ hr hunit Q hm K).1,hJ,?_⟩
  have hshift := (summable_nat_add_iff 1).2 hJ
  have hashift := (summable_nat_add_iff 1).2 ha
  calc
    _ ≤ ∑'n : ℕ,a (n+1)*Real.exp (-Δ/2) :=
      hshift.tsum_le_tsum (fun n ↦hbound (n+1) (by omega)) (hashift.mul_right _)
    _ = _ := by rw [tsum_mul_right]; rfl

/-- Any same-scene selected current dominated by the unchanged original
common-scale envelope inherits its explicit mean-square and norm budget. -/
theorem commonScaleOriginalSource_selected_bad_memLp_two_le
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (hB : MeasurableSet B) {Λ r : ℝ} (hΛ : 0≤Λ) (hr : 0≤r)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 1)≤ENNReal.ofReal Λ)
    {kin : ℝ→ℝ→(Fin q→ℝ)→ℝ} {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) {K : ℝ}
    (hK : commonScaleSourceCountThreshold q Λ r≤K)
    {k : LegalMarkedOptimalInputScene q→ℕ} (hk : Measurable k)
    {f : LegalMarkedOptimalInputScene q→ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0≤C)
    (hdom : ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      scene∈D.commonScaleOriginalSourcePhaseBadEvent T cut δ B (k scene) r K→
      |f scene|≤C*|D.commonScaleOriginalSourceGlobalCount T cut δ B (k scene) r scene|) :
    let err := {scene |1≤k scene∧
      scene∈D.commonScaleOriginalSourcePhaseBadEvent T cut δ B (k scene) r K}.indicator f
    let budget : ℝ := (C ^ 2 * commonScaleSourceEnvelopeBudget q Λ r) *
      Real.exp (-(K - commonScaleSourceCountThreshold q Λ r) / 2)
    MemLp err 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫scene,(err scene)^2 ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤budget ∧
    eLpNorm err 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))≤
      ENNReal.ofReal (Real.sqrt budget) := by
  dsimp only
  let A := {scene |1≤k scene∧
    scene∈D.commonScaleOriginalSourcePhaseBadEvent T cut δ B (k scene) r K}
  have hbad := fun m ↦D.measurableSet_commonScaleOriginalSourcePhaseBadEvent hF hw T hcut δ hB m r K
  have hs := D.commonScaleOriginalSource_bad_globalCount_summable_le_exp
    hF hw T hcut hδ hB hΛ hr hunit Q hK
  have he := integrable_selected_bad_sq_and_integral_le_tsum hk hbad hf hC hdom
    hs.1 hs.2.1 (N:=1) le_rfl
  have hI : Integrable (fun scene ↦(A.indicator f scene)^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) := he.1
  have hm : (∫scene,(A.indicator f scene)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤
      C ^ 2*commonScaleSourceEnvelopeBudget q Λ r * 
        Real.exp (-(K-commonScaleSourceCountThreshold q Λ r)/2) := by
    calc
      _ ≤ C ^ 2*∑'n : ℕ,∫scene,
          ((D.commonScaleOriginalSourcePhaseBadEvent T cut δ B (n+1) r K).indicator
            (D.commonScaleOriginalSourceGlobalCount T cut δ B (n+1) r) scene)^2
            ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) := he.2
      _ ≤ C ^ 2*(commonScaleSourceEnvelopeBudget q Λ r * 
          Real.exp (-(K-commonScaleSourceCountThreshold q Λ r)/2)) :=
        mul_le_mul_of_nonneg_left hs.2.2 (sq_nonneg C)
      _ = _ := (mul_assoc _ _ _).symm
  have hsel : MeasurableSet {scene |scene∈D.commonScaleOriginalSourcePhaseBadEvent
      T cut δ B (k scene) r K} := by
    have heq : {scene |scene∈D.commonScaleOriginalSourcePhaseBadEvent T cut δ B (k scene) r K}=
        ⋃m : ℕ,{scene |k scene=m}∩D.commonScaleOriginalSourcePhaseBadEvent T cut δ B m r K := by
      ext scene
      simp only [mem_ofPred_eq,mem_iUnion,mem_inter_iff]
      exact ⟨fun hs ↦⟨k scene,rfl,hs⟩,fun ⟨m,hm,hs⟩↦hm.symm ▸ hs⟩
    rw [heq]
    exact MeasurableSet.iUnion (fun m ↦
      ((measurableSet_singleton m).preimage hk).inter (hbad m))
  have hAm : MeasurableSet A := (measurableSet_le measurable_const hk).inter hsel
  have hLp : MemLp (A.indicator f) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
    (memLp_two_iff_integrable_sq (hf.indicator hAm).aestronglyMeasurable).mpr hI
  exact ⟨hLp,hm,eLpNorm_two_le_sqrt_of_integral_sq_le hLp hm⟩
/-- Every actual edge near an admissible common-scale phase curve has its
unchanged original source in the radius-2m+r cell, on the same clock carrier. -/
theorem commonScaleOriginalSourcePhaseCell_contains_edge_of_phase_tube
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {δ : ℝ} (hδ : 0 < δ)
    {B : Set ℝ} (e : LegalMarkedPhysicalEdge q)
    (ha : e.1.2 ∈ D.sourcePhaseClocks cut) (hB : e.1.2 ∈ B)
    {m : ℕ} (γ : ℝ → Fin (2 * q) → ℝ) (hroot : ‖γ 0‖ ≤ (m : ℝ))
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ s - γ t‖ ≤ (m : ℝ) * |s - t|)
    {r : ℝ} (hr : 0 ≤ r)
    (htube : ∃ t ∈ Icc (0 : ℝ) 1,
      ‖phasePairVector
        (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e)
        (commonScaleNormalizedMomentumNodeValue S w T δ e) - γ t‖ ≤ r) :
    e.1 ∈ D.commonScaleOriginalSourcePhaseCell T cut δ B 0 0 (2 * (m : ℝ) + r) := by
  obtain ⟨t, ht, hnear⟩ := htube
  have hphase : ‖phasePairVector
      (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e)
      (commonScaleNormalizedMomentumNodeValue S w T δ e)‖ ≤ 2 * (m : ℝ) + r := by
    calc
      _ = ‖(phasePairVector
          (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e)
          (commonScaleNormalizedMomentumNodeValue S w T δ e) - γ t) + γ t‖ := by
        rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by linarith [norm_phaseCurve_le_two_mul γ hroot hLip ht]
  exact D.commonScaleOriginalSourcePhaseCell_contains_edge hF hw T hcut hδ e ha hB
    (by positivity) 0 0
    (by simpa only [sub_zero] using (norm_position_le_phasePairVector _ _).trans hphase)
    (by simpa only [sub_zero] using (norm_momentum_le_phasePairVector _ _).trans hphase)


/-- The SAME original attained minimizer's actual traffic is dominated by the
unchanged original source count at its genuinely divided canonical scale. The
source clock carrier is retained before applying the original input marginal. -/
theorem ae_original_minimizer_commonScale_traffic_le_globalCount
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
      (D.commonScaleOriginalSourcePhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
    ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f scene).toReal≤
        Bedge*D.commonScaleOriginalSourceGlobalCount T cut δ Band (k scene) radius scene := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|τ| *G/h)
  let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
  let R := originalNormalizedClockMobility S w T (cut+S.level) ell
  let d := fun z : PhysicalPairPalmMark (Fin q)×ℝ ↦originalSeedPathOffset S w z.2 z.1
  have hd : Measurable d := (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hρ : 0≤ρ := (norm_nonneg (R 0)).trans (hR 0 (by norm_num))
  have hradius : 0≤radius := by dsimp only [radius,b]; positivity
  have hδpos : 0<δ := by linarith
  have htube := D.ae_original_minimizer_commonScale_completePath_contributors_uniform
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh hclockRange hsmall hρ hR
  have hN := ae_all_iff.mpr (fun m : ℕ ↦
    (D.commonScaleOriginalSourceGlobalCount_fourth_moment
      hF hw T hcut hδpos hBand hΛ hradius hunit Q m).1)
  have hfiniteIntegral : (∫⁻scene,legalMarkedCompletePathTraffic q d η f scene
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≠(⊤:ℝ≥0∞) := by
    rw [Q.lintegral_completePathTraffic d hd hη hf]
    exact ENNReal.mul_ne_top hηfinite hffinite
  filter_upwards [htube,Q.full_matching,hN,
    ae_lt_top (measurable_legalMarkedCompletePathTraffic d hd hη hf) hfiniteIntegral]
    with scene hsTube hsFull hsN hsfinite
  let m := k scene
  let V := occupiedCompletePathTrafficContributors q d η f scene
  let W := D.commonScaleOriginalSourceGlobalEnvelope T cut δ Band m radius
  have hW : MeasurableSet W :=
    D.measurableSet_commonScaleOriginalSourceGlobalEnvelope hF hw T hcut δ hBand m radius
  have hV : MeasurableSet V := (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).isClosed_support.measurableSet.inter
    (measurableSet_legalMarkedCompletePathContributors d hd hη hf)
  have hcurve := D.commonScaleNormalizedCanonicalCurveIntegerScale_covers
    T cut h L R hsmall hδpos hρ hA hR hRLip scene
  have hsource : ∀e∈V,e.1∈W := by
    intro e he
    obtain ⟨r,hr,_hηne,hfne,hpath⟩ :=
      original_completePathEdgeTraffic_ne_zero_exists_affineWindow_contributor S w η f T
        (cut+S.level) ell e he.2 hclock hηwindow
    have heE := hmask e _ hfne
    have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hsFull.simple_edges).1
    have heN := (mem_support_originalCountingNodeRestriction_iff
      (0:LegalMarkedPhysicalEdge q) scene.1.1 hcount
      (D.normalizedMomentumPhaseEligibleEdges T cut h) e).mpr ⟨he.1,heE.1⟩
    exact D.commonScaleOriginalSourcePhaseCell_contains_edge_of_phase_tube
      hF hw T hcut hδpos e heE.1.1 heE.2
      (D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ scene)
      (hcurve.1 0 (by norm_num)) hcurve.2 hradius ⟨r,hr,hsTube r hr e heN a hpath⟩
  have hc : (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)) V≤
      (scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{0}) := by
    calc
      _ ≤ (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Prod.fst ⁻¹' W) := measure_mono hsource
      _ = (scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{0}) := by
        rw [←Measure.fst_apply hW,hsFull.source_marginal,legalInputColorMeasure_apply_prod _ _ _ hW]
  have hcfin := hc.trans_lt (hsN m)
  have hzero : ∀ᵐe ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      e∉V→legalMarkedCompletePathEdgeTraffic q d η f e=0 := by
    filter_upwards [(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).support_mem_ae] with e he hn
    by_contra hne
    exact hn ⟨he,hne⟩
  have hb : ∀ᵐe ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict V,
      (legalMarkedCompletePathEdgeTraffic q d η f e).toReal≤Bedge := by
    filter_upwards [ae_restrict_mem hV] with e he
    exact hbound e he.2
  have hu := legalMarkedCompletePathTraffic_le_bound_mul_count d hd hη hf scene V hcfin
    hsfinite.ne hzero hb
  exact hu.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hsN m).ne hc) hBedge)


/-- The actual attained minimizer's selected-current bad traffic has an
explicit uniform original-input eLpNorm budget in the true common-scale frame.
Its envelope domination is derived from the same actual occupied edges. -/
theorem original_minimizer_commonScale_selected_bad_traffic_memLp_two_le
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
      commonScaleSourceCountThreshold q Λ radius≤K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
    let traffic := fun scene ↦
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f scene).toReal
    let err := {scene |1≤k scene∧
      scene∈D.commonScaleOriginalSourcePhaseBadEvent T cut δ Band (k scene) radius K}.indicator traffic
    let budget := Bedge^2*commonScaleSourceEnvelopeBudget q Λ radius*
      Real.exp (-(K-commonScaleSourceCountThreshold q Λ radius)/2)
    MemLp err 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫scene,(err scene)^2 ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤budget ∧
    eLpNorm err 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))≤
      ENNReal.ofReal (Real.sqrt budget) := by
  dsimp only at hK ⊢
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|τ| *G/h)
  let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
  let d := fun z : PhysicalPairPalmMark (Fin q)×ℝ ↦originalSeedPathOffset S w z.2 z.1
  let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
    (legalMarkedCompletePathTraffic q d η f scene).toReal
  have hd : Measurable d := (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hρ : 0≤ρ := (norm_nonneg
    (originalNormalizedClockMobility S w T (cut+S.level) ell 0)).trans (hR 0 (by norm_num))
  have hradius : 0≤radius := by dsimp only [radius,b]; positivity
  have hδpos : 0<δ := by linarith
  have hdom := D.ae_original_minimizer_commonScale_traffic_le_globalCount
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hBand hmask hηfinite hffinite hBedge hΛ hbound hunit
  have hk : Measurable k :=
    D.measurable_commonScaleNormalizedCanonicalCurveIntegerScale hF hw T hcut h L ρ A δ
  have ht : Measurable traffic :=
    (measurable_legalMarkedCompletePathTraffic d hd hη hf).ennreal_toReal
  exact D.commonScaleOriginalSource_selected_bad_memLp_two_le hF hw T hcut hδpos
    hBand hΛ hradius hunit Q hK hk ht hBedge (by
      filter_upwards [hdom] with scene hs _hbad
      have ht0 : 0≤traffic scene := ENNReal.toReal_nonneg
      have hN0 : 0≤D.commonScaleOriginalSourceGlobalCount T cut δ Band (k scene) radius scene :=
        ENNReal.toReal_nonneg
      rw [abs_of_nonneg ht0,abs_of_nonneg hN0]
      exact hs)


/-- The actual supported physical birth window supplies its own band, clock
support and window length to the original large-phase Campbell estimate. -/
theorem exists_original_left_supportedBirthWindow_coarseWeightedPalm_rate
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ} (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η,
      originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ε₀ ≤ η ∧ ε₀ ≤ 1 ∧ 0 < C ∧
      ∀ {ε cap : ℝ}, 0 < ε → ε < ε₀ → 0 < cap →
      ∀ {gap : ℝ} {g : ℝ → ℝ → ℝ}
      (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g),
      ∀ n j i ell : ℕ, i < dyadicBirthBandCount j →
        ell < birthPhysicalClockWindowCount cap →
      let t := birthDyadicShellScale ε n
      let s := birthDyadicElapsedScale ε n j
      let B : Set (PhysicalPairPalmMark (Fin q)) := {m | m.1.1 ∈ D.originalLeftBirthNarrowClockBand ε n j i}
      ENNReal.ofReal ((birthTrafficCoarseScale q t s)⁻¹) *
        (∫⁻ m, ∫⁻ c : ℝ,
          ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ *
            D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell (m, c)
          ∂volume ∂legalMarkedJointPalm q Q.law) ≤
        ENNReal.ofReal (cap * C) *
          (ENNReal.ofReal (s ^ 2 * t ^ (-2 + 1 / (q : ℝ))) *
            (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
              ∂legalMarkedJointPalm q Q.law) +
           ENNReal.ofReal (s ^ 2 * t ^ (-1 + 1 / (q : ℝ))) *
            (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
              ∂legalMarkedJointPalm q Q.law)) := by
  obtain ⟨εmoment, C, hεmoment, hεη, hC, hrate⟩ :=
    D.exists_original_left_birthBand_largePhaseMoment_bound hF hw hη hG hRem hpole
  let ε₀ := min (εmoment / 2) 1
  have hε₀ : 0 < ε₀ := lt_min (by positivity) zero_lt_one
  have hε₀half : ε₀ ≤ εmoment / 2 := min_le_left _ _
  have hε₀one : ε₀ ≤ 1 := min_le_right _ _
  refine ⟨ε₀, C, hε₀, by linarith, hε₀one, hC, ?_⟩
  intro ε cap hε hεlt hcap gap g Q n j i ell hi hell
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let B : Set (PhysicalPairPalmMark (Fin q)) := {m | m.1.1 ∈ D.originalLeftBirthNarrowClockBand ε n j i}
  let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
  let width := birthPhysicalClockWindowWidth cap s
  let I : Set ℝ := Ioc ref (ref + width)
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hbase := birthDyadicClockBand_base_bounds hε n j i hi
  change 0 < s ∧ s ≤ t ∧ t ≤ t + (i : ℝ) * (s / 8) ∧
    t + (i : ℝ) * (s / 8) + s / 8 ≤ 2 * t at hbase
  have h2t : 2 * t ≤ ε := by
    dsimp [t]
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have htone : t ≤ 1 := by linarith
  have htε : 4 * t < εmoment := by linarith
  have hB : MeasurableSet B :=
    (D.measurableSet_originalLeftBirthNarrowClockBand ε n j i).preimage measurable_fst.fst
  have ha : ∀ m ∈ B, m.1.1 - (S.level : ℝ) - D.lo ∈ Icc t (2 * t) := by
    intro m hm
    change m.1.1 - S.level ∈ clockGridBand (D.lo + t) (s / 8) i at hm
    change D.lo + t + (i : ℝ) * (s / 8) < m.1.1 - S.level ∧
      m.1.1 - S.level ≤ D.lo + t + ((i : ℝ) + 1) * (s / 8) at hm
    constructor <;> nlinarith [hm.1, hm.2, hbase.2.2.1, hbase.2.2.2]
  have hI : MeasurableSet I := measurableSet_Ioc
  have hc : ∀ c ∈ I, c - (S.level : ℝ) - D.lo ∈ Icc t (4 * t) := by
    intro c hc
    exact D.originalLeftBirthPhysicalClockWindow_inward_bounds hε hcap n j i ell hi hell
      ⟨hc.1.le, hc.2⟩
  have hlen : volume I ≤ ENNReal.ofReal (cap * s) := by
    rw [Real.volume_Ioc]
    apply ENNReal.ofReal_le_ofReal
    have hw := (birthPhysicalClockWindow_spec hcap hbase.1).2.2.1
    change birthPhysicalClockWindowWidth cap s ≤ cap * s at hw
    dsimp [I, width]
    linarith
  have hzero : ∀ m c, m ∉ B ∨ c ∉ I →
      D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell (m, c) = 0 := by
    intro m c hout
    by_contra hn
    have hf := (D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff
      ε cap n j i ell (m, c)).mp hn
    have hb := D.originalSupportedLeftBirthPhysicalClockMask_birth
      ε cap n j i ell (m, c) hn
    have hmb : m ∈ B := D.originalLeftBirthClockMask_source_mem_clockGridBand
      ε n j i (m, c) hb.1
    have hci : c ∈ I := D.originalLeftBirthPhysicalClockMask_clock_mem
      ε cap n j i ell (m, c) hf.2.2
    exact hout.elim (fun h ↦ h hmb) (fun h ↦ h hci)
  exact hrate Q ht htone hbase.1 htε hB ha hI hc hcap.le hlen
    (D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell)
    (D.originalSupportedLeftBirthPhysicalClockMask_le_one ε cap n j i ell) hzero


/-- Every literal finite common-scale original-input candidate has a finite
count almost surely, before the actual minimizer selects any of its codes. -/
theorem ae_commonScaleOriginalSourceCandidate_count_finite
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {Band : Set ℝ} (hBand : MeasurableSet Band) {Λ R : ℝ} (hΛ : 0≤Λ) (hR : 0≤R)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
    {kin : ℝ→ℝ→(Fin q→ℝ)→ℝ} {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) :
    ∀ᵐ(scene : LegalMarkedOptimalInputScene q) ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀m : ℕ,∀code : PhaseWalkCode (2*q) m,
        (scene.2 : Measure (LegalColoredInputPoint q))
          (D.commonScaleOriginalSourceCandidate T cut δ Band code R ×ˢ {0})<(∞:ℝ≥0∞) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro code
  have hfin : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourceCandidate T cut δ Band code R)≠(∞:ℝ≥0∞) := by
    have hsum : (∑'j : Fin (m+1),((volume : Measure (Fin q→ℝ)).prod μ)
        (D.commonScaleOriginalSourcePhaseCell T cut δ Band
          (phaseWalkPosition code j) (phaseWalkMomentum code j) R))≠(∞:ℝ≥0∞) := by
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.mpr (fun j _ ↦ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (D.commonScaleOriginalSourcePhaseCell_intensity_le_of_unit hF hw T hcut hδ hBand hΛ hR hunit _ _))
    exact ne_top_of_le_ne_top hsum (measure_iUnion_le _)
  exact (Q.original_source_fourth_moment
    (D.measurableSet_commonScaleOriginalSourceCandidate hF hw T hcut δ hBand code R) hfin).1

/-- Off the SAME original all-code event, actual positive contributor count
is at most K times the genuinely divided cover scale, giving the literal
inverse-delta gain relative to the original field amplitude. -/
theorem ae_original_minimizer_commonScale_count_le_amplitude
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
    (hclock : ∀m c,f (m,c)≠0→∃r∈Icc (0:ℝ) 1,c=cut+S.level+ell*r)
    (hηwindow : ∀x,η x≠0→‖T*ᵥx‖≤a*δ)
    {Band : Set ℝ} (hBand : MeasurableSet Band)
    (hmask : ∀(e : LegalMarkedPhysicalEdge q) c,
      f ((physicalPairAnchor e).2,c)≠0→e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.1.2∈Band)
    {Λ : ℝ} (hΛ : 0≤Λ)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
    (K : ℝ) (hK : 0≤K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
    let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
    ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      scene∉D.commonScaleOriginalSourcePhaseBadEvent T cut δ Band (k scene) radius K→
      δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖→
      (scene.1.1 : Measure (LegalMarkedPhysicalEdge q))
        (legalMarkedCompletePathContributors q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f)<(⊤:ℝ≥0∞) ∧
      (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).real
        (legalMarkedCompletePathContributors q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f)≤
        (K*(C+1)/δ)*‖D.normalizedMomentumPhaseField T cut h L scene 0‖ := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|τ| *G/h)
  let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
  let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
  let d := fun z : PhysicalPairPalmMark (Fin q)×ℝ ↦originalSeedPathOffset S w z.2 z.1
  let R := originalNormalizedClockMobility S w T (cut+S.level) ell
  have hρ : 0≤ρ := (norm_nonneg (R 0)).trans (hR 0 (by norm_num))
  have hradius : 0≤radius := by dsimp only [radius,b]; positivity
  have hδpos : 0<δ := by linarith
  have htube := D.ae_original_minimizer_commonScale_completePath_contributors_uniform
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh hclockRange hsmall hρ hR
  have hN := D.ae_commonScaleOriginalSourceCandidate_count_finite hF hw T hcut hδpos
    hBand hΛ (show 0≤radius+2 by positivity) hunit Q
  filter_upwards [htube,Q.full_matching,hN] with scene hsTube hsFull hsN
  intro hsnot hamp
  have hscale := D.commonScaleNormalizedCanonicalCurveIntegerScale_spec
    T cut h L ρ A δ (N:=1) le_rfl scene (by simpa only [Nat.cast_one,L] using (one_le_div hδpos).mpr hamp)
  have hcurve := D.commonScaleNormalizedCanonicalCurveIntegerScale_covers
    T cut h L R hsmall hδpos hρ hA hR hRLip scene
  obtain ⟨code,hcode⟩ := exists_phaseWalkCode_cover_of_curve
    (d:=2*q) (m:=k scene) hscale.1
    (D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ scene)
    (hcurve.1 0 (by norm_num)) hcurve.2
  let W := D.commonScaleOriginalSourceCandidate T cut δ Band code (radius+2)
  let V := occupiedCompletePathTrafficContributors q d η f scene
  have hW : MeasurableSet W :=
    D.measurableSet_commonScaleOriginalSourceCandidate hF hw T hcut δ hBand code (radius+2)
  have hsource : ∀e∈V,e.1∈W := by
    intro e he
    obtain ⟨r,hr,_hηne,hfne,hpath⟩ :=
      original_completePathEdgeTraffic_ne_zero_exists_affineWindow_contributor S w η f T
        (cut+S.level) ell e he.2 hclock hηwindow
    have heE := hmask e _ hfne
    have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hsFull.simple_edges).1
    have heN := (mem_support_originalCountingNodeRestriction_iff
      (0:LegalMarkedPhysicalEdge q) scene.1.1 hcount
      (D.normalizedMomentumPhaseEligibleEdges T cut h) e).mpr ⟨he.1,heE.1⟩
    have hnear := hsTube r hr e heN a hpath
    obtain ⟨j,hj⟩ := hcode r hr
    apply D.commonScaleOriginalSourceCandidate_contains_edge_of_phase_cover
      hF hw T hcut hδpos e heE.1.1 heE.2 (by positivity) code
    refine ⟨j,?_⟩
    calc
      _ ≤ ‖phasePairVector
          (commonScaleNormalizedMomentumNodePosition S w T δ (cut+S.level) e)
          (commonScaleNormalizedMomentumNodeValue S w T δ e)-
            D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ scene r‖+
          ‖D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ scene r-
            phaseWalkVertex code j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add hnear hj
  have hc : (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)) V≤
      (scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{0}) := by
    calc
      _ ≤ (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Prod.fst ⁻¹' W) := measure_mono hsource
      _ = _ := by
        rw [←Measure.fst_apply hW,hsFull.source_marginal,legalInputColorMeasure_apply_prod _ _ _ hW]
  have hcfin := hc.trans_lt (hsN (k scene) code)
  have hreal : ((scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{0})).toReal<K*(k scene:ℝ) := by
    apply lt_of_not_ge
    intro hn
    exact hsnot (mem_iUnion.mpr ⟨code,hn⟩)
  have hcountreal : (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).real V≤
      (K*(C+1)/δ)*‖D.normalizedMomentumPhaseField T cut h L scene 0‖ := by
    calc
      _ ≤ ((scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{0})).toReal :=
        ENNReal.toReal_mono (hsN (k scene) code).ne hc
      _ ≤ K*(k scene:ℝ) := hreal.le
      _ ≤ K*((C+1)*(‖D.normalizedMomentumPhaseField T cut h L scene 0‖/δ)) :=
        mul_le_mul_of_nonneg_left hscale.2.2 hK
      _ = _ := by ring
  constructor
  · simpa only [V,measure_occupiedCompletePathTrafficContributors] using hcfin
  · simpa only [V,Measure.real,measure_occupiedCompletePathTrafficContributors] using hcountreal


/-- The actual common-scale count produces the inverse-delta coefficient in
the SAME minimizer's original momentum-weighted whole-path square estimate. -/
theorem ae_original_minimizer_commonScale_good_traffic_square_le
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
    (hclock : ∀m c,f (m,c)≠0→∃r∈Icc (0:ℝ) 1,c=cut+S.level+ell*r)
    (hηwindow : ∀x,η x≠0→‖T*ᵥx‖≤a*δ)
    {Band : Set ℝ} (hBand : MeasurableSet Band)
    (hmask : ∀(e : LegalMarkedPhysicalEdge q) c,
      f ((physicalPairAnchor e).2,c)≠0→e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.1.2∈Band)
    {Λ : ℝ} (hΛ : 0≤Λ)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
    (K : ℝ) (hK : 0≤K)
    (hη : Measurable η) (hf : Measurable f)
    (hηfinite : (∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))≠(⊤:ℝ≥0∞))
    (hffinite : (∫⁻m,∫⁻c : ℝ,f (m,c) ∂volume ∂legalMarkedJointPalm q Q.law)≠(⊤:ℝ≥0∞))
    {Bedge : ℝ} (hBedge : 0≤Bedge)
    (hbound : ∀e∈legalMarkedCompletePathContributors q
      (fun z ↦originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic q
        (fun z ↦originalSeedPathOffset S w z.2 z.1) η f e).toReal≤Bedge) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
    let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
    ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      scene∉D.commonScaleOriginalSourcePhaseBadEvent T cut δ Band (k scene) radius K→
      δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖→
      2*((L:ℝ)*(a*δ)+b)≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖→
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f scene).toReal^2≤
        (3*Bedge*(K*(C+1)/δ))*
          (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η
            (fun z ↦ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T z.1)*f z) scene).toReal := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|τ| *G/h)
  let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
  let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
  let Good := fun scene : LegalMarkedOptimalInputScene q ↦
    scene∉D.commonScaleOriginalSourcePhaseBadEvent T cut δ Band (k scene) radius K∧
      δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖
  let Count := fun scene : LegalMarkedOptimalInputScene q ↦
    (scene.1.1 : Measure (LegalMarkedPhysicalEdge q))
      (legalMarkedCompletePathContributors q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f)<(⊤:ℝ≥0∞) ∧
    (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).real
      (legalMarkedCompletePathContributors q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f)≤
      (K*(C+1)/δ)*‖D.normalizedMomentumPhaseField T cut h L scene 0‖
  have hδpos : 0<δ := by linarith
  have hC : 1≤C := (canonicalPhaseCurveScaleCoefficient_bounds (L:ℝ) ρ A).1
  have hκ : 0≤K*(C+1)/δ := div_nonneg (mul_nonneg hK (by linarith)) hδpos.le
  have hcount := D.ae_original_minimizer_commonScale_count_le_amplitude
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hBand hmask hΛ hunit K hK
  have hsquare := D.ae_original_minimizer_completePathTraffic_sq_le_of_count
    hF hw hgap hbounds T hg hgb τ Q hmin hcut hh hclockRange hsmall hη hf hηfinite hffinite
    hclock hηwindow (fun e c hfne ↦(hmask e c hfne).1) (fun scene ↦Good scene∧Count scene)
    hBedge hκ hbound (fun _ hs ↦hs.2)
  filter_upwards [hcount,hsquare] with scene hsCount hsSquare
  intro hsnot hamp hlarge
  exact hsSquare ⟨⟨hsnot,hamp⟩,hsCount hsnot hamp⟩ hlarge


/-- Quantitative large-amplitude norm bound in the genuine common scale.
The good term pays the actual inverse-delta original Palm moment; the same
actual selected-current bad term has the uniform exponential envelope budget. -/
theorem original_minimizer_commonScale_large_traffic_memLp_two_le
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
    let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
    let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
    let traffic := fun scene ↦
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f scene).toReal
    let Big := {scene |1≤k scene∧δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖∧
      2*((L:ℝ)*(a*δ)+b)≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖}
    let palm := ((∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))*
      (∫⁻m,∫⁻c : ℝ,ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,c)
        ∂volume ∂legalMarkedJointPalm q Q.law)).toReal
    let badBudget := Bedge^2*commonScaleSourceEnvelopeBudget q Λ radius*
      Real.exp (-(K-commonScaleSourceCountThreshold q Λ radius)/2)
    let budget := (3*Bedge*(K*(C+1)/δ))*palm+badBudget
    MemLp (Big.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫scene,(Big.indicator traffic scene)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤budget ∧
    eLpNorm (Big.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))≤
      ENNReal.ofReal (Real.sqrt budget) := by
  dsimp only at hK ⊢
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|τ| *G/h)
  let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
  let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
  let d := fun z : PhysicalPairPalmMark (Fin q)×ℝ ↦originalSeedPathOffset S w z.2 z.1
  let pweight := fun z : PhysicalPairPalmMark (Fin q)×ℝ ↦
    ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T z.1)*f z
  let traffic := fun scene : LegalMarkedOptimalInputScene q ↦
    (legalMarkedCompletePathTraffic q d η f scene).toReal
  let weighted := fun scene : LegalMarkedOptimalInputScene q ↦
    (legalMarkedCompletePathTraffic q d η pweight scene).toReal
  let Big := {scene |1≤k scene∧δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖∧
    2*((L:ℝ)*(a*δ)+b)≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖}
  let Err := {scene |1≤k scene∧
    scene∈D.commonScaleOriginalSourcePhaseBadEvent T cut δ Band (k scene) radius K}.indicator traffic
  let coeff := 3*Bedge*(K*(C+1)/δ)
  let badBudget := Bedge^2*commonScaleSourceEnvelopeBudget q Λ radius*
    Real.exp (-(K-commonScaleSourceCountThreshold q Λ radius)/2)
  have hδpos : 0<δ := by linarith
  have hρ : 0≤ρ := (norm_nonneg
    (originalNormalizedClockMobility S w T (cut+S.level) ell 0)).trans (hR 0 (by norm_num))
  have hradius : 0≤radius := by dsimp only [radius,b]; positivity
  have he1 : 0≤Real.exp 1-1 := sub_nonneg.mpr (Real.one_le_exp zero_le_one)
  have hK0 : 0≤K := (show 0≤commonScaleSourceCountThreshold q Λ radius by
    unfold commonScaleSourceCountThreshold
    positivity).trans hK
  have hC : 1≤C := (canonicalPhaseCurveScaleCoefficient_bounds (L:ℝ) ρ A).1
  have hcoeff : 0≤coeff := by dsimp only [coeff]; positivity
  have hd : Measurable d := (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hpweight : Measurable pweight :=
    ((measurable_originalNormalizedMomentumMarkNorm S hF hw T).comp measurable_fst).ennreal_ofReal.mul hf
  have htraffic : Measurable traffic :=
    (measurable_legalMarkedCompletePathTraffic d hd hη hf).ennreal_toReal
  have hweighted := measurable_legalMarkedCompletePathTraffic d hd hη hpweight
  have hweightedMean : (∫⁻scene,legalMarkedCompletePathTraffic q d η pweight scene
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≠(⊤:ℝ≥0∞) := by
    rw [Q.lintegral_completePathTraffic d hd hη hpweight]
    exact ENNReal.mul_ne_top hηfinite hpfinite
  have hiweighted : Integrable weighted (Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
    integrable_toReal_of_lintegral_ne_top hweighted.aemeasurable hweightedMean
  have heqweighted : (∫scene,weighted scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))=
      ((∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))*
        (∫⁻m,∫⁻c : ℝ,ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,c)
          ∂volume ∂legalMarkedJointPalm q Q.law)).toReal := by
    rw [integral_toReal hweighted.aemeasurable (ae_lt_top hweighted hweightedMean),
      Q.lintegral_completePathTraffic d hd hη hpweight]
  have hbad := D.original_minimizer_commonScale_selected_bad_traffic_memLp_two_le
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hBand hmask hηfinite hffinite hBedge hΛ hbound hunit hK
  have hgood := D.ae_original_minimizer_commonScale_good_traffic_square_le
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hBand hmask hΛ hunit K hK0 hη hf hηfinite hffinite hBedge hbound
  have hk : Measurable k :=
    D.measurable_commonScaleNormalizedCanonicalCurveIntegerScale hF hw T hcut h L ρ A δ
  have hamp : Measurable (fun scene ↦‖D.normalizedMomentumPhaseField T cut h L scene 0‖) :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have hBig : MeasurableSet Big := (measurableSet_le measurable_const hk).inter
    ((measurableSet_le measurable_const hamp).inter (measurableSet_le measurable_const hamp))
  have hiBad : Integrable (fun scene ↦(Err scene)^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) := hbad.1.integrable_sq
  have hmajor : ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      (Big.indicator traffic scene)^2≤coeff*weighted scene+(Err scene)^2 := by
    filter_upwards [hgood] with scene hs
    by_cases hbig : scene∈Big
    · rw [indicator_of_mem hbig]
      by_cases hb : scene∈D.commonScaleOriginalSourcePhaseBadEvent T cut δ Band (k scene) radius K
      · have he : scene∈{scene |1≤k scene∧
          scene∈D.commonScaleOriginalSourcePhaseBadEvent T cut δ Band (k scene) radius K} := ⟨hbig.1,hb⟩
        dsimp only [Err]
        rw [indicator_of_mem he]
        exact le_add_of_nonneg_left (mul_nonneg hcoeff ENNReal.toReal_nonneg)
      · exact (hs hb hbig.2.1 hbig.2.2).trans (le_add_of_nonneg_right (sq_nonneg _))
    · rw [indicator_of_notMem hbig,zero_pow (by norm_num : 2≠0)]
      exact add_nonneg (mul_nonneg hcoeff ENNReal.toReal_nonneg) (sq_nonneg _)
  have hiMajor := (hiweighted.const_mul coeff).add hiBad
  have hiLarge : Integrable (fun scene ↦(Big.indicator traffic scene)^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
    apply hiMajor.mono' ((htraffic.indicator hBig).pow_const 2).aestronglyMeasurable
    filter_upwards [hmajor] with scene hs
    rwa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hmean : (∫scene,(Big.indicator traffic scene)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤
      coeff*((∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))*
        (∫⁻m,∫⁻c : ℝ,ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,c)
          ∂volume ∂legalMarkedJointPalm q Q.law)).toReal+badBudget := by
    calc
      _ ≤ ∫scene,coeff*weighted scene+(Err scene)^2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) := integral_mono_ae hiLarge hiMajor hmajor
      _ = coeff*(∫scene,weighted scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))+
          ∫scene,(Err scene)^2 ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
        rw [integral_add (hiweighted.const_mul coeff) hiBad,integral_const_mul]
      _ ≤ _ := by rw [heqweighted]; exact add_le_add le_rfl hbad.2.1
  have hLp : MemLp (Big.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
    (memLp_two_iff_integrable_sq (htraffic.indicator hBig).aestronglyMeasurable).mpr hiLarge
  exact ⟨hLp,hmean,eLpNorm_two_le_sqrt_of_integral_sq_le hLp hmean⟩


/-- The true supported birth weight has finite normalized-momentum occupation
on its actual affine physical-clock window, without a finite-moment premise. -/
theorem original_left_supportedBirthWindow_weightedPalm_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (T : Matrix (Fin q) (Fin q) ℝ) (ε cap : ℝ) (n j i ell : ℕ)
    (hwidth : 0 < birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j))
    (hclock : ∀ r ∈ Icc (0 : ℝ) 1,
      D.originalLeftBirthPhysicalClockReference ε cap n j i ell +
        birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j) * r -
        (S.level : ℝ) ∈ Ioo D.lo D.hi) :
    (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal ‖(Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m‖ *
        D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell (m, c)
      ∂volume ∂legalMarkedJointPalm q Q.law) < (∞ : ℝ≥0∞) := by
  let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
  let width := birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)
  let J : Set ℝ := Icc ref (ref + width)
  have hJclock : ∀ c ∈ J, c - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    intro c hc
    have hr : (c - ref) / width ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith [hc.1]) hwidth.le,
        (div_le_iff₀ hwidth).mpr (by linarith [hc.2])⟩
    have heq : ref + width * ((c - ref) / width) = c := by
      field_simp [show width ≠ 0 from hwidth.ne']
      ring
    have h := hclock ((c - ref) / width) hr
    change ref + width * ((c - ref) / width) - (S.level : ℝ) ∈ Ioo D.lo D.hi at h
    rwa [heq] at h
  have hzero : ∀ m c, c ∉ J →
      D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell (m, c) = 0 := by
    intro m c hc
    by_contra hn
    have hf := (D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff
      ε cap n j i ell (m, c)).mp hn
    have hmem := D.originalLeftBirthPhysicalClockMask_clock_mem
      ε cap n j i ell (m, c) hf.2.2
    exact hc ⟨hmem.1.le, hmem.2⟩
  exact D.lintegral_original_compactClock_maskedWeightedOccupation_lt_top hF hw
    hgap hbounds Q (Tᵀ)⁻¹ isCompact_Icc hJclock
    (D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell)
    (D.originalSupportedLeftBirthPhysicalClockMask_le_one ε cap n j i ell) hzero


/-- The literal supported birth weight has finite original first Palm
occupation from the same weighted law, without a supplied moment bound. -/
theorem original_left_supportedBirthWindow_palm_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (ε cap : ℝ) (n j i ell : ℕ) :
    (∫⁻m,∫⁻c : ℝ,D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell (m,c)
      ∂volume ∂legalMarkedJointPalm q Q.law)<(∞:ℝ≥0∞) := by
  apply lt_of_le_of_lt (b:=∫⁻m,∫⁻c : ℝ,ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖
    ∂volume ∂legalMarkedJointPalm q Q.law)
  · apply lintegral_mono
    intro m
    apply lintegral_mono
    intro c
    exact mul_le_of_le_one_right (by positivity)
      (D.originalSupportedLeftBirthPhysicalClockMask_le_one ε cap n j i ell (m,c))
  · rw [D.lintegral_original_clockOccupation_norm_eq_pathLength hF hw hbounds Q]
    exact ENNReal.ofReal_lt_top

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
