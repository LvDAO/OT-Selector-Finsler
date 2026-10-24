import OTSelector.Reconstruction.FinslerOriginalNormalizedPhaseSourceContainment
import OTSelector.Reconstruction.FinslerOriginalCommonScaleWholePathAssembly
import OTSelector.Reconstruction.FinslerOriginalBirthContributorClockBands
import OTSelector.Reconstruction.FinslerOriginalShellBandMass
import OTSelector.Reconstruction.OriginalFocalPositiveResidue
import OTSelector.Reconstruction.BirthBandOriginalPhaseIntensity
import OTSelector.Reconstruction.OriginalBirthBandPoissonCounts
import OTSelector.Probability.FiniteIntensityCandidateUnionBound

/-! Actual common-scale original input envelopes, retaining the independent
coarse division of both phase position and momentum and its literal Haar frame. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

/-- A genuine scalar upper compliance bound supplies a single determinant
constant, independent of clocks, dyadic scales and phase-cell centers. -/
theorem exists_det_bound_of_posSemidef_scalar_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι] (U₀ : ℝ) :
    ∃ Ddet : ℝ, 0<Ddet ∧ ∀ A : Matrix ι ι ℝ,
      A.PosSemidef → (U₀ • 1-A).PosSemidef → (1+A).det≤Ddet := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_bound_of_posSemidef_scalar_upper (ι:=ι) U₀
  have hc : Continuous (fun A : Matrix ι ι ℝ ↦ (1+A).det) :=
    (continuous_const.add continuous_id).matrix_det
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:Matrix ι ι ℝ) C).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max D 0+1,by positivity,fun A hA hu ↦ ?_⟩
  have ha : A ∈ Metric.closedBall (0:Matrix ι ι ℝ) C := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hbound A hA hu
  exact (le_abs_self _).trans ((hD A ha).trans (by linarith [le_max_left D 0]))

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "q" => finrank ℝ S.covector.ker

/-- The physical center of a cell in the actually divided phase coordinates. -/
def commonScaleOriginalSourcePhaseCenter (T : Matrix (Fin q) (Fin q) ℝ)
    (cut δ : ℝ) (z₀ p₀ : Fin q → ℝ) (a : ℝ) : Fin q → ℝ :=
  (δ • T⁻¹) *ᵥ (z₀-(T*D.sourcePhaseLeg cut a*Tᵀ)*ᵥp₀)

/-- Exact unchanged original-source input cell in the independent common scale. -/
def commonScaleOriginalSourcePhaseCell (T : Matrix (Fin q) (Fin q) ℝ)
    (cut δ : ℝ) (B : Set ℝ) (z₀ p₀ : Fin q → ℝ) (R : ℝ) :
    Set (LegalMarkedPhysicalPoint q) :=
  markedPhaseSourceCell (δ • T⁻¹) (fun a ↦ T*D.sourcePhaseLeg cut a*Tᵀ)
    (D.commonScaleOriginalSourcePhaseCenter T cut δ z₀ p₀) B R

theorem measurable_commonScaleOriginalSourcePhaseCenter
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (δ : ℝ) (z₀ p₀ : Fin q → ℝ) :
    Measurable (D.commonScaleOriginalSourcePhaseCenter T cut δ z₀ p₀) :=
  ((δ • T⁻¹).mulVecLin.toContinuousLinearMap).continuous.measurable.comp
    (measurable_const.sub ((completePathMatrixApply p₀).continuous.measurable.comp
      (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)))

theorem measurableSet_commonScaleOriginalSourcePhaseCell
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (z₀ p₀ : Fin q → ℝ) (R : ℝ) :
    MeasurableSet (D.commonScaleOriginalSourcePhaseCell T cut δ B z₀ p₀ R) :=
  measurableSet_markedPhaseSourceCell _
    (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
    (D.measurable_commonScaleOriginalSourcePhaseCenter hF hw T hcut δ z₀ p₀) hB R

/-- The same actual edge gives an original source in the divided phase cell,
with physical frame δ T inverse and identical compliance, at the same radius. -/
theorem commonScaleOriginalSourcePhaseCell_contains_edge
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (e : LegalMarkedPhysicalEdge q)
    (ha : e.1.2 ∈ D.sourcePhaseClocks cut) (hB : e.1.2 ∈ B)
    {R : ℝ} (hR : 0≤R) (z₀ p₀ : Fin q → ℝ)
    (hz : ‖commonScaleNormalizedMomentumNodePosition S w T δ (cut+S.level) e-z₀‖≤R)
    (hp : ‖commonScaleNormalizedMomentumNodeValue S w T δ e-p₀‖≤R) :
    e.1 ∈ D.commonScaleOriginalSourcePhaseCell T cut δ B z₀ p₀ R := by
  have hL : IsUnit (δ • T⁻¹).det := by
    rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hδ.ne')).mul
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
  have hm := mk_add_mulVec_sub_mem_markedPhaseSourceCell hL
    (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
    (D.commonScaleOriginalSourcePhaseCenter T cut δ z₀ p₀) hB hR hz hp
  have hs := D.commonScaleNormalizedMomentumNode_source_identity T hδ e ha
  have heq : D.commonScaleOriginalSourcePhaseCenter T cut δ z₀ p₀ e.1.2 +
      (δ • T⁻¹) *ᵥ
        ((commonScaleNormalizedMomentumNodePosition S w T δ (cut+S.level) e-z₀)-
          (T*D.sourcePhaseLeg cut e.1.2*Tᵀ)*ᵥ
            (commonScaleNormalizedMomentumNodeValue S w T δ e-p₀)) = e.1.1 := by
    rw [hs]
    dsimp only [commonScaleOriginalSourcePhaseCenter]
    simp only [Matrix.mulVec_sub]
    abel
  rwa [heq] at hm

/-- One literal finite code in the truly common-divided original source cells. -/
def commonScaleOriginalSourceCandidate (T : Matrix (Fin q) (Fin q) ℝ)
    (cut δ : ℝ) (B : Set ℝ) {m : ℕ} (code : PhaseWalkCode (2*q) m) (R : ℝ) :
    Set (LegalMarkedPhysicalPoint q) :=
  ⋃ j : Fin (m+1), D.commonScaleOriginalSourcePhaseCell T cut δ B
    (phaseWalkPosition code j) (phaseWalkMomentum code j) R

theorem measurableSet_commonScaleOriginalSourceCandidate
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) {m : ℕ}
    (code : PhaseWalkCode (2*q) m) (R : ℝ) :
    MeasurableSet (D.commonScaleOriginalSourceCandidate T cut δ B code R) :=
  MeasurableSet.iUnion (fun _ ↦ D.measurableSet_commonScaleOriginalSourcePhaseCell
    hF hw T hcut δ hB _ _ R)

/-- Full original input counts simultaneously control every common-scale
candidate. The cell intensity bound concerns the original input, before any
matching-adaptive candidate or contributor is selected. -/
theorem commonScaleOriginalSourceCandidates_count_le_exp
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (R : ℝ)
    {Λ : ℝ} (hΛ : 0≤Λ)
    (hcell : ∀ z₀ p₀, ((volume : Measure (Fin q → ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B z₀ p₀ R) ≤ ENNReal.ofReal Λ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    {m : ℕ} (hm : 1≤m) (K : ℝ) :
    (Q.law : Measure (LegalMarkedOptimalInputScene q)).real
      (⋃ code : PhaseWalkCode (2*q) m, {scene | K*(m:ℝ) ≤
        ((scene.2 : Measure (LegalColoredInputPoint q))
          (D.commonScaleOriginalSourceCandidate T cut δ B code R ×ˢ {0})).toReal}) ≤
      Real.exp (-(K-(3*(2*q:ℝ)+(3:ℝ)^(2*q))-2*Λ*(Real.exp 1-1))*(m:ℝ)) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have hbound (code : PhaseWalkCode (2*q) m) :
      ((volume : Measure (Fin q → ℝ)).prod μ)
        (D.commonScaleOriginalSourceCandidate T cut δ B code R) ≤
        (m+1:ℝ≥0∞)*ENNReal.ofReal Λ := by
    calc
      _ ≤ ∑' j : Fin (m+1), ((volume : Measure (Fin q → ℝ)).prod μ)
          (D.commonScaleOriginalSourcePhaseCell T cut δ B
            (phaseWalkPosition code j) (phaseWalkMomentum code j) R) := measure_iUnion_le _
      _ = ∑ j : Fin (m+1), ((volume : Measure (Fin q → ℝ)).prod μ)
          (D.commonScaleOriginalSourcePhaseCell T cut δ B
            (phaseWalkPosition code j) (phaseWalkMomentum code j) R) := tsum_fintype _
      _ ≤ ∑ _j : Fin (m+1), ENNReal.ofReal Λ := Finset.sum_le_sum (fun _ _ ↦ hcell _ _)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
  have hfin : (m+1:ℝ≥0∞)*ENNReal.ofReal Λ ≠ (⊤:ℝ≥0∞) :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hreal (code : PhaseWalkCode (2*q) m) :
      (((volume : Measure (Fin q → ℝ)).prod μ)
        (D.commonScaleOriginalSourceCandidate T cut δ B code R)).toReal ≤ 2*Λ*(m:ℝ) := by
    have hh := ENNReal.toReal_mono hfin (hbound code)
    rw [ENNReal.toReal_mul,ENNReal.toReal_add (by simp) (by simp),
      ENNReal.toReal_natCast,ENNReal.toReal_one,ENNReal.toReal_ofReal hΛ] at hh
    have hm' : (1:ℝ)≤m := by exact_mod_cast hm
    nlinarith
  have hp := Q.original_source_candidates_count_le_exp
    (Finset.univ : Finset (PhaseWalkCode (2*q) m))
    (fun code ↦ D.commonScaleOriginalSourceCandidate T cut δ B code R)
    (fun code _ ↦ D.measurableSet_commonScaleOriginalSourceCandidate hF hw T hcut δ hB code R)
    (fun code _ ↦ ne_top_of_le_ne_top hfin (hbound code))
    (by simpa only [Finset.card_univ] using card_phaseWalkCode_le_exp (2*q) m hm)
    (fun code _ ↦ hreal code) (K:=K)
  simpa only [Finset.mem_univ,iUnion_true,Nat.cast_mul,Nat.cast_ofNat] using hp

/-- A deterministic source-clock carrier keeps the original band and a
verified upper short-leg determinant; every actual supported contributor will
be shown to lie in this carrier by the original geometric short-leg bound. -/
def originalBirthSourceDetCarrier (T : Matrix (Fin q) (Fin q) ℝ)
    (cut : ℝ) (Band : Set ℝ) (Ddet : ℝ) : Set ℝ :=
  Band ∩ {a | (1+T*D.sourcePhaseLeg cut a*Tᵀ).det≤Ddet}

theorem measurableSet_originalBirthSourceDetCarrier
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {Band : Set ℝ} (hBand : MeasurableSet Band) (Ddet : ℝ) :
    MeasurableSet (D.originalBirthSourceDetCarrier T cut Band Ddet) :=
  hBand.inter (measurableSet_le
    (((continuous_const.add continuous_id).matrix_det.measurable :
      Measurable (fun A : Matrix (Fin q) (Fin q) ℝ ↦ (1+A).det)).comp
        (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)) measurable_const)


/-- The true divided birth phase cell has intensity of order `s/t`. Both its
physical dilation and its residue-rank density factor are retained. Restricting
the unchanged original clock band by a deterministic determinant carrier needs
no distributional claim about the subsequently selected edges. -/
theorem exists_commonScaleOriginalSourcePhaseCell_birth_intensity
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    (hq : 0<q) (R : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ {t s Ddet K : ℝ}, 0<t → t≤1 → 0<s → 0≤Ddet → 0≤K →
      ∀ {cut : ℝ}, cut ∈ Ioo D.lo D.hi →
      ∀ {Band : Set ℝ}, MeasurableSet Band → μ Band≤ENNReal.ofReal (K*t^G.rank*s) →
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      let δ := birthTrafficCoarseScale q t s
      let B := D.originalBirthSourceDetCarrier T cut Band Ddet
      ∀ z₀ p₀, ((volume : Measure (Fin q → ℝ)).prod μ)
        (D.commonScaleOriginalSourcePhaseCell T cut δ B z₀ p₀ R) ≤
          ENNReal.ofReal (C*Ddet*K*(s/t)) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  obtain ⟨C,hC,hcell⟩ := exists_birthBand_original_phaseCell_intensity_bound
    hG (by simpa only [Fintype.card_fin] using hq) R
  refine ⟨C,hC,?_⟩
  intro t s Ddet K ht ht1 hs hD hK cut hcut Band hBand hmass
  dsimp only
  intro z₀ p₀
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  let δ := birthTrafficCoarseScale q t s
  let B := D.originalBirthSourceDetCarrier T cut Band Ddet
  have hB : MeasurableSet B :=
    D.measurableSet_originalBirthSourceDetCarrier hF hw T hcut hBand Ddet
  have hb := hcell μ ht ht1 hs hD hK
    (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
    (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_commonScaleOriginalSourcePhaseCenter hF hw T hcut δ z₀ p₀)
    hB (fun a ha ↦ ha.2) ((measure_mono inter_subset_left).trans hmass)
  simpa only [commonScaleOriginalSourcePhaseCell,birthTrafficSpatialFrame,Fintype.card_fin]
    using hb


/-- Actual original source birth bands have a uniform density-rank bound. The
constant and outer collar are produced from the original density and pole. -/
theorem exists_original_left_birth_narrowBand_mass_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ρ : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) ρ v c.toReal)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η,
      originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ εmass Cmass : ℝ, 0 < εmass ∧ εmass < D.hi - D.lo ∧ 0 < Cmass ∧
      ∀ {ε : ℝ}, 0 < ε → ε < εmass → ∀ n j i : ℕ,
        i < dyadicBirthBandCount j →
        μ (D.originalLeftBirthNarrowClockBand ε n j i) ≤
          ENNReal.ofReal (Cmass * (birthDyadicShellScale ε n) ^ G.rank *
            birthDyadicElapsedScale ε n j) := by
  obtain ⟨εmass, Cmass, hεmass, hspan, hCmass, hmass⟩ :=
    D.exists_original_left_shell_band_mass_bound hF hw c hρ hρ0 hv hv0
      hdensity hη hRem hpole
  refine ⟨εmass, Cmass, hεmass, hspan, hCmass, ?_⟩
  intro ε hε hεlt n j i hi
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hbase := birthDyadicClockBand_base_bounds hε n j i hi
  change 0 < s ∧ s ≤ t ∧ t ≤ t + (i : ℝ) * (s / 8) ∧
    t + (i : ℝ) * (s / 8) + s / 8 ≤ 2 * t at hbase
  have h2t : 2 * t < εmass := by
    have hle : 2 * t ≤ ε := by
      dsimp [t]
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    exact hle.trans_lt hεlt
  have ha : D.lo + t ≤ D.lo + t + (i : ℝ) * (s / 8) := by
    linarith [hbase.2.2.1]
  have hb : D.lo + t + ((i : ℝ) + 1) * (s / 8) ≤ D.lo + 2 * t := by
    nlinarith [hbase.2.2.2]
  have hwidth :
      (D.lo + t + ((i : ℝ) + 1) * (s / 8)) -
        (D.lo + t + (i : ℝ) * (s / 8)) ≤ s := by
    nlinarith [hbase.1]
  have h := hmass ht h2t ha hb hwidth
  have hmeas : Measurable (fun x : ℝ ↦ x - S.level) :=
    measurable_id.sub_const (S.level : ℝ)
  rw [Measure.map_apply hmeas measurableSet_Ioc] at h
  simpa only [OriginalSeedConditionalMoments.originalLeftBirthNarrowClockBand,
    clockGridBand, Nat.cast_add, Nat.cast_one, t, s, Set.preimage] using h


/-- Original geometry and the original source density internally generate one
collar, genuine contractive windows and a uniform common-scale source-input
intensity budget. The same supported contributors lie in the deterministic
original-clock carriers; no selected-input Poisson hypothesis is used. -/
theorem exists_original_left_birth_commonScale_input_envelopes
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0<q)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (hgap : 0<gap)
    {ρden : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρden) (hρ0 : ∀x,0≤ρden x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x-S.level)) ρden v c.toReal)
    {basecap : ℝ} (hbasecap : 0<basecap) :
    ∃ G : Matrix (Fin q) (Fin q) ℝ, G.PosSemidef ∧
    ∃ ε : ℝ, 0<ε ∧ ε≤1 ∧ ∃ h : ℝ, 0<h ∧ ∃ cap : ℝ, 0<cap ∧
    ∃ ρ : ℝ, 0≤ρ ∧ ∃ Ddet : ℝ, 0<Ddet ∧
    ∀ Rcell : ℝ, ∃ Λ : ℝ, 0<Λ ∧
      let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
      ∀ n j i ell : ℕ, i<dyadicBirthBandCount j → ell<birthPhysicalClockWindowCount cap →
      let t := birthDyadicShellScale ε n
      let s := birthDyadicElapsedScale ε n j
      let δ := birthTrafficCoarseScale q t s
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      let cut := D.originalLeftBirthPhysicalClockReference ε cap n j i ell-S.level
      let width := birthPhysicalClockWindowWidth cap s
      let mobility := originalNormalizedClockMobility S w T (cut+S.level) width
      let B := D.originalBirthSourceDetCarrier T cut
        (D.originalLeftBirthNarrowClockBand ε n j i) Ddet
      IsUnit T.det ∧ cut∈Ioo D.lo D.hi ∧
      (∀r∈Icc (0:ℝ) 1,cut+width*r∈Ioo D.lo D.hi) ∧
      mobility 0=0 ∧ (∀r∈Icc (0:ℝ) 1,‖mobility r‖≤ρ) ∧
      (∀r∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,‖mobility r-mobility v‖≤ρ*|r-v|) ∧
      (∀r∈Icc (0:ℝ) 1,‖mobility r‖*(L:ℝ)≤(1/2:ℝ)) ∧
      (∀ (e : LegalMarkedPhysicalEdge q) clock,
        D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
          ((physicalPairAnchor e).2,clock)≠0 →
        e∈D.normalizedMomentumPhaseEligibleEdges T cut h ∧ e.1.2∈B ∧
        ∃r∈Icc (0:ℝ) 1,clock=cut+S.level+width*r) ∧
      ∀z₀ p₀,((volume : Measure (Fin q→ℝ)).prod μ)
        (D.commonScaleOriginalSourcePhaseCell T cut δ B z₀ p₀ Rcell)≤
          ENNReal.ofReal (Λ*(s/t)) := by
  obtain ⟨poleη,hpoleη,hpolespan,G,Rem,hG,hRem,hpole⟩ :=
    D.exists_original_kernel_left_positive_double_pole hF hw
  obtain ⟨εmass,Cmass,hεmass,_hεmassspan,hCmass,hmass⟩ :=
    D.exists_original_left_birth_narrowBand_mass_bound hF hw c hρ hρ0 hv hv0 hdensity
      hpoleη (hRem.continuousOn.continuousAt
        (Ioo_mem_nhds (by linarith) hpoleη)) hpole
  let ηsmall := min poleη (min εmass 1)
  have hηsmall : 0<ηsmall := lt_min hpoleη (lt_min hεmass zero_lt_one)
  have hηpole : ηsmall≤poleη := min_le_left _ _
  have hηmass : ηsmall≤εmass := (min_le_right _ _).trans (min_le_left _ _)
  have hηone : ηsmall≤1 := (min_le_right _ _).trans (min_le_right _ _)
  have hRemSmall : ContinuousOn Rem (Ioo (-ηsmall) ηsmall) :=
    hRem.continuousOn.mono (fun r hr ↦
      ⟨lt_of_le_of_lt (neg_le_neg hηpole) hr.1,hr.2.trans_le hηpole⟩)
  obtain ⟨ε,hε,hεη,h,hh,Bmob,hBmob,U,hU,hwindows⟩ :=
    D.exists_original_left_supported_contractive_birthWindows_sameResidue hF hw hbounds hgap
      hηsmall (hηpole.trans_lt hpolespan) hG hRemSmall
      (fun r hr ↦ hpole r ⟨hr.1,hr.2.trans_le hηpole⟩)
  have hεone : ε≤1 := hεη.le.trans hηone
  have hεmasslt : ε<εmass := hεη.trans_le hηmass
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let cap := commonPhysicalNormalizedWindowFraction basecap Bmob (L:ℝ)
  have hcap : 0<cap :=
    (commonPhysicalNormalizedWindowFraction_spec hbasecap hBmob L.coe_nonneg).1
  let ρ := cap*Bmob
  have hρ : 0≤ρ := mul_nonneg hcap.le hBmob
  obtain ⟨Ddet,hDdet,hdet⟩ :=
    exists_det_bound_of_posSemidef_scalar_upper (ι:=Fin q) U
  refine ⟨G,hG,ε,hε,hεone,h,hh,cap,hcap,ρ,hρ,Ddet,hDdet,?_⟩
  intro Rcell
  obtain ⟨Ccell,hCcell,hcell⟩ :=
    D.exists_commonScaleOriginalSourcePhaseCell_birth_intensity hF hw hG hq Rcell
  let Λ := Ccell*Ddet*Cmass
  have hΛ : 0<Λ := by dsimp [Λ]; positivity
  refine ⟨Λ,hΛ,?_⟩
  dsimp only
  intro n j i ell hi hell
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let δ := birthTrafficCoarseScale q t s
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
  let cut := ref-S.level
  let width := birthPhysicalClockWindowWidth cap s
  let B := D.originalBirthSourceDetCarrier T cut
    (D.originalLeftBirthNarrowClockBand ε n j i) Ddet
  have ht : 0<t := birthDyadicShellScale_pos hε n
  have hs : 0<s := (birthDyadicClockBand_base_bounds hε n j i hi).1
  have htε : 2*t≤ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have htone : t≤1 := by linarith
  rcases hwindows L basecap hbasecap n j i ell hi hell with
    ⟨hT,hcut,hclockRange,hzero,hbound,hLip,hsmall,helig⟩
  have hmass' : μ (D.originalLeftBirthNarrowClockBand ε n j i)≤
      ENNReal.ofReal (Cmass*t^G.rank*s) := hmass hε hεmasslt n j i hi
  have hcell' := hcell ht htone hs hDdet.le hCmass.le hcut
    (D.measurableSet_originalLeftBirthNarrowClockBand ε n j i) hmass'
  have hclockRange' : ∀r∈Icc (0:ℝ) 1,cut+width*r∈Ioo D.lo D.hi := by
    intro r hr
    have heq : cut+width*r=ref+width*r-S.level := by dsimp only [cut]; ring
    rw [heq]
    exact hclockRange r hr
  refine ⟨hT,hcut,hclockRange',?_,?_,?_,?_,?_,?_⟩
  · simpa only [cut,sub_add_cancel] using hzero
  · simpa only [cut,sub_add_cancel] using hbound
  · simpa only [cut,sub_add_cancel] using hLip
  · simpa only [cut,sub_add_cancel] using hsmall
  · intro e clock hf
    have he := helig e clock hf
    refine ⟨he.1,?_,?_⟩
    · exact ⟨D.originalSupportedLeftBirthPhysicalClockWeight_source_mem_band
        ε cap n j i ell _ hf,
        hdet _ (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut e.1.2) he.2.1⟩
    · obtain ⟨r,hr,heq⟩ := he.2.2
      exact ⟨r,hr,by simpa only [cut,sub_add_cancel] using heq⟩
  · exact hcell'


/-- A vertex covering the actual divided phase pair covers the unchanged
original source by the exact cell used in the original-input candidate count. -/
theorem commonScaleOriginalSourceCandidate_contains_edge_of_phase_cover
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (e : LegalMarkedPhysicalEdge q)
    (ha : e.1.2∈D.sourcePhaseClocks cut) (hB : e.1.2∈B)
    {R : ℝ} (hR : 0≤R) {m : ℕ} (code : PhaseWalkCode (2*q) m)
    (hcover : ∃j : Fin (m+1),
      ‖phasePairVector
        (commonScaleNormalizedMomentumNodePosition S w T δ (cut+S.level) e)
        (commonScaleNormalizedMomentumNodeValue S w T δ e)-phaseWalkVertex code j‖≤R) :
    e.1∈D.commonScaleOriginalSourceCandidate T cut δ B code R := by
  obtain ⟨j,hj⟩ := hcover
  apply mem_iUnion.mpr
  refine ⟨j,?_⟩
  exact D.commonScaleOriginalSourcePhaseCell_contains_edge hF hw T hcut hδ e ha hB hR
    (phaseWalkPosition code j) (phaseWalkMomentum code j)
    ((norm_position_sub_phaseWalkPosition_le _ _ code j).trans hj)
    ((norm_momentum_sub_phaseWalkMomentum_le _ _ code j).trans hj)

/-- The common-scale birth cell budget gives the simultaneous all-code
original-Poisson count estimate with its literal `s/t` rate still present. -/
theorem commonScaleOriginalSourceCandidates_count_le_exp_of_birth_rate
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (R : ℝ)
    {Λ t s : ℝ} (hΛ : 0≤Λ) (ht : 0<t) (hs : 0≤s)
    (hcell : ∀z₀ p₀,((volume : Measure (Fin q→ℝ)).prod μ)
      (D.commonScaleOriginalSourcePhaseCell T cut δ B z₀ p₀ R)≤ENNReal.ofReal (Λ*(s/t)))
    {kin : ℝ→ℝ→(Fin q→ℝ)→ℝ} {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    {m : ℕ} (hm : 1≤m) (K : ℝ) :
    (Q.law : Measure (LegalMarkedOptimalInputScene q)).real
      (⋃code : PhaseWalkCode (2*q) m,{scene | K*(m:ℝ)≤
        ((scene.2 : Measure (LegalColoredInputPoint q))
          (D.commonScaleOriginalSourceCandidate T cut δ B code R ×ˢ {0})).toReal})≤
      Real.exp (-(K-(3*(2*q:ℝ)+(3:ℝ)^(2*q))-2*(Λ*(s/t))*(Real.exp 1-1))*(m:ℝ)) :=
  D.commonScaleOriginalSourceCandidates_count_le_exp hF hw T hcut δ hB R
    (mul_nonneg hΛ (div_nonneg hs ht.le)) hcell Q hm K

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
