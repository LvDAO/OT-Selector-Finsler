import OTSelector.Reconstruction.OriginalMinimizerDyadicTrafficNorm
import OTSelector.Reconstruction.OriginalMarkedCountSelectedEnvelope
import OTSelector.Reconstruction.FinslerOriginalNormalizedPhaseTargetContainment
import OTSelector.Reconstruction.FinslerOriginalReflectedShellBandMass
import OTSelector.Reconstruction.OriginalCompletePathGoodEventLtwo

/-! Actual right-endpoint common-scale traffic uses the original target density,
the same right pole and normalizer, and the positive target compliance leg. -/
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
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "q" => finrank ℝ S.covector.ker

/-- The physical center of a cell in the actually divided phase coordinates. -/
def commonScaleOriginalTargetPhaseCenter (T : Matrix (Fin q) (Fin q) ℝ)
    (cut δ : ℝ) (z₀ p₀ : Fin q → ℝ) (a : ℝ) : Fin q → ℝ :=
  (δ • T⁻¹) *ᵥ (z₀+(T*D.targetPhaseLeg cut a*Tᵀ)*ᵥp₀)

/-- Exact unchanged original-target input cell in the independent common scale. -/
def commonScaleOriginalTargetPhaseCell (T : Matrix (Fin q) (Fin q) ℝ)
    (cut δ : ℝ) (B : Set ℝ) (z₀ p₀ : Fin q → ℝ) (R : ℝ) :
    Set (LegalMarkedPhysicalPoint q) :=
  markedPhaseSourceCell (δ • T⁻¹) (fun a ↦ T*D.targetPhaseLeg cut a*Tᵀ)
    (D.commonScaleOriginalTargetPhaseCenter T cut δ z₀ p₀) B R

theorem measurable_commonScaleOriginalTargetPhaseCenter
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (δ : ℝ) (z₀ p₀ : Fin q → ℝ) :
    Measurable (D.commonScaleOriginalTargetPhaseCenter T cut δ z₀ p₀) :=
  ((δ • T⁻¹).mulVecLin.toContinuousLinearMap).continuous.measurable.comp
    (measurable_const.add ((completePathMatrixApply p₀).continuous.measurable.comp
      (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)))

theorem measurableSet_commonScaleOriginalTargetPhaseCell
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (z₀ p₀ : Fin q → ℝ) (R : ℝ) :
    MeasurableSet (D.commonScaleOriginalTargetPhaseCell T cut δ B z₀ p₀ R) :=
  measurableSet_markedPhaseSourceCell _
    (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
    (D.measurable_commonScaleOriginalTargetPhaseCenter hF hw T hcut δ z₀ p₀) hB R

/-- The same actual edge gives an original target in the divided phase cell,
with physical frame δ T inverse and identical compliance, at the same radius. -/
theorem commonScaleOriginalTargetPhaseCell_contains_edge
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (e : LegalMarkedPhysicalEdge q)
    (ha : e.1.2 ∈ D.sourcePhaseClocks cut) (hb : e.2.2 ∈ D.targetPhaseClocks cut)
    (hB : e.2.2 ∈ B)
    {R : ℝ} (hR : 0≤R) (z₀ p₀ : Fin q → ℝ)
    (hz : ‖commonScaleNormalizedMomentumNodePosition S w T δ (cut+S.level) e-z₀‖≤R)
    (hp : ‖commonScaleNormalizedMomentumNodeValue S w T δ e-p₀‖≤R) :
    e.2 ∈ D.commonScaleOriginalTargetPhaseCell T cut δ B z₀ p₀ R := by
  have hL : IsUnit (δ • T⁻¹).det := by
    rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hδ.ne')).mul
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
  have hpneg : ‖-(commonScaleNormalizedMomentumNodeValue S w T δ e-p₀)‖≤R := by
    simpa only [norm_neg] using hp
  have hm := mk_add_mulVec_sub_mem_markedPhaseSourceCell hL
    (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
    (D.commonScaleOriginalTargetPhaseCenter T cut δ z₀ p₀) hB hR hz hpneg
  have hs := D.commonScaleNormalizedMomentumNode_target_identity hF hw T hδ hcut e
    ha hb
  have heq : D.commonScaleOriginalTargetPhaseCenter T cut δ z₀ p₀ e.2.2 +
      (δ • T⁻¹) *ᵥ
        ((commonScaleNormalizedMomentumNodePosition S w T δ (cut+S.level) e-z₀)-
          (T*D.targetPhaseLeg cut e.2.2*Tᵀ)*ᵥ
            (-(commonScaleNormalizedMomentumNodeValue S w T δ e-p₀))) = e.2.1 := by
    rw [hs]
    dsimp only [commonScaleOriginalTargetPhaseCenter]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_neg]
    abel
  rwa [heq] at hm

/-- One literal finite code in the truly common-divided original target cells. -/
def commonScaleOriginalTargetCandidate (T : Matrix (Fin q) (Fin q) ℝ)
    (cut δ : ℝ) (B : Set ℝ) {m : ℕ} (code : PhaseWalkCode (2*q) m) (R : ℝ) :
    Set (LegalMarkedPhysicalPoint q) :=
  ⋃ j : Fin (m+1), D.commonScaleOriginalTargetPhaseCell T cut δ B
    (phaseWalkPosition code j) (phaseWalkMomentum code j) R

theorem measurableSet_commonScaleOriginalTargetCandidate
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) {m : ℕ}
    (code : PhaseWalkCode (2*q) m) (R : ℝ) :
    MeasurableSet (D.commonScaleOriginalTargetCandidate T cut δ B code R) :=
  MeasurableSet.iUnion (fun _ ↦ D.measurableSet_commonScaleOriginalTargetPhaseCell
    hF hw T hcut δ hB _ _ R)

/-- Full original input counts simultaneously control every common-scale
candidate. The cell intensity bound concerns the original input, before any
matching-adaptive candidate or contributor is selected. -/
theorem commonScaleOriginalTargetCandidates_count_le_exp
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (R : ℝ)
    {Λ : ℝ} (hΛ : 0≤Λ)
    (hcell : ∀ z₀ p₀, ((volume : Measure (Fin q → ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ B z₀ p₀ R) ≤ ENNReal.ofReal Λ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    {m : ℕ} (hm : 1≤m) (K : ℝ) :
    (Q.law : Measure (LegalMarkedOptimalInputScene q)).real
      (⋃ code : PhaseWalkCode (2*q) m, {scene | K*(m:ℝ) ≤
        ((scene.2 : Measure (LegalColoredInputPoint q))
          (D.commonScaleOriginalTargetCandidate T cut δ B code R ×ˢ {1})).toReal}) ≤
      Real.exp (-(K-(3*(2*q:ℝ)+(3:ℝ)^(2*q))-2*Λ*(Real.exp 1-1))*(m:ℝ)) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have hbound (code : PhaseWalkCode (2*q) m) :
      ((volume : Measure (Fin q → ℝ)).prod ν)
        (D.commonScaleOriginalTargetCandidate T cut δ B code R) ≤
        (m+1:ℝ≥0∞)*ENNReal.ofReal Λ := by
    calc
      _ ≤ ∑' j : Fin (m+1), ((volume : Measure (Fin q → ℝ)).prod ν)
          (D.commonScaleOriginalTargetPhaseCell T cut δ B
            (phaseWalkPosition code j) (phaseWalkMomentum code j) R) := measure_iUnion_le _
      _ = ∑ j : Fin (m+1), ((volume : Measure (Fin q → ℝ)).prod ν)
          (D.commonScaleOriginalTargetPhaseCell T cut δ B
            (phaseWalkPosition code j) (phaseWalkMomentum code j) R) := tsum_fintype _
      _ ≤ ∑ _j : Fin (m+1), ENNReal.ofReal Λ := Finset.sum_le_sum (fun _ _ ↦ hcell _ _)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
  have hfin : (m+1:ℝ≥0∞)*ENNReal.ofReal Λ ≠ (⊤:ℝ≥0∞) :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hreal (code : PhaseWalkCode (2*q) m) :
      (((volume : Measure (Fin q → ℝ)).prod ν)
        (D.commonScaleOriginalTargetCandidate T cut δ B code R)).toReal ≤ 2*Λ*(m:ℝ) := by
    have hh := ENNReal.toReal_mono hfin (hbound code)
    rw [ENNReal.toReal_mul,ENNReal.toReal_add (by simp) (by simp),
      ENNReal.toReal_natCast,ENNReal.toReal_one,ENNReal.toReal_ofReal hΛ] at hh
    have hm' : (1:ℝ)≤m := by exact_mod_cast hm
    nlinarith
  have hp := Q.original_target_candidates_count_le_exp
    (Finset.univ : Finset (PhaseWalkCode (2*q) m))
    (fun code ↦ D.commonScaleOriginalTargetCandidate T cut δ B code R)
    (fun code _ ↦ D.measurableSet_commonScaleOriginalTargetCandidate hF hw T hcut δ hB code R)
    (fun code _ ↦ ne_top_of_le_ne_top hfin (hbound code))
    (by simpa only [Finset.card_univ] using card_phaseWalkCode_le_exp (2*q) m hm)
    (fun code _ ↦ hreal code) (K:=K)
  simpa only [Finset.mem_univ,iUnion_true,Nat.cast_mul,Nat.cast_ofNat] using hp

/-- A deterministic target-clock carrier keeps the original band and a
verified upper short-leg determinant; every actual supported contributor will
be shown to lie in this carrier by the original geometric short-leg bound. -/
def originalBirthTargetDetCarrier (T : Matrix (Fin q) (Fin q) ℝ)
    (cut : ℝ) (Band : Set ℝ) (Ddet : ℝ) : Set ℝ :=
  Band ∩ {a | (1+T*D.targetPhaseLeg cut a*Tᵀ).det≤Ddet}

theorem measurableSet_originalBirthTargetDetCarrier
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {Band : Set ℝ} (hBand : MeasurableSet Band) (Ddet : ℝ) :
    MeasurableSet (D.originalBirthTargetDetCarrier T cut Band Ddet) :=
  hBand.inter (measurableSet_le
    (((continuous_const.add continuous_id).matrix_det.measurable :
      Measurable (fun A : Matrix (Fin q) (Fin q) ℝ ↦ (1+A).det)).comp
        (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)) measurable_const)


/-- The true divided birth phase cell has intensity of order `s/t`. Both its
physical dilation and its residue-rank density factor are retained. Restricting
the unchanged original clock band by a deterministic determinant carrier needs
no distributional claim about the subsequently selected edges. -/
theorem exists_commonScaleOriginalTargetPhaseCell_birth_intensity
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    (hq : 0<q) (R : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ {t s Ddet K : ℝ}, 0<t → t≤1 → 0<s → 0≤Ddet → 0≤K →
      ∀ {cut : ℝ}, cut ∈ Ioo D.lo D.hi →
      ∀ {Band : Set ℝ}, MeasurableSet Band → ν Band≤ENNReal.ofReal (K*t^G.rank*s) →
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      let δ := birthTrafficCoarseScale q t s
      let B := D.originalBirthTargetDetCarrier T cut Band Ddet
      ∀ z₀ p₀, ((volume : Measure (Fin q → ℝ)).prod ν)
        (D.commonScaleOriginalTargetPhaseCell T cut δ B z₀ p₀ R) ≤
          ENNReal.ofReal (C*Ddet*K*(s/t)) := by
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨C,hC,hcell⟩ := exists_birthBand_original_phaseCell_intensity_bound
    hG (by simpa only [Fintype.card_fin] using hq) R
  refine ⟨C,hC,?_⟩
  intro t s Ddet K ht ht1 hs hD hK cut hcut Band hBand hmass
  dsimp only
  intro z₀ p₀
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  let δ := birthTrafficCoarseScale q t s
  let B := D.originalBirthTargetDetCarrier T cut Band Ddet
  have hB : MeasurableSet B :=
    D.measurableSet_originalBirthTargetDetCarrier hF hw T hcut hBand Ddet
  have hb := hcell ν ht ht1 hs hD hK
    (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
    (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_commonScaleOriginalTargetPhaseCenter hF hw T hcut δ z₀ p₀)
    hB (fun a ha ↦ ha.2) ((measure_mono inter_subset_left).trans hmass)
  simpa only [commonScaleOriginalTargetPhaseCell,birthTrafficSpatialFrame,Fintype.card_fin]
    using hb


/-- Actual original target birth bands have a uniform density-rank bound. The
constant and outer collar are produced from the original density and pole. -/
theorem exists_original_right_birth_narrowBand_mass_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ρ : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ ↦ x - S.level)) ρ v c.toReal)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η,
      originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ εmass Cmass : ℝ, 0 < εmass ∧ εmass < D.hi - D.lo ∧ 0 < Cmass ∧
      ∀ {ε : ℝ}, 0 < ε → ε < εmass → ∀ n j i : ℕ,
        i < dyadicBirthBandCount j →
        ν (D.originalRightBirthNarrowClockBand ε n j i) ≤
          ENNReal.ofReal (Cmass * (birthDyadicShellScale ε n) ^ G.rank *
            birthDyadicElapsedScale ε n j) := by
  obtain ⟨εmass, Cmass, hεmass, hspan, hCmass, hmass⟩ :=
    D.exists_original_right_reflected_shell_band_mass_bound hF hw c hρ hρ0 hv hv0
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
  have ha : D.hi - 2 * t ≤ D.hi - (t + ((i : ℝ) + 1) * (s / 8)) := by
    nlinarith [hbase.2.2.2]
  have hb : D.hi - (t + (i : ℝ) * (s / 8)) ≤ D.hi - t := by
    linarith [hbase.2.2.1]
  have hwidth : (D.hi - (t + (i : ℝ) * (s / 8))) -
      (D.hi - (t + ((i : ℝ) + 1) * (s / 8))) ≤ s := by
    nlinarith [hbase.1]
  have h := hmass ht h2t ha hb hwidth
  have hmeas : Measurable (fun x : ℝ ↦ x - S.level) :=
    measurable_id.sub_const (S.level : ℝ)
  rw [Measure.map_apply hmeas measurableSet_Ico] at h
  simpa only [OriginalSeedConditionalMoments.originalRightBirthNarrowClockBand, Nat.cast_add,
    Nat.cast_one, t, s, Set.preimage] using h


/-- The SAME explicit original pole and density generate uniform true target
cell intensities for every later smaller collar and every interior common cut.
The determinant certificate is returned with the constant, so actual supported
contributors can consume the same short-leg bound without reselecting data. -/
theorem exists_original_right_samePole_shrinkable_commonScale_intensity
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 0<q)
    {poleRadius : ℝ} (hpoleRadius : 0<poleRadius)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ→Matrix (Fin q) (Fin q) ℝ} (hRem : ContinuousAt Rem 0)
    (hpole : ∀r∈Ioo 0 poleRadius,
      originalSeedKernel S w (D.hi-r)=(r^2)⁻¹•G+Rem r)
    {ρden : M→ℝ} {v : M→E→ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρden) (hρ0 : ∀x,0≤ρden x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensity : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ ↦x-S.level)) ρden v c.toReal)
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
      ((volume : Measure (Fin q→ℝ)).prod ν)
        (D.commonScaleOriginalTargetPhaseCell T cut δ
          (D.originalBirthTargetDetCarrier T cut
            (D.originalRightBirthNarrowClockBand ε n j i) Ddet) z₀ p₀ Rcell)≤
        ENNReal.ofReal (Λ*(s/t)) := by
  obtain ⟨εmass,Cmass,hεmass,_hεspan,hCmass,hmass⟩ :=
    D.exists_original_right_birth_narrowBand_mass_bound hF hw c hρ hρ0 hv hv0 hdensity
      hpoleRadius hRem hpole
  obtain ⟨Ddet,hDdet,hdet⟩ :=
    exists_det_bound_of_posSemidef_scalar_upper (ι:=Fin q) U₀
  let ε₀ := min εmass 1
  refine ⟨ε₀,Ddet,lt_min hεmass zero_lt_one,min_le_right _ _,hDdet,hdet,?_⟩
  intro Rcell
  obtain ⟨Ccell,hCcell,hcell⟩ :=
    D.exists_commonScaleOriginalTargetPhaseCell_birth_intensity hF hw hG hq Rcell
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
    (D.measurableSet_originalRightBirthNarrowClockBand ε n j i)
    (hmass hε hεmasslt n j i hi) z₀ p₀


/-- Deterministic phase centers preserve the unchanged original input intensity. -/
theorem commonScaleOriginalTargetPhaseCell_intensity_eq_zeroCenter
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {δ : ℝ} (hδ : 0 < δ)
    {B : Set ℝ} (hB : MeasurableSet B) (z₀ p₀ : Fin q → ℝ) (R : ℝ) :
    ((volume : Measure (Fin q → ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ B z₀ p₀ R) =
      ((volume : Measure (Fin q → ℝ)).prod ν)
        (D.commonScaleOriginalTargetPhaseCell T cut δ B 0 0 R) := by
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have hL : IsUnit (δ • T⁻¹).det := by
    rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hδ.ne')).mul
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
  unfold commonScaleOriginalTargetPhaseCell
  rw [prod_volume_markedPhaseSourceCell hL
    (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
    (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_commonScaleOriginalTargetPhaseCenter hF hw T hcut δ z₀ p₀) hB ν R,
    prod_volume_markedPhaseSourceCell hL
    (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
    (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_commonScaleOriginalTargetPhaseCenter hF hw T hcut δ 0 0) hB ν R]

/-- At fixed actual frame and clock carrier, original intensity is homogeneous
of degree q in the radius. -/
theorem commonScaleOriginalTargetPhaseCell_intensity_scale
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {δ : ℝ} (hδ : 0 < δ)
    {B : Set ℝ} (hB : MeasurableSet B) {R : ℝ} (hR : 0 ≤ R) :
    ((volume : Measure (Fin q → ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ B 0 0 R) =
      ENNReal.ofReal R ^ q * ((volume : Measure (Fin q → ℝ)).prod ν)
        (D.commonScaleOriginalTargetPhaseCell T cut δ B 0 0 1) := by
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have hL : IsUnit (δ • T⁻¹).det := by
    rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hδ.ne')).mul
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
  simpa only [commonScaleOriginalTargetPhaseCell, Fintype.card_fin] using
    prod_volume_markedPhaseSourceCell_radius_scale hL
      (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
      (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
      (D.measurable_commonScaleOriginalTargetPhaseCenter hF hw T hcut δ 0 0) hB ν hR

/-- The actual global radius has exact polynomial original intensity in real form. -/
theorem commonScaleOriginalTargetGlobalEnvelope_intensity_real
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {δ : ℝ} (hδ : 0 < δ)
    {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (((volume : Measure (Fin q → ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ B 0 0 (2 * (m : ℝ) + r))).toReal =
      (2 * (m : ℝ) + r) ^ q *
        (((volume : Measure (Fin q → ℝ)).prod ν)
          (D.commonScaleOriginalTargetPhaseCell T cut δ B 0 0 1)).toReal := by
  rw [D.commonScaleOriginalTargetPhaseCell_intensity_scale hF hw T hcut hδ hB (by positivity),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]


/-- The same true unit-cell intensity controls every radius and center. -/
theorem commonScaleOriginalTargetPhaseCell_intensity_le_of_unit
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (hB : MeasurableSet B) {Λ R : ℝ} (_hΛ : 0≤Λ) (hR : 0≤R)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ B 0 0 1)≤ENNReal.ofReal Λ)
    (z₀ p₀ : Fin q→ℝ) :
    ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ B z₀ p₀ R)≤ENNReal.ofReal (R^q*Λ) := by
  rw [D.commonScaleOriginalTargetPhaseCell_intensity_eq_zeroCenter hF hw T hcut hδ hB,
    D.commonScaleOriginalTargetPhaseCell_intensity_scale hF hw T hcut hδ hB hR]
  calc
    _ ≤ ENNReal.ofReal R^q*ENNReal.ofReal Λ := by
      simpa only [mul_comm] using mul_le_mul_left hunit (ENNReal.ofReal R^q)
    _ = _ := by rw [←ENNReal.ofReal_pow hR,←ENNReal.ofReal_mul (pow_nonneg hR _)]

/-- The all-code event is fixed before any actual adaptive current is selected. -/
def commonScaleOriginalTargetPhaseBadEvent
    (T : Matrix (Fin q) (Fin q) ℝ) (cut δ : ℝ) (B : Set ℝ)
    (m : ℕ) (r K : ℝ) : Set (LegalMarkedOptimalInputScene q) :=
  ⋃code : PhaseWalkCode (2*q) m,{scene | K*(m:ℝ)≤
    ((scene.2 : Measure (LegalColoredInputPoint q))
      (D.commonScaleOriginalTargetCandidate T cut δ B code (r+2) ×ˢ {1})).toReal}

def commonScaleOriginalTargetGlobalEnvelope
    (T : Matrix (Fin q) (Fin q) ℝ) (cut δ : ℝ) (B : Set ℝ)
    (m : ℕ) (r : ℝ) : Set (LegalMarkedPhysicalPoint q) :=
  D.commonScaleOriginalTargetPhaseCell T cut δ B 0 0 (2*(m:ℝ)+r)

def commonScaleOriginalTargetGlobalCount
    (T : Matrix (Fin q) (Fin q) ℝ) (cut δ : ℝ) (B : Set ℝ)
    (m : ℕ) (r : ℝ) (scene : LegalMarkedOptimalInputScene q) : ℝ :=
  ((scene.2 : Measure (LegalColoredInputPoint q))
    (D.commonScaleOriginalTargetGlobalEnvelope T cut δ B m r ×ˢ {1})).toReal

theorem measurableSet_commonScaleOriginalTargetPhaseBadEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) (r K : ℝ) :
    MeasurableSet (D.commonScaleOriginalTargetPhaseBadEvent T cut δ B m r K) := by
  apply MeasurableSet.iUnion
  intro code
  exact measurableSet_le measurable_const
    (((Measure.measurable_coe
      ((D.measurableSet_commonScaleOriginalTargetCandidate hF hw T hcut δ hB code (r+2)).prod
        (measurableSet_singleton 1))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal)

theorem measurableSet_commonScaleOriginalTargetGlobalEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) (r : ℝ) :
    MeasurableSet (D.commonScaleOriginalTargetGlobalEnvelope T cut δ B m r) :=
  D.measurableSet_commonScaleOriginalTargetPhaseCell hF hw T hcut δ hB 0 0 _

theorem measurable_commonScaleOriginalTargetGlobalCount
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi)
    (δ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) (r : ℝ) :
    Measurable (D.commonScaleOriginalTargetGlobalCount T cut δ B m r) :=
  ((Measure.measurable_coe
    ((D.measurableSet_commonScaleOriginalTargetGlobalEnvelope hF hw T hcut δ hB m r).prod
      (measurableSet_singleton 1))).comp
    (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal

/-- The unchanged original Poisson envelope has a uniform polynomial fourth
moment in the genuine divided frame and deterministic original clock carrier. -/
theorem commonScaleOriginalTargetGlobalCount_fourth_moment
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (hB : MeasurableSet B) {Λ r : ℝ} (hΛ : 0≤Λ) (hr : 0≤r)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ B 0 0 1)≤ENNReal.ofReal Λ)
    {kin : ℝ→ℝ→(Fin q→ℝ)→ℝ} {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) (m : ℕ) :
    (∀ᵐ (scene : LegalMarkedOptimalInputScene q) ∂(Q.law : Measure (LegalMarkedOptimalInputScene
      q)),
      (scene.2 : Measure (LegalColoredInputPoint q))
        (D.commonScaleOriginalTargetGlobalEnvelope T cut δ B m r ×ˢ {1})<(∞:ℝ≥0∞)) ∧
    Integrable (fun scene ↦ (D.commonScaleOriginalTargetGlobalCount T cut δ B m r scene)^4)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫scene,(D.commonScaleOriginalTargetGlobalCount T cut δ B m r scene)^4
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤
      192*Real.exp (Real.exp 1-1)*(1+((2*(m:ℝ)+r)^q*Λ)^4) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have hi := D.commonScaleOriginalTargetPhaseCell_intensity_le_of_unit hF hw T hcut hδ hB
    hΛ (show 0≤2*(m:ℝ)+r by positivity) hunit 0 0
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi
  have h4 := Q.original_target_fourth_moment
    (D.measurableSet_commonScaleOriginalTargetGlobalEnvelope hF hw T hcut δ hB m r) hfin
  refine ⟨h4.1,h4.2.1,h4.2.2.trans ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
  rw [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (by positivity) _) hΛ)] at hreal
  gcongr
  exact hreal

/-- A vertex covering the actual divided phase pair covers the unchanged
original target by the exact cell used in the original-input candidate count. -/
theorem commonScaleOriginalTargetCandidate_contains_edge_of_phase_cover
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (e : LegalMarkedPhysicalEdge q)
    (ha : e.1.2∈D.sourcePhaseClocks cut) (hb : e.2.2∈D.targetPhaseClocks cut)
    (hB : e.2.2∈B)
    {R : ℝ} (hR : 0≤R) {m : ℕ} (code : PhaseWalkCode (2*q) m)
    (hcover : ∃j : Fin (m+1),
      ‖phasePairVector
        (commonScaleNormalizedMomentumNodePosition S w T δ (cut+S.level) e)
        (commonScaleNormalizedMomentumNodeValue S w T δ e)-phaseWalkVertex code j‖≤R) :
    e.2∈D.commonScaleOriginalTargetCandidate T cut δ B code R := by
  obtain ⟨j,hj⟩ := hcover
  apply mem_iUnion.mpr
  refine ⟨j,?_⟩
  exact D.commonScaleOriginalTargetPhaseCell_contains_edge hF hw T hcut hδ e ha hb hB hR
    (phaseWalkPosition code j) (phaseWalkMomentum code j)
    ((norm_position_sub_phaseWalkPosition_le _ _ code j).trans hj)
    ((norm_momentum_sub_phaseWalkMomentum_le _ _ code j).trans hj)

/-- Every actual edge near an admissible common-scale phase curve has its
unchanged original target in the radius-2m+r cell, on the same clock carrier. -/
theorem commonScaleOriginalTargetPhaseCell_contains_edge_of_phase_tube
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {δ : ℝ} (hδ : 0 < δ)
    {B : Set ℝ} (e : LegalMarkedPhysicalEdge q)
    (ha : e.1.2 ∈ D.sourcePhaseClocks cut) (hb : e.2.2 ∈ D.targetPhaseClocks cut)
    (hB : e.2.2 ∈ B)
    {m : ℕ} (γ : ℝ → Fin (2 * q) → ℝ) (hroot : ‖γ 0‖ ≤ (m : ℝ))
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ s - γ t‖ ≤ (m : ℝ) * |s - t|)
    {r : ℝ} (hr : 0 ≤ r)
    (htube : ∃ t ∈ Icc (0 : ℝ) 1,
      ‖phasePairVector
        (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e)
        (commonScaleNormalizedMomentumNodeValue S w T δ e) - γ t‖ ≤ r) :
    e.2 ∈ D.commonScaleOriginalTargetPhaseCell T cut δ B 0 0 (2 * (m : ℝ) + r) := by
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
  exact D.commonScaleOriginalTargetPhaseCell_contains_edge hF hw T hcut hδ e ha hb hB
    (by positivity) 0 0
    (by simpa only [sub_zero] using (norm_position_le_phasePairVector _ _).trans hphase)
    (by simpa only [sub_zero] using (norm_momentum_le_phasePairVector _ _).trans hphase)


/-- The SAME original attained minimizer's actual traffic is dominated by the
unchanged original target count at its genuinely divided canonical scale. The
target clock carrier is retained before applying the original input marginal. -/
theorem ae_original_minimizer_commonScale_traffic_le_targetGlobalCount
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
      (D.commonScaleOriginalTargetPhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
    ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f
        scene).toReal≤
        Bedge*D.commonScaleOriginalTargetGlobalCount T cut δ Band (k scene) radius scene := by
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
    (D.commonScaleOriginalTargetGlobalCount_fourth_moment
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
  let W := D.commonScaleOriginalTargetGlobalEnvelope T cut δ Band m radius
  have hW : MeasurableSet W :=
    D.measurableSet_commonScaleOriginalTargetGlobalEnvelope hF hw T hcut δ hBand m radius
  have hV : MeasurableSet V := (scene.1.1 : Measure (LegalMarkedPhysicalEdge
    q)).isClosed_support.measurableSet.inter
    (measurableSet_legalMarkedCompletePathContributors d hd hη hf)
  have hcurve := D.commonScaleNormalizedCanonicalCurveIntegerScale_covers
    T cut h L R hsmall hδpos hρ hA hR hRLip scene
  have htarget : ∀e∈V,e.2∈W := by
    intro e he
    obtain ⟨r,hr,_hηne,hfne,hpath⟩ :=
      original_completePathEdgeTraffic_ne_zero_exists_affineWindow_contributor S w η f T
        (cut+S.level) ell e he.2 hclock hηwindow
    have heE := hmask e _ hfne
    have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hsFull.simple_edges).1
    have heN := (mem_support_originalCountingNodeRestriction_iff
      (0:LegalMarkedPhysicalEdge q) scene.1.1 hcount
      (D.normalizedMomentumPhaseEligibleEdges T cut h) e).mpr ⟨he.1,heE.1⟩
    exact D.commonScaleOriginalTargetPhaseCell_contains_edge_of_phase_tube
      hF hw T hcut hδpos e heE.1.1 heE.1.2.1 heE.2
      (D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ scene)
      (hcurve.1 0 (by norm_num)) hcurve.2 hradius ⟨r,hr,hsTube r hr e heN a hpath⟩
  have hc : (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)) V≤
      (scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{1}) := by
    calc
      _ ≤ (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Prod.snd ⁻¹' W) := measure_mono htarget
      _ = (scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{1}) := by
        rw [←Measure.snd_apply hW,hsFull.target_marginal,legalInputColorMeasure_apply_prod _ _ _ hW]
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


/-- Every literal finite common-scale original-input candidate has a finite
count almost surely, before the actual minimizer selects any of its codes. -/
theorem ae_commonScaleOriginalTargetCandidate_count_finite
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {Band : Set ℝ} (hBand : MeasurableSet Band) {Λ R : ℝ} (hΛ : 0≤Λ) (hR : 0≤R)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
    {kin : ℝ→ℝ→(Fin q→ℝ)→ℝ} {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) :
    ∀ᵐ(scene : LegalMarkedOptimalInputScene q) ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀m : ℕ,∀code : PhaseWalkCode (2*q) m,
        (scene.2 : Measure (LegalColoredInputPoint q))
          (D.commonScaleOriginalTargetCandidate T cut δ Band code R ×ˢ {1})<(∞:ℝ≥0∞) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro code
  have hfin : ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetCandidate T cut δ Band code R)≠(∞:ℝ≥0∞) := by
    have hsum : (∑'j : Fin (m+1),((volume : Measure (Fin q→ℝ)).prod ν)
        (D.commonScaleOriginalTargetPhaseCell T cut δ Band
          (phaseWalkPosition code j) (phaseWalkMomentum code j) R))≠(∞:ℝ≥0∞) := by
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.mpr (fun j _ ↦ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (D.commonScaleOriginalTargetPhaseCell_intensity_le_of_unit hF hw T hcut hδ hBand hΛ hR
          hunit _ _))
    exact ne_top_of_le_ne_top hsum (measure_iUnion_le _)
  exact (Q.original_target_fourth_moment
    (D.measurableSet_commonScaleOriginalTargetCandidate hF hw T hcut δ hBand code R) hfin).1


/-- Right common-scale selected bad counts inherit the shared original-color
statistical engine. The intensity and all-code probabilities are derived from
the true target cells here, with no finished summability premise. -/
theorem commonScaleOriginalTarget_selected_bad_memLp_two_le
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) {δ : ℝ} (hδ : 0<δ)
    {B : Set ℝ} (hB : MeasurableSet B) {Λ r : ℝ} (hΛ : 0≤Λ) (hr : 0≤r)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ B 0 0 1)≤ENNReal.ofReal Λ)
    {kin : ℝ→ℝ→(Fin q→ℝ)→ℝ} {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) {K : ℝ}
    (hK : commonScaleSourceCountThreshold q Λ r≤K)
    {k : LegalMarkedOptimalInputScene q→ℕ} (hk : Measurable k)
    {f : LegalMarkedOptimalInputScene q→ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0≤C)
    (hdom : ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      scene∈D.commonScaleOriginalTargetPhaseBadEvent T cut δ B (k scene) r K→
      |f scene|≤C*|D.commonScaleOriginalTargetGlobalCount T cut δ B (k scene) r scene|) :
    let err := {scene |1≤k scene∧
      scene∈D.commonScaleOriginalTargetPhaseBadEvent T cut δ B (k scene) r K}.indicator f
    let budget : ℝ := C ^ 2 * commonScaleSourceEnvelopeBudget q Λ r *
      Real.exp (-(K - commonScaleSourceCountThreshold q Λ r) / 2)
    MemLp err 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫scene,(err scene)^2 ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤budget ∧
    eLpNorm err 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))≤
      ENNReal.ofReal (Real.sqrt budget) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  apply Q.originalMarkedCount_selected_bad_memLp_two_le (1:Fin 2)
    (D.commonScaleOriginalTargetGlobalEnvelope T cut δ B · r)
    (D.commonScaleOriginalTargetPhaseBadEvent T cut δ B · r K)
    (fun m ↦ D.measurableSet_commonScaleOriginalTargetGlobalEnvelope hF hw T hcut δ hB m r)
    (fun m ↦ D.measurableSet_commonScaleOriginalTargetPhaseBadEvent hF hw T hcut δ hB m r K)
    hΛ hr ?_ ?_ hK hk hf hC hdom
  · intro m _hm
    simpa only [originalMarkedColorLaw, show (1:Fin 2) ≠ 0 by decide, ite_false,
      commonScaleOriginalTargetGlobalEnvelope] using
      D.commonScaleOriginalTargetPhaseCell_intensity_le_of_unit hF hw T hcut hδ hB
        hΛ (show 0≤2*(m:ℝ)+r by positivity) hunit 0 0
  · intro m hm
    exact D.commonScaleOriginalTargetCandidates_count_le_exp hF hw T hcut δ hB (r+2)
      (mul_nonneg (pow_nonneg (by positivity) _) hΛ)
      (fun z₀ p₀ ↦ D.commonScaleOriginalTargetPhaseCell_intensity_le_of_unit
        hF hw T hcut hδ hB hΛ (by positivity) hunit z₀ p₀) Q hm K

/-- The actual attained minimizer's selected-current bad traffic has an
explicit uniform original-input eLpNorm budget in the true common-scale frame.
Its envelope domination is derived from the same actual occupied edges. -/
theorem original_minimizer_commonScale_target_selected_bad_traffic_memLp_two_le
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
      commonScaleSourceCountThreshold q Λ radius≤K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
    let traffic := fun scene ↦
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f
        scene).toReal
    let err := {scene |1≤k scene∧
      scene∈D.commonScaleOriginalTargetPhaseBadEvent T cut δ Band (k scene) radius K}.indicator
        traffic
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
  have hdom := D.ae_original_minimizer_commonScale_traffic_le_targetGlobalCount
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hBand hmask hηfinite hffinite hBedge hΛ hbound hunit
  have hk : Measurable k :=
    D.measurable_commonScaleNormalizedCanonicalCurveIntegerScale hF hw T hcut h L ρ A δ
  have ht : Measurable traffic :=
    (measurable_legalMarkedCompletePathTraffic d hd hη hf).ennreal_toReal
  exact D.commonScaleOriginalTarget_selected_bad_memLp_two_le hF hw T hcut hδpos
    hBand hΛ hradius hunit Q hK hk ht hBedge (by
      filter_upwards [hdom] with scene hs _hbad
      have ht0 : 0≤traffic scene := ENNReal.toReal_nonneg
      have hN0 : 0≤D.commonScaleOriginalTargetGlobalCount T cut δ Band (k scene) radius scene :=
        ENNReal.toReal_nonneg
      rw [abs_of_nonneg ht0,abs_of_nonneg hN0]
      exact hs)


/-- Off the SAME original all-code event, actual positive contributor count
is at most K times the genuinely divided cover scale, giving the literal
inverse-delta gain relative to the original field amplitude. -/
theorem ae_original_minimizer_commonScale_target_count_le_amplitude
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
      f ((physicalPairAnchor e).2,c)≠0→e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.2.2∈Band)
    {Λ : ℝ} (hΛ : 0≤Λ)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
    (K : ℝ) (hK : 0≤K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|τ| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
    let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
    ∀ᵐscene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      scene∉D.commonScaleOriginalTargetPhaseBadEvent T cut δ Band (k scene) radius K→
      δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖→
      (scene.1.1 : Measure (LegalMarkedPhysicalEdge q))
        (legalMarkedCompletePathContributors q (fun z ↦originalSeedPathOffset S w z.2 z.1) η
          f)<(⊤:ℝ≥0∞) ∧
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
  have hN := D.ae_commonScaleOriginalTargetCandidate_count_finite hF hw T hcut hδpos
    hBand hΛ (show 0≤radius+2 by positivity) hunit Q
  filter_upwards [htube,Q.full_matching,hN] with scene hsTube hsFull hsN
  intro hsnot hamp
  have hscale := D.commonScaleNormalizedCanonicalCurveIntegerScale_spec
    T cut h L ρ A δ (N:=1) le_rfl scene (by
      simpa only [Nat.cast_one,L] using (one_le_div hδpos).mpr hamp)
  have hcurve := D.commonScaleNormalizedCanonicalCurveIntegerScale_covers
    T cut h L R hsmall hδpos hρ hA hR hRLip scene
  obtain ⟨code,hcode⟩ := exists_phaseWalkCode_cover_of_curve
    (d:=2*q) (m:=k scene) hscale.1
    (D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ scene)
    (hcurve.1 0 (by norm_num)) hcurve.2
  let W := D.commonScaleOriginalTargetCandidate T cut δ Band code (radius+2)
  let V := occupiedCompletePathTrafficContributors q d η f scene
  have hW : MeasurableSet W :=
    D.measurableSet_commonScaleOriginalTargetCandidate hF hw T hcut δ hBand code (radius+2)
  have htarget : ∀e∈V,e.2∈W := by
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
    apply D.commonScaleOriginalTargetCandidate_contains_edge_of_phase_cover
      hF hw T hcut hδpos e heE.1.1 heE.1.2.1 heE.2 (by positivity) code
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
      (scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{1}) := by
    calc
      _ ≤ (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Prod.snd ⁻¹' W) := measure_mono htarget
      _ = _ := by
        rw [←Measure.snd_apply hW,hsFull.target_marginal,legalInputColorMeasure_apply_prod _ _ _ hW]
  have hcfin := hc.trans_lt (hsN (k scene) code)
  have hreal : ((scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{1})).toReal<K*(k scene:ℝ) := by
    apply lt_of_not_ge
    intro hn
    exact hsnot (mem_iUnion.mpr ⟨code,hn⟩)
  have hcountreal : (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).real V≤
      (K*(C+1)/δ)*‖D.normalizedMomentumPhaseField T cut h L scene 0‖ := by
    calc
      _ ≤ ((scene.2 : Measure (LegalColoredInputPoint q)) (W×ˢ{1})).toReal :=
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
theorem ae_original_minimizer_commonScale_target_good_traffic_square_le
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
      f ((physicalPairAnchor e).2,c)≠0→e∈D.normalizedMomentumPhaseEligibleEdges T cut h∧e.2.2∈Band)
    {Λ : ℝ} (hΛ : 0≤Λ)
    (hunit : ((volume : Measure (Fin q→ℝ)).prod ν)
      (D.commonScaleOriginalTargetPhaseCell T cut δ Band 0 0 1)≤ENNReal.ofReal Λ)
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
      scene∉D.commonScaleOriginalTargetPhaseBadEvent T cut δ Band (k scene) radius K→
      δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖→
      2*((L:ℝ)*(a*δ)+b)≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖→
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f
        scene).toReal^2≤
        (3*Bedge*(K*(C+1)/δ))*
          (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η
            (fun z ↦ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T z.1)*f z)
              scene).toReal := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|τ| *G/h)
  let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
  let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
  let Good := fun scene : LegalMarkedOptimalInputScene q ↦
    scene∉D.commonScaleOriginalTargetPhaseBadEvent T cut δ Band (k scene) radius K∧
      δ≤‖D.normalizedMomentumPhaseField T cut h L scene 0‖
  let Count := fun scene : LegalMarkedOptimalInputScene q ↦
    (scene.1.1 : Measure (LegalMarkedPhysicalEdge q))
      (legalMarkedCompletePathContributors q (fun z ↦originalSeedPathOffset S w z.2 z.1) η
        f)<(⊤:ℝ≥0∞) ∧
    (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).real
      (legalMarkedCompletePathContributors q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f)≤
      (K*(C+1)/δ)*‖D.normalizedMomentumPhaseField T cut h L scene 0‖
  have hδpos : 0<δ := by linarith
  have hC : 1≤C := (canonicalPhaseCurveScaleCoefficient_bounds (L:ℝ) ρ A).1
  have hκ : 0≤K*(C+1)/δ := div_nonneg (mul_nonneg hK (by linarith)) hδpos.le
  have hcount := D.ae_original_minimizer_commonScale_target_count_le_amplitude
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
theorem original_minimizer_commonScale_target_large_traffic_memLp_two_le
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
    let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ
    let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
    let traffic := fun scene ↦
      (legalMarkedCompletePathTraffic q (fun z ↦originalSeedPathOffset S w z.2 z.1) η f
        scene).toReal
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
    scene∈D.commonScaleOriginalTargetPhaseBadEvent T cut δ Band (k scene) radius K}.indicator
      traffic
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
    ((measurable_originalNormalizedMomentumMarkNorm S hF hw T).comp
      measurable_fst).ennreal_ofReal.mul hf
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
  have hbad := D.original_minimizer_commonScale_target_selected_bad_traffic_memLp_two_le
    hF hw hgap hbounds T hδ hg hgb τ Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hη hf hclock hηwindow hBand hmask hηfinite hffinite hBedge hΛ hbound hunit hK
  have hgood := D.ae_original_minimizer_commonScale_target_good_traffic_square_le
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
      by_cases hb : scene∈D.commonScaleOriginalTargetPhaseBadEvent T cut δ Band (k scene) radius K
      · have he : scene∈{scene |1≤k scene∧
          scene∈D.commonScaleOriginalTargetPhaseBadEvent T cut δ Band (k scene) radius K} :=
            ⟨hbig.1,hb⟩
        dsimp only [Err]
        rw [indicator_of_mem he]
        exact le_add_of_nonneg_left (mul_nonneg hcoeff ENNReal.toReal_nonneg)
      · exact (hs hb hbig.2.1 hbig.2.2).trans (le_add_of_nonneg_right (sq_nonneg _))
    · rw [indicator_of_notMem hbig,zero_pow (by norm_num : 2≠0)]
      exact add_nonneg (mul_nonneg hcoeff ENNReal.toReal_nonneg) (sq_nonneg _)
  have hiMajor := (hiweighted.const_mul coeff).add hiBad
  have hLpData := goodEvent_memLp_two_of_integrable_majorant
    (htraffic.indicator hBig).aestronglyMeasurable
    (MeasurableSet.empty : MeasurableSet (∅ : Set (LegalMarkedOptimalInputScene q)))
    (U := fun scene ↦ coeff*weighted scene+(Err scene)^2)
    (C := 1) zero_le_one hiMajor
    (Eventually.of_forall fun _ ↦ add_nonneg
      (mul_nonneg hcoeff ENNReal.toReal_nonneg) (sq_nonneg _))
    (hmajor.mono fun _ hs _ ↦ by simpa only [one_mul] using hs)
  simp only [compl_empty,indicator_univ,one_mul] at hLpData
  have hmean : (∫scene,(Big.indicator traffic scene)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))≤
      coeff*((∫⁻x,η x ∂(volume : Measure (Fin q→ℝ)))*
        (∫⁻m,∫⁻c : ℝ,ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*f (m,c)
          ∂volume ∂legalMarkedJointPalm q Q.law)).toReal+badBudget := by
    apply hLpData.2.trans
    rw [integral_add (hiweighted.const_mul coeff) hiBad,integral_const_mul,heqweighted]
    exact add_le_add le_rfl hbad.2.1
  exact ⟨hLpData.1,hmean,eLpNorm_two_le_sqrt_of_integral_sq_le hLpData.1 hmean⟩

/-- The actual supported physical birth window supplies its own band, clock
support and window length to the original large-phase Campbell estimate. -/
theorem exists_original_right_supportedBirthWindow_coarseWeightedPalm_rate
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ} (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η,
      originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ε₀ ≤ η ∧ ε₀ ≤ 1 ∧ 0 < C ∧
      ∀ {ε cap : ℝ}, 0 < ε → ε < ε₀ → 0 < cap →
      ∀ {gap : ℝ} {g : ℝ → ℝ → ℝ}
      (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g),
      ∀ n j i ell : ℕ, i < dyadicBirthBandCount j →
        ell < birthPhysicalClockWindowCount cap →
      let t := birthDyadicShellScale ε n
      let s := birthDyadicElapsedScale ε n j
      let B : Set (PhysicalPairPalmMark (Fin q)) := {m | m.1.2 ∈
        D.originalRightBirthNarrowClockBand ε n j i}
      ENNReal.ofReal ((birthTrafficCoarseScale q t s)⁻¹) *
        (∫⁻ m, ∫⁻ c : ℝ,
          ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ *
            D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell (m, c)
          ∂volume ∂legalMarkedJointPalm q Q.law) ≤
        ENNReal.ofReal (cap * C) *
          (ENNReal.ofReal (s ^ 2 * t ^ (-2 + 1 / (q : ℝ))) *
            (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
              ∂legalMarkedJointPalm q Q.law) +
           ENNReal.ofReal (s ^ 2 * t ^ (-1 + 1 / (q : ℝ))) *
            (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
              ∂legalMarkedJointPalm q Q.law)) := by
  obtain ⟨εmoment, C, hεmoment, hεη, hC, hrate⟩ :=
    D.exists_original_right_birthBand_largePhaseMoment_bound hF hw hη hG hRem hpole
  let ε₀ := min (εmoment / 2) 1
  have hε₀ : 0 < ε₀ := lt_min (by positivity) zero_lt_one
  have hε₀half : ε₀ ≤ εmoment / 2 := min_le_left _ _
  have hε₀one : ε₀ ≤ 1 := min_le_right _ _
  refine ⟨ε₀, C, hε₀, by linarith, hε₀one, hC, ?_⟩
  intro ε cap hε hεlt hcap gap g Q n j i ell hi hell
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let B : Set (PhysicalPairPalmMark (Fin q)) := {m | m.1.2 ∈ D.originalRightBirthNarrowClockBand ε
    n j i}
  let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
  let width := birthPhysicalClockWindowWidth cap s
  let I : Set ℝ := Ico (ref - width) ref
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
    (D.measurableSet_originalRightBirthNarrowClockBand ε n j i).preimage measurable_fst.snd
  have ha : ∀ m ∈ B, D.hi - (m.1.2 - (S.level : ℝ)) ∈ Icc t (2 * t) := by
    intro m hm
    change m.1.2 - S.level ∈ Ico
      (D.hi - (t + ((i : ℝ) + 1) * (s / 8)))
      (D.hi - (t + (i : ℝ) * (s / 8))) at hm
    constructor <;> nlinarith [hm.1,hm.2,hbase.2.2.1,hbase.2.2.2]
  have hI : MeasurableSet I := measurableSet_Ico
  have hc : ∀ c ∈ I, D.hi - (c - (S.level : ℝ)) ∈ Icc t (4 * t) := by
    intro c hc
    exact D.originalRightBirthPhysicalClockWindow_inward_bounds hε hcap n j i ell hi hell
      ⟨hc.1, hc.2.le⟩
  have hlen : volume I ≤ ENNReal.ofReal (cap * s) := by
    rw [Real.volume_Ico]
    apply ENNReal.ofReal_le_ofReal
    have hw := (birthPhysicalClockWindow_spec hcap hbase.1).2.2.1
    change birthPhysicalClockWindowWidth cap s ≤ cap * s at hw
    dsimp [I, width]
    linarith
  have hzero : ∀ m c, m ∉ B ∨ c ∉ I →
      D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell (m, c) = 0 := by
    intro m c hout
    by_contra hn
    have hf := (D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff
      ε cap n j i ell (m, c)).mp hn
    have hb := D.originalSupportedRightBirthPhysicalClockMask_birth
      ε cap n j i ell (m, c) hn
    have hmb : m ∈ B := D.originalRightBirthClockMask_target_mem_reflectedClockBand
      ε n j i (m, c) hb.1
    have hci : c ∈ I := D.originalRightBirthPhysicalClockMask_clock_mem
      ε cap n j i ell (m, c) hf.2.2
    exact hout.elim (fun h ↦ h hmb) (fun h ↦ h hci)
  exact hrate Q ht htone hbase.1 htε hB ha hI hc hcap.le hlen
    (D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell)
    (D.originalSupportedRightBirthPhysicalClockMask_le_one ε cap n j i ell) hzero


/-- The true supported birth weight has finite normalized-momentum occupation
on its actual affine physical-clock window, without a finite-moment premise. -/
theorem original_right_supportedBirthWindow_weightedPalm_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (T : Matrix (Fin q) (Fin q) ℝ) (ε cap : ℝ) (n j i ell : ℕ)
    (hwidth : 0 < birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j))
    (hclock : ∀ r ∈ Icc (0 : ℝ) 1,
      D.originalRightBirthPhysicalClockReference ε cap n j i ell +
        (-birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)) * r -
        (S.level : ℝ) ∈ Ioo D.lo D.hi) :
    (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal ‖(Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m‖ *
        D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell (m, c)
      ∂volume ∂legalMarkedJointPalm q Q.law) < (∞ : ℝ≥0∞) := by
  let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
  let width := birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)
  let J : Set ℝ := Icc (ref - width) ref
  have hJclock : ∀ c ∈ J, c - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    intro c hc
    have hr : (ref-c)/width ∈ Icc (0:ℝ) 1 :=
      ⟨div_nonneg (by linarith [hc.2]) hwidth.le,
        (div_le_iff₀ hwidth).mpr (by linarith [hc.1])⟩
    have heq : ref+(-width)*((ref-c)/width)=c := by
      field_simp [show width≠0 from hwidth.ne']
      ring
    have h := hclock ((ref-c)/width) hr
    change ref+(-width)*((ref-c)/width)-(S.level:ℝ) ∈ Ioo D.lo D.hi at h
    rwa [heq] at h
  have hzero : ∀ m c, c ∉ J →
      D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell (m, c) = 0 := by
    intro m c hc
    by_contra hn
    have hf := (D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff
      ε cap n j i ell (m, c)).mp hn
    have hmem := D.originalRightBirthPhysicalClockMask_clock_mem
      ε cap n j i ell (m, c) hf.2.2
    exact hc ⟨hmem.1,hmem.2.le⟩
  exact D.lintegral_original_compactClock_maskedWeightedOccupation_lt_top hF hw
    hgap hbounds Q (Tᵀ)⁻¹ isCompact_Icc hJclock
    (D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell)
    (D.originalSupportedRightBirthPhysicalClockMask_le_one ε cap n j i ell) hzero


/-- The literal supported birth weight has finite original first Palm
occupation from the same weighted law, without a supplied moment bound. -/
theorem original_right_supportedBirthWindow_palm_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (ε cap : ℝ) (n j i ell : ℕ) :
    (∫⁻m,∫⁻c : ℝ,D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell (m,c)
      ∂volume ∂legalMarkedJointPalm q Q.law)<(∞:ℝ≥0∞) := by
  apply lt_of_le_of_lt (b:=∫⁻m,∫⁻c : ℝ,ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖
    ∂volume ∂legalMarkedJointPalm q Q.law)
  · apply lintegral_mono
    intro m
    apply lintegral_mono
    intro c
    exact mul_le_of_le_one_right (by positivity)
      (D.originalSupportedRightBirthPhysicalClockMask_le_one ε cap n j i ell (m,c))
  · rw [D.lintegral_original_clockOccupation_norm_eq_pathLength hF hw hbounds Q]
    exact ENNReal.ofReal_lt_top


end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
