import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthGeometry
import OTSelector.Reconstruction.CommonPhysicalNormalizedPhaseWindow

/-! Nonzero actual regular physical windows have one common contractive scalar frame. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
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

/-- A nonzero right regular birth window has its entire closed physical clock
window in a fixed enlarged compact regular strip. -/
theorem originalRegularBirth_right_window_in_compact
    {H ε gap diameter cap : ℝ} (hH : 0 < H) (_hε : 0 < ε) (_hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hcap : 0 < cap)
    (hcapH : cap*H ≤ min ε (gap/2)/4)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalRegularBirthWindowMask H ε cap 1 n j i ell z ≠ 0) :
    ∀ c ∈ Icc (D.originalRightBirthPhysicalClockReference H cap n j i ell -
        birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale H n j))
      (D.originalRightBirthPhysicalClockReference H cap n j i ell),
      c-(S.level:ℝ) ∈ Icc (D.lo+min ε (gap/2)/2) (D.hi-min ε (gap/2)/2) := by
  change originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 5 z *
    D.originalSupportedRightBirthPhysicalClockMask H cap n j i ell z ≠ 0 at hz
  have hr := left_ne_zero_of_mul hz
  have hm := right_ne_zero_of_mul hz
  have hsupport := D.originalSupportedRightBirthPhysicalClockMask_support H cap n j i ell z hm
  have hb := D.originalSupportedRightBirthPhysicalClockMask_birth H cap n j i ell z hm
  have hbase := birthDyadicClockBand_base_bounds hH n j i hb.2
  have hclock := D.originalRightBirthPhysicalClockMask_clock_mem H cap n j i ell z
    ((D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff H cap n j i ell z).mp hm).2.2
  have hsep := hbounds.separated _ hsupport.1 _ hsupport.2.1
  have hreg := (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp hr
  have hgaplen : gap ≤ z.1.1.2-z.1.1.1 := by
    simpa only [Real.dist_eq,abs_of_neg (sub_neg.mpr (hreg.2.2.1.trans hreg.2.2.2.1)),neg_sub] using hsep
  have hstrip := original_regularClock_mask_compact_strip (Or.inr (Or.inr (Or.inl rfl))) hr hgaplen
  have htH : 2*birthDyadicShellScale H n ≤ H := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hH.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hsH : birthDyadicElapsedScale H n j ≤ H := by linarith [hbase.2.1]
  have hwcap := (birthPhysicalClockWindow_spec hcap hbase.1).2.2.1
  have hwidth : birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale H n j) ≤
      min ε (gap/2)/4 :=
    hwcap.trans ((mul_le_mul_of_nonneg_left hsH hcap.le).trans hcapH)
  intro c hc
  constructor <;> linarith [hc.1,hc.2,hclock.1,hclock.2,hstrip.1,hstrip.2]

/-- One positive fraction, chosen after the actual phase h, gives both physical
regularity and canonical contraction at every nonzero original left birth window. -/
theorem exists_original_regularBirth_right_contractive_windows
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {H ε gap diameter basecap h : ℝ} (hH : 0 < H) (hε : 0 < ε) (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hbasecap : 0 < basecap)
    (_hh : 0 < h) :
    ∃ cap ρ : ℝ, 0 < cap ∧ cap ≤ basecap ∧ 0 ≤ ρ ∧
      ∀ n j i ell : ℕ,
      (∃ z : MarkClock,D.originalRegularBirthWindowMask H ε cap 1 n j i ell z ≠ 0) →
      let s := birthDyadicElapsedScale H n j
      let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
      let ref := D.originalRightBirthPhysicalClockReference H cap n j i ell
      let width := birthPhysicalClockWindowWidth cap s
      let R := originalNormalizedClockMobility S w T ref (-width)
      IsUnit T.det ∧ ref-S.level ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0:ℝ) 1,ref+(-width)*r-S.level ∈ Ioo D.lo D.hi) ∧ R 0 = 0 ∧
        (∀ r ∈ Icc (0:ℝ) 1,‖R r‖ ≤ ρ) ∧
        (∀ r ∈ Icc (0:ℝ) 1,∀ v ∈ Icc (0:ℝ) 1,‖R r-R v‖ ≤ ρ*|r-v|) ∧
        ∀ r ∈ Icc (0:ℝ) 1,‖R r‖*Real.sqrt ((qdim:ℝ)/h^2) ≤ (1/2:ℝ) := by
  let d := min ε (gap/2)
  have hd : 0 < d := lt_min hε (half_pos hgap)
  let J := Icc (D.lo+d/2) (D.hi-d/2)
  have hJI : J ⊆ Ioo D.lo D.hi := by intro x hx;constructor <;> dsimp [J] at hx <;> linarith [hx.1,hx.2]
  obtain ⟨B,hB,hcurve⟩ := D.exists_original_regularBirth_complianceCurve_bounds hF hw isCompact_Icc hJI
  let L := Real.sqrt ((qdim:ℝ)/h^2)
  let base := min basecap (d/(4*H))
  have hbase : 0 < base := lt_min hbasecap (div_pos hd (by positivity))
  let cap := commonPhysicalNormalizedWindowFraction base B L
  have hspec := commonPhysicalNormalizedWindowFraction_spec hbase hB (show 0 ≤ L from Real.sqrt_nonneg _)
  have hcap : 0 < cap := hspec.1
  have hcapbase : cap ≤ base := commonPhysicalNormalizedWindowFraction_le_cap _ _ _
  have hcapH : cap*H ≤ d/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*H)).mp (hcapbase.trans (min_le_right _ _))
    nlinarith
  refine ⟨cap,cap*B,hcap,hcapbase.trans (min_le_left _ _),mul_nonneg hcap.le hB,?_⟩
  intro n j i ell hnonzero
  dsimp only
  obtain ⟨z,hz⟩ := hnonzero
  let s := birthDyadicElapsedScale H n j
  let ref := D.originalRightBirthPhysicalClockReference H cap n j i ell
  let width := birthPhysicalClockWindowWidth cap s
  let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
  have hs : 0 < s := div_pos (birthDyadicShellScale_pos hH n) (by positivity)
  have hwidth := (birthPhysicalClockWindow_spec hcap hs).2.1
  have hwcap := (birthPhysicalClockWindow_spec hcap hs).2.2.1
  have hwin := D.originalRegularBirth_right_window_in_compact hH hε hgap hbounds hcap hcapH n j i ell z hz
  have hsub : uIcc (ref-S.level) (ref-S.level+(-width)) ⊆ J := by
    rw [uIcc_of_ge (by linarith)]
    intro v hv
    have hv' := hwin (v+S.level) ⟨by linarith [hv.1],by linarith [hv.2]⟩
    simpa only [add_sub_cancel_right] using hv'
  have hm := hcurve hs hsub
  have hcoef : B*|-width|/s ≤ cap*B := by
    rw [abs_neg,abs_of_pos hwidth]
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hwcap hB]
  have hR : ∀ r ∈ Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T ref (-width) r‖ ≤ cap*B :=
    fun r hr ↦ (hm.2.1 r hr).trans hcoef
  refine ⟨(positiveMatrixNormalizer_spec (Matrix.PosDef.one.smul hs)).1,
    hJI (hsub left_mem_uIcc),?_,hm.1,hR,?_,?_⟩
  · intro r hr
    apply hJI
    apply hwin
    constructor <;> nlinarith [hr.1,hr.2]
  · intro r hr v hv
    exact (hm.2.2 r hr v hv).trans (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))
  · exact commonPhysicalNormalizedWindowFraction_contractive hbase hB (show 0 ≤ L from Real.sqrt_nonneg _) hR

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
