import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthMinBound
import OTSelector.Reconstruction.OriginalMinimizerRightRegularBounded

/-! The actual endpoint-confined regular birth count event has its K s² band
moment and original-input exponential count tail. No selected-cloud law is used. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
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
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker
local notation "MarkClock" => PhysicalPairPalmMark (Fin qdim) × ℝ

/-- A single compact regular strip selects the physical min-one coefficient
before any phase h or canonical cap is chosen. Every smaller actual right window
retains this same coefficient. -/
theorem exists_original_regularBirth_right_window_min_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {H ε gap diameter : ℝ} (hH : 0 < H) (hε : 0 < ε) (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) :
    ∃ basecap Cedge : ℝ,0 < basecap ∧ 0 ≤ Cedge ∧
    ∀ {cap : ℝ},0 < cap → cap ≤ basecap → ∀ n j i ell : ℕ,
    ∀ {R M₀ : ℝ},0 ≤ R → 0 ≤ M₀ →
    ∀ η : (Fin qdim → ℝ) → ℝ,(∀ x,0 ≤ η x) → (∀ x,η x ≤ M₀) →
      (∀ x,R < ‖x‖ → η x = 0) →
    ∀ x : Fin qdim → ℝ,∀ m : PhysicalPairPalmMark (Fin qdim),
      (∫⁻ clock : ℝ,ENNReal.ofReal (η (x+originalSeedPathOffset S w clock m))*
        D.originalRegularBirthWindowWeight H ε cap 1 n j i ell (m,clock)) ≤
      ENNReal.ofReal ((4*M₀*(R+1))*min 1 ((Cedge*Real.sqrt (birthDyadicElapsedScale H n j))*
        ‖((positiveMatrixNormalizer ((birthDyadicElapsedScale H n j) •
          (1:Matrix (Fin qdim) (Fin qdim) ℝ)))ᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m‖)) := by
  let d := min ε (min (gap/2) ((D.hi-D.lo)/4))
  have hd : 0 < d := lt_min hε (lt_min (half_pos hgap) (by linarith [D.support.lt]))
  have hdε : d ≤ ε := min_le_left _ _
  have hdgap : d ≤ gap/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdspan : d ≤ (D.hi-D.lo)/4 := (min_le_right _ _).trans (min_le_right _ _)
  let a := D.lo+d/2+S.level
  let b := D.hi-d/2+S.level
  have ha : a-S.level ∈ Ioo D.lo D.hi := by dsimp [a];constructor <;> linarith
  have hb : b-S.level ∈ Ioo D.lo D.hi := by dsimp [b];constructor <;> linarith
  obtain ⟨Cedge,δedge,hCedge,hδedge,hedge⟩ :=
    D.exists_original_regularBirth_fullClock_min_bound hF hw zero_le_one ha hb
  let basecap := min 1 (δedge/H)
  have hbasecap : 0 < basecap := lt_min zero_lt_one (div_pos hδedge hH)
  refine ⟨basecap,Cedge,hbasecap,hCedge,?_⟩
  intro cap hcap hcapbase n j i ell R M₀ hR hM η hη0 hηM hηR x m
  let mask := D.originalRegularBirthWindowMask H ε cap 1 n j i ell
  let ref := D.originalRightBirthPhysicalClockReference H cap n j i ell
  let s := birthDyadicElapsedScale H n j
  let width := birthPhysicalClockWindowWidth cap s
  have hs : 0 < s := div_pos (birthDyadicShellScale_pos hH n) (by positivity)
  have hwidth : 0 < width := (birthPhysicalClockWindow_spec hcap hs).2.1
  have hwcap : width ≤ cap*s := (birthPhysicalClockWindow_spec hcap hs).2.2.1
  have hcap1 : cap ≤ 1 := hcapbase.trans (min_le_left _ _)
  have hcapδ : cap*H ≤ δedge := (le_div_iff₀ hH).mp (hcapbase.trans (min_le_right _ _))
  have hclock (z : MarkClock) (hz : mask z ≠ 0) : z.2 ∈ Ico (ref-width) ref := by
    have hm : D.originalSupportedRightBirthPhysicalClockMask H cap n j i ell z ≠ 0 :=
      right_ne_zero_of_mul hz
    exact D.originalRightBirthPhysicalClockMask_clock_mem H cap n j i ell z
      ((D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff H cap n j i ell z).mp hm).2.2
  by_cases hnonzero : ∃ z : MarkClock,mask z ≠ 0
  · obtain ⟨z,hz⟩ := hnonzero
    have hr : originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 5 z ≠ 0 :=
      left_ne_zero_of_mul hz
    have hm : D.originalSupportedRightBirthPhysicalClockMask H cap n j i ell z ≠ 0 :=
      right_ne_zero_of_mul hz
    have hsupport := D.originalSupportedRightBirthPhysicalClockMask_support H cap n j i ell z hm
    have hreg := (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp hr
    have hsep := hbounds.separated _ hsupport.1 _ hsupport.2.1
    have hgaplen : gap ≤ z.1.1.2-z.1.1.1 := by
      simpa only [Real.dist_eq,abs_of_neg (sub_neg.mpr (hreg.2.2.1.trans hreg.2.2.2.1)),neg_sub] using hsep
    have hstrip := original_regularClock_mask_compact_strip (Or.inr (Or.inr (Or.inl rfl))) hr hgaplen
    have hc : z.2 ∈ Icc a b := by
      have hdm : d ≤ min ε (gap/2) := le_min hdε hdgap
      constructor <;> dsimp [a,b] <;> linarith [hstrip.1,hstrip.2]
    have hbase := birthDyadicClockBand_base_bounds hH n j i
      (D.originalSupportedRightBirthPhysicalClockMask_birth H cap n j i ell z hm).2
    have htH : 2*birthDyadicShellScale H n ≤ H := by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hH.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    have hsH : s ≤ H := by linarith [hbase.2.1]
    have hwδ : width ≤ δedge := hwcap.trans
      ((mul_le_mul_of_nonneg_left hsH hcap.le).trans hcapδ)
    have hwin : ∀ v ∈ Icc (ref-width) ref,|v-z.2| ≤ δedge := by
      intro v hv
      apply (abs_le.mpr ?_).trans hwδ
      constructor <;> linarith [(hclock z hz).1,(hclock z hz).2,hv.1,hv.2]
    have hzout : ∀ m clock,clock ∉ Icc (ref-width) ref → mask (m,clock) = 0 := by
      intro m clock hout
      by_contra hn
      exact hout ⟨(hclock (m,clock) hn).1,(hclock (m,clock) hn).2.le⟩
    have hsource : ∀ m clock,mask (m,clock) ≠ 0 → m.1.1-S.level ∈ Ioo D.lo D.hi := by
      intro m clock hn
      have hr' := (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp (left_ne_zero_of_mul hn)
      constructor <;> linarith [hr'.1,hr'.2.1,hr'.2.2.1,hr'.2.2.2.1]
    exact hedge z.2 hc (by linarith) hs (by nlinarith [mul_le_mul_of_nonneg_right hcap1 hs.le])
      hwin hR hM η hη0 hηM hηR mask
      (D.originalRegularBirthWindowMask_le_one H ε cap 1 n j i ell) hzout hsource x m
  · have hz : ∀ z,mask z = 0 := fun z ↦ by by_contra hn;exact hnonzero ⟨z,hn⟩
    have hz' : ∀ clock,D.originalRegularBirthWindowWeight H ε cap 1 n j i ell (m,clock) = 0 :=
      fun clock ↦ mul_eq_zero_of_right _ (hz (m,clock))
    simp only [hz',mul_zero,lintegral_zero]
    exact zero_le

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
