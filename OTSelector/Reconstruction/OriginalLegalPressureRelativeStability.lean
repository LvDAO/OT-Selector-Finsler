import OTSelector.Reconstruction.FinslerOriginalLegalPressureCoefficientStability
import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureLimit

/-! Relative original continuous geometric and probe changes control the true
scalar-legal pressure on unchanged original mark laws, before every limit. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The actual continuous scalar-legal pressures inherit the relative kernel
and physical probe comparison on their unchanged original iid populations. -/
theorem legalMarkedPressure_abs_sub_le_relative
    (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {K Kref G H ε η : ℝ}
    (hK : 0 ≤ K) (hKref : 0 ≤ Kref) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    (kin reference : A → B → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (href : Measurable (Function.uncurry (fun p : A × B ↦ reference p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ K * ∑ l, v l ^ 2)
    (hrefb : ∀ a b v, |reference a b v| ≤ Kref * ∑ l, v l ^ 2)
    (probe refProbe : A → B → ℝ)
    (hp : Measurable (Function.uncurry probe)) (hpref : Measurable (Function.uncurry refProbe))
    (hprobe : ∀ a b, |probe a b| ≤ H) (hprobeRef : ∀ a b, |refProbe a b| ≤ G)
    (hkin : ∀ a b, source a < target b → ∀ v,
      |kin a b v - reference a b v| ≤ ε * reference a b v)
    (hprobeDiff : ∀ a b, source a < target b → |probe a b - refProbe a b| ≤ η) (t : ℝ) :
    |legalMarkedPressure q source target α β r kin probe t -
      legalMarkedPressure q source target α β r reference refProbe t| ≤
      ε * (legalMarkedPressure q source target α β r reference refProbe t +
        (r : ℝ) * (|t| * G)) + (r : ℝ) * (|t| * η) := by
  let V := legalMarkedTilted q source target r kin probe t
  let Vref := legalMarkedTilted q source target r reference refProbe t
  let law := twoMarkedCloudLaw q A B α β r
  have hI : Integrable V law := integrable_legalMarkedTilted q hs ht α β r hK hH hk hkb hp hprobe t
  have hIref : Integrable Vref law := integrable_legalMarkedTilted q hs ht α β r
    hKref hG href hrefb hpref hprobeRef t
  let b := ε * (|t| * G) + |t| * η
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hbound (sample : TwoMarkedCloudSpace q A B) :
      |V sample - Vref sample| ≤ ε * Vref sample + (mSourceCount sample : ℝ) * b := by
    have hv := finiteClassLegalTilted_abs_sub_le_relative q (fun a b ↦ source a < target b)
      r kin reference probe refProbe hε0 hε1 hkin (fun a b _ ↦ hprobeRef a b) hprobeDiff t sample
    change |V sample - Vref sample| ≤ ε * (Vref sample +
      (PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount sample) (mTargetCount sample) source target sample) : ℝ) * (|t| * G)) +
      (PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount sample) (mTargetCount sample) source target sample) : ℝ) * (|t| * η) at hv
    have hcard : (PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount sample) (mTargetCount sample) source target sample) : ℝ) ≤
        (mSourceCount sample : ℝ) := by
      exact_mod_cast (PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _)
    have hc := mul_le_mul_of_nonneg_right hcard hb
    dsimp only [b] at hc ⊢
    linarith only [hv,hc]
  have hcount := integrable_mSourceCount q α β r
  have hright : Integrable (fun sample ↦ ε * Vref sample + (mSourceCount sample : ℝ) * b) law :=
    (hIref.const_mul ε).add (hcount.mul_const b)
  calc
    _ = |∫ sample, V sample - Vref sample ∂law| := by rw [integral_sub hI hIref]; rfl
    _ ≤ ∫ sample, |V sample - Vref sample| ∂law := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun sample ↦ V sample - Vref sample)
    _ ≤ ∫ sample, ε * Vref sample + (mSourceCount sample : ℝ) * b ∂law :=
      integral_mono_ae (hI.sub hIref).abs hright (.of_forall hbound)
    _ = _ := by
      rw [integral_add (hIref.const_mul ε) (hcount.mul_const b),integral_const_mul,integral_mul_const,
        integral_mSourceCount_eq]
      dsimp only [b,Vref,law,legalMarkedPressure]
      ring

/-- The same actual relative comparison is uniform in every positive real
spatial scale. -/
theorem legalMarkedScalePressure_abs_sub_le_relative
    (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {K Kref G H ε η : ℝ}
    (hK : 0 ≤ K) (hKref : 0 ≤ Kref) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    (kin reference : A → B → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (href : Measurable (Function.uncurry (fun p : A × B ↦ reference p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ K * ∑ l, v l ^ 2)
    (hrefb : ∀ a b v, |reference a b v| ≤ Kref * ∑ l, v l ^ 2)
    (probe refProbe : A → B → ℝ)
    (hp : Measurable (Function.uncurry probe)) (hpref : Measurable (Function.uncurry refProbe))
    (hprobe : ∀ a b, |probe a b| ≤ H) (hprobeRef : ∀ a b, |refProbe a b| ≤ G)
    (hkin : ∀ a b, source a < target b → ∀ v,
      |kin a b v - reference a b v| ≤ ε * reference a b v)
    (hprobeDiff : ∀ a b, source a < target b → |probe a b - refProbe a b| ≤ η)
    {R : ℝ} (hR : 0 < R) (t : ℝ) :
    |legalMarkedScalePressure q source target α β kin probe R t -
      legalMarkedScalePressure q source target α β reference refProbe R t| ≤
      ε * (legalMarkedScalePressure q source target α β reference refProbe R t + |t| * G) + |t| * η := by
  have hV : 0 < R ^ q := pow_pos hR q
  have hb := legalMarkedPressure_abs_sub_le_relative q source target hs ht α β (Real.toNNReal (R ^ q))
    hK hKref hG hH hε0 hε1 hη kin reference hk href hkb hrefb probe refProbe hp hpref
    hprobe hprobeRef hkin hprobeDiff t
  rw [Real.coe_toNNReal _ hV.le] at hb
  simp only [legalMarkedScalePressure,hR,↓reduceIte]
  rw [← sub_div,abs_div,abs_of_pos hV]
  apply (div_le_iff₀ hV).mpr
  apply hb.trans_eq
  field_simp [hV.ne']

/-- The true continuous thermodynamic limits inherit the relative original
geometric/probe comparison, with no optimizer moment assumption. -/
theorem legalMarkedScalePressure_limits_abs_sub_le_relative
    (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {K Kref G H ε η : ℝ}
    (hK : 0 ≤ K) (hKref : 0 ≤ Kref) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    (kin reference : A → B → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (href : Measurable (Function.uncurry (fun p : A × B ↦ reference p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ K * ∑ l, v l ^ 2)
    (hrefb : ∀ a b v, |reference a b v| ≤ Kref * ∑ l, v l ^ 2)
    (probe refProbe : A → B → ℝ)
    (hp : Measurable (Function.uncurry probe)) (hpref : Measurable (Function.uncurry refProbe))
    (hprobe : ∀ a b, |probe a b| ≤ H) (hprobeRef : ∀ a b, |refProbe a b| ≤ G)
    (hkin : ∀ a b, source a < target b → ∀ v,
      |kin a b v - reference a b v| ≤ ε * reference a b v)
    (hprobeDiff : ∀ a b, source a < target b → |probe a b - refProbe a b| ≤ η)
    (p pref : ℝ → ℝ)
    (hplim : ∀ t, Tendsto (fun R ↦ legalMarkedScalePressure q source target α β kin probe R t) atTop (𝓝 (p t)))
    (hpreflim : ∀ t, Tendsto (fun R ↦ legalMarkedScalePressure q source target α β reference refProbe R t) atTop (𝓝 (pref t)))
    (t : ℝ) : |p t - pref t| ≤ ε * (pref t + |t| * G) + |t| * η := by
  have hleft := ((hplim t).sub (hpreflim t)).abs
  have hright := (((hpreflim t).add_const (|t| * G)).const_mul ε).add_const (|t| * η)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact legalMarkedScalePressure_abs_sub_le_relative q source target hs ht α β
    hK hKref hG hH hε0 hε1 hη kin reference hk href hkb hrefb probe refProbe hp hpref
    hprobe hprobeRef hkin hprobeDiff hR t

end OTSelector.Reconstruction
