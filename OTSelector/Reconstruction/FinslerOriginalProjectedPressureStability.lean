import OTSelector.Reconstruction.FinslerOriginalClassPressurePullback

/-! Cost resampling is compared on the unchanged original continuous-mark law.
Finite class observation records its exact legal mask and mark pushforward. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]
  [Fintype C] [Fintype D] [DecidableEq D]
  [MeasurableSingletonClass C] [MeasurableSingletonClass D]

/-- Relative cost resampling on original continuous marks controls the actual
expected pressure with the same constant as the original finite-class bound.
All integrability inputs are produced from ordinary quadratic/probe growth. -/
theorem finiteClassLegalPressure_pullback_abs_sub_le_relative
    (q : ℕ) (allowed : C → D → Prop)
    (hnested : ∀ c c', (∀ d, allowed c d → allowed c' d) ∨
      (∀ d, allowed c' d → allowed c d))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (r : ℝ≥0) {K Kref G H ε η : ℝ}
    (hK : 0 ≤ K) (hKref : 0 ≤ Kref) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    {kin reference : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (href : Measurable (Function.uncurry (fun p : A × B ↦ reference p.1 p.2)))
    (hkb : ∀ a b, allowed (f a) (g b) → ∀ v, |kin a b v| ≤ K * ∑ l, v l ^ 2)
    (hrefb : ∀ a b, allowed (f a) (g b) → ∀ v, |reference a b v| ≤ Kref * ∑ l, v l ^ 2)
    (probe refProbe : A → B → ℝ)
    (hp : Measurable (Function.uncurry probe)) (hpref : Measurable (Function.uncurry refProbe))
    (hprobe : ∀ a b, allowed (f a) (g b) → |probe a b| ≤ H)
    (hprobeRef : ∀ a b, allowed (f a) (g b) → |refProbe a b| ≤ G)
    (hkin : ∀ a b, allowed (f a) (g b) → ∀ v,
      |kin a b v - reference a b v| ≤ ε * reference a b v)
    (hprobeDiff : ∀ a b, allowed (f a) (g b) → |probe a b - refProbe a b| ≤ η) (t : ℝ) :
    |finiteClassLegalPressure q (fun a b ↦ allowed (f a) (g b)) α β r kin probe t -
      finiteClassLegalPressure q (fun a b ↦ allowed (f a) (g b)) α β r reference refProbe t| ≤
      ε * (finiteClassLegalPressure q (fun a b ↦ allowed (f a) (g b)) α β r reference refProbe t +
        (r : ℝ) * (|t| * G)) + (r : ℝ) * (|t| * η) := by
  let mask := fun a b ↦ allowed (f a) (g b)
  let V := finiteClassLegalTilted q mask r kin probe t
  let Vref := finiteClassLegalTilted q mask r reference refProbe t
  let law := twoMarkedCloudLaw q A B α β r
  have hI : Integrable V law := integrable_finiteClassLegalTilted_pullback_mask q allowed hnested
    α β hf hg r hK hH hk hkb probe hp hprobe t
  have hIref : Integrable Vref law := integrable_finiteClassLegalTilted_pullback_mask q allowed hnested
    α β hf hg r hKref hG href hrefb refProbe hpref hprobeRef t
  let b := ε * (|t| * G) + |t| * η
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hbound (ω : TwoMarkedCloudSpace q A B) :
      |V ω - Vref ω| ≤ ε * Vref ω + (mSourceCount ω : ℝ) * b := by
    have hv := finiteClassLegalTilted_abs_sub_le_relative q mask r kin reference probe refProbe
      hε0 hε1 hkin hprobeRef hprobeDiff t ω
    have hcard : (PartialMatching.legalMaximumCard
        (finiteClassLegalGraph q (mSourceCount ω) (mTargetCount ω) mask ω) : ℝ) ≤
        (mSourceCount ω : ℝ) := by
      exact_mod_cast (PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _)
    have hc := mul_le_mul_of_nonneg_right hcard hb
    dsimp only [V,Vref,b] at hc ⊢
    linarith only [hv,hc]
  have hcount := integrable_mSourceCount q α β r
  have hright : Integrable (fun ω ↦ ε * Vref ω + (mSourceCount ω : ℝ) * b) law :=
    (hIref.const_mul ε).add (hcount.mul_const b)
  calc
    _ = |∫ ω, V ω - Vref ω ∂law| := by rw [integral_sub hI hIref]; rfl
    _ ≤ ∫ ω, |V ω - Vref ω| ∂law := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω ↦ V ω - Vref ω)
    _ ≤ ∫ ω, ε * Vref ω + (mSourceCount ω : ℝ) * b ∂law :=
      integral_mono_ae (hI.sub hIref).abs hright (.of_forall hbound)
    _ = _ := by
      rw [integral_add (hIref.const_mul ε) (hcount.mul_const b),integral_const_mul,integral_mul_const,
        integral_mSourceCount_eq]
      dsimp only [b,Vref,law,finiteClassLegalPressure,mask]
      ring

/-- The resampled reference may be evaluated at the exact observed class laws,
while its comparison is still with the actual original continuous-mark pressure. -/
theorem finiteClassLegalPressure_resampling_abs_sub_le
    (q : ℕ) (allowed : C → D → Prop)
    (hnested : ∀ c c', (∀ d, allowed c d → allowed c' d) ∨
      (∀ d, allowed c' d → allowed c d))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (γ : Measure C) [IsProbabilityMeasure γ] (δ : Measure D) [IsProbabilityMeasure δ]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (hγ : α.map f = γ) (hδ : β.map g = δ)
    (r : ℝ≥0) {K Kref G H ε η : ℝ}
    (hK : 0 ≤ K) (hKref : 0 ≤ Kref) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    {kin : A → B → (Fin q → ℝ) → ℝ} {reference : C → D → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (href : Measurable (Function.uncurry (fun p : C × D ↦ reference p.1 p.2)))
    (hkb : ∀ a b, allowed (f a) (g b) → ∀ v, |kin a b v| ≤ K * ∑ l, v l ^ 2)
    (hrefb : ∀ c d, allowed c d → ∀ v, |reference c d v| ≤ Kref * ∑ l, v l ^ 2)
    (probe : A → B → ℝ) (refProbe : C → D → ℝ)
    (hp : Measurable (Function.uncurry probe))
    (hprobe : ∀ a b, allowed (f a) (g b) → |probe a b| ≤ H)
    (hprobeRef : ∀ c d, allowed c d → |refProbe c d| ≤ G)
    (hkin : ∀ a b, allowed (f a) (g b) → ∀ v,
      |kin a b v - reference (f a) (g b) v| ≤ ε * reference (f a) (g b) v)
    (hprobeDiff : ∀ a b, allowed (f a) (g b) → |probe a b - refProbe (f a) (g b)| ≤ η) (t : ℝ) :
    |finiteClassLegalPressure q (fun a b ↦ allowed (f a) (g b)) α β r kin probe t -
      finiteClassLegalPressure q allowed γ δ r reference refProbe t| ≤
      ε * (finiteClassLegalPressure q allowed γ δ r reference refProbe t + (r : ℝ) * (|t| * G)) +
        (r : ℝ) * (|t| * η) := by
  rw [finiteClassLegalPressure_eq_pullback q allowed hnested α β γ δ hf hg hγ hδ r reference href]
  exact finiteClassLegalPressure_pullback_abs_sub_le_relative q allowed hnested α β hf hg r
    (kin := kin) (reference := fun a b ↦ reference (f a) (g b))
    hK hKref hG hH hε0 hε1 hη hk
    (href.comp ((hf.prodMap hg).prodMap measurable_id)) hkb
    (fun a b hab ↦ hrefb (f a) (g b) hab) probe (fun a b ↦ refProbe (f a) (g b)) hp
    ((measurable_of_countable (Function.uncurry refProbe)).comp (hf.prodMap hg)) hprobe
    (fun a b hab ↦ hprobeRef (f a) (g b) hab) hkin hprobeDiff t

end OTSelector.Reconstruction
