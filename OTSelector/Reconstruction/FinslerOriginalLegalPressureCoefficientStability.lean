import OTSelector.Reconstruction.FinslerOriginalPressureKineticScaling
import OTSelector.Reconstruction.RelativePressureComparison
import OTSelector.Reconstruction.MarkedStationaryValueLegalRegularity

/-! Relative geometric coefficient and probe errors compare the actual two
legal minima on the same original class graph. No additional moment of the
perturbed optimizer and no completion of its legal graph are needed. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace PartialMatching

/-- Relative kinetic and bounded probe perturbations control the actual signed
legal optimum by the reference optimum plus the true legal matching cardinality.
The comparison is valid for arbitrary finite legal graphs and signed probes. -/
theorem abs_legalMaximumValue_perturbed_sub_le_relative {m n : ℕ}
    (allowed : Finset (Fin m × Fin n)) (c g d h : Fin m → Fin n → ℝ)
    {t ε G B : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hkin : ∀ i j, (i,j) ∈ allowed → |c i j - d i j| ≤ ε * d i j)
    (hprobe : ∀ i j, (i,j) ∈ allowed → |h i j| ≤ G)
    (hprobeDiff : ∀ i j, (i,j) ∈ allowed → |g i j - h i j| ≤ B) :
    |legalMaximumValue allowed (fun i j ↦ c i j + t * g i j) -
      legalMaximumValue allowed (fun i j ↦ d i j + t * h i j)| ≤
      ε * (legalMaximumValue allowed (fun i j ↦ d i j + t * h i j) +
        (legalMaximumCard allowed : ℝ) * (|t| * G)) +
          (legalMaximumCard allowed : ℝ) * (|t| * B) := by
  let S : Set (OTSelector.PartialMatching m n) :=
    {σ | IsLegal allowed σ ∧ σ.card = legalMaximumCard allowed}
  have hlin (σ : OTSelector.PartialMatching m n) (x y : Fin m → Fin n → ℝ) :
      σ.cost (fun i j ↦ x i j + t * y i j) = σ.cost x + t * σ.cost y := by
    simp only [OTSelector.PartialMatching.cost,Finset.sum_add_distrib,Finset.mul_sum]
  obtain ⟨σ,hσ,hcardσ,hcostσ⟩ := exists_cost_eq_legalMaximumValue allowed
    (fun i j ↦ c i j + t * g i j)
  obtain ⟨τ,hτ,hcardτ,hcostτ⟩ := exists_cost_eq_legalMaximumValue allowed
    (fun i j ↦ d i j + t * h i j)
  have hc (κ : OTSelector.PartialMatching m n) (hκ : κ ∈ S) :
      |κ.cost c - κ.cost d| ≤ ε * κ.cost d := by
    simp only [OTSelector.PartialMatching.cost,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ e ∈ κ.edges, |c e.1 e.2 - d e.1 e.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ κ.edges, ε * d e.1 e.2 :=
        Finset.sum_le_sum fun e he ↦ hkin e.1 e.2 (hκ.1 he)
      _ = _ := (Finset.mul_sum ..).symm
  have hh (κ : OTSelector.PartialMatching m n) (hκ : κ ∈ S) :
      |κ.cost h| ≤ (legalMaximumCard allowed : ℝ) * G := by
    rw [← hκ.2]
    exact abs_cost_le_card_mul_of_allowed κ hκ.1 hprobe
  have hgh (κ : OTSelector.PartialMatching m n) (hκ : κ ∈ S) :
      |κ.cost g - κ.cost h| ≤ (legalMaximumCard allowed : ℝ) * B := by
    have hb := abs_cost_le_card_mul_of_allowed (c := fun i j ↦ g i j - h i j)
      κ hκ.1 hprobeDiff
    simpa only [OTSelector.PartialMatching.cost,Finset.sum_sub_distrib,hκ.2] using hb
  have hσmin (κ : OTSelector.PartialMatching m n) (hκ : κ ∈ S) :
      σ.cost c + t * σ.cost g ≤ κ.cost c + t * κ.cost g := by
    have hb := legalMaximumValue_le (fun i j ↦ c i j + t * g i j) hκ.1 hκ.2
    rw [← hcostσ,hlin,hlin] at hb
    exact hb
  have hτmin (κ : OTSelector.PartialMatching m n) (hκ : κ ∈ S) :
      τ.cost d + t * τ.cost h ≤ κ.cost d + t * κ.cost h := by
    have hb := legalMaximumValue_le (fun i j ↦ d i j + t * h i j) hκ.1 hκ.2
    rw [← hcostτ,hlin,hlin] at hb
    exact hb
  have hσobj : σ.cost c + t * σ.cost g =
      legalMaximumValue allowed (fun i j ↦ c i j + t * g i j) :=
    (hlin σ c g).symm.trans hcostσ
  have hτobj : τ.cost d + t * τ.cost h =
      legalMaximumValue allowed (fun i j ↦ d i j + t * h i j) :=
    (hlin τ d h).symm.trans hcostτ
  have hb := relative_tilted_minimum_abs_sub_le
    (S := S) (fun κ ↦ κ.cost c) (fun κ ↦ κ.cost d)
    (fun κ ↦ κ.cost g) (fun κ ↦ κ.cost h)
    (x := σ) (y := τ) ⟨hσ,hcardσ⟩ ⟨hτ,hcardτ⟩ hε0 hε1 hc hh hgh hσmin hτmin
  rw [hσobj,hτobj] at hb
  convert hb using 1
  ring

end PartialMatching

open OTSelector.Probability

/-- The same relative comparison for each literal original marked cloud.
The kinetic scale is the actual point intensity, and the cardinality is the
original class graph's true maximum, including clouds with Hall deficits. -/
theorem finiteClassLegalTilted_abs_sub_le_relative
    {A B : Type*} (q : ℕ) (allowed : A → B → Prop) (r : ℝ≥0)
    (kin reference : A → B → (Fin q → ℝ) → ℝ) (probe refProbe : A → B → ℝ)
    {ε G η : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hkin : ∀ a b, allowed a b → ∀ v, |kin a b v - reference a b v| ≤ ε * reference a b v)
    (hprobe : ∀ a b, allowed a b → |refProbe a b| ≤ G)
    (hprobeDiff : ∀ a b, allowed a b → |probe a b - refProbe a b| ≤ η)
    (t : ℝ) (ω : TwoMarkedCloudSpace q A B) :
    |finiteClassLegalTilted q allowed r kin probe t ω -
      finiteClassLegalTilted q allowed r reference refProbe t ω| ≤
      ε * (finiteClassLegalTilted q allowed r reference refProbe t ω +
        (PartialMatching.legalMaximumCard
          (finiteClassLegalGraph q (mSourceCount ω) (mTargetCount ω) allowed ω) : ℝ) * (|t| * G)) +
      (PartialMatching.legalMaximumCard
        (finiteClassLegalGraph q (mSourceCount ω) (mTargetCount ω) allowed ω) : ℝ) * (|t| * η) := by
  apply PartialMatching.abs_legalMaximumValue_perturbed_sub_le_relative _ _ _ _ _ hε0 hε1
  · intro i j hij
    have ha : allowed (mSourceMark ω i) (mTargetMark ω j) := (Finset.mem_filter.mp hij).2
    have hs : 0 ≤ (r : ℝ) ^ (2 / (q : ℝ)) := Real.rpow_nonneg (NNReal.coe_nonneg _) _
    dsimp only [mKineticCost]
    rw [← mul_sub,abs_mul,abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left (hkin _ _ ha _) hs).trans_eq (by ring)
  · intro i j hij
    exact hprobe _ _ (Finset.mem_filter.mp hij).2
  · intro i j hij
    exact hprobeDiff _ _ (Finset.mem_filter.mp hij).2


section FiniteOriginalLaws
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [Fintype A] [Fintype B] [DecidableEq B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B]

/-- Ordinary measurability and quadratic growth give integrability of the
literal finite-mask pressure. The exact finite nested mask is encoded internally
only to reuse the original legal-cloud integrability theorem. -/
theorem integrable_finiteClassLegalTilted_of_nested
    (q : ℕ) (allowed : A → B → Prop)
    (hnested : ∀ a a', (∀ b, allowed a b → allowed a' b) ∨
      (∀ b, allowed a' b → allowed a b))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, allowed a b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (probe : A → B → ℝ) (hprobe : ∀ a b, allowed a b → |probe a b| ≤ G) (t : ℝ) :
    Integrable (finiteClassLegalTilted q allowed r kin probe t)
      (twoMarkedCloudLaw q A B α β r) := by
  obtain ⟨source,target,hcode,_⟩ :=
    OTSelector.FiniteRelation.exists_strict_clocks_of_nested_relation allowed hnested
  have hb := integrable_legalMarkedTilted_of_forward q
    (measurable_of_countable source) (measurable_of_countable target) α β r hC hG hk
    (fun a b hab ↦ hkb a b ((hcode a b).mpr hab))
    (measurable_of_countable (Function.uncurry probe))
    (fun a b hab ↦ hprobe a b ((hcode a b).mpr hab)) t
  have heq : finiteClassLegalTilted q allowed (r : ℝ) kin probe t =
      legalMarkedTilted q source target r kin probe t :=
    funext (finiteClassLegalTilted_eq_clock q allowed source target hcode r kin probe t)
  rw [heq]
  exact hb

/-- Expected relative coefficient error is paid by the original reference
pressure and one original mean count. No optimizer second-moment assumption or
additional geometric restriction is required. -/
theorem finiteClassLegalPressure_abs_sub_le_relative
    (q : ℕ) (allowed : A → B → Prop)
    (hnested : ∀ a a', (∀ b, allowed a b → allowed a' b) ∨
      (∀ b, allowed a' b → allowed a b))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {C Cref G H ε η : ℝ}
    (hC : 0 ≤ C) (hCref : 0 ≤ Cref) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    {kin reference : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (href : Measurable (Function.uncurry (fun p : A × B ↦ reference p.1 p.2)))
    (hkb : ∀ a b, allowed a b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hrefb : ∀ a b, allowed a b → ∀ v, |reference a b v| ≤ Cref * ∑ l, v l ^ 2)
    (probe refProbe : A → B → ℝ)
    (hprobe : ∀ a b, allowed a b → |probe a b| ≤ H)
    (hprobeRef : ∀ a b, allowed a b → |refProbe a b| ≤ G)
    (hkin : ∀ a b, allowed a b → ∀ v, |kin a b v - reference a b v| ≤ ε * reference a b v)
    (hprobeDiff : ∀ a b, allowed a b → |probe a b - refProbe a b| ≤ η) (t : ℝ) :
    |finiteClassLegalPressure q allowed α β r kin probe t -
      finiteClassLegalPressure q allowed α β r reference refProbe t| ≤
      ε * (finiteClassLegalPressure q allowed α β r reference refProbe t + (r : ℝ) * (|t| * G)) +
        (r : ℝ) * (|t| * η) := by
  let V := finiteClassLegalTilted q allowed r kin probe t
  let Vref := finiteClassLegalTilted q allowed r reference refProbe t
  let law := twoMarkedCloudLaw q A B α β r
  have hI : Integrable V law := integrable_finiteClassLegalTilted_of_nested q allowed hnested
    α β r hC hH hk hkb probe hprobe t
  have hIref : Integrable Vref law := integrable_finiteClassLegalTilted_of_nested q allowed hnested
    α β r hCref hG href hrefb refProbe hprobeRef t
  let b := ε * (|t| * G) + |t| * η
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hbound (ω : TwoMarkedCloudSpace q A B) :
      |V ω - Vref ω| ≤ ε * Vref ω + (mSourceCount ω : ℝ) * b := by
    have hv := finiteClassLegalTilted_abs_sub_le_relative q allowed r kin reference probe refProbe
      hε0 hε1 hkin hprobeRef hprobeDiff t ω
    have hcard : (PartialMatching.legalMaximumCard
        (finiteClassLegalGraph q (mSourceCount ω) (mTargetCount ω) allowed ω) : ℝ) ≤
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
      dsimp only [b,Vref,law,finiteClassLegalPressure]
      ring


/-- The relative bound survives the original spatial-volume normalization
with exactly the same constants, uniformly over every positive side length. -/
theorem finiteClassLegalScalePressure_abs_sub_le_relative
    (q : ℕ) (allowed : A → B → Prop)
    (hnested : ∀ a a', (∀ b, allowed a b → allowed a' b) ∨
      (∀ b, allowed a' b → allowed a b))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {C G ε η : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    {kin reference : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (href : Measurable (Function.uncurry (fun p : A × B ↦ reference p.1 p.2)))
    (hkb : ∀ a b, allowed a b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hrefb : ∀ a b, allowed a b → ∀ v, |reference a b v| ≤ C * ∑ l, v l ^ 2)
    (probe refProbe : A → B → ℝ)
    (hprobe : ∀ a b, allowed a b → |probe a b| ≤ G)
    (hprobeRef : ∀ a b, allowed a b → |refProbe a b| ≤ G)
    (hkin : ∀ a b, allowed a b → ∀ v, |kin a b v - reference a b v| ≤ ε * reference a b v)
    (hprobeDiff : ∀ a b, allowed a b → |probe a b - refProbe a b| ≤ η)
    {R : ℝ} (hR : 0 < R) (t : ℝ) :
    |finiteClassLegalScalePressure q allowed α β kin probe R t -
      finiteClassLegalScalePressure q allowed α β reference refProbe R t| ≤
      ε * (finiteClassLegalScalePressure q allowed α β reference refProbe R t + |t| * G) +
        |t| * η := by
  have hV : 0 < R ^ q := pow_pos hR q
  have hb := finiteClassLegalPressure_abs_sub_le_relative q allowed hnested α β
    (Real.toNNReal (R ^ q)) hC hC hG hG hε0 hε1 hη hk href hkb hrefb probe refProbe
    hprobe hprobeRef hkin hprobeDiff t
  rw [Real.coe_toNNReal _ hV.le] at hb
  simp only [finiteClassLegalScalePressure,hR,↓reduceIte]
  rw [← sub_div,abs_div,abs_of_pos hV]
  apply (div_le_iff₀ hV).mpr
  apply hb.trans_eq
  field_simp [hV.ne']

/-- The actual thermodynamic limits inherit the relative geometric stability
bound. Kernel and probe changes require no extra transport rank, topology or
optimizer moment hypotheses. -/
theorem finiteClassLegalPressure_limits_abs_sub_le_relative
    (q : ℕ) (allowed : A → B → Prop)
    (hnested : ∀ a a', (∀ b, allowed a b → allowed a' b) ∨
      (∀ b, allowed a' b → allowed a b))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {C G ε η : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    {kin reference : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (href : Measurable (Function.uncurry (fun p : A × B ↦ reference p.1 p.2)))
    (hkb : ∀ a b, allowed a b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hrefb : ∀ a b, allowed a b → ∀ v, |reference a b v| ≤ C * ∑ l, v l ^ 2)
    (probe refProbe : A → B → ℝ)
    (hprobe : ∀ a b, allowed a b → |probe a b| ≤ G)
    (hprobeRef : ∀ a b, allowed a b → |refProbe a b| ≤ G)
    (hkin : ∀ a b, allowed a b → ∀ v, |kin a b v - reference a b v| ≤ ε * reference a b v)
    (hprobeDiff : ∀ a b, allowed a b → |probe a b - refProbe a b| ≤ η)
    (p pref : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q allowed α β kin probe R t)
      atTop (𝓝 (p t)))
    (hpref : ∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q allowed α β reference refProbe R t)
      atTop (𝓝 (pref t))) (t : ℝ) :
    |p t - pref t| ≤ ε * (pref t + |t| * G) + |t| * η := by
  have hleft := ((hp t).sub (hpref t)).abs
  have hright := (((hpref t).add_const (|t| * G)).const_mul ε).add_const (|t| * η)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact finiteClassLegalScalePressure_abs_sub_le_relative q allowed hnested α β hC hG
    hε0 hε1 hη hk href hkb hrefb probe refProbe hprobe hprobeRef hkin hprobeDiff hR t

end FiniteOriginalLaws
end OTSelector.Reconstruction
