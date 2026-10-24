import OTSelector.Reconstruction.MarkedStationaryValueLegalShapeExpectation
import OTSelector.Probability.MarkedCountShapeCloud

/-! Uniform finite-sample shape filling for the original binomial count law.
The shape and kinetic scale may change with N; the estimate is pointwise in
these inputs and uses the exact original deleted-point mean. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Any original independent integrable count law makes the bounded legal
marked value integrable, with its kinetic scale left independent of that law. -/
theorem integrable_legalMarkedTilted_countLaw (q : ℕ)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (κ : Measure ℕ) [IsProbabilityMeasure κ]
    (hκ : Integrable (fun n : ℕ ↦ (n : ℝ)) κ) {r : ℝ} (hr : 0 ≤ r)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (legalMarkedTilted q source target r kin g t) (twoMarkedCountLaw q α β κ) := by
  have hcount := (hκ.comp_fst (markedSeqLaw q A α)).comp_fst (markedCountLaw q β κ)
  have hB0 : 0 ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by positivity
  apply (hcount.mul_const (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G)).mono'
    (measurable_legalMarkedTilted q hs ht hk hg r t).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (abs_legalMarkedTilted_le q source target hr hC hG hkb hgb t ω).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_left _ _)) hB0)

/-- Exact original count-law filling/deletion comparison at finite kinetic
scale, uniform over every measurable shape. -/
theorem FiniteScalarBins.integral_shapeLegalMarkedTilted_countLaw_sub_le
    {clockSet : Set ℝ} {gap : ℝ} (D : FiniteScalarBins clockSet gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (κ : Measure ℕ) [IsProbabilityMeasure κ]
    (hκ : Integrable (fun n : ℕ ↦ (n : ℝ)) κ) {r : ℝ} (hr : 0 ≤ r)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hsource : ∀ᵐ a ∂α, source a ∈ clockSet)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (shapeLegalMarkedTilted q source target S r kin g t)
      (twoMarkedCountLaw q α β κ) ∧
    |(∫ ω, shapeLegalMarkedTilted q source target S r kin g t ω
        ∂twoMarkedCountLaw q α β κ) - (∫ ω, legalMarkedTilted q source target r kin g t ω
          ∂twoMarkedCountLaw q α β κ)| ≤
      (2 * (∫ n : ℕ, (n : ℝ) ∂κ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          (r ^ (2 / (q : ℝ)) * (C * q) + |t| * G)) := by
  let _instA : Nonempty A := nonempty_of_isProbabilityMeasure α
  let _instB : Nonempty B := nonempty_of_isProbabilityMeasure β
  let P := twoMarkedCountLaw q α β κ
  let V := shapeLegalMarkedTilted q source target S r kin g t
  let W := legalMarkedTilted q source target r kin g t
  let K := 2 * ((D.count : ℝ) + 1) *
    (r ^ (2 / (q : ℝ)) * (C * q) + |t| * G)
  let missing : TwoMarkedCloudSpace q A B → ℝ := fun ω ↦
    (((mSourceCount ω - (shapeCloud S ω.1).1) +
      (mTargetCount ω - (shapeCloud S ω.2).1) : ℕ) : ℝ)
  have hsourceI := (integrable_markedCount_shape_missing q α κ hκ hS).comp_fst
    (markedCountLaw q β κ)
  have htargetI := (integrable_markedCount_shape_missing q β κ hκ hS).comp_snd
    (markedCountLaw q α κ)
  have hmissingI : Integrable missing P := by
    have hsum := hsourceI.add htargetI
    apply hsum.congr
    filter_upwards [] with ω
    simp only [missing, Nat.cast_add, mSourceCount, mTargetCount, Pi.add_apply]
  have hboundI := hmissingI.mul_const K
  have hfullI : Integrable W P := integrable_legalMarkedTilted_countLaw q hs ht α β κ hκ
    hr hC hG hk hkb hg hgb t
  have hAE : ∀ᵐ ω ∂P, |V ω - W ω| ≤ missing ω * K := by
    have hac := twoMarkedCountLaw_absolutelyContinuous_poisson_one q α β κ
    filter_upwards [hac.ae_le (ae_all_mSourceMark q α β 1 hsource),
      hac.ae_le (ae_all_mMarkPair q α β 1 (P := fun a b ↦ gap ≤ |target b - source a|) hsep)]
      with ω hsrc hpair
    exact D.abs_shapeLegalMarkedTilted_sub_le hgap q source target S hr hC hG
      kin g t hkb hgb ω hsrc hpair
  have hmeas : Measurable V := measurable_shapeLegalMarkedTilted q hs ht hS r hk hg t
  have hshapeI : Integrable V P := (hfullI.norm.add hboundI).mono'
      hmeas.aestronglyMeasurable (by
    filter_upwards [hAE] with ω hω
    simp only [Pi.add_apply, Real.norm_eq_abs]
    apply abs_le.mpr
    have hlow := (abs_le.mp hω).1
    have hupp := (abs_le.mp hω).2
    have hpos := le_abs_self (W ω)
    have hneg := neg_abs_le (W ω)
    constructor <;> linarith)
  have hmeanSource :
      (∫ ω : TwoMarkedCloudSpace q A B, ((mSourceCount ω - (shapeCloud S ω.1).1 : ℕ) : ℝ) ∂P) =
        (∫ n : ℕ, (n : ℝ) ∂κ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal := by
    change (∫ ω, ((ω.1.1 - (shapeCloud S ω.1).1 : ℕ) : ℝ)
      ∂(markedCountLaw q α κ).prod (markedCountLaw q β κ)) = _
    rw [integral_fun_fst (fun z : MarkedCloudSpace q A ↦ ((z.1 - (shapeCloud S z).1 : ℕ) : ℝ))]
    simpa using integral_markedCount_shape_missing q α κ hκ hS
  have hmeanTarget :
      (∫ ω : TwoMarkedCloudSpace q A B, ((mTargetCount ω - (shapeCloud S ω.2).1 : ℕ) : ℝ) ∂P) =
        (∫ n : ℕ, (n : ℝ) ∂κ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal := by
    change (∫ ω, ((ω.2.1 - (shapeCloud S ω.2).1 : ℕ) : ℝ)
      ∂(markedCountLaw q α κ).prod (markedCountLaw q β κ)) = _
    rw [integral_fun_snd (fun z : MarkedCloudSpace q B ↦ ((z.1 - (shapeCloud S z).1 : ℕ) : ℝ))]
    simpa using integral_markedCount_shape_missing q β κ hκ hS
  have hmean : (∫ ω, missing ω ∂P) =
      2 * (∫ n : ℕ, (n : ℝ) ∂κ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal := by
    simp only [missing, Nat.cast_add]
    have hadd := integral_add hsourceI htargetI
    change (∫ ω, ((ω.1.1 - (shapeCloud S ω.1).1 : ℕ) : ℝ) +
      ((ω.2.1 - (shapeCloud S ω.2).1 : ℕ) : ℝ)
      ∂(markedCountLaw q α κ).prod (markedCountLaw q β κ)) = _
    rw [hadd]
    change (∫ ω : TwoMarkedCloudSpace q A B, ((mSourceCount ω - (shapeCloud S ω.1).1 : ℕ) : ℝ) ∂P) +
      (∫ ω : TwoMarkedCloudSpace q A B, ((mTargetCount ω - (shapeCloud S ω.2).1 : ℕ) : ℝ) ∂P) = _
    rw [hmeanSource, hmeanTarget]
    ring
  refine ⟨hshapeI, ?_⟩
  change |(∫ ω, V ω ∂P) - ∫ ω, W ω ∂P| ≤ _
  calc
    _ = |∫ ω, V ω - W ω ∂P| := by rw [integral_sub hshapeI hfullI]
    _ ≤ ∫ ω, |V ω - W ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, missing ω * K ∂P :=
      integral_mono_ae (hshapeI.sub hfullI).abs hboundI hAE
    _ = _ := by rw [integral_mul_const, hmean]

/-- Exact original binomial finite-N shape comparison. The kinetic scale r is
independent of N*p and may vary along with the measurable shape. -/
theorem FiniteScalarBins.integral_shapeLegalMarkedTilted_binomial_sub_le
    {clockSet : Set ℝ} {gap : ℝ} (D : FiniteScalarBins clockSet gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) {r : ℝ} (hr : 0 ≤ r)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hsource : ∀ᵐ a ∂α, source a ∈ clockSet)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (shapeLegalMarkedTilted q source target S r kin g t)
      (twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)) ∧
    |(∫ ω, shapeLegalMarkedTilted q source target S r kin g t ω
        ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)) - (∫ ω, legalMarkedTilted q source target r kin g t ω
          ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p))| ≤
      (2 * ((N : ℝ) * (p : ℝ)) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          (r ^ (2 / (q : ℝ)) * (C * q) + |t| * G)) := by
  simpa only [integral_binomial_id] using
    D.integral_shapeLegalMarkedTilted_countLaw_sub_le hgap q hs ht α β
      (ProbabilityTheory.binomial N p) (integrable_binomial _) hr hS hsource hsep
      hC hG hk hkb hg hgb t

end OTSelector.Reconstruction
