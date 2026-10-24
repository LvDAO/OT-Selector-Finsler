import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureLimit
import OTSelector.Reconstruction.MarkedStationaryValueLegalLocallyUniform
import OTSelector.Finite.NestedRelationClock

/-!
# Actual finite-class legal pressure limit

The allowed class mask is kept literally on the original finite class indices.
Exact finite nested-neighborhood clock coding supplies the half-gap and compact
scalar bins needed by the true legal pressure engine. The input kernel, probe,
class laws and feasible original coupling are unchanged.
-/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The literal allowed finite-class mask on original cloud vertices. -/
def finiteClassLegalGraph (q m n : ℕ) (allowed : A → B → Prop)
    (ω : TwoMarkedCloudSpace q A B) : Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun e ↦ allowed (mSourceMark ω e.1) (mTargetMark ω e.2))

/-- The true maximum-cardinality signed minimum inside the original class mask. -/
def finiteClassLegalTilted (q : ℕ) (allowed : A → B → Prop) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  PartialMatching.legalMaximumValue
    (finiteClassLegalGraph q (mSourceCount ω) (mTargetCount ω) allowed ω)
    (fun i j ↦ mKineticCost q r kin ω i j + t * mProbe probe ω i j)

/-- Original independent class clouds with their literal finite allowed mask. -/
def finiteClassLegalPressure (q : ℕ) (allowed : A → B → Prop)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, finiteClassLegalTilted q allowed r kin probe t ω ∂twoMarkedCloudLaw q A B α β r

def finiteClassLegalScalePressure (q : ℕ) (allowed : A → B → Prop)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (R t : ℝ) : ℝ :=
  if 0 < R then
    finiteClassLegalPressure q allowed α β (Real.toNNReal (R ^ q)) kin probe t / R ^ q
  else 0

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem finiteClassLegalGraph_eq_clock (q m n : ℕ) (allowed : A → B → Prop)
    (source : A → ℝ) (target : B → ℝ)
    (hcode : ∀ a b, allowed a b ↔ source a < target b) (ω : TwoMarkedCloudSpace q A B) :
    finiteClassLegalGraph q m n allowed ω = legalMarkedGraph q m n source target ω := by
  ext e
  simp only [finiteClassLegalGraph, legalMarkedGraph, Finset.mem_filter, Finset.mem_univ,
    true_and, hcode]

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem finiteClassLegalTilted_eq_clock (q : ℕ) (allowed : A → B → Prop)
    (source : A → ℝ) (target : B → ℝ) (hcode : ∀ a b, allowed a b ↔ source a < target b)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    finiteClassLegalTilted q allowed r kin probe t ω =
      legalMarkedTilted q source target r kin probe t ω := by
  unfold finiteClassLegalTilted legalMarkedTilted legalMarkedFixedValue
  rw [finiteClassLegalGraph_eq_clock q _ _ allowed source target hcode]

theorem finiteClassLegalPressure_eq_clock (q : ℕ) (allowed : A → B → Prop)
    (source : A → ℝ) (target : B → ℝ) (hcode : ∀ a b, allowed a b ↔ source a < target b)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ) :
    finiteClassLegalPressure q allowed α β r kin probe t =
      legalMarkedPressure q source target α β r kin probe t := by
  apply integral_congr_ae
  filter_upwards with ω
  exact finiteClassLegalTilted_eq_clock q allowed source target hcode r kin probe t ω

theorem finiteClassLegalScalePressure_eq_clock (q : ℕ) (allowed : A → B → Prop)
    (source : A → ℝ) (target : B → ℝ) (hcode : ∀ a b, allowed a b ↔ source a < target b)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (R t : ℝ) :
    finiteClassLegalScalePressure q allowed α β kin probe R t =
      legalMarkedScalePressure q source target α β kin probe R t := by
  by_cases hR : 0 < R
  · simp only [finiteClassLegalScalePressure, legalMarkedScalePressure, hR, ↓reduceIte,
      finiteClassLegalPressure_eq_clock q allowed source target hcode]
  · simp only [finiteClassLegalScalePressure, legalMarkedScalePressure, hR, ↓reduceIte]

/-- The actual finite nested class mask has a full real-scale pressure limit.
The exact mask clocks, half-gap, compact range and scalar bins are all produced
internally. The feasible input coupling is the original class population plan. -/
theorem exists_finiteClassLegalScalePressure_limit_of_nested
    [Fintype A] [Fintype B] [DecidableEq B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (allowed : A → B → Prop)
    (hnested : ∀ a a', (∀ b, allowed a b → allowed a' b) ∨
      (∀ b, allowed a' b → allowed a b))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (π : Measure (A × B)) [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π α β)
    (hlegal : ∀ᵐ p ∂π, allowed p.1 p.2)
    (q : ℕ) (hq : 4 < q) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (probe : A → B → ℝ) (hpb : ∀ a b, |probe a b| ≤ G) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q allowed α β kin probe R t)
        atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G, hG⟩ p := by
  obtain ⟨source, target, hcode, hsep, hsource, htarget⟩ :=
    OTSelector.FiniteRelation.exists_strict_clocks_of_nested_relation allowed hnested
  have hs : Measurable source := measurable_of_countable _
  have ht : Measurable target := measurable_of_countable _
  have hp : Measurable (Function.uncurry probe) := measurable_of_countable _
  let I : Set ℝ := Icc (-((Fintype.card B : ℝ) + 1)) 1
  obtain ⟨D⟩ := exists_finiteScalarBins (show IsCompact I from isCompact_Icc)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I :=
    Filter.Eventually.of_forall (fun p ↦ ⟨hsource p.1, htarget p.2⟩)
  have hgap : ∀ᵐ p ∂π, (1 / 2 : ℝ) ≤ target p.2 - source p.1 := by
    filter_upwards [hlegal] with p hp
    simpa only [abs_of_pos (sub_pos.mpr ((hcode p.1 p.2).mp hp))] using hsep p.1 p.2
  obtain ⟨p, hpt, hconc, hlip⟩ := exists_legalMarkedScalePressure_limit_of_scalarBins D
    (by norm_num) (show MeasurableSet I from measurableSet_Icc) source target hs ht π α β hπ
    hI hgap (Filter.Eventually.of_forall (fun p ↦ hsep p.1 p.2)) q hq hC hG hk hkn hkb hhom hp hpb
  refine ⟨p, ?_, hconc, hlip⟩
  intro t
  simpa only [finiteClassLegalScalePressure_eq_clock q allowed source target hcode] using hpt t

/-- On the same original class clouds, any actual pointwise pressure limit is
uniform on every compact tilt set. No choice of clock encoding affects it. -/
theorem tendstoUniformlyOn_finiteClassLegalScalePressure_of_nested
    [Fintype A] [Fintype B] [DecidableEq B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (allowed : A → B → Prop)
    (hnested : ∀ a a', (∀ b, allowed a b → allowed a' b) ∨
      (∀ b, allowed a' b → allowed a b))
    (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (probe : A → B → ℝ) (hpb : ∀ a b, |probe a b| ≤ G)
    {p : ℝ → ℝ}
    (hpt : ∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q allowed α β kin probe R t)
      atTop (𝓝 (p t))) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun R ↦ finiteClassLegalScalePressure q allowed α β kin probe R)
      p atTop K := by
  obtain ⟨source, target, hcode, _⟩ :=
    OTSelector.FiniteRelation.exists_strict_clocks_of_nested_relation allowed hnested
  have hpt' : ∀ t, Tendsto (fun R ↦
      legalMarkedScalePressure q source target α β kin probe R t) atTop (𝓝 (p t)) := by
    intro t
    simpa only [finiteClassLegalScalePressure_eq_clock q allowed source target hcode] using hpt t
  have h := tendstoUniformlyOn_legalMarkedScalePressure q (measurable_of_countable source)
    (measurable_of_countable target) α β hC hG hk (fun a b _ ↦ hkb a b)
    (measurable_of_countable (Function.uncurry probe)) (fun a b _ ↦ hpb a b) hpt' hK
  have heq : (fun R ↦ finiteClassLegalScalePressure q allowed α β kin probe R) =
      (fun R ↦ legalMarkedScalePressure q source target α β kin probe R) := by
    funext R t
    exact finiteClassLegalScalePressure_eq_clock q allowed source target hcode α β kin probe R t
  rw [heq]
  exact h

/-- Intensity normalization has the same actual finite-mask limit. -/
theorem tendsto_finiteClassLegalPressure_div_of_nested
    [Fintype A] [Fintype B] [DecidableEq B]
    (allowed : A → B → Prop)
    (hnested : ∀ a a', (∀ b, allowed a b → allowed a' b) ∨
      (∀ b, allowed a' b → allowed a b))
    (q : ℕ) (hq : 0 < q) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (p : ℝ → ℝ)
    (hpt : ∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q allowed α β kin probe R t)
      atTop (𝓝 (p t))) :
    ∀ t, Tendsto (fun r : ℝ ↦
      finiteClassLegalPressure q allowed α β (Real.toNNReal r) kin probe t / r)
      atTop (𝓝 (p t)) := by
  obtain ⟨source, target, hcode, _⟩ :=
    OTSelector.FiniteRelation.exists_strict_clocks_of_nested_relation allowed hnested
  have hpt' : ∀ t, Tendsto (fun R ↦
      legalMarkedScalePressure q source target α β kin probe R t) atTop (𝓝 (p t)) := by
    intro t
    simpa only [finiteClassLegalScalePressure_eq_clock q allowed source target hcode] using hpt t
  intro t
  simpa only [finiteClassLegalPressure_eq_clock q allowed source target hcode] using
    tendsto_legalMarkedPressure_div q hq source target α β kin probe p hpt' t

end OTSelector.Reconstruction
