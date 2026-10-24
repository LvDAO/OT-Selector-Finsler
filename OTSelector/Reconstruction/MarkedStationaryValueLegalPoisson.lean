import OTSelector.Reconstruction.MarkedStationaryValueLegalTypes
import OTSelector.Reconstruction.MarkedStationaryValueLegalCloud
import OTSelector.Probability.PoissonLabelSplittingGeneral
import OTSelector.Probability.MarkedGridDiscrepancy
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Original marked Poisson type laws and legal matching deficits

Forgetting positions preserves the literal original Poisson count and iid type
law. Finite type counts split into independent Poisson coordinates, giving an
integrable square-root discrepancy bound under the actual two-color marked cloud
law. Same-type legal rectangles then bound the actual forward-graph Hall defect,
including unequal realized color counts. The final producer checks legality on
the original product mark law and derives it simultaneously for every cloud edge.
This establishes finite-count control; it does not assert a legal pressure limit
or a stationary Palm value identification.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

variable {q : ℕ} {A B T : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace T]

/-- Forget positions and retain only the original Poisson count and mark types. -/
def markedTypeCloud (tag : A → T) (z : MarkedCloudSpace q A) : ℕ × (ℕ → T) :=
  (z.1, fun i ↦ tag (z.2 i).2)

theorem measurable_markedTypeCloud {tag : A → T} (htag : Measurable tag) :
    Measurable (markedTypeCloud (q := q) tag) := by
  unfold markedTypeCloud
  fun_prop

/-- Types of iid marked points have their exact original type law. -/
theorem map_markedSeqLaw_types (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    {tag : A → T} (htag : Measurable tag) :
    (markedSeqLaw q A α).map (fun x : ℕ → (Fin q → ℝ) × A ↦ fun i ↦ tag (x i).2) =
      Measure.infinitePi (fun _ : ℕ ↦ α.map tag) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  unfold markedSeqLaw
  change (Measure.infinitePi (fun _ : ℕ ↦ (cubeMeasure (Fin q) 1).prod α)).map
    (fun x i ↦ (tag ∘ (Prod.snd : (Fin q → ℝ) × A → A)) (x i)) = _
  rw [Measure.infinitePi_map_pi
    (μ := fun _ : ℕ ↦ (cubeMeasure (Fin q) 1).prod α)
    (f := fun _ : ℕ ↦ tag ∘ (Prod.snd : (Fin q → ℝ) × A → A))
    (fun _ ↦ htag.comp measurable_snd)]
  congr 1
  funext i
  rw [← Measure.map_map htag measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

/-- The actual marked Poisson count is independent of its iid type sequence. -/
theorem map_markedPoissonLaw_types (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    {tag : A → T} (htag : Measurable tag) (r : ℝ≥0) :
    (markedPoissonLaw q A α r).map (markedTypeCloud tag) =
      (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ α.map tag)) := by
  unfold markedPoissonLaw markedTypeCloud
  change ((poissonMeasure r).prod (markedSeqLaw q A α)).map
    (Prod.map id (fun x : ℕ → (Fin q → ℝ) × A ↦ fun i ↦ tag (x i).2)) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
    map_markedSeqLaw_types q α htag]

/-- Common original type laws give the exact independent two-color type process. -/
theorem map_twoMarkedCloudLaw_types (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {tagA : A → T} {tagB : B → T} (hA : Measurable tagA) (hB : Measurable tagB)
    (L : Measure T) (hLA : α.map tagA = L) (hLB : β.map tagB = L) (r : ℝ≥0) :
    (twoMarkedCloudLaw q A B α β r).map
      (Prod.map (markedTypeCloud tagA) (markedTypeCloud tagB)) =
      ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ L))).prod
        ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ L))) := by
  unfold twoMarkedCloudLaw
  rw [← Measure.map_prod_map _ _ (measurable_markedTypeCloud hA) (measurable_markedTypeCloud hB),
    map_markedPoissonLaw_types q α hA, map_markedPoissonLaw_types q β hB, hLA, hLB]


/-- A Poisson count and its independent original iid type marks. -/
def poissonTypeLaw (T : Type*) [MeasurableSpace T] (L : Measure T)
    [IsProbabilityMeasure L] (r : ℝ≥0) : Measure (ℕ × (ℕ → T)) :=
  (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ L))

instance (T : Type*) [MeasurableSpace T] (L : Measure T) [IsProbabilityMeasure L] (r : ℝ≥0) :
    IsProbabilityMeasure (poissonTypeLaw T L r) := by
  unfold poissonTypeLaw
  infer_instance

/-- The actual number of points of a prescribed finite type. -/
def poissonTypeCount [DecidableEq T] (z : ℕ × (ℕ → T)) (t : T) : ℕ :=
  (Finset.univ.filter (fun i : Fin z.1 ↦ z.2 i = t)).card

/-- Type counts are measurable before any conditioning or realization is chosen. -/
theorem measurable_poissonTypeCount [Fintype T] [MeasurableSingletonClass T] [DecidableEq T] :
    Measurable (poissonTypeCount (T := T)) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun seq : ℕ → T ↦ fun t ↦
    (Finset.univ.filter (fun i : Fin n ↦ seq i = t)).card)
  let f : (Fin n → T) → (T → ℕ) := fun v t ↦ (Finset.univ.filter (fun i ↦ v i = t)).card
  exact (measurable_of_countable f).comp (measurable_pi_lambda _
    (fun i : Fin n ↦ measurable_pi_apply (i : ℕ)))

/-- Every finite original type law is exactly its singleton-weight representation. -/
theorem finiteTypeLaw_eq_sum_dirac {K : ℕ} (L : Measure (Fin K)) [IsProbabilityMeasure L] :
    L = Measure.sum (fun b : Fin K ↦ ((L {b}).toNNReal : ℝ≥0∞) • Measure.dirac b) := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.sum_apply _ (measurableSet_singleton b)]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton b)]
  simpa [Pi.single_apply, eq_comm] using (ENNReal.coe_toNNReal (measure_ne_top L {b})).symm

/-- Original finite type masses form a probability vector, including zero-mass types. -/
theorem sum_finiteTypeWeight_eq_one {K : ℕ} (L : Measure (Fin K)) [IsProbabilityMeasure L] :
    (∑ b : Fin K, (L {b}).toNNReal) = 1 := by
  apply NNReal.eq
  push_cast
  change (∑ b : Fin K, L.real {b}) = 1
  simp

/-- The actual Poisson type histogram has independent Poisson coordinates. -/
theorem map_poissonTypeCount {K : ℕ} [NeZero K]
    (L : Measure (Fin K)) [IsProbabilityMeasure L] (r : ℝ≥0) :
    (poissonTypeLaw (Fin K) L r).map poissonTypeCount =
      Measure.pi (fun b : Fin K ↦ poissonMeasure (r * (L {b}).toNNReal)) := by
  let P := poissonTypeLaw (Fin K) L r
  let N : (ℕ × (ℕ → Fin K)) → ℕ := Prod.fst
  let w : ℕ → (ℕ × (ℕ → Fin K)) → Fin K := fun i z ↦ z.2 i
  have hN : P.map N = poissonMeasure r := by
    simp [P, N, poissonTypeLaw, Measure.map_fst_prod]
  have hw : ∀ n, iIndepFun (fun i : Fin n ↦ w i) P := by
    intro n
    have hseq : iIndepFun (fun (i : ℕ) (z : ℕ → Fin K) ↦ z i)
        (Measure.infinitePi (fun _ : ℕ ↦ L)) :=
      iIndepFun_infinitePi (X := fun _ x ↦ x) (fun _ ↦ measurable_id)
    exact iIndepFun_snd_prod
      (ν₁ := poissonMeasure r) (ν₂ := Measure.infinitePi (fun _ : ℕ ↦ L))
      (fun i : Fin n ↦ measurable_pi_apply (i : ℕ))
      (hseq.precomp (fun i j hij ↦ Fin.ext hij))
  have hlaw (i : ℕ) : P.map (w i) =
      Measure.sum (fun b : Fin K ↦ ((L {b}).toNNReal : ℝ≥0∞) • Measure.dirac b) := by
    change P.map ((Function.eval i) ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_pi_apply i) measurable_snd]
    simp only [P, poissonTypeLaw, Measure.map_snd_prod, measure_univ, one_smul,
      Measure.infinitePi_map_eval]
    exact finiteTypeLaw_eq_sum_dirac L
  have hindep : ∀ n, IndepFun N (fun z ↦ fun i : Fin n ↦ w i z) P := by
    intro n
    exact indepFun_prod measurable_id (measurable_pi_lambda _
      (fun i : Fin n ↦ measurable_pi_apply (i : ℕ)))
  exact map_poisson_label_counts_general r N w (fun b ↦ (L {b}).toNNReal)
    (sum_finiteTypeWeight_eq_one L) hN hw hlaw hindep


/-- The expected actual two-color type discrepancy is of square-root order. -/
theorem poissonType_discrepancy_integrable_bound {K : ℕ} [NeZero K]
    (L : Measure (Fin K)) [IsProbabilityMeasure L] (r : ℝ≥0) :
    let P := poissonTypeLaw (Fin K) L r
    let F := fun z : (ℕ × (ℕ → Fin K)) × (ℕ × (ℕ → Fin K)) ↦
      ∑ b : Fin K, |(poissonTypeCount z.1 b : ℝ) - (poissonTypeCount z.2 b : ℝ)|
    Integrable F (P.prod P) ∧ (∫ z, F z ∂P.prod P) ≤ Real.sqrt (2 * (r : ℝ) * K) := by
  let P := poissonTypeLaw (Fin K) L r
  let F := fun z : (ℕ × (ℕ → Fin K)) × (ℕ × (ℕ → Fin K)) ↦
    ∑ b : Fin K, |(poissonTypeCount z.1 b : ℝ) - (poissonTypeCount z.2 b : ℝ)|
  have hcount : Measurable (poissonTypeCount (T := Fin K)) := measurable_poissonTypeCount
  have hFm : Measurable F := by
    apply Finset.measurable_sum
    intro b _
    have hfst : Measurable (fun z : (ℕ × (ℕ → Fin K)) × (ℕ × (ℕ → Fin K)) ↦
        (poissonTypeCount z.1 b : ℝ)) :=
      measurable_from_nat.comp (((measurable_pi_apply b).comp hcount).comp measurable_fst)
    have hsnd : Measurable (fun z : (ℕ × (ℕ → Fin K)) × (ℕ × (ℕ → Fin K)) ↦
        (poissonTypeCount z.2 b : ℝ)) :=
      measurable_from_nat.comp (((measurable_pi_apply b).comp hcount).comp measurable_snd)
    exact (hfst.sub hsnd).abs
  have hNi : Integrable (fun z : ℕ × (ℕ → Fin K) ↦ (z.1 : ℝ)) P :=
    (integrable_id_poissonMeasure r).comp_fst _
  have hsum (z : ℕ × (ℕ → Fin K)) : ∑ b : Fin K, poissonTypeCount z b = z.1 :=
    sum_card_blockFinset (fun i : Fin z.1 ↦ z.2 i)
  have hbound : ∀ z, ‖F z‖ ≤ (z.1.1 : ℝ) + z.2.1 := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))]
    calc
      F z ≤ ∑ b : Fin K, ((poissonTypeCount z.1 b : ℝ) + poissonTypeCount z.2 b) := by
        apply Finset.sum_le_sum
        intro b _
        have ha : |(poissonTypeCount z.1 b : ℝ)| = (poissonTypeCount z.1 b : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg _)
        have hb : |(poissonTypeCount z.2 b : ℝ)| = (poissonTypeCount z.2 b : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg _)
        simpa only [ha, hb] using
          (abs_sub (poissonTypeCount z.1 b : ℝ) (poissonTypeCount z.2 b : ℝ))
      _ = (z.1.1 : ℝ) + z.2.1 := by
        rw [Finset.sum_add_distrib, ← Nat.cast_sum, ← Nat.cast_sum, hsum, hsum]
  have hFi : Integrable F (P.prod P) :=
    ((hNi.comp_fst P).add (hNi.comp_snd P)).mono' hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  let rate := fun b : Fin K ↦ r * (L {b}).toNNReal
  let Q := Measure.pi (fun b : Fin K ↦ poissonMeasure (rate b))
  let f : (Fin K → ℕ) × (Fin K → ℕ) → ℝ :=
    fun z ↦ ∑ b : Fin K, |(z.1 b : ℝ) - z.2 b|
  have hfm : Measurable f := measurable_of_countable f
  have hpair : (P.prod P).map (Prod.map poissonTypeCount poissonTypeCount) = Q.prod Q := by
    rw [← Measure.map_prod_map _ _ hcount hcount, map_poissonTypeCount L r]
  have hI : (∫ z, F z ∂P.prod P) = ∫ z, f z ∂Q.prod Q := by
    rw [← hpair]
    exact (integral_map (hcount.prodMap hcount).aemeasurable hfm.aestronglyMeasurable).symm
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ (Fin K)
  have hmp : MeasurePreserving e
      (Measure.pi (fun b : Fin K ↦ (poissonMeasure (rate b)).prod (poissonMeasure (rate b))))
      (Q.prod Q) :=
    measurePreserving_arrowProdEquivProdArrow ℕ ℕ (Fin K)
      (fun b ↦ poissonMeasure (rate b)) (fun b ↦ poissonMeasure (rate b))
  have hCS : (∑ b : Fin K, Real.sqrt (2 * (rate b : ℝ))) ≤
      Real.sqrt (2 * (r : ℝ) * K) := by
    have h := sum_sqrt_typeMass_le (fun b : Fin K ↦ 2 * (rate b : ℝ)) (fun _ ↦ by positivity)
    have hp : (∑ b : Fin K, ((L {b}).toNNReal : ℝ)) = 1 := by
      exact_mod_cast sum_finiteTypeWeight_eq_one L
    have hr : (∑ b : Fin K, 2 * (rate b : ℝ)) = 2 * r := by
      simp only [rate, NNReal.coe_mul, ← Finset.mul_sum, hp, mul_one]
    rw [hr, Fintype.card_fin] at h
    convert h using 1
    congr 1
    ring
  refine ⟨hFi, hI.trans_le ?_⟩
  rw [← hmp.integral_comp e.measurableEmbedding f]
  exact (integral_sum_abs_sub_poissonPi_le rate).trans hCS


/-- The actual original marked cloud's two-color histogram discrepancy. -/
def markedTypeDiscrepancy {K : ℕ} (tagA : A → Fin K) (tagB : B → Fin K)
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  ∑ b : Fin K, |(poissonTypeCount (markedTypeCloud tagA ω.1) b : ℝ) -
    (poissonTypeCount (markedTypeCloud tagB ω.2) b : ℝ)|

/-- The original shared type laws discharge the Poisson histogram error. -/
theorem markedType_discrepancy_integrable_bound (q : ℕ) {K : ℕ} [NeZero K]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {tagA : A → Fin K} {tagB : B → Fin K} (hA : Measurable tagA) (hB : Measurable tagB)
    (L : Measure (Fin K)) [IsProbabilityMeasure L]
    (hLA : α.map tagA = L) (hLB : β.map tagB = L) (r : ℝ≥0) :
    Integrable (markedTypeDiscrepancy (q := q) tagA tagB) (twoMarkedCloudLaw q A B α β r) ∧
      (∫ ω, markedTypeDiscrepancy (q := q) tagA tagB ω ∂twoMarkedCloudLaw q A B α β r) ≤
        Real.sqrt (2 * (r : ℝ) * K) := by
  let P := poissonTypeLaw (Fin K) L r
  let f := fun z : (ℕ × (ℕ → Fin K)) × (ℕ × (ℕ → Fin K)) ↦
    ∑ b : Fin K, |(poissonTypeCount z.1 b : ℝ) - (poissonTypeCount z.2 b : ℝ)|
  let project := Prod.map (markedTypeCloud (q := q) tagA) (markedTypeCloud (q := q) tagB)
  have hp : MeasurePreserving project (twoMarkedCloudLaw q A B α β r) (P.prod P) :=
    ⟨(measurable_markedTypeCloud hA).prodMap (measurable_markedTypeCloud hB),
      map_twoMarkedCloudLaw_types q α β hA hB L hLA hLB r⟩
  have hbase := poissonType_discrepancy_integrable_bound L r
  have hcount : Measurable (poissonTypeCount (T := Fin K)) := measurable_poissonTypeCount
  have hfm : Measurable f := by
    apply Finset.measurable_sum
    intro b _
    have hfst : Measurable (fun z : (ℕ × (ℕ → Fin K)) × (ℕ × (ℕ → Fin K)) ↦
        (poissonTypeCount z.1 b : ℝ)) :=
      measurable_from_nat.comp (((measurable_pi_apply b).comp hcount).comp measurable_fst)
    have hsnd : Measurable (fun z : (ℕ × (ℕ → Fin K)) × (ℕ × (ℕ → Fin K)) ↦
        (poissonTypeCount z.2 b : ℝ)) :=
      measurable_from_nat.comp (((measurable_pi_apply b).comp hcount).comp measurable_snd)
    exact (hfst.sub hsnd).abs
  have hid : (∫ ω, markedTypeDiscrepancy (q := q) tagA tagB ω
      ∂twoMarkedCloudLaw q A B α β r) = ∫ z, f z ∂P.prod P := by
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable hfm.aestronglyMeasurable).symm
  exact ⟨hp.integrable_comp_of_integrable hbase.1, hid.trans_le hbase.2⟩

/-- The actual forward graph's realized maximum cardinality. -/
def legalMarkedMaximumCard (q : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) : ℕ :=
  PartialMatching.legalMaximumCard
    (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω)

/-- The realized legal cardinality is measurable at the original random cloud sizes. -/
theorem measurable_legalMarkedMaximumCard_cast (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock) :
    Measurable (fun ω ↦ (legalMarkedMaximumCard q sourceClock targetClock ω : ℝ)) := by
  intro S hS
  let fixed : ℕ → ℕ → TwoMarkedCloudSpace q A B → ℝ := fun m n ω ↦
    PartialMatching.legalMaximumCard (legalMarkedGraph q m n sourceClock targetClock ω)
  have hfixed (m n : ℕ) : Measurable (fixed m n) :=
    measurable_legalMaximumCard_cast (legalMarkedGraph q m n sourceClock targetClock)
      (measurableSet_legalMarkedGraph_eq q m n hsource htarget)
  have hpre : (fun ω ↦ (legalMarkedMaximumCard q sourceClock targetClock ω : ℝ)) ⁻¹' S =
      ⋃ m : ℕ, ⋃ n : ℕ,
        ({ω : TwoMarkedCloudSpace q A B | mSourceCount ω = m} ∩
          {ω | mTargetCount ω = n}) ∩ (fixed m n) ⁻¹' S := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨mSourceCount ω, mTargetCount ω, ⟨rfl, rfl⟩, hω⟩
    · rintro ⟨m, n, ⟨hm, hn⟩, hω⟩
      change (fixed (mSourceCount ω) (mTargetCount ω) ω) ∈ S
      simpa only [hm, hn] using hω
  rw [hpre]
  exact MeasurableSet.iUnion fun m ↦ MeasurableSet.iUnion fun n ↦
    ((measurableSet_eq_fun (measurable_mSourceCount q) measurable_const).inter
      (measurableSet_eq_fun (measurable_mTargetCount q) measurable_const)).inter (hfixed m n hS)

/-- The actual legal Hall defect is integrable, with no Hall-feasibility premise. -/
theorem integrable_legalMarkedMaximumCard_defect (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) :
    Integrable (fun ω ↦ ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) -
      legalMarkedMaximumCard q sourceClock targetClock ω) (twoMarkedCloudLaw q A B α β r) := by
  have hm : Measurable (fun ω : TwoMarkedCloudSpace q A B ↦
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)) :=
    measurable_from_nat.comp ((measurable_mSourceCount q).min (measurable_mTargetCount q))
  refine (integrable_mMinCount q α β r).mono'
    (hm.sub (measurable_legalMarkedMaximumCard_cast q hsource htarget)).aestronglyMeasurable ?_
  filter_upwards with ω
  have hcard : (legalMarkedMaximumCard q sourceClock targetClock ω : ℝ) ≤
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (PartialMatching.legalMaximumCard_le_min _)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hcard)]
  exact sub_le_self _ (Nat.cast_nonneg _)

/-- Same-type legal rectangles and the original shared Poisson type law give a
square-root Hall defect for the actual independent marked clouds. -/
theorem integral_legalMarkedMaximumCard_defect_le_of_types (q : ℕ) {K : ℕ} [NeZero K]
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {tagA : A → Fin K} {tagB : B → Fin K} (hA : Measurable tagA) (hB : Measurable tagB)
    (L : Measure (Fin K)) [IsProbabilityMeasure L]
    (hLA : α.map tagA = L) (hLB : β.map tagB = L) (r : ℝ≥0)
    (hlegal : ∀ᵐ ω ∂twoMarkedCloudLaw q A B α β r,
      ∀ (i : Fin (mSourceCount ω)) (j : Fin (mTargetCount ω)),
        tagA (mSourceMark ω i) = tagB (mTargetMark ω j) →
          sourceClock (mSourceMark ω i) < targetClock (mTargetMark ω j)) :
    (∫ ω, ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) -
      legalMarkedMaximumCard q sourceClock targetClock ω ∂twoMarkedCloudLaw q A B α β r) ≤
        (1 / 2 : ℝ) * Real.sqrt (2 * (r : ℝ) * K) := by
  obtain ⟨hdisc, hmean⟩ := markedType_discrepancy_integrable_bound q α β hA hB L hLA hLB r
  have hpt : ∀ᵐ ω ∂twoMarkedCloudLaw q A B α β r,
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) -
        legalMarkedMaximumCard q sourceClock targetClock ω ≤
          (1 / 2 : ℝ) * markedTypeDiscrepancy (q := q) tagA tagB ω := by
    filter_upwards [hlegal] with ω hω
    have h := legalMaximumCard_defect_le_type_discrepancy
      (fun i : Fin (mSourceCount ω) ↦ tagA (mSourceMark ω i))
      (fun j : Fin (mTargetCount ω) ↦ tagB (mTargetMark ω j))
      (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω)
      (fun i j hij ↦ by
        simpa only [legalMarkedGraph, Finset.mem_filter, Finset.mem_univ, true_and] using hω i j hij)
    have hc := PartialMatching.legalMaximumCard_le_min
      (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω)
    rw [Nat.cast_sub hc] at h
    change 2 * (((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) -
      legalMarkedMaximumCard q sourceClock targetClock ω) ≤
        markedTypeDiscrepancy tagA tagB ω at h
    linarith
  have hi := integrable_legalMarkedMaximumCard_defect q hsource htarget α β r
  have hbound := integral_mono_ae hi (hdisc.const_mul (1 / 2)) hpt
  rw [integral_const_mul] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left hmean (by norm_num))


/-- Every original mark has its original law at every cloud index. -/
theorem map_markedPoissonLaw_mark (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (r : ℝ≥0) (i : ℕ) :
    (markedPoissonLaw q A α r).map (fun z : MarkedCloudSpace q A ↦ (z.2 i).2) = α := by
  let project := markedTypeCloud (q := q) (id : A → A)
  let read : (ℕ × (ℕ → A)) → A := fun z ↦ z.2 i
  have hp : (markedPoissonLaw q A α r).map project = poissonTypeLaw A α r := by
    simpa only [project, poissonTypeLaw, Measure.map_id] using
      map_markedPoissonLaw_types q α (tag := id) measurable_id r
  have hm : Measurable project := measurable_markedTypeCloud measurable_id
  have hr : Measurable read := by fun_prop
  change (markedPoissonLaw q A α r).map (read ∘ project) = _
  rw [← Measure.map_map hr hm, hp]
  change (poissonTypeLaw A α r).map ((Function.eval i) ∘ Prod.snd) = α
  rw [← Measure.map_map (measurable_pi_apply i) measurable_snd]
  simp [poissonTypeLaw, Measure.map_snd_prod, Measure.infinitePi_map_eval]

/-- Every cross-color mark pair has the exact original independent product law. -/
theorem map_twoMarkedCloudLaw_mark_pair (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (i j : ℕ) :
    (twoMarkedCloudLaw q A B α β r).map
      (fun ω ↦ (mSourceMark ω i, mTargetMark ω j)) = α.prod β := by
  unfold twoMarkedCloudLaw
  change ((markedPoissonLaw q A α r).prod (markedPoissonLaw q B β r)).map
    (Prod.map (fun z : MarkedCloudSpace q A ↦ (z.2 i).2)
      (fun z : MarkedCloudSpace q B ↦ (z.2 j).2)) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    map_markedPoissonLaw_mark q α r i, map_markedPoissonLaw_mark q β r j]

/-- Original product-law legal type rectangles hold simultaneously for every
actual cross-color cloud edge, before a matching is selected. -/
theorem ae_markedCloud_forward_of_typeRectangles (q : ℕ) {K : ℕ}
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (tagA : A → Fin K) (tagB : B → Fin K) (r : ℝ≥0)
    (htype : ∀ᵐ p ∂α.prod β, tagA p.1 = tagB p.2 → sourceClock p.1 < targetClock p.2) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q A B α β r, ∀ (i : Fin (mSourceCount ω))
      (j : Fin (mTargetCount ω)),
        tagA (mSourceMark ω i) = tagB (mTargetMark ω j) →
          sourceClock (mSourceMark ω i) < targetClock (mTargetMark ω j) := by
  have hall : ∀ᵐ ω ∂twoMarkedCloudLaw q A B α β r, ∀ i j : ℕ,
      tagA (mSourceMark ω i) = tagB (mTargetMark ω j) →
        sourceClock (mSourceMark ω i) < targetClock (mTargetMark ω j) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    have hp : MeasurePreserving (fun ω : TwoMarkedCloudSpace q A B ↦
        (mSourceMark ω i, mTargetMark ω j)) (twoMarkedCloudLaw q A B α β r) (α.prod β) :=
      ⟨(measurable_mSourceMark q i).prodMk (measurable_mTargetMark q j),
        map_twoMarkedCloudLaw_mark_pair q α β r i j⟩
    exact hp.quasiMeasurePreserving.ae htype
  filter_upwards [hall] with ω hω
  exact fun i j ↦ hω i j

/-- A concrete version of the Poisson Hall-defect bound: only original type
marginals and their product-law legal rectangles remain as inputs. -/
theorem integral_legalMarkedMaximumCard_defect_le_of_typeRectangles
    (q : ℕ) {K : ℕ} [NeZero K]
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {tagA : A → Fin K} {tagB : B → Fin K} (hA : Measurable tagA) (hB : Measurable tagB)
    (L : Measure (Fin K)) [IsProbabilityMeasure L]
    (hLA : α.map tagA = L) (hLB : β.map tagB = L) (r : ℝ≥0)
    (htype : ∀ᵐ p ∂α.prod β, tagA p.1 = tagB p.2 → sourceClock p.1 < targetClock p.2) :
    (∫ ω, ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) -
      legalMarkedMaximumCard q sourceClock targetClock ω ∂twoMarkedCloudLaw q A B α β r) ≤
        (1 / 2 : ℝ) * Real.sqrt (2 * (r : ℝ) * K) := by
  exact integral_legalMarkedMaximumCard_defect_le_of_types q hsource htarget α β hA hB
    L hLA hLB r (ae_markedCloud_forward_of_typeRectangles q α β sourceClock targetClock
      tagA tagB r htype)

end OTSelector.Reconstruction
