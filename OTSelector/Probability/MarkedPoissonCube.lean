import OTSelector.Probability.PoissonCubePressure
import OTSelector.Probability.PoissonDyadicUpperBound
import OTSelector.Probability.CloudPressureRegularity

/-!
# Marked Poisson clouds on the unit cube

The homogeneous high-dimensional pressure model has two independent clouds of
marked points: a uniform transverse position in the unit `q`-cube and a mark in
a compact mark space, with the position and the mark independent.  The kinetic
edge cost depends on the mark pair and on the transverse displacement, while the
tilt probe depends on the mark pair only.  This is the model that is invariant
under the spatial dilation used in the block comparison: dilating a block of
side `L` to the unit cube rescales the kinetic cost by `L^{-2}` but leaves the
mark probe unchanged.

This module sets up the model, its product law, the measurable accessors, a
globally bounded clamped cost, and the measurability, integrability, concavity
and Lipschitz regularity of the tilted pressure.  The dyadic upper bound is
proved separately by reducing the kinetic term to the unmarked squared distance.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## The marked cloud model -/

/-- The iid law of an infinite sequence of independent marked cube points. -/
noncomputable def markedSeqLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] : Measure (ℕ → (Fin q → ℝ) × A) :=
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  letI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) :=
    fun _ => inferInstance
  Measure.infinitePi (fun _ : ℕ => (cubeMeasure (Fin q) 1).prod α)

instance isProbabilityMeasure_markedSeqLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] :
    IsProbabilityMeasure (markedSeqLaw (q := q) A α) := by
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) :=
    fun _ => inferInstance
  unfold markedSeqLaw
  change IsProbabilityMeasure
    (Measure.infinitePi (fun _ : ℕ => (cubeMeasure (Fin q) 1).prod α))
  infer_instance

/-- One Poissonized marked cloud: a Poisson count and an infinite iid sequence
of marked cube points. -/
abbrev MarkedCloudSpace (q : ℕ) (A : Type*) := ℕ × (ℕ → (Fin q → ℝ) × A)

/-- The Poissonized marked cloud law of mean count `r`. -/
noncomputable def markedPoissonLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (r : ℝ≥0) :
    Measure (MarkedCloudSpace q A) :=
  (poissonMeasure r).prod (markedSeqLaw (q := q) A α)

instance isProbabilityMeasure_markedPoissonLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (r : ℝ≥0) :
    IsProbabilityMeasure (markedPoissonLaw (q := q) A α r) := by
  unfold markedPoissonLaw
  infer_instance

/-- Two independent marked clouds with possibly different mark spaces and laws. -/
abbrev TwoMarkedCloudSpace (q : ℕ) (A B : Type*) :=
  MarkedCloudSpace q A × MarkedCloudSpace q B

/-- The law of two independent marked clouds with common mean count `r`. -/
noncomputable def twoMarkedCloudLaw (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    Measure (TwoMarkedCloudSpace q A B) :=
  (markedPoissonLaw (q := q) A α r).prod (markedPoissonLaw (q := q) B β r)

instance isProbabilityMeasure_twoMarkedCloudLaw (q : ℕ) (A B : Type*)
    [MeasurableSpace A] [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    IsProbabilityMeasure (twoMarkedCloudLaw (q := q) A B α β r) := by
  unfold twoMarkedCloudLaw
  infer_instance

/-! ## Accessors -/

/-- The source count. -/
def mSourceCount {q : ℕ} (ω : TwoMarkedCloudSpace q A B) : ℕ := ω.1.1

/-- The target count. -/
def mTargetCount {q : ℕ} (ω : TwoMarkedCloudSpace q A B) : ℕ := ω.2.1

/-- The source position. -/
def mSourcePoint {q : ℕ} (ω : TwoMarkedCloudSpace q A B) (i : ℕ) : Fin q → ℝ :=
  (ω.1.2 i).1

/-- The source mark. -/
def mSourceMark {q : ℕ} (ω : TwoMarkedCloudSpace q A B) (i : ℕ) : A :=
  (ω.1.2 i).2

/-- The target position. -/
def mTargetPoint {q : ℕ} (ω : TwoMarkedCloudSpace q A B) (j : ℕ) : Fin q → ℝ :=
  (ω.2.2 j).1

/-- The target mark. -/
def mTargetMark {q : ℕ} (ω : TwoMarkedCloudSpace q A B) (j : ℕ) : B :=
  (ω.2.2 j).2

theorem measurable_mSourceCount (q : ℕ) :
    Measurable (mSourceCount : TwoMarkedCloudSpace q A B → ℕ) := by
  unfold mSourceCount
  fun_prop

theorem measurable_mTargetCount (q : ℕ) :
    Measurable (mTargetCount : TwoMarkedCloudSpace q A B → ℕ) := by
  unfold mTargetCount
  fun_prop

theorem measurable_mSourcePoint (q : ℕ) (i : ℕ) :
    Measurable fun ω : TwoMarkedCloudSpace q A B => mSourcePoint ω i := by
  unfold mSourcePoint
  fun_prop

theorem measurable_mTargetPoint (q : ℕ) (j : ℕ) :
    Measurable fun ω : TwoMarkedCloudSpace q A B => mTargetPoint ω j := by
  unfold mTargetPoint
  fun_prop

theorem measurable_mSourceMark (q : ℕ) (i : ℕ) :
    Measurable fun ω : TwoMarkedCloudSpace q A B => mSourceMark ω i := by
  unfold mSourceMark
  fun_prop

theorem measurable_mTargetMark (q : ℕ) (j : ℕ) :
    Measurable fun ω : TwoMarkedCloudSpace q A B => mTargetMark ω j := by
  unfold mTargetMark
  fun_prop

/-- The pair of counts is measurable. -/
theorem measurable_mCounts (q : ℕ) :
    Measurable fun ω : TwoMarkedCloudSpace q A B =>
      (mSourceCount ω, mTargetCount ω) :=
  (measurable_mSourceCount q).prodMk (measurable_mTargetCount q)

/-- The source count is integrable. -/
theorem integrable_mSourceCount (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B => ((mSourceCount ω : ℕ) : ℝ))
      (twoMarkedCloudLaw (q := q) A B α β r) := by
  have h1 : Integrable (fun z : MarkedCloudSpace q A => ((z.1 : ℕ) : ℝ))
      (markedPoissonLaw (q := q) A α r) := by
    unfold markedPoissonLaw
    exact (integrable_id_poissonMeasure r).comp_fst _
  unfold twoMarkedCloudLaw mSourceCount
  exact h1.comp_fst _

/-- The target count is integrable. -/
theorem integrable_mTargetCount (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B => ((mTargetCount ω : ℕ) : ℝ))
      (twoMarkedCloudLaw (q := q) A B α β r) := by
  have h1 : Integrable (fun z : MarkedCloudSpace q B => ((z.1 : ℕ) : ℝ))
      (markedPoissonLaw (q := q) B β r) := by
    unfold markedPoissonLaw
    exact (integrable_id_poissonMeasure r).comp_fst _
  unfold twoMarkedCloudLaw mTargetCount
  exact h1.comp_snd _

/-- The minimum count is integrable. -/
theorem integrable_mMinCount (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ))
      (twoMarkedCloudLaw (q := q) A B α β r) := by
  have hsrc := integrable_mSourceCount (q := q) α β r
  have htgt := integrable_mTargetCount (q := q) α β r
  refine (hsrc.add htgt).mono' ?_ ?_
  · exact Measurable.aestronglyMeasurable
      (Measurable.comp measurable_from_nat
        ((measurable_mSourceCount q).min (measurable_mTargetCount q)))
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
        ≤ (mSourceCount ω : ℝ) := by exact_mod_cast min_le_left _ _
      _ ≤ (mSourceCount ω : ℝ) + (mTargetCount ω : ℝ) :=
          le_add_of_nonneg_right (Nat.cast_nonneg _)

/-! ## The edge cost and probe -/

/-- The clamped displacement of two truncated cube points.  On the unit cube
this is the true displacement; globally it keeps every kinetic edge bounded. -/
def mDisplacement {q : ℕ} (x y : Fin q → ℝ) : Fin q → ℝ :=
  fun l => cubeTruncPoint y l - cubeTruncPoint x l

/-- The kinetic edge cost at intensity `r`. -/
noncomputable def mKineticCost (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (ω : TwoMarkedCloudSpace q A B)
    (i j : ℕ) : ℝ :=
  r ^ (2 / (q : ℝ)) * kin (mSourceMark ω i) (mTargetMark ω j)
    (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))

/-- The mark probe. -/
def mProbe (g : A → B → ℝ) {q : ℕ} (ω : TwoMarkedCloudSpace q A B)
    (i j : ℕ) : ℝ :=
  g (mSourceMark ω i) (mTargetMark ω j)

/-- The marked tilted value. -/
noncomputable def markedTilted (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  tiltedCloudValue (mKineticCost q r kin) (mProbe (q := q) g) t ω
    (mSourceCount ω) (mTargetCount ω)

/-- The marked Poissonized pressure. -/
noncomputable def markedPressure (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, markedTilted (q := q) (r := (r : ℝ)) kin g t ω
    ∂(twoMarkedCloudLaw (q := q) A B α β r)

/-! ## Measurability and boundedness of one edge -/

/-- Coordinatewise truncation is measurable in the point. -/
theorem measurable_cubeTruncPoint_apply (q : ℕ) (l : Fin q) :
    Measurable fun x : Fin q → ℝ => cubeTruncPoint x l := by
  unfold cubeTruncPoint
  refine Measurable.ite ?_ (measurable_pi_apply l) measurable_const
  exact (measurableSet_le measurable_const (measurable_pi_apply l)).inter
    (measurableSet_lt (measurable_pi_apply l) measurable_const)

/-- The displacement depends measurably on the sample. -/
theorem measurable_mDisplacement (q : ℕ) (i j : ℕ) :
    Measurable fun ω : TwoMarkedCloudSpace q A B =>
      mDisplacement (mSourcePoint ω i) (mTargetPoint ω j) := by
  unfold mDisplacement
  apply measurable_pi_lambda
  intro l
  exact (measurable_cubeTruncPoint_apply q l).comp
    (measurable_mTargetPoint q j) |>.sub
    ((measurable_cubeTruncPoint_apply q l).comp (measurable_mSourcePoint q i))

/-- Measurability of the kinetic edge cost. -/
theorem measurable_mKineticCost (q : ℕ) (r : ℝ)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (i j : ℕ) :
    Measurable fun ω : TwoMarkedCloudSpace q A B => mKineticCost q r kin ω i j := by
  unfold mKineticCost
  refine Measurable.const_mul ?_ _
  exact hkin.comp (Measurable.prodMk
    (Measurable.prodMk (measurable_mSourceMark q i) (measurable_mTargetMark q j))
    (measurable_mDisplacement q i j))

/-- Measurability of the mark probe. -/
theorem measurable_mProbe (q : ℕ) {g : A → B → ℝ}
    (hg : Measurable (Function.uncurry g)) (i j : ℕ) :
    Measurable fun ω : TwoMarkedCloudSpace q A B => mProbe g ω i j := by
  unfold mProbe
  exact hg.comp (Measurable.prodMk
    (measurable_mSourceMark q i) (measurable_mTargetMark q j))

/-- A uniform bound on the truncated displacement. -/
theorem mDisplacement_sq_sum_le (q : ℕ) (x y : Fin q → ℝ) :
    ∑ l, (mDisplacement x y l) ^ 2 ≤ (q : ℝ) := by
  have hb (l : Fin q) : (mDisplacement x y l) ^ 2 ≤ 1 := by
    have h1 := (cubeTruncPoint_mem y l).1
    have h2 := (cubeTruncPoint_mem y l).2
    have h3 := (cubeTruncPoint_mem x l).1
    have h4 := (cubeTruncPoint_mem x l).2
    unfold mDisplacement
    rw [sq_le_one_iff_abs_le_one, abs_le]
    constructor <;> linarith
  calc ∑ l, (mDisplacement x y l) ^ 2 ≤ ∑ _l : Fin q, (1 : ℝ) :=
        Finset.sum_le_sum fun l _ => hb l
    _ = (q : ℝ) := by simp

/-- A uniform bound on a kinetic edge under the quadratic upper bound. -/
theorem abs_mKineticCost_le (q : ℕ) {r C : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (ω : TwoMarkedCloudSpace q A B) (i j : ℕ) :
    |mKineticCost q r kin ω i j| ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) := by
  unfold mKineticCost
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hr _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr _)
  refine (hkin_bound _ _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (mDisplacement_sq_sum_le q _ _) hC0

/-- The probe is bounded by `G`. -/
theorem abs_mProbe_le (q : ℕ) {g : A → B → ℝ} {G : ℝ}
    (hg : ∀ a b, |g a b| ≤ G) (ω : TwoMarkedCloudSpace q A B) (i j : ℕ) :
    |mProbe g ω i j| ≤ G := by
  unfold mProbe
  exact hg _ _

/-! ## Measurability and integrability of the tilted value -/

set_option maxHeartbeats 4000000 in
/-- The marked edge cost used in the matching, extended by zero outside the
two used prefixes. -/
def mMarkedEdge (q : ℕ) (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ)
    (g : A → B → ℝ) (t : ℝ) (ω : TwoMarkedCloudSpace q A B) (i j : ℕ) : ℝ :=
  if i < mSourceCount ω ∧ j < mTargetCount ω then
    mKineticCost q r kin ω i j + t * mProbe g ω i j
  else 0

/-- The marked edge value on the used prefix is the marked tilted value. -/
theorem cloudValueNat_mMarkedEdge (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    cloudValueNat (mMarkedEdge (A := A) (B := B) q r kin g t)
        (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω =
      markedTilted (q := q) (r := r) kin g t ω := by
  unfold cloudValueNat markedTilted tiltedCloudValue mMarkedEdge
  congr 1
  funext i j
  rw [if_pos ⟨i.isLt, j.isLt⟩]

/-- Coordinatewise measurability of the marked edge. -/
theorem measurable_mMarkedEdge (q : ℕ) (r : ℝ)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (t : ℝ) (i j : ℕ) :
    Measurable fun ω : TwoMarkedCloudSpace q A B =>
      mMarkedEdge q r kin g t ω i j := by
  unfold mMarkedEdge
  have hset : MeasurableSet
      {ω : TwoMarkedCloudSpace q A B | i < mSourceCount ω ∧ j < mTargetCount ω} :=
    measurableSet_setOf.mpr
      ((measurable_const.lt (measurable_mSourceCount q)).and
        (measurable_const.lt (measurable_mTargetCount q)))
  exact Measurable.ite hset
    ((measurable_mKineticCost q r hkin i j).add
      (Measurable.const_mul (measurable_mProbe q hg i j) t))
    measurable_const

set_option maxHeartbeats 800000 in
/-- Measurability of the tilted marked value. -/
theorem measurable_markedTilted (q : ℕ) (r : ℝ) {C G : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C)
    (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Measurable (markedTilted (q := q) (r := r) kin g t) := by
  have hB0 : 0 ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G :=
    add_nonneg (mul_nonneg (Real.rpow_nonneg hr _)
      (mul_nonneg hC0 (Nat.cast_nonneg q))) (mul_nonneg (abs_nonneg _) hG0)
  have h := measurable_cloudValueNat
    (Ω := TwoMarkedCloudSpace q A B)
    (e := mMarkedEdge (A := A) (B := B) q r kin g t)
    (Np := mSourceCount (A := A) (B := B)) (Nm := mTargetCount (A := A) (B := B))
    (B := fun _ => r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G)
    (fun i j => measurable_mMarkedEdge q r hkin hg t i j)
    (measurable_mSourceCount q) (measurable_mTargetCount q)
    measurable_const ?_
  · have hfun : cloudValueNat (mMarkedEdge (A := A) (B := B) q r kin g t)
        (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) =
        markedTilted (q := q) (r := r) kin g t :=
      funext (cloudValueNat_mMarkedEdge q r kin g t)
    rw [hfun] at h
    exact h
  · intro ω i j
    unfold mMarkedEdge
    by_cases hij : i < mSourceCount ω ∧ j < mTargetCount ω
    · rw [if_pos hij]
      have h1 := abs_mKineticCost_le q hr hC0 hkin_bound ω i j
      have h2 := abs_mProbe_le q hgb ω i j
      have h2' : |t * mProbe g ω i j| ≤ |t| * G := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left h2 (abs_nonneg t)
      calc mKineticCost q r kin ω i j + t * mProbe g ω i j
          ≤ |mKineticCost q r kin ω i j + t * mProbe g ω i j| := le_abs_self _
        _ ≤ |mKineticCost q r kin ω i j| + |t * mProbe g ω i j| := abs_add_le _ _
        _ ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G :=
            add_le_add h1 h2'
    · rw [if_neg hij]
      exact hB0

/-- Integrability of the tilted marked value. -/
theorem integrable_markedTilted (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) {C G : ℝ}
    (hr : 0 ≤ (r : ℝ)) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (markedTilted (q := q) (r := (r : ℝ)) kin g t)
      (twoMarkedCloudLaw (q := q) A B α β r) := by
  have hmeas := measurable_markedTilted (q := q) (r := (r : ℝ)) (C := C) (G := G)
    hr hC0 hG0 hkin hkin_bound hg hgb t
  have hcount := integrable_mMinCount (q := q) α β r
  have hbound : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) *
        (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G))
      (twoMarkedCloudLaw (q := q) A B α β r) :=
    hcount.mul_const _
  refine hbound.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  unfold markedTilted tiltedCloudValue
  have hpt : ∀ i : Fin (mSourceCount ω), ∀ j : Fin (mTargetCount ω),
      |mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) +
          t * mProbe g ω (i : ℕ) (j : ℕ)| ≤
        r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
    intro i j
    have h1 := abs_mKineticCost_le q hr hC0 hkin_bound ω (i : ℕ) (j : ℕ)
    have h2 := abs_mProbe_le q hgb ω (i : ℕ) (j : ℕ)
    calc |mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) + t * mProbe g ω (i : ℕ) (j : ℕ)|
        ≤ |mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ)| +
            |t * mProbe g ω (i : ℕ) (j : ℕ)| := abs_add_le _ _
      _ ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
          rw [abs_mul]
          gcongr
  calc |PartialMatching.maxCardValue
        (fun i : Fin (mSourceCount ω) => fun j : Fin (mTargetCount ω) =>
          mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) +
            t * mProbe g ω (i : ℕ) (j : ℕ))|
      ≤ ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) *
          (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) :=
        PartialMatching.abs_maxCardValue_perturbed_le
          (fun i : Fin (mSourceCount ω) => fun j : Fin (mTargetCount ω) =>
            mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ))
          (fun i : Fin (mSourceCount ω) => fun j : Fin (mTargetCount ω) =>
            mProbe g ω (i : ℕ) (j : ℕ))
          (fun i j => abs_mKineticCost_le q hr hC0 hkin_bound ω (i : ℕ) (j : ℕ))
          (mul_nonneg (Real.rpow_nonneg hr _) (mul_nonneg hC0 (Nat.cast_nonneg q)))
          (fun i j => abs_mProbe_le q hgb ω (i : ℕ) (j : ℕ))
          hG0

/-! ## Concavity and Lipschitz regularity of the pressure -/

set_option maxHeartbeats 800000 in
/-- The marked pressure is concave in the tilt. -/
theorem concaveOn_markedPressure (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) {C G : ℝ}
    (hr : 0 ≤ (r : ℝ)) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    ConcaveOn ℝ Set.univ (fun t =>
      markedPressure q A B α β r kin g t) := by
  have hV : ∀ t, (fun ω => markedTilted (q := q) (r := (r : ℝ)) kin g t ω) =
      fun ω => tiltedCloudValue (mKineticCost q (r : ℝ) kin) (mProbe (q := q) g)
        t ω (mSourceCount ω) (mTargetCount ω) := by
    intro t
    rfl
  have hInt : ∀ t, Integrable
      (fun ω => markedTilted (q := q) (r := (r : ℝ)) kin g t ω)
      (twoMarkedCloudLaw (q := q) A B α β r) := by
    intro t
    exact integrable_markedTilted (q := q) α β r (C := C) (G := G) hr hC0 hG0
      hkin hkin_bound hg hgb t
  simpa only [markedPressure] using
    concaveOn_integral_tiltedCloudValue (twoMarkedCloudLaw (q := q) A B α β r)
      (mKineticCost q (r : ℝ) kin) (mProbe (q := q) g)
      (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B))
      (fun t ω => markedTilted (q := q) (r := (r : ℝ)) kin g t ω) hV hInt

set_option maxHeartbeats 800000 in
/-- The marked pressure is `G`-Lipschitz in the tilt. -/
theorem abs_markedPressure_sub_le (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) {C G : ℝ}
    (hr : 0 ≤ (r : ℝ)) (hC0 : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t u : ℝ) :
    |markedPressure q A B α β r kin g t - markedPressure q A B α β r kin g u| ≤
      (∫ ω, ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
        ∂(twoMarkedCloudLaw (q := q) A B α β r)) * (G * |t - u|) := by
  have hV : ∀ t, (fun ω => markedTilted (q := q) (r := (r : ℝ)) kin g t ω) =
      fun ω => tiltedCloudValue (mKineticCost q (r : ℝ) kin) (mProbe (q := q) g)
        t ω (mSourceCount ω) (mTargetCount ω) := by
    intro t
    rfl
  have hInt : ∀ t, Integrable
      (fun ω => markedTilted (q := q) (r := (r : ℝ)) kin g t ω)
      (twoMarkedCloudLaw (q := q) A B α β r) := by
    intro t
    exact integrable_markedTilted (q := q) α β r (C := C) (G := G) hr hC0 hG
      hkin hkin_bound hg hgb t
  have hprobe : ∀ ω i j, |mProbe (q := q) g ω i j| ≤ G :=
    fun ω i j => abs_mProbe_le q hgb ω i j
  have hcard := integrable_mMinCount (q := q) α β r
  simpa only [markedPressure] using
    abs_integral_tiltedCloudValue_sub_le (twoMarkedCloudLaw (q := q) A B α β r)
      (mKineticCost q (r : ℝ) kin) (mProbe (q := q) g)
      (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B))
      (fun t ω => markedTilted (q := q) (r := (r : ℝ)) kin g t ω)
      hV hG hprobe hInt hcard t u

end OTSelector.Probability
