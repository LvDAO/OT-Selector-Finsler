import OTSelector.Finite.LegalMatchingValue
import OTSelector.Probability.MarkedPressureLimit

/-!
# Legal maximum-cardinality pressure of the actual marked Poisson cloud

The scalar clock maps determine the legal domain `sourceClock a < targetClock b`.
We minimize over its actual finite maximum-cardinality matchings, so unequal
counts and Hall deficits are retained.  Measurability and integrability are
proved from the original independent marked-cloud law and the kernel bounds;
no measurable optimum or pressure regularity is assumed as an input.
-/

open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The actual forward-edge graph on two finite prefixes of a marked cloud. -/
def legalMarkedGraph (q m n : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) : Finset (Fin m × Fin n) := by
  classical
  exact Finset.univ.filter (fun e ↦
    sourceClock (mSourceMark ω e.1) < targetClock (mTargetMark ω e.2))

/-- The legal tilted value at fixed color counts. -/
def legalMarkedFixedValue (q m n : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  PartialMatching.legalMaximumValue (legalMarkedGraph q m n sourceClock targetClock ω)
    (fun i j ↦ mKineticCost q r kin ω i j + t * mProbe g ω i j)

/-- The actual legal tilted value at the realized Poisson color counts. -/
def legalMarkedTilted (q : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  legalMarkedFixedValue q (mSourceCount ω) (mTargetCount ω)
    sourceClock targetClock r kin g t ω

/-- The finite-volume pressure on the original independent marked Poisson inputs. -/
def legalMarkedPressure (q : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, legalMarkedTilted q sourceClock targetClock r kin g t ω
    ∂twoMarkedCloudLaw q A B α β r

/-- The legal pressure per unit volume in the cube of side length `R`. -/
def legalMarkedScalePressure (q : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (R t : ℝ) : ℝ :=
  if 0 < R then
    legalMarkedPressure q sourceClock targetClock α β (Real.toNNReal (R ^ q)) kin g t / R ^ q
  else 0

/-- Scalar-clock measurability gives every finite legal-graph event. -/
theorem measurableSet_legalMarkedGraph_eq (q m n : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock)
    (E : Finset (Fin m × Fin n)) :
    MeasurableSet {ω : TwoMarkedCloudSpace q A B |
      legalMarkedGraph q m n sourceClock targetClock ω = E} := by
  classical
  have hrepr : {ω : TwoMarkedCloudSpace q A B |
      legalMarkedGraph q m n sourceClock targetClock ω = E} =
      ⋂ e : Fin m × Fin n, {ω |
        (sourceClock (mSourceMark ω e.1) < targetClock (mTargetMark ω e.2)) ↔ e ∈ E} := by
    ext ω
    simp [Finset.ext_iff, legalMarkedGraph]
  rw [hrepr]
  apply MeasurableSet.iInter
  intro e
  have hlt := measurableSet_lt (hsource.comp (measurable_mSourceMark q e.1))
    (htarget.comp (measurable_mTargetMark q e.2))
  by_cases he : e ∈ E
  · simpa [he, Function.comp_def] using hlt
  · have hle : MeasurableSet {ω : TwoMarkedCloudSpace q A B |
        targetClock (mTargetMark ω e.2) ≤ sourceClock (mSourceMark ω e.1)} :=
      measurableSet_le (htarget.comp (measurable_mTargetMark q e.2))
        (hsource.comp (measurable_mSourceMark q e.1))
    simpa only [he, iff_false, not_lt] using hle

/-- The signed legal minimum is measurable at every fixed pair of color counts. -/
theorem measurable_legalMarkedFixedValue (q m n : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g)) (r t : ℝ) :
    Measurable (legalMarkedFixedValue q m n sourceClock targetClock r kin g t) := by
  apply PartialMatching.measurable_legalMaximumValue
    (legalMarkedGraph q m n sourceClock targetClock)
    (measurableSet_legalMarkedGraph_eq q m n hsource htarget)
  intro i j
  exact (measurable_mKineticCost q r hkin i j).add
    ((measurable_mProbe q hg i j).const_mul t)

/-- Count-layer partitioning proves measurability at the realized Poisson counts. -/
theorem measurable_legalMarkedTilted (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g)) (r t : ℝ) :
    Measurable (legalMarkedTilted q sourceClock targetClock r kin g t) := by
  intro S hS
  have hpre : (legalMarkedTilted q sourceClock targetClock r kin g t) ⁻¹' S =
      ⋃ m : ℕ, ⋃ n : ℕ,
        ({ω : TwoMarkedCloudSpace q A B | mSourceCount ω = m} ∩
          {ω | mTargetCount ω = n}) ∩
        (legalMarkedFixedValue q m n sourceClock targetClock r kin g t) ⁻¹' S := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨mSourceCount ω, mTargetCount ω, ⟨rfl, rfl⟩, hω⟩
    · rintro ⟨m, n, ⟨hm, hn⟩, hω⟩
      simpa only [legalMarkedTilted, hm, hn] using hω
  rw [hpre]
  exact MeasurableSet.iUnion fun m ↦ MeasurableSet.iUnion fun n ↦
    ((measurableSet_eq_fun (measurable_mSourceCount q) measurable_const).inter
      (measurableSet_eq_fun (measurable_mTargetCount q) measurable_const)).inter
      ((measurable_legalMarkedFixedValue q m n hsource htarget hkin hg r t) hS)

/-- A uniform absolute bound for the original tilted marked edge. -/
theorem abs_legalMarkedEdge_le (q : ℕ) {r C G : ℝ} (hr : 0 ≤ r)
    (hC : 0 ≤ C) {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : ∀ a b, |g a b| ≤ G)
    (t : ℝ) (ω : TwoMarkedCloudSpace q A B) (i j : ℕ) :
    |mKineticCost q r kin ω i j + t * mProbe g ω i j| ≤
      r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
  calc |mKineticCost q r kin ω i j + t * mProbe g ω i j|
      ≤ |mKineticCost q r kin ω i j| + |t * mProbe g ω i j| := abs_add_le _ _
    _ = |mKineticCost q r kin ω i j| + |t| * |mProbe g ω i j| := by rw [abs_mul]
    _ ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
      exact add_le_add (abs_mKineticCost_le q hr hC hkin ω i j)
        (mul_le_mul_of_nonneg_left (abs_mProbe_le q hg ω i j) (abs_nonneg t))

/-- The true legal value is bounded even on Hall-deficient realizations. -/
theorem abs_legalMarkedTilted_le (q : ℕ)
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : ∀ a b, |g a b| ≤ G)
    (t : ℝ) (ω : TwoMarkedCloudSpace q A B) :
    |legalMarkedTilted q sourceClock targetClock r kin g t ω| ≤
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) *
        (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) := by
  apply PartialMatching.abs_legalMaximumValue_le_min
  · exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg hr _) (mul_nonneg hC (Nat.cast_nonneg q)))
      (mul_nonneg (abs_nonneg t) hG)
  · intro i j
    exact abs_legalMarkedEdge_le q hr hC hkin hg t ω i j

/-- Integrability is proved from the actual Poisson count moment and the edge bound. -/
theorem integrable_legalMarkedTilted (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (legalMarkedTilted q sourceClock targetClock r kin g t)
      (twoMarkedCloudLaw q A B α β r) := by
  refine ((integrable_mMinCount q α β r).mul_const
    ((r : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G)).mono'
    ((measurable_legalMarkedTilted q hsource htarget hkin hg r t).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_legalMarkedTilted_le q sourceClock targetClock r.coe_nonneg
    hC hG hkin_bound hgb t ω

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- An actual legal matching of the graph's maximum cardinality bounds the finite value. -/
theorem legalMarkedTilted_le_matchingCost (q : ℕ)
    (sourceClock : A → ℝ) (targetClock : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B)
    (σ : OTSelector.PartialMatching (mSourceCount ω) (mTargetCount ω))
    (hlegal : ∀ e ∈ σ.edges,
      sourceClock (mSourceMark ω e.1) < targetClock (mTargetMark ω e.2))
    (hcard : σ.card = PartialMatching.legalMaximumCard
      (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω)) :
    legalMarkedTilted q sourceClock targetClock r kin g t ω ≤
      σ.cost (fun i j ↦ mKineticCost q r kin ω i j + t * mProbe g ω i j) := by
  apply PartialMatching.legalMaximumValue_le _ _ hcard
  intro e he
  simpa only [legalMarkedGraph, Finset.mem_filter, Finset.mem_univ, true_and] using
    hlegal e he

end OTSelector.Reconstruction
