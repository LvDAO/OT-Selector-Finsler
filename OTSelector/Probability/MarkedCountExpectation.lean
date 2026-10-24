import OTSelector.Probability.MarkedCountStability
import OTSelector.Probability.MarkedBlockComparison
import OTSelector.Probability.MarkedPressureScale
import OTSelector.Finite.MaxCardValueMeasurable

/-!
# Count stability of the expected marked block value

The fixed-size block value of the marked cube at sizes `m` and `k` is the
least cost of a maximum-cardinality matching between the first `m` source and
the first `k` target marked points.  Its expectation over the (Poissonized)
iid marked sequences is Lipschitz in `m` and `k` with constant `2 B`, where `B`
is the uniform edge bound: adding or removing `δ` rows or columns changes every
matching value by at most `2 B δ`.

This is the deterministic count-concentration input that replaces the binomial
cell counts of the physical sample by the deterministic intensity of the marked
model.
-/

open MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The fixed-size block value of the marked cube at sizes `m`, `k`. -/
noncomputable def markedFixedBlockValue (q : ℕ) (r t : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (m k : ℕ) (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  PartialMatching.maxCardValue
    (fun i : Fin m => fun j : Fin k => markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ))

/-- Its expectation under the marked Poisson cloud of intensity `R`. -/
noncomputable def markedFixedBlockExpectation (q : ℕ) (r t : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) (m k : ℕ) : ℝ :=
  ∫ ω, markedFixedBlockValue q r t kin g m k ω ∂(twoMarkedCloudLaw q A B α β R)

/-- Measurability of the block value. -/
theorem measurable_markedFixedBlockValue (q : ℕ) (r t : ℝ)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (m k : ℕ) :
    Measurable (markedFixedBlockValue q r t kin g m k) := by
  classical
  apply PartialMatching.measurable_maxCardValue
  intro i j
  exact ((measurable_mKineticCost q r hkin (i : ℕ) (j : ℕ))).add
    (measurable_const.mul (measurable_mProbe q hg (i : ℕ) (j : ℕ)))

/-- The uniform edge bound. -/
theorem abs_markedEdgeCost_le (q : ℕ) {r t C G : ℝ} (hr : 0 ≤ r)
    (hC0 : 0 ≤ C) (_hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G)
    (ω : TwoMarkedCloudSpace q A B) (i j : ℕ) :
    |markedEdgeCost q r kin g t ω i j| ≤
      r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
  unfold markedEdgeCost
  have h1 := abs_mKineticCost_le q hr hC0 hkin_bound ω i j
  have h2 : |t * mProbe g ω i j| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_mProbe_le q hgb ω i j) (abs_nonneg t)
  calc |mKineticCost q r kin ω i j + t * mProbe g ω i j|
      ≤ |mKineticCost q r kin ω i j| + |t * mProbe g ω i j| := abs_add_le _ _
    _ ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := add_le_add h1 h2

/-- The block value is bounded by the minimum cardinality times the edge bound. -/
theorem abs_markedFixedBlockValue_le (q : ℕ) {r t C G : ℝ} (hr : 0 ≤ r)
    (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G)
    (m k : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    |markedFixedBlockValue q r t kin g m k ω| ≤
      ((min m k : ℕ) : ℝ) * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) := by
  unfold markedFixedBlockValue
  have hBc0 : 0 ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hr _) (mul_nonneg hC0 (Nat.cast_nonneg q))
  refine PartialMatching.abs_maxCardValue_perturbed_le
    (c := fun i : Fin m => fun j : Fin k => mKineticCost q r kin ω (i : ℕ) (j : ℕ))
    (g := fun i : Fin m => fun j : Fin k => mProbe g ω (i : ℕ) (j : ℕ))
    ?_ hBc0 ?_ hG0
  · intro i j
    exact abs_mKineticCost_le q hr hC0 hkin_bound ω (i : ℕ) (j : ℕ)
  · intro i j
    exact abs_mProbe_le q hgb ω (i : ℕ) (j : ℕ)

/-- **Row-count stability of the expected block value.** -/
theorem abs_markedFixedBlockExpectation_sub_le_add_rows
    (q : ℕ) {r t C G : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) (m δ k : ℕ) :
    |markedFixedBlockExpectation q r t kin g α β R (m + δ) k -
      markedFixedBlockExpectation q r t kin g α β R m k| ≤
      2 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) * (δ : ℝ) := by
  classical
  set Bnd : ℝ := r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G with hBnd
  have hB0 : 0 ≤ Bnd := by
    rw [hBnd]
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg hr _) (mul_nonneg hC0 (Nat.cast_nonneg q)))
      (mul_nonneg (abs_nonneg t) hG0)
  have hedge : ∀ (ω : TwoMarkedCloudSpace q A B) (i j : ℕ),
      |markedEdgeCost q r kin g t ω i j| ≤ Bnd := by
    intro ω i j
    exact abs_markedEdgeCost_le q hr hC0 hG0 hkin_bound hgb ω i j
  -- The pointwise row-difference bound.
  have hpoint : ∀ ω : TwoMarkedCloudSpace q A B,
      |markedFixedBlockValue q r t kin g (m + δ) k ω - markedFixedBlockValue q r t kin g m k ω| ≤
        2 * Bnd * (δ : ℝ) := by
    intro ω
    unfold markedFixedBlockValue
    exact PartialMatching.abs_maxCardValue_sub_le_add_rows
      (a := m) (δ := δ) (b := k)
      (c := fun i : Fin (m + δ) => fun j : Fin k =>
        markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ)) hB0 (fun i j => hedge ω i j)
  -- Integrability of both block values.
  have hmeas1 : Measurable (markedFixedBlockValue q r t kin g (m + δ) k) :=
    measurable_markedFixedBlockValue q r t hkin hg (m + δ) k
  have hmeas2 : Measurable (markedFixedBlockValue q r t kin g m k) :=
    measurable_markedFixedBlockValue q r t hkin hg m k
  have hint1 : Integrable (markedFixedBlockValue q r t kin g (m + δ) k)
      (twoMarkedCloudLaw q A B α β R) := by
    refine Integrable.of_bound hmeas1.aestronglyMeasurable
      (((min (m + δ) k : ℕ) : ℝ) * Bnd) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_markedFixedBlockValue_le q hr hC0 hG0 hkin_bound hgb (m + δ) k ω
  have hint2 : Integrable (markedFixedBlockValue q r t kin g m k)
      (twoMarkedCloudLaw q A B α β R) := by
    refine Integrable.of_bound hmeas2.aestronglyMeasurable
      (((min m k : ℕ) : ℝ) * Bnd) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_markedFixedBlockValue_le q hr hC0 hG0 hkin_bound hgb m k ω
  have habs : Integrable (fun ω => |markedFixedBlockValue q r t kin g (m + δ) k ω -
      markedFixedBlockValue q r t kin g m k ω|) (twoMarkedCloudLaw q A B α β R) :=
    (hint1.sub hint2).abs
  -- Integrate the pointwise bound.
  calc |markedFixedBlockExpectation q r t kin g α β R (m + δ) k -
        markedFixedBlockExpectation q r t kin g α β R m k|
      = |∫ ω, (markedFixedBlockValue q r t kin g (m + δ) k ω -
          markedFixedBlockValue q r t kin g m k ω)
          ∂(twoMarkedCloudLaw q A B α β R)| := by
        rw [markedFixedBlockExpectation, markedFixedBlockExpectation,
          integral_sub hint1 hint2]
    _ ≤ ∫ ω, |markedFixedBlockValue q r t kin g (m + δ) k ω -
          markedFixedBlockValue q r t kin g m k ω| ∂(twoMarkedCloudLaw q A B α β R) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _ω, 2 * Bnd * (δ : ℝ) ∂(twoMarkedCloudLaw q A B α β R) := by
        apply integral_mono habs (integrable_const _)
        intro ω
        exact hpoint ω
    _ = 2 * Bnd * (δ : ℝ) := by simp

/-- **Column-count stability of the expected block value.** -/
theorem abs_markedFixedBlockExpectation_sub_le_add_cols
    (q : ℕ) {r t C G : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) (m k δ : ℕ) :
    |markedFixedBlockExpectation q r t kin g α β R m (k + δ) -
      markedFixedBlockExpectation q r t kin g α β R m k| ≤
      2 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) * (δ : ℝ) := by
  classical
  set Bnd : ℝ := r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G with hBnd
  have hB0 : 0 ≤ Bnd := by
    rw [hBnd]
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg hr _) (mul_nonneg hC0 (Nat.cast_nonneg q)))
      (mul_nonneg (abs_nonneg t) hG0)
  have hedge : ∀ (ω : TwoMarkedCloudSpace q A B) (i j : ℕ),
      |markedEdgeCost q r kin g t ω i j| ≤ Bnd := by
    intro ω i j
    exact abs_markedEdgeCost_le q hr hC0 hG0 hkin_bound hgb ω i j
  have hpoint : ∀ ω : TwoMarkedCloudSpace q A B,
      |markedFixedBlockValue q r t kin g m (k + δ) ω - markedFixedBlockValue q r t kin g m k ω| ≤
        2 * Bnd * (δ : ℝ) := by
    intro ω
    unfold markedFixedBlockValue
    exact PartialMatching.abs_maxCardValue_sub_le_add_cols
      (a := m) (b := k) (δ := δ)
      (c := fun i : Fin m => fun j : Fin (k + δ) =>
        markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ)) hB0 (fun i j => hedge ω i j)
  have hmeas1 : Measurable (markedFixedBlockValue q r t kin g m (k + δ)) :=
    measurable_markedFixedBlockValue q r t hkin hg m (k + δ)
  have hmeas2 : Measurable (markedFixedBlockValue q r t kin g m k) :=
    measurable_markedFixedBlockValue q r t hkin hg m k
  have hint1 : Integrable (markedFixedBlockValue q r t kin g m (k + δ))
      (twoMarkedCloudLaw q A B α β R) := by
    refine Integrable.of_bound hmeas1.aestronglyMeasurable
      (((min m (k + δ) : ℕ) : ℝ) * Bnd) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_markedFixedBlockValue_le q hr hC0 hG0 hkin_bound hgb m (k + δ) ω
  have hint2 : Integrable (markedFixedBlockValue q r t kin g m k)
      (twoMarkedCloudLaw q A B α β R) := by
    refine Integrable.of_bound hmeas2.aestronglyMeasurable
      (((min m k : ℕ) : ℝ) * Bnd) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_markedFixedBlockValue_le q hr hC0 hG0 hkin_bound hgb m k ω
  have habs : Integrable (fun ω => |markedFixedBlockValue q r t kin g m (k + δ) ω -
      markedFixedBlockValue q r t kin g m k ω|) (twoMarkedCloudLaw q A B α β R) :=
    (hint1.sub hint2).abs
  calc |markedFixedBlockExpectation q r t kin g α β R m (k + δ) -
        markedFixedBlockExpectation q r t kin g α β R m k|
      = |∫ ω, (markedFixedBlockValue q r t kin g m (k + δ) ω -
          markedFixedBlockValue q r t kin g m k ω)
          ∂(twoMarkedCloudLaw q A B α β R)| := by
        rw [markedFixedBlockExpectation, markedFixedBlockExpectation,
          integral_sub hint1 hint2]
    _ ≤ ∫ ω, |markedFixedBlockValue q r t kin g m (k + δ) ω -
          markedFixedBlockValue q r t kin g m k ω| ∂(twoMarkedCloudLaw q A B α β R) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _ω, 2 * Bnd * (δ : ℝ) ∂(twoMarkedCloudLaw q A B α β R) := by
        apply integral_mono habs (integrable_const _)
        intro ω
        exact hpoint ω
    _ = 2 * Bnd * (δ : ℝ) := by simp

end OTSelector.Probability
