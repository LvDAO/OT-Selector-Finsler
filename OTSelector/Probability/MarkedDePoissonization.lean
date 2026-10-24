import OTSelector.Finite.MaxCardValueMeasurable
import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Probability.MarkedPressureLimitBlock
import OTSelector.Probability.PoissonSingleDeviation
import OTSelector.Probability.MarkedCountStability
import OTSelector.Probability.DePoissonError

/-!
# De-Poissonization of the marked cube pressure

The Poissonized marked pressure at intensity `n` is compared with the pressure
of exactly `n` source and `n` target points.  Both are evaluated on the same
infinite iid sequence: the Poisson value uses the random counts, the fixed value
the first `n` entries.  Adjoining or removing rows and columns of a
maximum-cardinality assignment changes the value by at most the uniform edge
bound times the number of changed rows/columns, so the difference is controlled
by `|N - n|`, whose expectation is at most `sqrt n`.  After division by `n` the
error vanishes when `q > 4`, so the fixed-size pressures inherit the Poissonized
limit.
-/

open scoped BigOperators NNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The marked tilted value at the fixed sample sizes `n` and `n`, evaluated on
the first `n` entries of the two infinite sequences. -/
noncomputable def markedFixedValue (q : ℕ) (r t : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (n : ℕ) (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  PartialMatching.maxCardValue
    (fun i : Fin n => fun j : Fin n =>
      mKineticCost q r kin ω (i : ℕ) (j : ℕ) + t * mProbe g ω (i : ℕ) (j : ℕ))

/-! ## The laws of the two Poisson counts -/

/-- The joint law of the two marked Poisson counts is the product of two Poisson
laws. -/
theorem map_markedCounts_twoMarkedCloudLaw (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    (twoMarkedCloudLaw (q := q) A B α β r).map
        (fun ω : TwoMarkedCloudSpace q A B => (mSourceCount ω, mTargetCount ω)) =
      (poissonMeasure r).prod (poissonMeasure r) := by
  have hcomp : (fun ω : TwoMarkedCloudSpace q A B => (mSourceCount ω, mTargetCount ω)) =
      (fun y : TwoCloudSpace q => (sourceCount y, targetCount y)) ∘
        (markedPosCloud (q := q) (A := A) (B := B)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_counts_pair q)
    (measurable_markedPosCloud q), map_markedPosCloud_twoMarkedCloudLaw,
    map_counts_twoCloudLaw]

/-- The expected deviation of the source Poisson count from `r` is at most
`sqrt r`. -/
theorem integral_abs_mSourceCount_sub_le (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∫ ω : TwoMarkedCloudSpace q A B,
        |((mSourceCount ω : ℕ) : ℝ) - (r : ℝ)|
      ∂(twoMarkedCloudLaw (q := q) A B α β r) ≤ Real.sqrt (r : ℝ) := by
  have hmap := map_markedCounts_twoMarkedCloudLaw (q := q) α β r
  have hmeas : Measurable
      (fun ω : TwoMarkedCloudSpace q A B => (mSourceCount ω, mTargetCount ω)) :=
    (measurable_mSourceCount q).prodMk (measurable_mTargetCount q)
  have hcont : Continuous (fun z : ℕ × ℕ => |(z.1 : ℝ) - (r : ℝ)|) := by
    continuity
  rw [← integral_map hmeas.aemeasurable hcont.aestronglyMeasurable, hmap]
  have hfst : Measure.map Prod.fst ((poissonMeasure r).prod (poissonMeasure r)) =
      poissonMeasure r := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  calc ∫ z : ℕ × ℕ, |(z.1 : ℝ) - (r : ℝ)|
        ∂((poissonMeasure r).prod (poissonMeasure r))
      = ∫ n : ℕ, |(n : ℝ) - (r : ℝ)| ∂Measure.map Prod.fst
          ((poissonMeasure r).prod (poissonMeasure r)) := by
        rw [integral_map measurable_fst.aemeasurable (by fun_prop :
          AEStronglyMeasurable (fun n : ℕ => |(n : ℝ) - (r : ℝ)|)
            (Measure.map Prod.fst ((poissonMeasure r).prod (poissonMeasure r))))]
    _ = ∫ n : ℕ, |(n : ℝ) - (r : ℝ)| ∂(poissonMeasure r) := by rw [hfst]
    _ ≤ Real.sqrt (r : ℝ) := integral_abs_sub_id_poissonMeasure_le r

/-- The expected deviation of the target Poisson count from `r` is at most
`sqrt r`. -/
theorem integral_abs_mTargetCount_sub_le (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∫ ω : TwoMarkedCloudSpace q A B,
        |((mTargetCount ω : ℕ) : ℝ) - (r : ℝ)|
      ∂(twoMarkedCloudLaw (q := q) A B α β r) ≤ Real.sqrt (r : ℝ) := by
  have hmap := map_markedCounts_twoMarkedCloudLaw (q := q) α β r
  have hmeas : Measurable
      (fun ω : TwoMarkedCloudSpace q A B => (mSourceCount ω, mTargetCount ω)) :=
    (measurable_mSourceCount q).prodMk (measurable_mTargetCount q)
  have hcont : Continuous (fun z : ℕ × ℕ => |(z.2 : ℝ) - (r : ℝ)|) := by
    continuity
  rw [← integral_map hmeas.aemeasurable hcont.aestronglyMeasurable, hmap]
  have hsnd : Measure.map Prod.snd ((poissonMeasure r).prod (poissonMeasure r)) =
      poissonMeasure r := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  calc ∫ z : ℕ × ℕ, |(z.2 : ℝ) - (r : ℝ)|
        ∂((poissonMeasure r).prod (poissonMeasure r))
      = ∫ n : ℕ, |(n : ℝ) - (r : ℝ)| ∂Measure.map Prod.snd
          ((poissonMeasure r).prod (poissonMeasure r)) := by
        rw [integral_map measurable_snd.aemeasurable (by fun_prop :
          AEStronglyMeasurable (fun n : ℕ => |(n : ℝ) - (r : ℝ)|)
            (Measure.map Prod.snd ((poissonMeasure r).prod (poissonMeasure r))))]
    _ = ∫ n : ℕ, |(n : ℝ) - (r : ℝ)| ∂(poissonMeasure r) := by rw [hsnd]
    _ ≤ Real.sqrt (r : ℝ) := integral_abs_sub_id_poissonMeasure_le r

/-! ## The de-Poissonization estimate -/

/-- The uniform edge bound at intensity `n`. -/
theorem abs_markedEdge_le {n : ℕ} {t C G : ℝ}
    (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G)
    (ω : TwoMarkedCloudSpace q A B) (i j : ℕ) :
    |mKineticCost q (n : ℝ) kin ω i j + t * mProbe g ω i j| ≤
      (n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (2 / (q : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hkin : |kin (mSourceMark ω i) (mTargetMark ω j)
      (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))| ≤
      C * (q : ℝ) := by
    calc |kin _ _ _| ≤ C * ∑ l,
          (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j)) l ^ 2 :=
        hkin_bound _ _ _
      _ ≤ C * (q : ℝ) := by
        apply mul_le_mul_of_nonneg_left
          (mDisplacement_sq_sum_le q (mSourcePoint ω i) (mTargetPoint ω j)) hC0
  have hprobe : |mProbe g ω i j| ≤ G := hgb _ _
  calc |mKineticCost q (n : ℝ) kin ω i j + t * mProbe g ω i j|
      ≤ |mKineticCost q (n : ℝ) kin ω i j| + |t * mProbe g ω i j| := abs_add_le _ _
    _ = (n : ℝ) ^ (2 / (q : ℝ)) *
          |kin (mSourceMark ω i) (mTargetMark ω j)
            (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))| +
          |t| * |mProbe g ω i j| := by
        rw [mKineticCost, abs_mul, abs_of_nonneg hrpow, abs_mul]
    _ ≤ (n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
        have h1 := mul_le_mul_of_nonneg_left hkin hrpow
        have h2 := mul_le_mul_of_nonneg_left hprobe (abs_nonneg t)
        linarith

/-- **Fixed-size versus Poissonized pressure.**  The pressures at fixed size `n`
and at Poisson intensity `n` differ, after division by `n`, by at most
`4 (C q n ^ (2/q - 1/2) + |t| G n ^ (-1/2))`, which vanishes for `q > 4`. -/
theorem abs_markedPressure_sub_fixed_div_le
    (q : ℕ) {t C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] {n : ℕ} (hn : 0 < n) :
    |markedPressure q A B α β (n : ℝ≥0) kin g t / (n : ℝ) -
        (∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0))) / (n : ℝ)| ≤
      4 * ((n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  classical
  set Bnd : ℝ := (n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G with hBnd
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hBnd0 : 0 ≤ Bnd := by
    rw [hBnd]
    have h1 : 0 ≤ (n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) := by positivity
    have h2 : 0 ≤ |t| * G := by positivity
    linarith
  -- Integrability of the Poissonized marked value.
  have hIntT : Integrable (markedTilted q (n : ℝ) kin g t)
      (twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) :=
    integrable_markedTilted q α β (n : ℝ≥0) (by positivity) hC0 hG0
      hkin hkin_bound hg hgb t
  -- Integrability and boundedness of the fixed value.
  have hmeas_fixed : Measurable (markedFixedValue q (n : ℝ) t kin g n) := by
    unfold markedFixedValue
    exact PartialMatching.measurable_maxCardValue _
      (fun i j => (measurable_mKineticCost q (n : ℝ) hkin (i : ℕ) (j : ℕ)).add
        ((measurable_mProbe q hg (i : ℕ) (j : ℕ)).const_mul t))
  have hbound_fixed : ∀ ω : TwoMarkedCloudSpace q A B,
      |markedFixedValue q (n : ℝ) t kin g n ω| ≤ (n : ℝ) * Bnd := by
    intro ω
    unfold markedFixedValue
    have h := PartialMatching.abs_maxCardValue_perturbed_le
      (c := fun i : Fin n => fun j : Fin n =>
        mKineticCost q (n : ℝ) kin ω (i : ℕ) (j : ℕ))
      (g := fun i : Fin n => fun j : Fin n => mProbe g ω (i : ℕ) (j : ℕ))
      (Bc := (n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ))) (G := G) (t := t)
      (fun i j => abs_mKineticCost_le (q := q) (r := (n : ℝ)) (C := C)
        (by positivity) hC0 hkin_bound ω (i : ℕ) (j : ℕ))
      (by positivity) (fun i j => hgb _ _) hG0
    simpa [Bnd, min_self] using h
  have hIntF : Integrable (markedFixedValue q (n : ℝ) t kin g n)
      (twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) :=
    Integrable.mono' (integrable_const ((n : ℝ) * Bnd))
      hmeas_fixed.aestronglyMeasurable (Filter.Eventually.of_forall hbound_fixed)
  -- The pointwise stability bound.
  have hstab : ∀ ω : TwoMarkedCloudSpace q A B,
      |markedTilted q (n : ℝ) kin g t ω - markedFixedValue q (n : ℝ) t kin g n ω| ≤
        2 * Bnd * (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
          |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|) := by
    intro ω
    have := abs_markedTilted_sub_fixedMatrix_le (q := q) (r := (n : ℝ)) (t := t)
      (C := C) (G := G) (by positivity) hC0 hG0 hkin_bound hgb ω n
    simpa [markedFixedValue, Bnd, mul_assoc] using this
  -- The integrals of the count deviations.
  have hcount : ∫ ω : TwoMarkedCloudSpace q A B,
      (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
        |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
      ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) ≤
      2 * Real.sqrt (n : ℝ) := by
    have h1 := integral_abs_mSourceCount_sub_le (q := q) (α := α) (β := β) (r := (n : ℝ≥0))
    have h2 := integral_abs_mTargetCount_sub_le (q := q) (α := α) (β := β) (r := (n : ℝ≥0))
    have h1' : ∫ ω : TwoMarkedCloudSpace q A B,
        |((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)|
        ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) ≤ Real.sqrt (n : ℝ) := by
      simpa only [NNReal.coe_natCast] using h1
    have h2' : ∫ ω : TwoMarkedCloudSpace q A B,
        |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|
        ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) ≤ Real.sqrt (n : ℝ) := by
      simpa only [NNReal.coe_natCast] using h2
    have hi1 : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
        |((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)|)
        (twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) :=
      (((integrable_mSourceCount (q := q) α β (n : ℝ≥0)).sub
        (integrable_const (n : ℝ)))).abs
    have hi2 : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
        |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
        (twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) :=
      (((integrable_mTargetCount (q := q) α β (n : ℝ≥0)).sub
        (integrable_const (n : ℝ)))).abs
    rw [integral_add hi1 hi2]
    linarith [h1', h2']
  -- Integrability of the difference.
  have hdiff_int : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      markedTilted q (n : ℝ) kin g t ω - markedFixedValue q (n : ℝ) t kin g n ω)
      (twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) :=
    hIntT.sub hIntF
  -- Triangle inequality.
  have htri : |markedPressure q A B α β (n : ℝ≥0) kin g t -
        ∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0))| ≤
      2 * Bnd * (2 * Real.sqrt (n : ℝ)) := by
    have hrepr : markedPressure q A B α β (n : ℝ≥0) kin g t =
        ∫ ω, markedTilted q (n : ℝ) kin g t ω
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) := rfl
    rw [hrepr]
    have habs : |∫ ω, markedTilted q (n : ℝ) kin g t ω
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) -
        ∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0))| ≤
        ∫ ω, |markedTilted q (n : ℝ) kin g t ω -
          markedFixedValue q (n : ℝ) t kin g n ω|
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) := by
      rw [← integral_sub hIntT hIntF]
      exact abs_integral_le_integral_abs
    refine habs.trans ?_
    have hmono : ∫ ω, |markedTilted q (n : ℝ) kin g t ω -
          markedFixedValue q (n : ℝ) t kin g n ω|
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) ≤
        ∫ ω, 2 * Bnd * (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
          |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) := by
      apply integral_mono _ _ hstab
      · exact hdiff_int.abs
      · exact ((((integrable_mSourceCount (q := q) α β (n : ℝ≥0)).sub
            (integrable_const (n : ℝ))).abs).add
            (((integrable_mTargetCount (q := q) α β (n : ℝ≥0)).sub
              (integrable_const (n : ℝ))).abs)) |>.const_mul (2 * Bnd)
    refine hmono.trans ?_
    calc ∫ ω, 2 * Bnd * (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
          |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0))
        = 2 * Bnd * ∫ ω, (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
            |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
            ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0)) := by
          rw [integral_const_mul]
      _ ≤ 2 * Bnd * (2 * Real.sqrt (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hcount
          positivity
  -- Divide by `n`.
  have hdiv : |markedPressure q A B α β (n : ℝ≥0) kin g t / (n : ℝ) -
        (∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0))) / (n : ℝ)| =
      |markedPressure q A B α β (n : ℝ≥0) kin g t -
        ∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0))| / (n : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hnR]
  rw [hdiv]
  refine (div_le_div_of_nonneg_right htri hnR.le).trans ?_
  rw [hBnd, show (2 * ((n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        (2 * Real.sqrt (n : ℝ))) / (n : ℝ) =
      4 * ((n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        (n : ℝ) ^ (-(1 / 2 : ℝ)) from by
    rw [show Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow _]
    have hnne : (n : ℝ) ≠ 0 := hnR.ne'
    rw [show (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / (n : ℝ) ^ (1 / 2 : ℝ) from by
      rw [Real.rpow_neg hnR.le]
      simp [one_div]]
    have hsq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnR.le]
      norm_num
    field_simp
    rw [hsq]
    ring]

/-- **De-Poissonized pressure limit.**  Along fixed sample sizes the marked
pressure divided by the sample size inherits the Poissonized limit. -/
theorem tendsto_markedFixedPressure_div
    (q : ℕ) (hq : 4 < q)
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun R => markedScalePressure q A B α β kin g R t)
      atTop (𝓝 (p t))) :
    ∀ t, Tendsto (fun n : ℕ =>
        (∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0))) / (n : ℝ))
      atTop (𝓝 (p t)) := by
  intro t
  have hq0 : 0 < q := by omega
  -- The Poissonized limit along the scale `n ^ (1/q)`.
  have hR : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (q : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (q : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hp' := (hp t).comp hR
  have heq : (fun n : ℕ =>
        markedScalePressure q A B α β kin g ((n : ℝ) ^ (1 / (q : ℝ))) t) =ᶠ[atTop]
      (fun n : ℕ => markedPressure q A B α β (n : ℝ≥0) kin g t / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have hpow : ((n : ℝ) ^ (1 / (q : ℝ))) ^ q = (n : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnR.le]
      have hq1 : (1 / (q : ℝ)) * (q : ℝ) = 1 := by field_simp
      rw [hq1, Real.rpow_one]
    have htoNN : Real.toNNReal (((n : ℝ) ^ (1 / (q : ℝ))) ^ q) = (n : ℝ≥0) := by
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal _ (by positivity), hpow]
      simp
    rw [markedScalePressure_of_pos q α β (by positivity), htoNN, hpow]
  have hP : Tendsto (fun n : ℕ =>
      markedPressure q A B α β (n : ℝ≥0) kin g t / (n : ℝ)) atTop (𝓝 (p t)) :=
    hp'.congr' heq
  -- The de-Poissonization difference vanishes.
  have hd : Tendsto (fun n : ℕ =>
      markedPressure q A B α β (n : ℝ≥0) kin g t / (n : ℝ) -
        (∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoMarkedCloudLaw (q := q) A B α β (n : ℝ≥0))) / (n : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_dePoissonError_zero hq C G t)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : 0 < n := hn
    simpa only [Real.norm_eq_abs] using
      abs_markedPressure_sub_fixed_div_le (q := q) (t := t) (C := C) (G := G)
        hC0 hG0 hkin hkin_bound hg hgb α β (n := n) hn0
  have hF := hP.sub hd
  simpa only [sub_sub_cancel, sub_zero] using hF

end OTSelector.Probability
