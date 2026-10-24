import OTSelector.Probability.MultinomialSplitting
import Mathlib.Probability.Moments.Variance

/-!
# Cell-count discrepancy for iid uniform labels

Fix `m` labels and `K ≥ 1` cells.  We equip the word space `Fin m → Fin K` with the product
measure `μ = Measure.pi (fun _ => uniformMeasure (Fin K))`, under which the labels are iid
uniform on `Fin K`.  For a word `w` and a cell `c`, `labelCount w c` is the number of labels in
cell `c`.

This file proves first- and second-moment bounds for the cell counts, and then uses them to
control the discrepancy between the cell-count vectors of two independent words:

* `integral_labelCount`: the expected count in a cell is `m / K`;
* `integral_sq_labelCount_sub_mean`: the centered second moment is at most `m / K`
  (the exact variance is `m * (1/K) * (1 - 1/K)`);
* `integral_abs_labelCount_sub_mean`: the `L¹` deviation from the mean is at most
  `Real.sqrt (m / K)`, by Cauchy–Schwarz;
* `integral_sum_abs_labelCount_sub_le`: the expected `ℓ¹` discrepancy of two independent
  samples is at most `Real.sqrt (2 * m * K)`;
* `integral_sum_abs_labelCount_sub_le_trivial`: the cruder deterministic bound `2 * m`.

The second moment is computed from the variance of a sum of independent Bernoulli indicators,
using `ProbabilityTheory.variance_sum_pi`.  All integrability statements are discharged
explicitly from boundedness, since the ambient space is finite and the measure is a probability
measure.
-/

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace OTSelector.Probability

/-- The joint law of `m` iid uniform labels in `Fin K`.  This is the measure called `μ` in the
statements below. -/
def iidUniformMeasure (m K : ℕ) : Measure (Fin m → Fin K) :=
  Measure.pi (fun _ : Fin m => uniformMeasure (Fin K))

/-- The iid uniform word measure is a probability measure when `K ≥ 1`. -/
instance iidUniformMeasure_isProbabilityMeasure (m K : ℕ) [NeZero K] :
    IsProbabilityMeasure (iidUniformMeasure m K) := by
  unfold iidUniformMeasure
  infer_instance

/-! ## Integrals against the uniform measure on `Fin K` -/

/-- The integral of a real function against the uniform measure is the average of its values. -/
private lemma integral_uniformMeasure_real {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∫ x, f x ∂(uniformMeasure α) = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  classical
  have hsum : ∫ x, f x ∂(∑ a : α, Measure.dirac a) = ∑ a, f a := by
    have h := integral_finsetSum_measure (μ := fun a : α => Measure.dirac a)
      (f := f) (s := Finset.univ) (fun i _ => integrable_dirac (by simp))
    simpa [integral_dirac] using h
  rw [uniformMeasure, integral_smul_measure, hsum]
  simp [Finset.mul_sum, ENNReal.toReal_inv]

/-- The integral of the indicator of a single cell against the uniform measure is `1 / K`. -/
private lemma integral_uniformMeasure_indicator (K : ℕ) [NeZero K] (c : Fin K) :
    ∫ x : Fin K, (if x = c then (1 : ℝ) else 0) ∂(uniformMeasure (Fin K)) = (K : ℝ)⁻¹ := by
  classical
  rw [integral_uniformMeasure_real]
  simp [Fintype.card_fin]

/-- The same indicator, viewed as a function of one coordinate of the product space. -/
private lemma integral_coord_indicator (m K : ℕ) [NeZero K] (c : Fin K) (i : Fin m) :
    ∫ w : Fin m → Fin K, (if w i = c then (1 : ℝ) else 0)
        ∂(Measure.pi (fun _ : Fin m => uniformMeasure (Fin K))) = (K : ℝ)⁻¹ := by
  rw [MeasureTheory.integral_comp_eval
    (μ := fun _ : Fin m => uniformMeasure (Fin K))
    (f := fun x : Fin K => if x = c then (1 : ℝ) else 0)
    (Measurable.aestronglyMeasurable (by fun_prop))]
  exact integral_uniformMeasure_indicator K c

/-- The cell count, cast to `ℝ`, is the sum of the indicators of the coordinates in that cell. -/
private lemma labelCount_eq_sum_indicator (m K : ℕ) (w : Fin m → Fin K) (c : Fin K) :
    (labelCount w c : ℝ) = ∑ i : Fin m, (if w i = c then (1 : ℝ) else 0) := by
  classical
  rw [labelCount, ← Finset.natCast_card_filter (fun i => w i = c) Finset.univ]

/-- A cell count never exceeds the total number of labels. -/
private lemma labelCount_cast_le (m K : ℕ) (w : Fin m → Fin K) (c : Fin K) :
    (labelCount w c : ℝ) ≤ (m : ℝ) := by
  classical
  have h' : (Finset.univ.filter (fun i : Fin m => w i = c)).card ≤ m := by
    simpa using Finset.card_filter_le (s := (Finset.univ : Finset (Fin m)))
      (p := fun i => w i = c)
  have h'' : ((Finset.univ.filter fun i => w i = c).card : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast h'
  simpa [labelCount] using h''

/-! ## First moment -/

/-- The expected number of labels in a fixed cell is `m / K`. -/
theorem integral_labelCount (m K : ℕ) [NeZero K] (c : Fin K) :
    ∫ w, (labelCount w c : ℝ) ∂(iidUniformMeasure m K) = (m : ℝ) / K := by
  classical
  have hcoord : ∀ i : Fin m, ∫ w : Fin m → Fin K, (if w i = c then (1 : ℝ) else 0)
      ∂(iidUniformMeasure m K) = (K : ℝ)⁻¹ := fun i => integral_coord_indicator m K c i
  have hInt : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      Integrable (fun w : Fin m → Fin K => (if w i = c then (1 : ℝ) else 0))
        (iidUniformMeasure m K) := by
    intro i _
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Measurable.aestronglyMeasurable (by fun_prop))
    · filter_upwards with w
      split_ifs <;> simp
  calc
    ∫ w, (labelCount w c : ℝ) ∂(iidUniformMeasure m K)
        = ∫ w, ∑ i : Fin m, (if w i = c then (1 : ℝ) else 0)
            ∂(iidUniformMeasure m K) := by
          simp_rw [labelCount_eq_sum_indicator]
    _ = ∑ i : Fin m, ∫ w, (if w i = c then (1 : ℝ) else 0)
            ∂(iidUniformMeasure m K) :=
          integral_finsetSum _ hInt
    _ = ∑ _i : Fin m, (K : ℝ)⁻¹ := by simp [hcoord]
    _ = (m : ℝ) / K := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-! ## Second moment -/

/-- The variance of the indicator of a cell under the uniform measure is `p - p ^ 2`, with
`p = 1 / K`. -/
private lemma variance_uniform_indicator (K : ℕ) [NeZero K] (c : Fin K) :
    ProbabilityTheory.variance (fun x : Fin K => if x = c then (1 : ℝ) else 0)
        (uniformMeasure (Fin K)) = (K : ℝ)⁻¹ - ((K : ℝ)⁻¹) ^ 2 := by
  classical
  let X : Fin K → ℝ := fun x => if x = c then (1 : ℝ) else 0
  have hmeas : Measurable X := by fun_prop
  have hmem : MemLp X 2 (uniformMeasure (Fin K)) := by
    refine MemLp.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards with x
    simp only [X]
    split_ifs <;> simp
  change ProbabilityTheory.variance X (uniformMeasure (Fin K)) = _
  rw [ProbabilityTheory.variance_eq_sub hmem]
  have h1 : ∫ x : Fin K, X x ∂(uniformMeasure (Fin K)) = (K : ℝ)⁻¹ :=
    integral_uniformMeasure_indicator K c
  have h2 : ∫ x : Fin K, (X ^ 2) x ∂(uniformMeasure (Fin K)) = (K : ℝ)⁻¹ := by
    rw [show (fun x : Fin K => (X ^ 2) x) = X by
      funext x
      simp only [Pi.pow_apply, X]
      split_ifs <;> simp]
    exact h1
  rw [h2, h1]

/-- The centered second moment of a cell count is at most `m / K`.  The exact variance is
`m * (1/K) * (1 - 1/K)`. -/
theorem integral_sq_labelCount_sub_mean (m K : ℕ) [NeZero K] (c : Fin K) :
    ∫ w, ((labelCount w c : ℝ) - (m : ℝ) / K) ^ 2 ∂(iidUniformMeasure m K) ≤ (m : ℝ) / K := by
  classical
  let X : Fin K → ℝ := fun x => if x = c then (1 : ℝ) else 0
  have hmeasN : Measurable (fun w : Fin m → Fin K => (labelCount w c : ℝ)) :=
    measurable_of_countable _
  have hfun : (fun w : Fin m → Fin K => (labelCount w c : ℝ))
      = fun w => ∑ i, X (w i) := by
    funext w
    rw [labelCount_eq_sum_indicator]
  have hmem : ∀ _i : Fin m, MemLp X 2 (uniformMeasure (Fin K)) := by
    intro i
    have hmeas : Measurable X := by fun_prop
    refine MemLp.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards with x
    simp only [X]
    split_ifs <;> simp
  have hvar : ∫ w, ((labelCount w c : ℝ) - (m : ℝ) / K) ^ 2 ∂(iidUniformMeasure m K)
      = ProbabilityTheory.variance (fun w => (labelCount w c : ℝ)) (iidUniformMeasure m K) := by
    have hv := ProbabilityTheory.variance_eq_integral
      (μ := iidUniformMeasure m K)
      (X := fun w : Fin m → Fin K => (labelCount w c : ℝ)) hmeasN.aemeasurable
    rw [hv, integral_labelCount]
  rw [hvar, hfun]
  have hsumfun : (fun w : Fin m → Fin K => ∑ i, X (w i))
      = ∑ i : Fin m, fun w : Fin m → Fin K => X (w i) := by
    funext w
    simp
  rw [hsumfun]
  unfold iidUniformMeasure
  rw [ProbabilityTheory.variance_sum_pi (μ := fun _ : Fin m => uniformMeasure (Fin K))
    (X := fun _ (x : Fin K) => X x) hmem]
  calc
    ∑ _i : Fin m, ProbabilityTheory.variance X (uniformMeasure (Fin K))
        = ∑ _i : Fin m, ((K : ℝ)⁻¹ - ((K : ℝ)⁻¹) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          exact variance_uniform_indicator K c
    _ ≤ ∑ _i : Fin m, (K : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro i _
          nlinarith [sq_nonneg ((K : ℝ)⁻¹)]
    _ = (m : ℝ) / K := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-! ## Cauchy–Schwarz and integrability -/

/-- For a probability measure, `(∫ |f|) ^ 2 ≤ ∫ f ^ 2`.  This is proved directly from
`2 c |f| ≤ |f| ^ 2 + c ^ 2` with `c = ∫ |f|`. -/
private lemma sq_integral_abs_le_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, |f x| ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  classical
  let c : ℝ := ∫ x, |f x| ∂μ
  have hc_nonneg : 0 ≤ c := integral_nonneg (fun x => abs_nonneg _)
  have hfabs : Integrable (fun x => |f x|) μ := hf.abs
  have hleft_int : Integrable (fun x => 2 * c * |f x|) μ := hfabs.const_mul (2 * c)
  have hfabs2 : Integrable (fun x => |f x| ^ 2) μ := by
    convert hf2 using 1
    funext x
    exact sq_abs (f x)
  have hright_int : Integrable (fun x => |f x| ^ 2 + c ^ 2) μ :=
    hfabs2.add (integrable_const (c ^ 2))
  have hpt : ∀ x, 2 * c * |f x| ≤ |f x| ^ 2 + c ^ 2 := by
    intro x
    nlinarith [sq_nonneg (|f x| - c)]
  have hmono : ∫ x, 2 * c * |f x| ∂μ ≤ ∫ x, |f x| ^ 2 + c ^ 2 ∂μ :=
    integral_mono hleft_int hright_int hpt
  have hleft_eq : ∫ x, 2 * c * |f x| ∂μ = 2 * c * c := by
    rw [integral_const_mul]
  have hAbsEq : ∫ x, |f x| ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    exact sq_abs (f x)
  have hright_eq : ∫ x, |f x| ^ 2 + c ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ + c ^ 2 := by
    rw [integral_add hfabs2 (integrable_const (c ^ 2)), integral_const, hAbsEq]
    simp
  rw [hleft_eq, hright_eq] at hmono
  have hfinal : c ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by nlinarith
  simpa [c] using hfinal

/-- A uniform bound on the centered cell count. -/
private lemma norm_labelCount_sub_mean_le (m K : ℕ) [NeZero K] (c : Fin K)
    (w : Fin m → Fin K) :
    ‖(labelCount w c : ℝ) - (m : ℝ) / K‖ ≤ (m : ℝ) + (m : ℝ) / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  rw [Real.norm_eq_abs, abs_le]
  have hN0 : 0 ≤ (labelCount w c : ℝ) := Nat.cast_nonneg _
  have hNm : (labelCount w c : ℝ) ≤ (m : ℝ) := labelCount_cast_le m K w c
  have hp0 : 0 ≤ (m : ℝ) / K := div_nonneg (Nat.cast_nonneg _) hKpos.le
  constructor <;> linarith

/-- The centered cell count is integrable. -/
private lemma integrable_labelCount_sub_mean (m K : ℕ) [NeZero K] (c : Fin K) :
    Integrable (fun w : Fin m → Fin K => (labelCount w c : ℝ) - (m : ℝ) / K)
      (iidUniformMeasure m K) := by
  have hmeas : Measurable (fun w : Fin m → Fin K => (labelCount w c : ℝ)) :=
    measurable_of_countable _
  exact Integrable.of_bound (hmeas.sub_const _).aestronglyMeasurable _
    (Filter.Eventually.of_forall (norm_labelCount_sub_mean_le m K c))

/-- The centered cell count is square-integrable. -/
private lemma memLp_labelCount_sub_mean (m K : ℕ) [NeZero K] (c : Fin K) :
    MemLp (fun w : Fin m → Fin K => (labelCount w c : ℝ) - (m : ℝ) / K) 2
      (iidUniformMeasure m K) := by
  have hmeas : Measurable (fun w : Fin m → Fin K => (labelCount w c : ℝ)) :=
    measurable_of_countable _
  exact MemLp.of_bound (hmeas.sub_const _).aestronglyMeasurable _
    (Filter.Eventually.of_forall (norm_labelCount_sub_mean_le m K c))

/-- The `L¹` deviation of a cell count from its mean is at most `sqrt (m / K)`. -/
theorem integral_abs_labelCount_sub_mean (m K : ℕ) [NeZero K] (c : Fin K) :
    ∫ w, |(labelCount w c : ℝ) - (m : ℝ) / K| ∂(iidUniformMeasure m K)
      ≤ Real.sqrt ((m : ℝ) / K) := by
  have hf : Integrable (fun w : Fin m → Fin K => (labelCount w c : ℝ) - (m : ℝ) / K)
      (iidUniformMeasure m K) := integrable_labelCount_sub_mean m K c
  have hf2 : Integrable
      (fun w : Fin m → Fin K => ((labelCount w c : ℝ) - (m : ℝ) / K) ^ 2)
      (iidUniformMeasure m K) := (memLp_labelCount_sub_mean m K c).integrable_sq
  have hcs := sq_integral_abs_le_integral_sq hf hf2
  have hsq : (∫ w, |(labelCount w c : ℝ) - (m : ℝ) / K| ∂(iidUniformMeasure m K)) ^ 2
      ≤ (m : ℝ) / K := le_trans hcs (integral_sq_labelCount_sub_mean m K c)
  exact Real.le_sqrt_of_sq_le hsq

/-! ## Two independent samples -/

/-- The mean-zero centered cell count integrates to zero. -/
private lemma integral_labelCount_sub_mean_zero (m K : ℕ) [NeZero K] (c : Fin K) :
    ∫ w, ((labelCount w c : ℝ) - (m : ℝ) / K) ∂(iidUniformMeasure m K) = 0 := by
  have hIntN : Integrable (fun w : Fin m → Fin K => (labelCount w c : ℝ))
      (iidUniformMeasure m K) := by
    have h := (integrable_labelCount_sub_mean m K c).add
      (integrable_const ((m : ℝ) / K))
    exact h.congr (by
      filter_upwards with w
      simp only [Pi.add_apply]
      ring)
  calc
    ∫ w, ((labelCount w c : ℝ) - (m : ℝ) / K) ∂(iidUniformMeasure m K)
        = ∫ w, (labelCount w c : ℝ) ∂(iidUniformMeasure m K)
            - ∫ _w : Fin m → Fin K, (m : ℝ) / K ∂(iidUniformMeasure m K) :=
          integral_sub hIntN (integrable_const _)
    _ = (m : ℝ) / K - (m : ℝ) / K := by
          rw [integral_labelCount, integral_const]
          simp
    _ = 0 := by ring

/-- The expected squared difference of the counts in one cell across two independent samples is
at most `2 * (m / K)`. -/
private lemma integral_sq_labelCount_sub_labelCount_le (m K : ℕ) [NeZero K] (c : Fin K) :
    ∫ z : (Fin m → Fin K) × (Fin m → Fin K),
      ((labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)) ^ 2
      ∂((iidUniformMeasure m K).prod (iidUniformMeasure m K)) ≤ 2 * ((m : ℝ) / K) := by
  classical
  let μ : Measure (Fin m → Fin K) := iidUniformMeasure m K
  let ν : Measure ((Fin m → Fin K) × (Fin m → Fin K)) := μ.prod μ
  let f : (Fin m → Fin K) → ℝ := fun w => (labelCount w c : ℝ) - (m : ℝ) / K
  have hf : Integrable f μ := integrable_labelCount_sub_mean m K c
  have hf2 : Integrable (fun w => f w ^ 2) μ := (memLp_labelCount_sub_mean m K c).integrable_sq
  have hpt : ∀ z : (Fin m → Fin K) × (Fin m → Fin K),
      (f z.1 - f z.2) ^ 2 = f z.1 ^ 2 + f z.2 ^ 2 - 2 * (f z.1 * f z.2) := by
    intro z
    ring
  have hA : Integrable (fun z : (Fin m → Fin K) × (Fin m → Fin K) => f z.1 ^ 2) ν :=
    hf2.comp_fst μ
  have hB : Integrable (fun z : (Fin m → Fin K) × (Fin m → Fin K) => f z.2 ^ 2) ν :=
    hf2.comp_snd μ
  have hC : Integrable (fun z : (Fin m → Fin K) × (Fin m → Fin K) => f z.1 * f z.2) ν :=
    hf.op_fst_snd (op := fun x y : ℝ => x * y) continuous_mul
      ⟨1, fun x y => by rw [one_mul]; exact norm_mul_le x y⟩ hf
  have step1 : ∫ z, ((f z.1) ^ 2 + (f z.2) ^ 2 - 2 * (f z.1 * f z.2)) ∂ν
      = ∫ z, ((f z.1) ^ 2 + (f z.2) ^ 2) ∂ν
          - ∫ z, 2 * (f z.1 * f z.2) ∂ν :=
    integral_sub (hA.add hB) (hC.const_mul 2)
  have step2 : ∫ z, ((f z.1) ^ 2 + (f z.2) ^ 2) ∂ν
      = ∫ z, (f z.1) ^ 2 ∂ν + ∫ z, (f z.2) ^ 2 ∂ν :=
    integral_add hA hB
  have step3 : ∫ z, 2 * (f z.1 * f z.2) ∂ν
      = 2 * ∫ z, f z.1 * f z.2 ∂ν :=
    integral_const_mul 2 _
  have hExpand : ∫ z, (f z.1 - f z.2) ^ 2 ∂ν
      = ∫ z, f z.1 ^ 2 ∂ν + ∫ z, f z.2 ^ 2 ∂ν
          - 2 * ∫ z, f z.1 * f z.2 ∂ν := by
    calc
      ∫ z, (f z.1 - f z.2) ^ 2 ∂ν
          = ∫ z, ((f z.1) ^ 2 + (f z.2) ^ 2 - 2 * (f z.1 * f z.2)) ∂ν := by
            apply integral_congr_ae
            filter_upwards with z
            exact hpt z
      _ = ∫ z, ((f z.1) ^ 2 + (f z.2) ^ 2) ∂ν
            - ∫ z, 2 * (f z.1 * f z.2) ∂ν := step1
      _ = (∫ z, (f z.1) ^ 2 ∂ν + ∫ z, (f z.2) ^ 2 ∂ν)
            - 2 * ∫ z, f z.1 * f z.2 ∂ν := by rw [step2, step3]
  have hAeq : ∫ z, f z.1 ^ 2 ∂ν = ∫ w, f w ^ 2 ∂μ := by
    have h := integral_fun_fst (μ := μ) (ν := μ) (f := fun w : Fin m → Fin K => f w ^ 2)
    simpa [ν] using h
  have hBeq : ∫ z, f z.2 ^ 2 ∂ν = ∫ w, f w ^ 2 ∂μ := by
    have h := integral_fun_snd (μ := μ) (ν := μ) (f := fun w : Fin m → Fin K => f w ^ 2)
    simpa [ν] using h
  have hzero : ∫ w, f w ∂μ = 0 := by
    simpa [μ, f] using integral_labelCount_sub_mean_zero m K c
  have hcross : ∫ z, f z.1 * f z.2 ∂ν = 0 := by
    have h := integral_prod_mul (μ := μ) (ν := μ) (f := f) (g := f)
    rw [hzero] at h
    simpa [ν] using h
  have hsingle : ∫ w, f w ^ 2 ∂μ ≤ (m : ℝ) / K := integral_sq_labelCount_sub_mean m K c
  have hmain : ∫ z, (f z.1 - f z.2) ^ 2 ∂ν ≤ 2 * ((m : ℝ) / K) := by
    rw [hExpand, hAeq, hBeq, hcross]
    nlinarith [hsingle]
  have hfun : (fun z : (Fin m → Fin K) × (Fin m → Fin K) =>
        ((labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)) ^ 2)
      = fun z => (f z.1 - f z.2) ^ 2 := by
    funext z
    simp only [f]
    ring_nf
  rw [hfun]
  exact hmain

/-- The expected absolute count difference in one cell is at most `sqrt (2 * (m / K))`. -/
private lemma integral_abs_labelCount_sub_labelCount_le (m K : ℕ) [NeZero K] (c : Fin K) :
    ∫ z : (Fin m → Fin K) × (Fin m → Fin K),
      |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|
      ∂((iidUniformMeasure m K).prod (iidUniformMeasure m K))
      ≤ Real.sqrt (2 * ((m : ℝ) / K)) := by
  classical
  let μ : Measure (Fin m → Fin K) := iidUniformMeasure m K
  let ν : Measure ((Fin m → Fin K) × (Fin m → Fin K)) := μ.prod μ
  let f : (Fin m → Fin K) → ℝ := fun w => (labelCount w c : ℝ) - (m : ℝ) / K
  let C : ℝ := (m : ℝ) + (m : ℝ) / K
  have hmeas : Measurable f := (measurable_of_countable _).sub_const _
  have hbound : ∀ w, ‖f w‖ ≤ C := fun w => norm_labelCount_sub_mean_le m K c w
  have hdiff_meas : AEStronglyMeasurable
      (fun z : (Fin m → Fin K) × (Fin m → Fin K) => f z.1 - f z.2) ν :=
    ((hmeas.comp measurable_fst).sub (hmeas.comp measurable_snd)).aestronglyMeasurable
  have hdiff_bound : ∀ z : (Fin m → Fin K) × (Fin m → Fin K),
      ‖f z.1 - f z.2‖ ≤ 2 * C := by
    intro z
    calc
      ‖f z.1 - f z.2‖ ≤ ‖f z.1‖ + ‖f z.2‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hbound _) (hbound _)
      _ = 2 * C := by ring
  have hmem : MemLp (fun z : (Fin m → Fin K) × (Fin m → Fin K) => f z.1 - f z.2) 2 ν :=
    MemLp.of_bound hdiff_meas (2 * C) (Filter.Eventually.of_forall hdiff_bound)
  have hdiff_int : Integrable
      (fun z : (Fin m → Fin K) × (Fin m → Fin K) => f z.1 - f z.2) ν :=
    hmem.integrable (by norm_num)
  have hdiff_sq_int : Integrable
      (fun z : (Fin m → Fin K) × (Fin m → Fin K) => (f z.1 - f z.2) ^ 2) ν :=
    hmem.integrable_sq
  have hcs := sq_integral_abs_le_integral_sq hdiff_int hdiff_sq_int
  have hsq_diff : ∫ z, (f z.1 - f z.2) ^ 2 ∂ν ≤ 2 * ((m : ℝ) / K) := by
    have h := integral_sq_labelCount_sub_labelCount_le m K c
    simpa [ν, μ, f] using h
  have hsq : (∫ z, |f z.1 - f z.2| ∂ν) ^ 2 ≤ 2 * ((m : ℝ) / K) :=
    le_trans hcs hsq_diff
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  have hfun : (fun z : (Fin m → Fin K) × (Fin m → Fin K) => |f z.1 - f z.2|)
      = fun z => |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)| := by
    funext z
    simp only [f]
    congr 1
    ring
  rw [hfun] at hsqrt
  simpa [ν, μ] using hsqrt

/-- For a fixed cell, the absolute difference of the two sample counts is integrable. -/
private lemma integrable_abs_labelCount_sub_labelCount (m K : ℕ) [NeZero K] (c : Fin K) :
    Integrable
      (fun z : (Fin m → Fin K) × (Fin m → Fin K) =>
        |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|)
      ((iidUniformMeasure m K).prod (iidUniformMeasure m K)) := by
  classical
  have hmeas : Measurable
      (fun z : (Fin m → Fin K) × (Fin m → Fin K) =>
        (labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)) := by
    exact (measurable_of_countable (fun z : (Fin m → Fin K) × (Fin m → Fin K) =>
      (labelCount z.1 c : ℝ))).sub
      (measurable_of_countable (fun z : (Fin m → Fin K) × (Fin m → Fin K) =>
        (labelCount z.2 c : ℝ)))
  refine Integrable.of_bound hmeas.norm.aestronglyMeasurable (2 * (m : ℝ)) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_abs, abs_le]
  have h1 : 0 ≤ (labelCount z.1 c : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ (labelCount z.2 c : ℝ) := Nat.cast_nonneg _
  have hm1 : (labelCount z.1 c : ℝ) ≤ (m : ℝ) := labelCount_cast_le m K z.1 c
  have hm2 : (labelCount z.2 c : ℝ) ≤ (m : ℝ) := labelCount_cast_le m K z.2 c
  constructor <;> linarith

/-- The integrand of the two-sample discrepancy is integrable. -/
private lemma integrable_sum_abs_labelCount_sub (m K : ℕ) [NeZero K] :
    Integrable
      (fun z : (Fin m → Fin K) × (Fin m → Fin K) =>
        ∑ c : Fin K, |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|)
      ((iidUniformMeasure m K).prod (iidUniformMeasure m K)) := by
  classical
  apply integrable_finsetSum
  intro c _
  exact integrable_abs_labelCount_sub_labelCount m K c

/-- The expected `ℓ¹` discrepancy of the cell-count vectors of two independent samples is at most
`sqrt (2 * m * K)`. -/
theorem integral_sum_abs_labelCount_sub_le (m K : ℕ) [NeZero K] :
    ∫ z : (Fin m → Fin K) × (Fin m → Fin K),
      ∑ c : Fin K, |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|
      ∂((iidUniformMeasure m K).prod (iidUniformMeasure m K))
      ≤ Real.sqrt (2 * (m : ℝ) * (K : ℝ)) := by
  classical
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hInt : Integrable
      (fun z : (Fin m → Fin K) × (Fin m → Fin K) =>
        ∑ c : Fin K, |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|)
      ((iidUniformMeasure m K).prod (iidUniformMeasure m K)) :=
    integrable_sum_abs_labelCount_sub m K
  have hsqrt : (K : ℝ) * Real.sqrt (2 * ((m : ℝ) / K)) = Real.sqrt (2 * (m : ℝ) * (K : ℝ)) := by
    calc
      (K : ℝ) * Real.sqrt (2 * ((m : ℝ) / K))
          = Real.sqrt ((K : ℝ) ^ 2) * Real.sqrt (2 * ((m : ℝ) / K)) := by
            rw [Real.sqrt_sq hKpos.le]
      _ = Real.sqrt ((K : ℝ) ^ 2 * (2 * ((m : ℝ) / K))) :=
            (Real.sqrt_mul (sq_nonneg (K : ℝ)) _).symm
      _ = Real.sqrt (2 * (m : ℝ) * (K : ℝ)) := by
            congr 1
            field_simp
  calc
    ∫ z : (Fin m → Fin K) × (Fin m → Fin K),
        ∑ c : Fin K, |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|
        ∂((iidUniformMeasure m K).prod (iidUniformMeasure m K))
        = ∑ c : Fin K, ∫ z : (Fin m → Fin K) × (Fin m → Fin K),
            |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|
            ∂((iidUniformMeasure m K).prod (iidUniformMeasure m K)) := by
          apply integral_finsetSum
          intro c _
          exact integrable_abs_labelCount_sub_labelCount m K c
    _ ≤ ∑ _c : Fin K, Real.sqrt (2 * ((m : ℝ) / K)) := by
          apply Finset.sum_le_sum
          intro c _
          exact integral_abs_labelCount_sub_labelCount_le m K c
    _ = (K : ℝ) * Real.sqrt (2 * ((m : ℝ) / K)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = Real.sqrt (2 * (m : ℝ) * (K : ℝ)) := hsqrt

/-- The trivial bound on the expected `ℓ¹` discrepancy of two independent samples: since each
cell-count difference is at most `2 * m`, the sum over `K` cells would be `2 * m * K`; summing the
counts instead gives the sharper deterministic bound `2 * m`. -/
theorem integral_sum_abs_labelCount_sub_le_trivial (m K : ℕ) [NeZero K] :
    ∫ z : (Fin m → Fin K) × (Fin m → Fin K),
      ∑ c : Fin K, |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|
      ∂((iidUniformMeasure m K).prod (iidUniformMeasure m K))
      ≤ 2 * (m : ℝ) := by
  classical
  have hInt : Integrable
      (fun z : (Fin m → Fin K) × (Fin m → Fin K) =>
        ∑ c : Fin K, |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|)
      ((iidUniformMeasure m K).prod (iidUniformMeasure m K)) :=
    integrable_sum_abs_labelCount_sub m K
  have hpt : ∀ z : (Fin m → Fin K) × (Fin m → Fin K),
      ∑ c : Fin K, |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)| ≤ 2 * (m : ℝ) := by
    intro z
    have hterm : ∀ c : Fin K,
        |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|
          ≤ (labelCount z.1 c : ℝ) + (labelCount z.2 c : ℝ) := by
      intro c
      have h1 : 0 ≤ (labelCount z.1 c : ℝ) := Nat.cast_nonneg _
      have h2 : 0 ≤ (labelCount z.2 c : ℝ) := Nat.cast_nonneg _
      rw [abs_sub_le_iff]
      constructor <;> linarith
    calc
      ∑ c : Fin K, |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|
          ≤ ∑ c : Fin K, ((labelCount z.1 c : ℝ) + (labelCount z.2 c : ℝ)) :=
            Finset.sum_le_sum fun c _ => hterm c
      _ = (∑ c : Fin K, (labelCount z.1 c : ℝ))
            + ∑ c : Fin K, (labelCount z.2 c : ℝ) := Finset.sum_add_distrib
      _ = (m : ℝ) + (m : ℝ) := by
            have h1 : (∑ c : Fin K, (labelCount z.1 c : ℝ)) = (m : ℝ) := by
              rw [← Nat.cast_sum, sum_labelCount]
            have h2 : (∑ c : Fin K, (labelCount z.2 c : ℝ)) = (m : ℝ) := by
              rw [← Nat.cast_sum, sum_labelCount]
            rw [h1, h2]
      _ = 2 * (m : ℝ) := by ring
  calc
    ∫ z : (Fin m → Fin K) × (Fin m → Fin K),
        ∑ c : Fin K, |(labelCount z.1 c : ℝ) - (labelCount z.2 c : ℝ)|
        ∂((iidUniformMeasure m K).prod (iidUniformMeasure m K))
        ≤ ∫ _z : (Fin m → Fin K) × (Fin m → Fin K), 2 * (m : ℝ)
            ∂((iidUniformMeasure m K).prod (iidUniformMeasure m K)) :=
          integral_mono hInt (integrable_const _) hpt
    _ = 2 * (m : ℝ) := by simp

end OTSelector.Probability
