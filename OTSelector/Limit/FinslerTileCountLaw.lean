import OTSelector.Limit.FinslerExpectationUpperBound
import Mathlib.Probability.Moments.Variance

/-!
# The binomial count law of the tile labels

This module supplies the two count-theoretic inputs left open by
`finslerExpectationUpperBound_of_block_model`:

* `hcount`, the mean absolute count discrepancy of two independent iid label
  families in one tile, bounded by `sqrt (2 m w)` where `m` is the sample size
  and `w` the common tile weight;
* `hintCount`, the integrability of the count difference, derived from
  measurability of the label maps alone.

The probabilistic core is proved on the product law
`(Measure.pi (fun _ : Fin m => pS)).prod (Measure.pi (fun _ : Fin m => pT))`
of two independent label words.  The count of a tile is a sum of independent
Bernoulli indicators, so its centred second moment is the sum of the indicator
variances; the two-sample squared difference has second moment at most
`m * wS + m * wT`, and Cauchy--Schwarz bounds the mean absolute difference.
A transfer theorem moves this to an arbitrary sample space through the joint
law of the two label vectors, and a corollary instantiates it for the
concrete weights `∑ c (w c) δ_c`.

The last section records the measurable part of the `hintBlock` analysis and
states precisely what is missing for the random-labelling block value.
-/

open MeasureTheory ProbabilityTheory Filter Manifold
open scoped BigOperators ENNReal NNReal Topology unitInterval ContDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-! ## The iid product law and the indicator decomposition of a count -/

/-- The law of `m` iid labels with common law `p`. -/
def iidLabelMeasure (m : ℕ) (p : Measure ι) : Measure (Fin m → ι) :=
  Measure.pi (fun _ : Fin m => p)

instance iidLabelMeasure_isProbabilityMeasure (m : ℕ) (p : Measure ι)
    [IsProbabilityMeasure p] : IsProbabilityMeasure (iidLabelMeasure m p) := by
  unfold iidLabelMeasure
  infer_instance

/-- The block count is the sum of its cell indicators. -/
theorem blockSizeS_eq_sum_indicator {N : ℕ} (block : Fin N → ι) (c : ι) :
    blockSizeS block c = ∑ i : Fin N, if block i = c then 1 else 0 := by
  classical
  rw [blockSizeS, blockFinset, Finset.card_filter]

/-- Real-valued form of the indicator decomposition. -/
theorem blockSizeS_cast_eq_sum_indicator {N : ℕ} (block : Fin N → ι) (c : ι) :
    (blockSizeS block c : ℝ) =
      ∑ i : Fin N, (if block i = c then (1 : ℝ) else 0) := by
  classical
  rw [blockSizeS_eq_sum_indicator]
  push_cast
  rfl

/-- The indicator of a singleton is measurable. -/
theorem measurable_singletonIndicator (c : ι) :
    Measurable (fun x : ι => if x = c then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_singleton c) measurable_const measurable_const

/-! ## First moment -/

/-- The integral of a singleton indicator against a probability measure is the
mass of the singleton. -/
theorem integral_singleton_indicator (p : Measure ι) [IsProbabilityMeasure p] (c : ι) :
    ∫ x : ι, (if x = c then (1 : ℝ) else 0) ∂p = (p {c}).toReal := by
  classical
  have hset : MeasurableSet ({c} : Set ι) := measurableSet_singleton c
  have hfun : (fun x : ι => if x = c then (1 : ℝ) else 0) =
      ({c} : Set ι).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x = c
    · subst hx
      simp
    · have hx' : x ∉ ({c} : Set ι) := by simpa using hx
      simp [Set.indicator, hx, hx']
  rw [hfun, integral_indicator hset]
  simp [Measure.real]

/-- The same indicator read on one coordinate of the product law. -/
theorem integral_coord_indicator (m : ℕ) (p : Measure ι) [IsProbabilityMeasure p]
    (c : ι) (i : Fin m) :
    ∫ w : Fin m → ι, (if w i = c then (1 : ℝ) else 0) ∂(iidLabelMeasure m p) =
      (p {c}).toReal := by
  rw [iidLabelMeasure, MeasureTheory.integral_comp_eval
    (μ := fun _ : Fin m => p)
    (f := fun x : ι => if x = c then (1 : ℝ) else 0)
    (measurable_singletonIndicator c).aestronglyMeasurable]
  exact integral_singleton_indicator p c

/-- The expected tile count under the iid product law. -/
theorem integral_blockSizeS (m : ℕ) (p : Measure ι) [IsProbabilityMeasure p] (c : ι) :
    ∫ w : Fin m → ι, (blockSizeS w c : ℝ) ∂(iidLabelMeasure m p) =
      (m : ℝ) * (p {c}).toReal := by
  classical
  have hInt : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      Integrable (fun w : Fin m → ι => (if w i = c then (1 : ℝ) else 0))
        (iidLabelMeasure m p) := by
    intro i _
    refine Integrable.of_bound ?_ 1 ?_
    · exact ((measurable_singletonIndicator c).comp (measurable_pi_apply i)).aestronglyMeasurable
    · filter_upwards with w
      split_ifs <;> simp
  calc
    ∫ w, (blockSizeS w c : ℝ) ∂(iidLabelMeasure m p)
        = ∫ w, ∑ i : Fin m, (if w i = c then (1 : ℝ) else 0)
            ∂(iidLabelMeasure m p) := by
          simp_rw [blockSizeS_cast_eq_sum_indicator]
    _ = ∑ i : Fin m, ∫ w, (if w i = c then (1 : ℝ) else 0)
            ∂(iidLabelMeasure m p) := integral_finsetSum _ hInt
    _ = ∑ _i : Fin m, (p {c}).toReal := by
          simp [integral_coord_indicator m p c]
    _ = (m : ℝ) * (p {c}).toReal := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-! ## Second moment -/

/-- The variance of a singleton indicator is `w - w ^ 2`, with `w = p {c}`. -/
theorem variance_singleton_indicator (p : Measure ι) [IsProbabilityMeasure p] (c : ι) :
    ProbabilityTheory.variance (fun x : ι => if x = c then (1 : ℝ) else 0) p =
      (p {c}).toReal - ((p {c}).toReal) ^ 2 := by
  classical
  let X : ι → ℝ := fun x => if x = c then (1 : ℝ) else 0
  have hmeas : Measurable X := measurable_singletonIndicator c
  have hmem : MemLp X 2 p :=
    MemLp.of_bound hmeas.aestronglyMeasurable 1 (by
      filter_upwards with x
      simp only [X]
      split_ifs <;> simp)
  change ProbabilityTheory.variance X p = _
  rw [ProbabilityTheory.variance_eq_sub hmem]
  have h1 : ∫ x : ι, X x ∂p = (p {c}).toReal :=
    integral_singleton_indicator p c
  have h2 : ∫ x : ι, (X ^ 2) x ∂p = (p {c}).toReal := by
    rw [show (fun x : ι => (X ^ 2) x) = X by
      funext x
      simp only [Pi.pow_apply, X]
      split_ifs <;> simp]
    exact h1
  rw [h2, h1]

/-- The centred second moment of a tile count is at most `m * p {c}`. -/
theorem integral_sq_blockSizeS_sub_mean_le (m : ℕ) (p : Measure ι)
    [IsProbabilityMeasure p] (c : ι) :
    ∫ w : Fin m → ι,
        ((blockSizeS w c : ℝ) - (m : ℝ) * (p {c}).toReal) ^ 2
        ∂(iidLabelMeasure m p) ≤ (m : ℝ) * (p {c}).toReal := by
  classical
  let X : ι → ℝ := fun x => if x = c then (1 : ℝ) else 0
  have hmeasN : Measurable (fun w : Fin m → ι => (blockSizeS w c : ℝ)) := by
    have h : (fun w : Fin m → ι => (blockSizeS w c : ℝ)) =
        fun w => ∑ i : Fin m, X (w i) := by
      funext w
      rw [blockSizeS_cast_eq_sum_indicator]
    rw [h]
    exact Finset.measurable_sum _ fun i _ =>
      (measurable_singletonIndicator c).comp (measurable_pi_apply i)
  have hmem : ∀ _i : Fin m, MemLp X 2 p := by
    intro i
    exact MemLp.of_bound (measurable_singletonIndicator c).aestronglyMeasurable 1 (by
      filter_upwards with x
      simp only [X]
      split_ifs <;> simp)
  have hvar : ∫ w : Fin m → ι,
        ((blockSizeS w c : ℝ) - (m : ℝ) * (p {c}).toReal) ^ 2
        ∂(iidLabelMeasure m p) =
      ProbabilityTheory.variance (fun w => (blockSizeS w c : ℝ)) (iidLabelMeasure m p) := by
    have hv := ProbabilityTheory.variance_eq_integral
      (μ := iidLabelMeasure m p)
      (X := fun w : Fin m → ι => (blockSizeS w c : ℝ)) hmeasN.aemeasurable
    rw [hv, integral_blockSizeS]
  rw [hvar]
  have hfun : (fun w : Fin m → ι => (blockSizeS w c : ℝ)) =
      fun w => ∑ i, X (w i) := by
    funext w
    rw [blockSizeS_cast_eq_sum_indicator]
  rw [hfun]
  have hsumfun : (fun w : Fin m → ι => ∑ i, X (w i)) =
      ∑ i : Fin m, fun w : Fin m → ι => X (w i) := by
    funext w
    simp
  rw [hsumfun]
  unfold iidLabelMeasure
  rw [ProbabilityTheory.variance_sum_pi (μ := fun _ : Fin m => p)
    (X := fun _ (x : ι) => X x) hmem]
  calc
    ∑ _i : Fin m, ProbabilityTheory.variance X p
        = ∑ _i : Fin m, ((p {c}).toReal - ((p {c}).toReal) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          exact variance_singleton_indicator p c
    _ ≤ ∑ _i : Fin m, (p {c}).toReal := by
          apply Finset.sum_le_sum
          intro i _
          nlinarith [sq_nonneg ((p {c}).toReal)]
    _ = (m : ℝ) * (p {c}).toReal := by
          simp [Finset.sum_const, nsmul_eq_mul]

end OTSelector.Probability

namespace OTSelector.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-! ## Elementary bound and integrability of a count -/

/-- The target block count is the source block count of the same labelling. -/
theorem blockSizeT_eq_blockSizeS {N : ℕ} (block : Fin N → ι) (c : ι) :
    blockSizeT block c = blockSizeS block c := rfl

/-- A tile count never exceeds the number of labels. -/
theorem blockSizeS_le {N : ℕ} (block : Fin N → ι) (c : ι) : blockSizeS block c ≤ N := by
  classical
  rw [blockSizeS, blockFinset]
  simpa using Finset.card_filter_le (s := (Finset.univ : Finset (Fin N)))
    (p := fun i => block i = c)

/-- Measurability of the real-valued tile count of a label word. -/
theorem measurable_blockSizeS_cast (m : ℕ) (c : ι) :
    Measurable (fun w : Fin m → ι => (blockSizeS w c : ℝ)) := by
  classical
  have h : (fun w : Fin m → ι => (blockSizeS w c : ℝ)) =
      fun w => ∑ i : Fin m, (if w i = c then (1 : ℝ) else 0) := by
    funext w
    rw [blockSizeS_cast_eq_sum_indicator]
  rw [h]
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_singletonIndicator c).comp (measurable_pi_apply i)

/-- Integrability of a tile count under the iid product law. -/
theorem integrable_blockSizeS_cast (m : ℕ) (p : Measure ι) [IsProbabilityMeasure p]
    (c : ι) :
    Integrable (fun w : Fin m → ι => (blockSizeS w c : ℝ)) (iidLabelMeasure m p) := by
  refine Integrable.of_bound (measurable_blockSizeS_cast m c).aestronglyMeasurable
    (m : ℝ) ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast blockSizeS_le w c

/-- Square-integrability of a tile count under the iid product law. -/
theorem memLp_blockSizeS_cast (m : ℕ) (p : Measure ι) [IsProbabilityMeasure p]
    (c : ι) :
    MemLp (fun w : Fin m → ι => (blockSizeS w c : ℝ)) 2 (iidLabelMeasure m p) := by
  refine MemLp.of_bound (measurable_blockSizeS_cast m c).aestronglyMeasurable
    (m : ℝ) ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast blockSizeS_le w c

/-- Integrability of the absolute two-sample count difference. -/
theorem integrable_abs_blockSizeS_sub (m : ℕ) (pS pT : Measure ι)
    [IsProbabilityMeasure pS] [IsProbabilityMeasure pT] (c : ι) :
    Integrable (fun z : (Fin m → ι) × (Fin m → ι) =>
      |(blockSizeS z.1 c : ℝ) - (blockSizeS z.2 c : ℝ)|)
      ((iidLabelMeasure m pS).prod (iidLabelMeasure m pT)) := by
  have h1 : Measurable (fun z : (Fin m → ι) × (Fin m → ι) =>
      (blockSizeS z.1 c : ℝ)) :=
    (measurable_blockSizeS_cast m c).comp measurable_fst
  have h2 : Measurable (fun z : (Fin m → ι) × (Fin m → ι) =>
      (blockSizeS z.2 c : ℝ)) :=
    (measurable_blockSizeS_cast m c).comp measurable_snd
  have hmeas : AEStronglyMeasurable
      (fun z : (Fin m → ι) × (Fin m → ι) =>
        |(blockSizeS z.1 c : ℝ) - (blockSizeS z.2 c : ℝ)|)
      ((iidLabelMeasure m pS).prod (iidLabelMeasure m pT)) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (h1.sub h2).norm.aestronglyMeasurable
  refine Integrable.of_bound hmeas (2 * (m : ℝ)) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_abs, abs_le]
  have hz1 : (0 : ℝ) ≤ (blockSizeS z.1 c : ℝ) := Nat.cast_nonneg _
  have hz2 : (0 : ℝ) ≤ (blockSizeS z.2 c : ℝ) := Nat.cast_nonneg _
  have hb1 : (blockSizeS z.1 c : ℝ) ≤ (m : ℝ) := by exact_mod_cast blockSizeS_le z.1 c
  have hb2 : (blockSizeS z.2 c : ℝ) ≤ (m : ℝ) := by exact_mod_cast blockSizeS_le z.2 c
  constructor <;> linarith

/-! ## Cauchy--Schwarz -/

/-- For a probability measure, `(∫ |f|) ^ 2 ≤ ∫ f ^ 2`.  This is proved directly from
`2 c |f| ≤ |f| ^ 2 + c ^ 2` with `c = ∫ |f|`. -/
theorem sq_integral_abs_le_integral_sq
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

end OTSelector.Probability

namespace OTSelector.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- The mean-zero centred count has zero integral. -/
theorem integral_blockSizeS_sub_mean_zero (m : ℕ) (p : Measure ι)
    [IsProbabilityMeasure p] (c : ι) :
    ∫ w : Fin m → ι,
        ((blockSizeS w c : ℝ) - (m : ℝ) * (p {c}).toReal) ∂(iidLabelMeasure m p) = 0 := by
  have h : Integrable (fun w : Fin m → ι => (blockSizeS w c : ℝ))
      (iidLabelMeasure m p) := integrable_blockSizeS_cast m p c
  calc
    ∫ w, ((blockSizeS w c : ℝ) - (m : ℝ) * (p {c}).toReal) ∂(iidLabelMeasure m p)
        = ∫ w, (blockSizeS w c : ℝ) ∂(iidLabelMeasure m p) -
            ∫ _w : Fin m → ι, ((m : ℝ) * (p {c}).toReal) ∂(iidLabelMeasure m p) :=
          integral_sub h (integrable_const _)
    _ = (m : ℝ) * (p {c}).toReal - (m : ℝ) * (p {c}).toReal := by
          rw [integral_blockSizeS, integral_const]
          simp
    _ = 0 := by ring

/-- **Two-sample second moment of the tile-count difference.**  For two independent
iid label words with the same mass `w` in the tile `c`, the expected squared count
difference is at most `m * w + m * w`. -/
theorem integral_sq_blockSizeS_sub_blockSizeS_le (m : ℕ)
    (pS pT : Measure ι) [IsProbabilityMeasure pS] [IsProbabilityMeasure pT] (c : ι)
    (hw : (pS {c}).toReal = (pT {c}).toReal) :
    ∫ z : (Fin m → ι) × (Fin m → ι),
        ((blockSizeS z.1 c : ℝ) - (blockSizeS z.2 c : ℝ)) ^ 2
        ∂((iidLabelMeasure m pS).prod (iidLabelMeasure m pT)) ≤
      (m : ℝ) * (pS {c}).toReal + (m : ℝ) * (pT {c}).toReal := by
  classical
  let μS : Measure (Fin m → ι) := iidLabelMeasure m pS
  let μT : Measure (Fin m → ι) := iidLabelMeasure m pT
  let ν : Measure ((Fin m → ι) × (Fin m → ι)) := μS.prod μT
  let w : ℝ := (pS {c}).toReal
  let f : (Fin m → ι) → ℝ := fun u => (blockSizeS u c : ℝ) - (m : ℝ) * w
  have hfS : Integrable f μS :=
    (integrable_blockSizeS_cast m pS c).sub (integrable_const _)
  have hfT : Integrable f μT :=
    (integrable_blockSizeS_cast m pT c).sub (integrable_const _)
  have hf2S : Integrable (fun u => f u ^ 2) μS := by
    have hmem : MemLp f 2 μS :=
      (memLp_blockSizeS_cast m pS c).sub (memLp_const ((m : ℝ) * w))
    exact hmem.integrable_sq
  have hf2T : Integrable (fun u => f u ^ 2) μT := by
    have hmem : MemLp f 2 μT :=
      (memLp_blockSizeS_cast m pT c).sub (memLp_const ((m : ℝ) * w))
    exact hmem.integrable_sq
  have hpt : ∀ z : (Fin m → ι) × (Fin m → ι),
      (f z.1 - f z.2) ^ 2 = f z.1 ^ 2 + f z.2 ^ 2 - 2 * (f z.1 * f z.2) := by
    intro z
    ring
  have hA : Integrable (fun z : (Fin m → ι) × (Fin m → ι) => f z.1 ^ 2) ν :=
    hf2S.comp_fst μT
  have hB : Integrable (fun z : (Fin m → ι) × (Fin m → ι) => f z.2 ^ 2) ν :=
    hf2T.comp_snd μS
  have hC : Integrable (fun z : (Fin m → ι) × (Fin m → ι) => f z.1 * f z.2) ν :=
    hfS.op_fst_snd (op := fun x y : ℝ => x * y) continuous_mul
      ⟨1, fun x y => by rw [one_mul]; exact norm_mul_le x y⟩ hfT
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
  have hAeq : ∫ z, f z.1 ^ 2 ∂ν = ∫ u, f u ^ 2 ∂μS := by
    have h := integral_fun_fst (μ := μS) (ν := μT) (f := fun u : Fin m → ι => f u ^ 2)
    simpa [ν] using h
  have hBeq : ∫ z, f z.2 ^ 2 ∂ν = ∫ u, f u ^ 2 ∂μT := by
    have h := integral_fun_snd (μ := μS) (ν := μT) (f := fun u : Fin m → ι => f u ^ 2)
    simpa [ν] using h
  have hzeroS : ∫ u, f u ∂μS = 0 := by
    simpa [μS, f, w] using integral_blockSizeS_sub_mean_zero m pS c
  have hzeroT : ∫ u, f u ∂μT = 0 := by
    have h := integral_blockSizeS_sub_mean_zero m pT c
    have hw' : (pT {c}).toReal = w := hw.symm
    simpa [μT, f, hw'] using h
  have hcross : ∫ z, f z.1 * f z.2 ∂ν = 0 := by
    have h := integral_prod_mul (μ := μS) (ν := μT) (f := f) (g := f)
    rw [hzeroS, hzeroT] at h
    simpa [ν] using h
  have hsingleS : ∫ u, f u ^ 2 ∂μS ≤ (m : ℝ) * (pS {c}).toReal := by
    simpa [μS, f, w] using integral_sq_blockSizeS_sub_mean_le m pS c
  have hsingleT : ∫ u, f u ^ 2 ∂μT ≤ (m : ℝ) * (pT {c}).toReal := by
    have h := integral_sq_blockSizeS_sub_mean_le m pT c
    have hw' : (pT {c}).toReal = w := hw.symm
    simpa [μT, f, hw'] using h
  have hmain : ∫ z, (f z.1 - f z.2) ^ 2 ∂ν ≤
      (m : ℝ) * (pS {c}).toReal + (m : ℝ) * (pT {c}).toReal := by
    rw [hExpand, hAeq, hBeq, hcross]
    nlinarith [hsingleS, hsingleT]
  have hfun : (fun z : (Fin m → ι) × (Fin m → ι) =>
        ((blockSizeS z.1 c : ℝ) - (blockSizeS z.2 c : ℝ)) ^ 2)
      = fun z => (f z.1 - f z.2) ^ 2 := by
    funext z
    simp only [f]
    ring
  rw [hfun]
  simpa [ν, μS, μT] using hmain

/-- **Mean absolute tile-count discrepancy under two iid label words.** -/
theorem integral_abs_blockSizeS_sub_le_iid (m : ℕ)
    (pS pT : Measure ι) [IsProbabilityMeasure pS] [IsProbabilityMeasure pT] (c : ι)
    (hw : (pS {c}).toReal = (pT {c}).toReal) :
    ∫ z : (Fin m → ι) × (Fin m → ι),
        |(blockSizeS z.1 c : ℝ) - (blockSizeS z.2 c : ℝ)|
        ∂((iidLabelMeasure m pS).prod (iidLabelMeasure m pT)) ≤
      Real.sqrt (2 * (m : ℝ) * (pS {c}).toReal) := by
  classical
  let μS : Measure (Fin m → ι) := iidLabelMeasure m pS
  let μT : Measure (Fin m → ι) := iidLabelMeasure m pT
  let ν : Measure ((Fin m → ι) × (Fin m → ι)) := μS.prod μT
  let w : ℝ := (pS {c}).toReal
  let f : (Fin m → ι) → ℝ := fun u => (blockSizeS u c : ℝ) - (m : ℝ) * w
  have hf_bound : ∀ u : Fin m → ι, ‖f u‖ ≤ (m : ℝ) + (m : ℝ) * |w| := by
    intro u
    have h1 : ‖(blockSizeS u c : ℝ)‖ ≤ (m : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast blockSizeS_le u c
    have h1 : ‖(blockSizeS u c : ℝ)‖ = (blockSizeS u c : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have h2 : ‖(m : ℝ) * w‖ = (m : ℝ) * |w| := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg m)]
    have hle : (blockSizeS u c : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast blockSizeS_le u c
    calc ‖f u‖ = ‖(blockSizeS u c : ℝ) - (m : ℝ) * w‖ := rfl
      _ ≤ ‖(blockSizeS u c : ℝ)‖ + ‖(m : ℝ) * w‖ := norm_sub_le _ _
      _ = (blockSizeS u c : ℝ) + (m : ℝ) * |w| := by rw [h1, h2]
      _ ≤ (m : ℝ) + (m : ℝ) * |w| := by linarith
  have hmeasF : AEStronglyMeasurable
      (fun z : (Fin m → ι) × (Fin m → ι) => f z.1 - f z.2) ν := by
    have hmeas : Measurable f := by
      have h : f = fun u => (blockSizeS u c : ℝ) - (m : ℝ) * w := rfl
      rw [h]
      exact (measurable_blockSizeS_cast m c).sub measurable_const
    exact ((hmeas.comp measurable_fst).sub (hmeas.comp measurable_snd)).aestronglyMeasurable
  have hboundF : ∀ z : (Fin m → ι) × (Fin m → ι), ‖f z.1 - f z.2‖ ≤
      2 * ((m : ℝ) + (m : ℝ) * |w|) := by
    intro z
    calc ‖f z.1 - f z.2‖ ≤ ‖f z.1‖ + ‖f z.2‖ := norm_sub_le _ _
      _ ≤ ((m : ℝ) + (m : ℝ) * |w|) + ((m : ℝ) + (m : ℝ) * |w|) :=
          add_le_add (hf_bound _) (hf_bound _)
      _ = 2 * ((m : ℝ) + (m : ℝ) * |w|) := by ring
  have hmem : MemLp (fun z : (Fin m → ι) × (Fin m → ι) => f z.1 - f z.2) 2 ν :=
    MemLp.of_bound hmeasF _ (Filter.Eventually.of_forall hboundF)
  have hdiff_int : Integrable (fun z : (Fin m → ι) × (Fin m → ι) => f z.1 - f z.2) ν :=
    hmem.integrable (by norm_num)
  have hdiff_sq_int : Integrable
      (fun z : (Fin m → ι) × (Fin m → ι) => (f z.1 - f z.2) ^ 2) ν :=
    hmem.integrable_sq
  have hcs := sq_integral_abs_le_integral_sq hdiff_int hdiff_sq_int
  have hsq_diff : ∫ z, (f z.1 - f z.2) ^ 2 ∂ν ≤ 2 * (m : ℝ) * w := by
    have h := integral_sq_blockSizeS_sub_blockSizeS_le m pS pT c hw
    have hsame : ∫ z, (f z.1 - f z.2) ^ 2 ∂ν =
        ∫ z : (Fin m → ι) × (Fin m → ι),
          ((blockSizeS z.1 c : ℝ) - (blockSizeS z.2 c : ℝ)) ^ 2 ∂ν := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [f]
      ring
    rw [hsame]
    have hwsum : 2 * (m : ℝ) * w =
        (m : ℝ) * (pS {c}).toReal + (m : ℝ) * (pT {c}).toReal := by
      rw [← hw]
      ring
    rw [hwsum]
    simpa [ν, μS, μT] using h
  have hsq : (∫ z, |f z.1 - f z.2| ∂ν) ^ 2 ≤ 2 * (m : ℝ) * w :=
    le_trans hcs hsq_diff
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  have hfun : (fun z : (Fin m → ι) × (Fin m → ι) => |f z.1 - f z.2|)
      = fun z => |(blockSizeS z.1 c : ℝ) - (blockSizeS z.2 c : ℝ)| := by
    funext z
    simp only [f]
    congr 1
    ring
  rw [hfun] at hsqrt
  simpa [ν, μS, μT, w] using hsqrt

end OTSelector.Probability

namespace OTSelector.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-! ## Transfer to an arbitrary sample space -/

/-- **Transfer of the iid count bound through the joint law of the label vectors.**

If the joint law of the two label words is the product of the two iid product
laws, the mean absolute count difference in a tile is at most
`sqrt (2 m w)`, where `m` is the word length and `w` the common tile mass. -/
theorem integral_abs_blockSizeS_sub_le_of_jointLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (blockS blockT : Fin m → Ω → ι)
    (pS pT : Measure ι) [IsProbabilityMeasure pS] [IsProbabilityMeasure pT] (c : ι)
    (hS : ∀ i, Measurable (blockS i)) (hT : ∀ j, Measurable (blockT j))
    (hjoint : P.map (fun ξ => (fun i => blockS i ξ, fun j => blockT j ξ)) =
      (iidLabelMeasure m pS).prod (iidLabelMeasure m pT))
    (hw : (pS {c}).toReal = (pT {c}).toReal) :
    ∫ ξ, |(blockSizeS (fun i => blockS i ξ) c : ℝ) -
        (blockSizeS (fun j => blockT j ξ) c : ℝ)| ∂P ≤
      Real.sqrt (2 * (m : ℝ) * (pS {c}).toReal) := by
  classical
  let φ : Ω → (Fin m → ι) × (Fin m → ι) := fun ξ => (fun i => blockS i ξ, fun j => blockT j ξ)
  have hφ : Measurable φ :=
    (measurable_pi_iff.mpr hS).prodMk (measurable_pi_iff.mpr hT)
  have hF : Measurable (fun z : (Fin m → ι) × (Fin m → ι) =>
      |(blockSizeS z.1 c : ℝ) - (blockSizeS z.2 c : ℝ)|) := by
    have h1 : Measurable (fun z : (Fin m → ι) × (Fin m → ι) =>
        (blockSizeS z.1 c : ℝ)) := (measurable_blockSizeS_cast m c).comp measurable_fst
    have h2 : Measurable (fun z : (Fin m → ι) × (Fin m → ι) =>
        (blockSizeS z.2 c : ℝ)) := (measurable_blockSizeS_cast m c).comp measurable_snd
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (h1.sub h2).norm
  have hgoal : (∫ ξ, |(blockSizeS (fun i => blockS i ξ) c : ℝ) -
        (blockSizeS (fun j => blockT j ξ) c : ℝ)| ∂P) =
      ∫ ξ, (fun z : (Fin m → ι) × (Fin m → ι) =>
        |(blockSizeS z.1 c : ℝ) - (blockSizeS z.2 c : ℝ)|) (φ ξ) ∂P := rfl
  rw [hgoal, ← integral_map hφ.aemeasurable hF.aestronglyMeasurable, hjoint]
  exact integral_abs_blockSizeS_sub_le_iid m pS pT c hw

/-! ## The weighted label law `∑ c (w c) δ_c` -/

/-- The weighted label law with masses `w c` at the labels `c`. -/
noncomputable def weightedLabelLaw {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (w : ι → I) : Measure ι :=
  ∑ c : ι, (ENNReal.ofReal (w c : ℝ)) • Measure.dirac c

/-- The total mass of the weighted label law. -/
theorem weightedLabelLaw_univ {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (w : ι → I) :
    weightedLabelLaw w Set.univ = ∑ c : ι, ENNReal.ofReal (w c : ℝ) := by
  rw [weightedLabelLaw, Measure.finsetSum_apply]
  simp

/-- The mass of a single label under the weighted label law. -/
theorem weightedLabelLaw_apply {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (w : ι → I) (c : ι) :
    weightedLabelLaw w {c} = ENNReal.ofReal (w c : ℝ) := by
  classical
  rw [weightedLabelLaw, Measure.finsetSum_apply, Finset.sum_eq_single c]
  · rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton c)]
    simp
  · intro b _ hbc
    rw [Measure.smul_apply, Measure.dirac_apply' b (measurableSet_singleton c)]
    simp [hbc]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-- The weighted label law is a probability measure when the weights sum to one. -/
theorem weightedLabelLaw_isProbability {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (w : ι → I) (hwsum : ∑ c, (w c : ℝ) = 1) :
    IsProbabilityMeasure (weightedLabelLaw w) := by
  refine ⟨?h⟩
  rw [weightedLabelLaw_univ,
    ← ENNReal.ofReal_sum_of_nonneg (fun c _ => (w c).2.1), hwsum]
  simp

/-- The real mass of a label under the weighted label law. -/
theorem weightedLabelLaw_apply_toReal {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (w : ι → I) (c : ι) :
    (weightedLabelLaw w {c}).toReal = (w c : ℝ) := by
  rw [weightedLabelLaw_apply, ENNReal.toReal_ofReal (w c).2.1]

end OTSelector.Probability

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

open OTSelector.Probability

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- Measurability of the source tile count from measurability of the label maps. -/
theorem measurable_tileSourceCount {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (blockS : Fin (n + 1) → Ω n → ι) (c : ι) (hS : ∀ i, Measurable (blockS i)) :
    Measurable (tileSourceCount blockS c) := by
  have h : tileSourceCount blockS c =
      fun ξ => ∑ i : Fin (n + 1), (if blockS i ξ = c then (1 : ℝ) else 0) := by
    funext ξ
    exact blockSizeS_cast_eq_sum_indicator (fun i => blockS i ξ) c
  rw [h]
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_singletonIndicator c).comp (hS i)

/-- Measurability of the target tile count from measurability of the label maps. -/
theorem measurable_tileTargetCount {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (blockT : Fin (n + 1) → Ω n → ι) (c : ι) (hT : ∀ j, Measurable (blockT j)) :
    Measurable (tileTargetCount blockT c) := by
  have h : tileTargetCount blockT c =
      fun ξ => ∑ j : Fin (n + 1), (if blockT j ξ = c then (1 : ℝ) else 0) := by
    funext ξ
    exact blockSizeS_cast_eq_sum_indicator (fun j => blockT j ξ) c
  rw [h]
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_singletonIndicator c).comp (hT j)

/-- Integrability of the source tile count. -/
theorem integrable_tileSourceCount {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (blockS : Fin (n + 1) → Ω n → ι) (c : ι) (P : Measure (Ω n))
    [IsProbabilityMeasure P] (hS : ∀ i, Measurable (blockS i)) :
    Integrable (tileSourceCount blockS c) P := by
  refine Integrable.of_bound (measurable_tileSourceCount blockS c hS).aestronglyMeasurable
    ((n + 1 : ℕ) : ℝ) ?_
  filter_upwards with ξ
  have hval : tileSourceCount blockS c ξ = (blockSizeS (fun i => blockS i ξ) c : ℝ) := rfl
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), hval]
  exact_mod_cast blockSizeS_le (fun i => blockS i ξ) c

/-- Integrability of the target tile count. -/
theorem integrable_tileTargetCount {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (blockT : Fin (n + 1) → Ω n → ι) (c : ι) (P : Measure (Ω n))
    [IsProbabilityMeasure P] (hT : ∀ j, Measurable (blockT j)) :
    Integrable (tileTargetCount blockT c) P := by
  refine Integrable.of_bound (measurable_tileTargetCount blockT c hT).aestronglyMeasurable
    ((n + 1 : ℕ) : ℝ) ?_
  filter_upwards with ξ
  have hval : tileTargetCount blockT c ξ = (blockSizeS (fun j => blockT j ξ) c : ℝ) := rfl
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), hval]
  exact_mod_cast blockSizeS_le (fun j => blockT j ξ) c

/-- **`hintCount`.**  The absolute tile-count difference is integrable as soon as both label
maps are measurable; no law assumption is used. -/
theorem integrable_abs_tileCount_sub {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (blockS blockT : Fin (n + 1) → Ω n → ι) (c : ι) (P : Measure (Ω n))
    [IsProbabilityMeasure P] (hS : ∀ i, Measurable (blockS i))
    (hT : ∀ j, Measurable (blockT j)) :
    Integrable (fun ξ => |tileSourceCount blockS c ξ - tileTargetCount blockT c ξ|) P :=
  ((integrable_tileSourceCount blockS c P hS).sub
    (integrable_tileTargetCount blockT c P hT)).abs

/-- **`hcount` from the joint law of the two label vectors.**  If the joint law of the two
label words is the product of the two iid product laws, the mean absolute tile-count
discrepancy is at most `sqrt (2 (n+1) w)`, where `w` is the common tile mass. -/
theorem integral_abs_tileCount_sub_le_of_jointLaw {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (blockS blockT : Fin (n + 1) → Ω n → ι) (c : ι) (P : Measure (Ω n))
    [IsProbabilityMeasure P]
    (pS pT : Measure ι) [IsProbabilityMeasure pS] [IsProbabilityMeasure pT]
    (hS : ∀ i, Measurable (blockS i)) (hT : ∀ j, Measurable (blockT j))
    (hjoint : P.map (fun ξ => (fun i => blockS i ξ, fun j => blockT j ξ)) =
      (iidLabelMeasure (n + 1) pS).prod (iidLabelMeasure (n + 1) pT))
    (hw : (pS {c}).toReal = (pT {c}).toReal) :
    ∫ ξ, |tileSourceCount blockS c ξ - tileTargetCount blockT c ξ| ∂P ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (pS {c}).toReal) := by
  have h := integral_abs_blockSizeS_sub_le_of_jointLaw (m := n + 1) P blockS blockT
    pS pT c hS hT hjoint hw
  simpa only [tileSourceCount, tileTargetCount, blockSizeT_eq_blockSizeS] using h

/-- **`hcount` for the weighted label law `∑ c (w c) δ_c`.** -/
theorem integral_abs_tileCount_sub_le_of_weighted {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (blockS blockT : Fin (n + 1) → Ω n → ι) (c : ι) (P : Measure (Ω n))
    [IsProbabilityMeasure P] (w : ι → I) (hwsum : ∑ d, (w d : ℝ) = 1)
    (hS : ∀ i, Measurable (blockS i)) (hT : ∀ j, Measurable (blockT j))
    (hjoint : P.map (fun ξ => (fun i => blockS i ξ, fun j => blockT j ξ)) =
      (iidLabelMeasure (n + 1) (weightedLabelLaw w)).prod
        (iidLabelMeasure (n + 1) (weightedLabelLaw w))) :
    ∫ ξ, |tileSourceCount blockS c ξ - tileTargetCount blockT c ξ| ∂P ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)) := by
  haveI : IsProbabilityMeasure (weightedLabelLaw w) :=
    weightedLabelLaw_isProbability w hwsum
  have h := integral_abs_tileCount_sub_le_of_jointLaw blockS blockT c P
    (weightedLabelLaw w) (weightedLabelLaw w) hS hT hjoint rfl
  simpa only [weightedLabelLaw_apply_toReal] using h

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

namespace OTSelector.Probability

/-! ## Partial measurability results for the physical tile block

`finslerNormalizedTileBlock` evaluates `PartialMatching.maxCardValue` on
`blockCost blockS blockT cost c`.  When the labelling `blockS`, `blockT` is
*fixed*, `blockCost` reads a fixed pair of enumerations
(`blockEmbeddingS`, `blockEmbeddingT`), so measurability in the ambient cost
family is immediate.  The random-labelling case is genuinely missing: the
enumeration is `Finset.equivFin` of the random block finset
(`OTSelector/Finite/BlockMaxValueComparison.lean:83-88`), and there is no
measurable selection of that enumeration.  The precise missing statement is a
measurability lemma for
`ξ ↦ maxCardValue (blockCost (fun i => blockS i ξ) (fun j => blockT j ξ) (cost ξ) c)`,
equivalently a padded fixed-size reformulation of the block value with the
cardinality constraint `min (#S_c) (#T_c)`. -/

/-- With a fixed labelling, the block cost matrix is measurable in a measurable
family of ambient cost matrices. -/
theorem measurable_blockCost_fixed {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    {α : Type*} [MeasurableSpace α] (blockS blockT : Fin N → β)
    (c : α → Fin N → Fin N → ℝ) (hc : ∀ i j, Measurable (fun a => c a i j)) (t : β) :
    ∀ i j, Measurable (fun a => blockCost blockS blockT (c a) t i j) := by
  intro i j
  exact hc (blockEmbeddingS blockS t i) (blockEmbeddingT blockT t j)

/-- With a fixed labelling, the maximum-cardinality block value is measurable in a
measurable family of ambient cost matrices. -/
theorem measurable_blockValue_fixed {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    {α : Type*} [MeasurableSpace α] (blockS blockT : Fin N → β)
    (c : α → Fin N → Fin N → ℝ) (hc : ∀ i j, Measurable (fun a => c a i j)) (t : β) :
    Measurable (fun a => PartialMatching.maxCardValue (blockCost blockS blockT (c a) t)) :=
  PartialMatching.measurable_maxCardValue _
    (measurable_blockCost_fixed blockS blockT c hc t)

end OTSelector.Probability

namespace OTSelector.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-! ## From the iid hypotheses to the joint law -/

/-- **The joint law of two independent iid label families.**  If each family is iid with its
common marginal law and the two families are independent, the joint law of the two label
words is the product of the two iid product laws.  This discharges the joint-law hypothesis
of `integral_abs_blockSizeS_sub_le_of_jointLaw` from the paper's sampling assumptions. -/
theorem jointLaw_of_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (blockS blockT : Fin m → Ω → ι)
    (pS pT : Measure ι) [IsProbabilityMeasure pS] [IsProbabilityMeasure pT]
    (hS : ∀ i, AEMeasurable (blockS i) P) (hT : ∀ j, AEMeasurable (blockT j) P)
    (hSindep : iIndepFun blockS P) (hTindep : iIndepFun blockT P)
    (hST : IndepFun (fun ξ => fun i => blockS i ξ) (fun ξ => fun j => blockT j ξ) P)
    (hSlaw : ∀ i, P.map (blockS i) = pS) (hTlaw : ∀ j, P.map (blockT j) = pT) :
    P.map (fun ξ => (fun i => blockS i ξ, fun j => blockT j ξ)) =
      (iidLabelMeasure m pS).prod (iidLabelMeasure m pT) := by
  have hSmap : P.map (fun ξ => fun i => blockS i ξ) = iidLabelMeasure m pS := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map hS).mp hSindep]
    simp only [hSlaw, iidLabelMeasure]
  have hTmap : P.map (fun ξ => fun j => blockT j ξ) = iidLabelMeasure m pT := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map hT).mp hTindep]
    simp only [hTlaw, iidLabelMeasure]
  have hST' := IndepFun.map_prod_eq_prod_map_map
    (aemeasurable_pi_iff.mpr hS) (aemeasurable_pi_iff.mpr hT) hST
  rw [hSmap, hTmap] at hST'
  exact hST'

end OTSelector.Probability

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

open OTSelector.Probability

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- **`hcount` from the iid label hypotheses.**  If the source and target tile labels are
iid with common marginal laws and the two families are independent, the mean absolute
tile-count discrepancy is at most `sqrt (2 (n+1) w)`. -/
theorem integral_abs_tileCount_sub_le_of_iid {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (blockS blockT : Fin (n + 1) → Ω n → ι) (c : ι) (P : Measure (Ω n))
    [IsProbabilityMeasure P]
    (pS pT : Measure ι) [IsProbabilityMeasure pS] [IsProbabilityMeasure pT]
    (hS : ∀ i, Measurable (blockS i)) (hT : ∀ j, Measurable (blockT j))
    (hSindep : iIndepFun blockS P) (hTindep : iIndepFun blockT P)
    (hST : IndepFun (fun ξ => fun i => blockS i ξ) (fun ξ => fun j => blockT j ξ) P)
    (hSlaw : ∀ i, P.map (blockS i) = pS) (hTlaw : ∀ j, P.map (blockT j) = pT)
    (hw : (pS {c}).toReal = (pT {c}).toReal) :
    ∫ ξ, |tileSourceCount blockS c ξ - tileTargetCount blockT c ξ| ∂P ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (pS {c}).toReal) :=
  integral_abs_tileCount_sub_le_of_jointLaw blockS blockT c P pS pT hS hT
    (jointLaw_of_iIndepFun P blockS blockT pS pT
      (fun i => (hS i).aemeasurable) (fun j => (hT j).aemeasurable)
      hSindep hTindep hST hSlaw hTlaw) hw

/-- **`hcount` for the weighted label law from the iid hypotheses.** -/
theorem integral_abs_tileCount_sub_le_of_weighted_iid {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (blockS blockT : Fin (n + 1) → Ω n → ι) (c : ι) (P : Measure (Ω n))
    [IsProbabilityMeasure P] (w : ι → I) (hwsum : ∑ d, (w d : ℝ) = 1)
    (hS : ∀ i, Measurable (blockS i)) (hT : ∀ j, Measurable (blockT j))
    (hSindep : iIndepFun blockS P) (hTindep : iIndepFun blockT P)
    (hST : IndepFun (fun ξ => fun i => blockS i ξ) (fun ξ => fun j => blockT j ξ) P)
    (hSlaw : ∀ i, P.map (blockS i) = weightedLabelLaw w)
    (hTlaw : ∀ j, P.map (blockT j) = weightedLabelLaw w) :
    ∫ ξ, |tileSourceCount blockS c ξ - tileTargetCount blockT c ξ| ∂P ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)) := by
  haveI : IsProbabilityMeasure (weightedLabelLaw w) :=
    weightedLabelLaw_isProbability w hwsum
  have h := integral_abs_tileCount_sub_le_of_iid blockS blockT c P
    (weightedLabelLaw w) (weightedLabelLaw w) hS hT hSindep hTindep hST hSlaw hTlaw rfl
  simpa only [weightedLabelLaw_apply_toReal] using h

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
