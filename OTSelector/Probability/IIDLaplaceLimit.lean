import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Pi

/-!
# IID Laplace Limit

Conditions: Finite iid product experiments, measurable nonnegative tests for probabilistic uses, sample sizes diverging and first-order scaled Laplace defects converging; masked tests retain raw restricted integrals.

Objects: Exact finite-product Laplace readouts and exponential limits, including two independent colors and masks on the unchanged original law.

Proof detail: Factor finite product integrals, rewrite each one-sample integral as one minus its defect and prove (1−d_n)^(N_n)→exp(−a). Masks move defects into raw restrictions; separate product colors multiply.

Relation to primary sources: A finite iid Laplace calculation related to Poisson Laplace limits, with only readout convergence concluded. Two formal identities use totalized Bochner integrals with weaker hypotheses than textbook Fubini; subsequent probabilistic theorems supply measurability/nonnegativity.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.7, Theorem 1.7.2, p. 38. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=46
* Gunter Last; Mathew Penrose, Lectures on the Poisson Process, author version 21 August 2017, Section 1.3, Proposition 1.4, pp. 4–5; Section 3.3, Theorem 3.9, pp. 23–24. https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=35
-/
/-!
# Finite original iid Laplace limits

A scaled one-point Laplace defect determines the actual finite iid array's
Laplace limit, allowing the sample sizes, spaces, laws and tests to vary.
Independent original colors factor exactly. Deterministic geometric cell masks
are kept inside each original endpoint test; only the one-point defect is
integrated against a restricted measure, without normalizing that restriction.

The geometric local-intensity limit remains an explicit input. These results do
not by themselves identify a limiting configuration law as Poisson.
-/


/-!
# Actual finite iid Laplace normalization, including measurable endpoint masks

The law of each original array is the full probability product. A deterministic
measurable mask enters through the indicator test; restricted measures occur only
in the one-point defect integral and are never normalized. No interior or
positive-mass condition is imposed on the retained measurable cells.

The scaled-defect limit remains a geometric input (for example a differentiation
statement for the actual rescaling and original mark law). These results alone do
not identify a Poisson point-process law or prove process tightness.
-/

open Set Function MeasureTheory Filter Topology
open scoped BigOperators
noncomputable section

namespace OTSelector.Probability

/-- Exact Laplace formula for a finite original iid array. -/
theorem integral_exp_neg_iidSum_eq_pow {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (f : X → ℝ) (N : ℕ) :
    (∫ x : Fin N → X, Real.exp (-(∑ i : Fin N, f (x i)))
      ∂Measure.pi (fun _ : Fin N ↦ μ)) = (∫ y, Real.exp (-f y) ∂μ) ^ N := by
  calc
    _ = ∫ x : Fin N → X, ∏ i : Fin N, Real.exp (-f (x i))
        ∂Measure.pi (fun _ : Fin N ↦ μ) := by
      congr 1
      funext x
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
    _ = _ := by
      simpa only [Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin N) (μ := μ) (fun y ↦ Real.exp (-f y)))

/-- Variable sample sizes need no injectivity or exact dependence on the sequence index. -/
theorem tendsto_one_sub_pow_of_scaled_defect {N : ℕ → ℕ} {d : ℕ → ℝ} {a : ℝ}
    (hN : Tendsto N atTop atTop)
    (hd : Tendsto (fun n ↦ (N n : ℝ) * d n) atTop (𝓝 a)) :
    Tendsto (fun n ↦ (1 - d n) ^ N n) atTop (𝓝 (Real.exp (-a))) := by
  have hNr : Tendsto (fun n ↦ (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hNnz : ∀ᶠ n in atTop, (N n : ℝ) ≠ 0 := hNr.eventually_ne_atTop 0
  have hd0 : Tendsto d atTop (𝓝 0) := by
    have h := hd.mul (tendsto_inv_atTop_zero.comp hNr)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [hNnz] with n hn
    dsimp
    field_simp
  let Q : ℝ → ℝ := Function.update (fun x : ℝ ↦ Real.log x / (x - 1)) 1 1
  have hQ : ContinuousAt Q 1 := by
    simpa only [one_ne_zero, inv_one, Real.log_one, sub_zero] using
      (Real.hasDerivAt_log (x := (1 : ℝ)) one_ne_zero).continuousAt_div
  have hbase : Tendsto (fun n ↦ 1 - d n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hd0
  have hQlim : Tendsto (fun n ↦ Q (1 - d n)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Q, Function.update_self, Function.comp_def] using hQ.tendsto.comp hbase
  have hlog (x : ℝ) : Real.log x = (x - 1) * Q x := by
    by_cases hx : x = 1
    · simp [hx, Q]
    · dsimp only [Q]
      rw [Function.update_of_ne hx]
      field_simp [sub_ne_zero.mpr hx]
  have hloglim : Tendsto (fun n ↦ (N n : ℝ) * Real.log (1 - d n)) atTop (𝓝 (-a)) := by
    have h := (hd.mul hQlim).neg
    simp only [mul_one] at h
    convert h using 1
    funext n
    rw [hlog]
    ring
  have hpos : ∀ᶠ n in atTop, 0 < 1 - d n :=
    hbase.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply (Real.continuous_exp.tendsto (-a) |>.comp hloglim).congr'
  filter_upwards [hpos] with n hn
  change Real.exp ((N n : ℝ) * Real.log (1 - d n)) = _
  rw [Real.exp_nat_mul, Real.exp_log hn]

/-- Nonnegative original tests have an integrable Laplace readout bounded by one. -/
theorem integrable_exp_neg_of_nonneg {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) :
    Integrable (fun x ↦ Real.exp (-f x)) μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.neg.exp.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact neg_nonpos.mpr (hfn x)

/-- The one-point Laplace defect has the exact normalization needed by iid powers. -/
theorem integral_exp_neg_eq_one_sub_defect {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) :
    (∫ x, Real.exp (-f x) ∂μ) = 1 - ∫ x, (1 - Real.exp (-f x)) ∂μ := by
  rw [integral_sub (integrable_const (1 : ℝ)) (integrable_exp_neg_of_nonneg μ hf hfn)]
  simp

/-- Actual binomial iid Laplace convergence, allowing varying original spaces,
probability laws, tests and sample sizes. The sole asymptotic input is the scaled
one-point defect, not a Laplace convergence assumption. -/
theorem tendsto_integral_exp_neg_iidSum
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (N : ℕ → ℕ) (f : (n : ℕ) → X n → ℝ) {a : ℝ}
    (hN : Tendsto N atTop atTop)
    (hf : ∀ n, Measurable (f n)) (hfn : ∀ n x, 0 ≤ f n x)
    (hdef : Tendsto (fun n ↦ (N n : ℝ) *
      ∫ x, (1 - Real.exp (-f n x)) ∂μ n) atTop (𝓝 a)) :
    Tendsto (fun n ↦ ∫ x : Fin (N n) → X n,
      Real.exp (-(∑ i : Fin (N n), f n (x i)))
        ∂Measure.pi (fun _ : Fin (N n) ↦ μ n)) atTop (𝓝 (Real.exp (-a))) := by
  simp_rw [integral_exp_neg_iidSum_eq_pow,
    integral_exp_neg_eq_one_sub_defect (μ _) (hf _) (hfn _)]
  exact tendsto_one_sub_pow_of_scaled_defect hN hdef

/-- Exact two-color factorization under the actual product of the two original iid laws. -/
theorem integral_exp_neg_twoIidSums_eq_mul
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (f : X → ℝ) (g : Y → ℝ) (NS NT : ℕ) :
    (∫ z : (Fin NS → X) × (Fin NT → Y),
      Real.exp (-((∑ i : Fin NS, f (z.1 i)) + (∑ j : Fin NT, g (z.2 j))))
      ∂(Measure.pi (fun _ : Fin NS ↦ μ)).prod (Measure.pi (fun _ : Fin NT ↦ ν))) =
      (∫ x, Real.exp (-f x) ∂μ) ^ NS * (∫ y, Real.exp (-g y) ∂ν) ^ NT := by
  have heq : (fun z : (Fin NS → X) × (Fin NT → Y) ↦
      Real.exp (-((∑ i : Fin NS, f (z.1 i)) + (∑ j : Fin NT, g (z.2 j))))) =
      (fun z ↦ Real.exp (-(∑ i : Fin NS, f (z.1 i))) *
        Real.exp (-(∑ j : Fin NT, g (z.2 j)))) := by
    funext z
    rw [neg_add, Real.exp_add]
  rw [heq, integral_prod_mul
    (fun x : Fin NS → X ↦ Real.exp (-(∑ i : Fin NS, f (x i))))
    (fun y : Fin NT → Y ↦ Real.exp (-(∑ j : Fin NT, g (y j)))),
    integral_exp_neg_iidSum_eq_pow, integral_exp_neg_iidSum_eq_pow]

/-- Joint Laplace convergence for two independent original iid colors,
with separately normalized one-point defects and potentially different spaces. -/
theorem tendsto_integral_exp_neg_twoIidSums
    {X Y : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    (μ : (n : ℕ) → Measure (X n)) (ν : (n : ℕ) → Measure (Y n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (NS NT : ℕ → ℕ) (f : (n : ℕ) → X n → ℝ) (g : (n : ℕ) → Y n → ℝ)
    {a b : ℝ} (hNS : Tendsto NS atTop atTop) (hNT : Tendsto NT atTop atTop)
    (hf : ∀ n, Measurable (f n)) (hg : ∀ n, Measurable (g n))
    (hfn : ∀ n x, 0 ≤ f n x) (hgn : ∀ n y, 0 ≤ g n y)
    (hdefS : Tendsto (fun n ↦ (NS n : ℝ) *
      ∫ x, (1 - Real.exp (-f n x)) ∂μ n) atTop (𝓝 a))
    (hdefT : Tendsto (fun n ↦ (NT n : ℝ) *
      ∫ y, (1 - Real.exp (-g n y)) ∂ν n) atTop (𝓝 b)) :
    Tendsto (fun n ↦ ∫ z : (Fin (NS n) → X n) × (Fin (NT n) → Y n),
      Real.exp (-((∑ i : Fin (NS n), f n (z.1 i)) +
        (∑ j : Fin (NT n), g n (z.2 j))))
      ∂(Measure.pi (fun _ : Fin (NS n) ↦ μ n)).prod
        (Measure.pi (fun _ : Fin (NT n) ↦ ν n)))
      atTop (𝓝 (Real.exp (-(a + b)))) := by
  have hS := tendsto_integral_exp_neg_iidSum μ NS f hNS hf hfn hdefS
  have hT := tendsto_integral_exp_neg_iidSum ν NT g hNT hg hgn hdefT
  simp_rw [integral_exp_neg_iidSum_eq_pow] at hS hT
  simpa only [integral_exp_neg_twoIidSums_eq_mul, ← Real.exp_add, ← neg_add] using hS.mul hT

/-- A masked test has zero Laplace defect off the retained measurable set.
The restricted law is used only for this single-point integral, without normalization. -/
theorem integral_laplaceDefect_indicator_eq_restrict
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {H : Set X}
    (hH : MeasurableSet H) (f : X → ℝ) :
    (∫ x, (1 - Real.exp (-H.indicator f x)) ∂μ) =
      ∫ x, (1 - Real.exp (-f x)) ∂μ.restrict H := by
  have heq : (fun x ↦ (1 : ℝ) - Real.exp (-H.indicator f x)) =
      H.indicator (fun x ↦ 1 - Real.exp (-f x)) := by
    funext x
    by_cases hx : x ∈ H <;> simp [hx]
  rw [heq, integral_indicator hH]

/-- Exact finite masked iid formula under the full original probability law. -/
theorem integral_exp_neg_maskedIidSum_eq_pow_defect
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {H : Set X} (hH : MeasurableSet H) {f : X → ℝ}
    (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) (N : ℕ) :
    (∫ x : Fin N → X, Real.exp (-(∑ i : Fin N, H.indicator f (x i)))
      ∂Measure.pi (fun _ : Fin N ↦ μ)) =
        (1 - ∫ x, (1 - Real.exp (-f x)) ∂μ.restrict H) ^ N := by
  rw [integral_exp_neg_iidSum_eq_pow,
    integral_exp_neg_eq_one_sub_defect μ (hf.indicator hH)
      (Set.indicator_nonneg (fun x _ ↦ hfn x)),
    integral_laplaceDefect_indicator_eq_restrict μ hH f]

/-- Actual masked iid Laplace convergence keeps the full original array law.
Only the defect integral is restricted to the deterministic measurable mask. -/
theorem tendsto_integral_exp_neg_maskedIidSum
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (N : ℕ → ℕ) (H : (n : ℕ) → Set (X n)) (f : (n : ℕ) → X n → ℝ) {a : ℝ}
    (hN : Tendsto N atTop atTop)
    (hH : ∀ n, MeasurableSet (H n)) (hf : ∀ n, Measurable (f n))
    (hfn : ∀ n x, 0 ≤ f n x)
    (hdef : Tendsto (fun n ↦ (N n : ℝ) *
      ∫ x, (1 - Real.exp (-f n x)) ∂(μ n).restrict (H n)) atTop (𝓝 a)) :
    Tendsto (fun n ↦ ∫ x : Fin (N n) → X n,
      Real.exp (-(∑ i : Fin (N n), (H n).indicator (f n) (x i)))
        ∂Measure.pi (fun _ : Fin (N n) ↦ μ n)) atTop (𝓝 (Real.exp (-a))) := by
  apply tendsto_integral_exp_neg_iidSum μ N (fun n ↦ (H n).indicator (f n)) hN
    (fun n ↦ (hf n).indicator (hH n))
    (fun n ↦ Set.indicator_nonneg (fun x _ ↦ hfn n x))
  simpa only [integral_laplaceDefect_indicator_eq_restrict (μ _) (hH _) (f _)] using hdef

/-- Exact two-color masked formula under the full, independent original array laws. -/
theorem integral_exp_neg_twoMaskedIidSums_eq_pow_defects
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {HS : Set X} {HT : Set Y} (hHS : MeasurableSet HS) (hHT : MeasurableSet HT)
    {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ y, 0 ≤ g y) (NS NT : ℕ) :
    (∫ z : (Fin NS → X) × (Fin NT → Y),
      Real.exp (-((∑ i : Fin NS, HS.indicator f (z.1 i)) +
        (∑ j : Fin NT, HT.indicator g (z.2 j))))
      ∂(Measure.pi (fun _ : Fin NS ↦ μ)).prod (Measure.pi (fun _ : Fin NT ↦ ν))) =
      (1 - ∫ x, (1 - Real.exp (-f x)) ∂μ.restrict HS) ^ NS *
        (1 - ∫ y, (1 - Real.exp (-g y)) ∂ν.restrict HT) ^ NT := by
  rw [integral_exp_neg_twoIidSums_eq_mul,
    integral_exp_neg_eq_one_sub_defect μ (hf.indicator hHS)
      (Set.indicator_nonneg (fun x _ ↦ hfn x)),
    integral_exp_neg_eq_one_sub_defect ν (hg.indicator hHT)
      (Set.indicator_nonneg (fun y _ ↦ hgn y)),
    integral_laplaceDefect_indicator_eq_restrict μ hHS f,
    integral_laplaceDefect_indicator_eq_restrict ν hHT g]

/-- Two colors can have different deterministic masks, spaces, laws and sample sizes.
The original probability laws and their independence remain the actual integration law. -/
theorem tendsto_integral_exp_neg_twoMaskedIidSums
    {X Y : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    (μ : (n : ℕ) → Measure (X n)) (ν : (n : ℕ) → Measure (Y n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (NS NT : ℕ → ℕ) (HS : (n : ℕ) → Set (X n)) (HT : (n : ℕ) → Set (Y n))
    (f : (n : ℕ) → X n → ℝ) (g : (n : ℕ) → Y n → ℝ)
    {a b : ℝ} (hNS : Tendsto NS atTop atTop) (hNT : Tendsto NT atTop atTop)
    (hHS : ∀ n, MeasurableSet (HS n)) (hHT : ∀ n, MeasurableSet (HT n))
    (hf : ∀ n, Measurable (f n)) (hg : ∀ n, Measurable (g n))
    (hfn : ∀ n x, 0 ≤ f n x) (hgn : ∀ n y, 0 ≤ g n y)
    (hdefS : Tendsto (fun n ↦ (NS n : ℝ) *
      ∫ x, (1 - Real.exp (-f n x)) ∂(μ n).restrict (HS n)) atTop (𝓝 a))
    (hdefT : Tendsto (fun n ↦ (NT n : ℝ) *
      ∫ y, (1 - Real.exp (-g n y)) ∂(ν n).restrict (HT n)) atTop (𝓝 b)) :
    Tendsto (fun n ↦ ∫ z : (Fin (NS n) → X n) × (Fin (NT n) → Y n),
      Real.exp (-((∑ i : Fin (NS n), (HS n).indicator (f n) (z.1 i)) +
        (∑ j : Fin (NT n), (HT n).indicator (g n) (z.2 j))))
      ∂(Measure.pi (fun _ : Fin (NS n) ↦ μ n)).prod
        (Measure.pi (fun _ : Fin (NT n) ↦ ν n)))
      atTop (𝓝 (Real.exp (-(a + b)))) := by
  apply tendsto_integral_exp_neg_twoIidSums μ ν NS NT
    (fun n ↦ (HS n).indicator (f n)) (fun n ↦ (HT n).indicator (g n)) hNS hNT
    (fun n ↦ (hf n).indicator (hHS n)) (fun n ↦ (hg n).indicator (hHT n))
    (fun n ↦ Set.indicator_nonneg (fun x _ ↦ hfn n x))
    (fun n ↦ Set.indicator_nonneg (fun y _ ↦ hgn n y))
  · simpa only [integral_laplaceDefect_indicator_eq_restrict (μ _) (hHS _) (f _)] using hdefS
  · simpa only [integral_laplaceDefect_indicator_eq_restrict (ν _) (hHT _) (g _)] using hdefT

end OTSelector.Probability
