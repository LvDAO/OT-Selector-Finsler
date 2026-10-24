import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

/-!
Conditions: Actual one/two-color independent Poisson laws with nonnegative finite rates; the general squared-integral comparison requires a genuine L2 observable on a probability space.

Objects: Poisson second moment a²+a, independent equal-rate pair discrepancy≤sqrt(2a), its real-cast form and a summed finite-cell discrepancy bound.

Proof detail: Evaluate the true Poisson second moments, expand the squared independent difference and use the L2/Jensen bound on its absolute first moment. Factor coordinate laws and add the finite-cell estimates.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.8)–(1.10), p. 2; Rick Durrett: Section 1.6.1, Theorem 1.6.2, p. 29.
Relation: Moment consequences of actual product Poisson laws. The squared-integral helper is distribution-free, and independent colors are part of the product experiment rather than inferred from equal marginal rates.
-/


/-!
# Poisson count discrepancies

Two independent Poisson variables with common rate `a` have expected absolute
difference at most `sqrt (2 a)`.  The proof uses the second moment of the
difference, which is `2 a`, and the elementary inequality
`(∫ |f|)² ≤ ∫ f²` on a probability space.

These estimates are the stochastic inputs of the hierarchical matching bound:
the mean of a Poisson count in a cell is its volume, so the total histogram
discrepancy at a dyadic level is bounded by the sum of square roots of the cell
volumes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

/-- The second moment of the Poisson law in integral form. -/
theorem integral_sq_id_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) ^ 2) ∂poissonMeasure r = (r : ℝ) ^ 2 + (r : ℝ) := by
  have hfac : Integrable (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1)) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    refine (poissonFactorialMoment2_hasSum r).summable.congr (fun n => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      cases n with
      | zero => simp
      | succ k =>
          have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          push_cast
          nlinarith)]
    rw [poissonMeasure_real_singleton]
    ring
  have hid : Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) :=
    integrable_id_poissonMeasure r
  have hadd := integral_add hfac hid
  have hfun : (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) + (n : ℝ)) =
      fun n : ℕ => ((n : ℝ) ^ 2) := by
    funext n
    ring
  rw [hfun, integral_factorialMoment_poissonMeasure r, integral_id_poissonMeasure r] at hadd
  rw [hadd]

/-- On a probability space, the square of the integral is at most the integral
of the square. -/
theorem integral_sq_le_integral_sq_of_prob
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, (f ω) ^ 2 ∂P := by
  have h := variance_nonneg f P
  rw [variance_eq_sub hf] at h
  exact sub_nonneg.mp h

/-- The expected absolute difference of two independent Poisson variables with the
same rate is at most the square root of twice the rate. -/
theorem integral_abs_sub_poissonPair_le (a : ℝ≥0) :
    ∫ z : ℕ × ℕ, |(z.1 : ℝ) - (z.2 : ℝ)|
        ∂((poissonMeasure a).prod (poissonMeasure a)) ≤
      Real.sqrt (2 * (a : ℝ)) := by
  classical
  let μ := poissonMeasure a
  let P := μ.prod μ
  let f : ℕ × ℕ → ℝ := fun z => (z.1 : ℝ) - (z.2 : ℝ)
  have hsq : Integrable (fun n : ℕ => ((n : ℝ) ^ 2)) μ := by
    rw [integrable_poissonMeasure_iff]
    refine (poissonSecondMoment_hasSum a).summable.congr (fun n => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [poissonMeasure_real_singleton]
    ring
  have hid : Integrable (fun n : ℕ => (n : ℝ)) μ := integrable_id_poissonMeasure a
  have hX2 : Integrable (fun z : ℕ × ℕ => ((z.1 : ℝ) ^ 2)) P :=
    hsq.comp_fst μ
  have hY2 : Integrable (fun z : ℕ × ℕ => ((z.2 : ℝ) ^ 2)) P :=
    hsq.comp_snd μ
  have hXY : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ) * (z.2 : ℝ)) P :=
    hid.mul_prod hid
  have hf2 : Integrable (fun z : ℕ × ℕ => (f z) ^ 2) P := by
    convert (hX2.add hY2).sub (hXY.const_mul 2) using 1
    funext z
    simp only [f, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have hfint : Integrable f P := by
    convert hid.comp_fst μ |>.sub (hid.comp_snd μ) using 1
    funext z
    rfl
  have hf_mem : MemLp f 2 P :=
    (memLp_two_iff_integrable_sq hfint.aestronglyMeasurable).mpr hf2
  have habs_mem : MemLp (fun z => |f z|) 2 P := hf_mem.abs
  have hjensen := integral_sq_le_integral_sq_of_prob P habs_mem
  have habs_int : Integrable (fun z => |f z|) P := hfint.abs
  have habs_nonneg : 0 ≤ ∫ z, |f z| ∂P := integral_nonneg fun z => abs_nonneg _
  have hstep : ∫ z, |f z| ∂P ≤ Real.sqrt (∫ z, (f z) ^ 2 ∂P) := by
    rw [← Real.sqrt_sq habs_nonneg]
    exact Real.sqrt_le_sqrt (by simpa only [Real.norm_eq_abs, sq_abs] using hjensen)
  have hval : ∫ z, (f z) ^ 2 ∂P = 2 * (a : ℝ) := by
    have hX2val : ∫ z : ℕ × ℕ, ((z.1 : ℝ) ^ 2) ∂P = (a : ℝ) ^ 2 + (a : ℝ) := by
      change ∫ z : ℕ × ℕ, ((z.1 : ℝ) ^ 2) ∂(μ.prod μ) = (a : ℝ) ^ 2 + (a : ℝ)
      rw [show ∫ z : ℕ × ℕ, ((z.1 : ℝ) ^ 2) ∂(μ.prod μ) =
          ∫ z : ℕ × ℕ, ((z.1 : ℝ) ^ 2) * (1 : ℝ) ∂(μ.prod μ) from
        integral_congr_ae (Filter.Eventually.of_forall fun z => by simp)]
      rw [integral_prod_mul (μ := μ) (ν := μ)
        (f := fun n : ℕ => ((n : ℝ) ^ 2)) (g := fun _ : ℕ => (1 : ℝ))]
      rw [integral_sq_id_poissonMeasure, integral_const]
      simp [measureReal_def]
    have hY2val : ∫ z : ℕ × ℕ, ((z.2 : ℝ) ^ 2) ∂P = (a : ℝ) ^ 2 + (a : ℝ) := by
      change ∫ z : ℕ × ℕ, ((z.2 : ℝ) ^ 2) ∂(μ.prod μ) = (a : ℝ) ^ 2 + (a : ℝ)
      rw [show ∫ z : ℕ × ℕ, ((z.2 : ℝ) ^ 2) ∂(μ.prod μ) =
          ∫ z : ℕ × ℕ, (1 : ℝ) * ((z.2 : ℝ) ^ 2) ∂(μ.prod μ) from
        integral_congr_ae (Filter.Eventually.of_forall fun z => by simp)]
      rw [integral_prod_mul (μ := μ) (ν := μ)
        (f := fun _ : ℕ => (1 : ℝ)) (g := fun n : ℕ => ((n : ℝ) ^ 2))]
      rw [integral_const, integral_sq_id_poissonMeasure]
      simp [measureReal_def]
    have hXYval : ∫ z : ℕ × ℕ, (z.1 : ℝ) * (z.2 : ℝ) ∂P = (a : ℝ) * (a : ℝ) := by
      change ∫ z : ℕ × ℕ, (z.1 : ℝ) * (z.2 : ℝ) ∂(μ.prod μ) = (a : ℝ) * (a : ℝ)
      rw [integral_prod_mul (μ := μ) (ν := μ)
        (f := fun n : ℕ => (n : ℝ)) (g := fun n : ℕ => (n : ℝ))]
      rw [integral_id_poissonMeasure]
    have hpt : (fun z : ℕ × ℕ => (f z) ^ 2) =
        (((fun z : ℕ × ℕ => (z.1 : ℝ) ^ 2) + (fun z : ℕ × ℕ => (z.2 : ℝ) ^ 2)) -
          (fun z : ℕ × ℕ => 2 * ((z.1 : ℝ) * (z.2 : ℝ)))) := by
      funext z
      simp only [f, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hpt]
    have hfun : ((fun z : ℕ × ℕ => (z.1 : ℝ) ^ 2) +
        (fun z : ℕ × ℕ => (z.2 : ℝ) ^ 2)) =
        (fun z : ℕ × ℕ => (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) := by
      funext z
      rfl
    have hsum_int : Integrable (fun z : ℕ × ℕ =>
        (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) P := by
      have h := hX2.add hY2
      rwa [hfun] at h
    rw [hfun]
    change ∫ z : ℕ × ℕ, ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) -
        2 * ((z.1 : ℝ) * (z.2 : ℝ)) ∂P = 2 * (a : ℝ)
    rw [integral_sub hsum_int (hXY.const_mul 2)]
    change ∫ z : ℕ × ℕ, ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ∂P -
        ∫ z : ℕ × ℕ, 2 * ((z.1 : ℝ) * (z.2 : ℝ)) ∂P = 2 * (a : ℝ)
    rw [integral_add hX2 hY2, integral_const_mul, hX2val, hY2val, hXYval]
    ring
  rw [hval] at hstep
  exact hstep

/-- The same Poisson discrepancy bound after pushing the counts forward to `ℝ`.
This is the form produced by the spatial Poisson random measure, whose counts
are `ℝ≥0∞`-valued. -/
theorem integral_abs_sub_poissonPair_cast_le (a : ℝ≥0) :
    ∫ z : ℝ × ℝ, |z.1 - z.2|
        ∂(((poissonMeasure a).map (Nat.cast : ℕ → ℝ)).prod
          ((poissonMeasure a).map (Nat.cast : ℕ → ℝ))) ≤
      Real.sqrt (2 * (a : ℝ)) := by
  rw [Measure.map_prod_map (poissonMeasure a) (poissonMeasure a)
    (measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)) measurable_from_nat]
  have hcont : Continuous (fun z : ℝ × ℝ => |z.1 - z.2|) := by
    continuity
  rw [integral_map (measurable_from_nat.prodMap measurable_from_nat).aemeasurable
    hcont.aestronglyMeasurable]
  have heq : (fun x : ℕ × ℕ =>
      |(Prod.map (Nat.cast : ℕ → ℝ) (Nat.cast : ℕ → ℝ) x).1 -
        (Prod.map (Nat.cast : ℕ → ℝ) (Nat.cast : ℕ → ℝ) x).2|) =
      fun z : ℕ × ℕ => |(z.1 : ℝ) - (z.2 : ℝ)| := by
    funext x
    cases x
    rfl
  rw [heq]
  exact integral_abs_sub_poissonPair_le a

section FiniteCells

open scoped BigOperators

/-- The expected total histogram discrepancy over finitely many independent cells
is at most the sum of square roots of twice the cell rates. -/
theorem integral_sum_abs_sub_poissonPi_le
    {ι : Type*} [Fintype ι] (a : ι → ℝ≥0) :
    ∫ z : ι → ℕ × ℕ,
        (∑ i, |((z i).1 : ℝ) - ((z i).2 : ℝ)|)
        ∂(Measure.pi (fun i => (poissonMeasure (a i)).prod (poissonMeasure (a i)))) ≤
      ∑ i, Real.sqrt (2 * (a i : ℝ)) := by
  classical
  let P : Measure (ι → ℕ × ℕ) :=
    Measure.pi (fun i => (poissonMeasure (a i)).prod (poissonMeasure (a i)))
  have hterm (i : ι) :
      Integrable (fun z : ι → ℕ × ℕ =>
        |((z i).1 : ℝ) - ((z i).2 : ℝ)|) P := by
    have hμ : Integrable (fun w : ℕ × ℕ => |(w.1 : ℝ) - (w.2 : ℝ)|)
        ((poissonMeasure (a i)).prod (poissonMeasure (a i))) := by
      have h1 : Integrable (fun w : ℕ × ℕ => ((w.1 : ℝ))) 
          ((poissonMeasure (a i)).prod (poissonMeasure (a i))) :=
        (integrable_id_poissonMeasure (a i)).comp_fst _
      have h2 : Integrable (fun w : ℕ × ℕ => ((w.2 : ℝ))) 
          ((poissonMeasure (a i)).prod (poissonMeasure (a i))) :=
        (integrable_id_poissonMeasure (a i)).comp_snd _
      exact (h1.sub h2).abs
    have hmp := (measurePreserving_eval (fun i => (poissonMeasure (a i)).prod
      (poissonMeasure (a i))) i)
    have hcont : Continuous (fun w : ℕ × ℕ => |(w.1 : ℝ) - (w.2 : ℝ)|) := by
      continuity
    exact (hmp.integrable_comp hcont.aestronglyMeasurable).mpr hμ
  have hpiece (i : ι) :
      ∫ z : ι → ℕ × ℕ, |((z i).1 : ℝ) - ((z i).2 : ℝ)| ∂P =
        ∫ w : ℕ × ℕ, |(w.1 : ℝ) - (w.2 : ℝ)|
          ∂((poissonMeasure (a i)).prod (poissonMeasure (a i))) := by
    have hmp := measurePreserving_eval (fun i => (poissonMeasure (a i)).prod
      (poissonMeasure (a i))) i
    have hcont : Continuous (fun w : ℕ × ℕ => |(w.1 : ℝ) - (w.2 : ℝ)|) := by
      continuity
    rw [← hmp.map_eq]
    exact (integral_map hmp.measurable.aemeasurable hcont.aestronglyMeasurable).symm
  calc
    ∫ z : ι → ℕ × ℕ, (∑ i, |((z i).1 : ℝ) - ((z i).2 : ℝ)|) ∂P
        = ∑ i, ∫ z : ι → ℕ × ℕ, |((z i).1 : ℝ) - ((z i).2 : ℝ)| ∂P :=
      integral_finsetSum _ (fun i _ => hterm i)
    _ = ∑ i, ∫ w : ℕ × ℕ, |(w.1 : ℝ) - (w.2 : ℝ)|
          ∂((poissonMeasure (a i)).prod (poissonMeasure (a i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hpiece i
    _ ≤ ∑ i, Real.sqrt (2 * (a i : ℝ)) :=
      Finset.sum_le_sum fun i _ => integral_abs_sub_poissonPair_le (a i)

end FiniteCells

end OTSelector.Probability
