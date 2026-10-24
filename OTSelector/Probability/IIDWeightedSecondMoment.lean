import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration

/-!
## Lemma skeleton

* **Conditions:** A finite iid product law, a measurable real observable, and arbitrary deterministic real weights. Boundedness is assumed in the weighted-sum theorem to obtain genuine finite moments; the first pair identity uses totalized Bochner integrals under measurability alone.
* **Objects:** Diagonal/distinct-coordinate pair moments and exact second moments of weighted observations and weighted indicators.
* **Proof detail:** Use the coordinate marginal law on the diagonal and independence off the diagonal. Expand the weighted square into a finite double sum, integrate termwise and collect diagonal terms.

## Mathematical sources

* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56
* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 2.2.1, Theorem 2.2.1 and proof, pp. 56–57.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=64
* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.6.3, p. 33, equations (1.6.2)–(1.6.4).
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=41

**Relationship to the sources:** Deterministic-weight and noncentered form of the independent second-moment expansion. The unbounded first helper must be read with Lean integral conventions.
-/

/-!
# Exact second moments of weighted iid observations

The diagonal and distinct-coordinate contributions are separated under the
actual finite product law. Indicator observations give local target counts,
with deterministic weights that will subsequently be integrated against their
original Dirichlet law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {S I : Type*} [MeasurableSpace S] [Fintype I] [DecidableEq I]

/-- The exact pair moment under an iid product law, including its diagonal. -/
theorem integral_iid_coordinate_mul (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) (i j : I) :
    (∫ y : I → S, f (y i) * f (y j) ∂Measure.pi (fun _ ↦ ν)) =
      (∫ x, f x ∂ν) ^ 2 +
        if i = j then (∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simpa only [ite_true, add_sub_cancel, ← pow_two] using
      (integral_comp_eval (μ := fun _ : I ↦ ν)
        (i := i) (by fun_prop : Measurable (fun x ↦ (f x) ^ 2)).aestronglyMeasurable)
  · have hi := iIndepFun_pi (μ := fun _ : I ↦ ν) (fun _ ↦ hf.aemeasurable)
    rw [(hi.indepFun hij).integral_fun_mul_eq_mul_integral
      (hf.comp (measurable_pi_apply i)).aestronglyMeasurable
      (hf.comp (measurable_pi_apply j)).aestronglyMeasurable,
      integral_comp_eval hf.aestronglyMeasurable,
      integral_comp_eval hf.aestronglyMeasurable]
    simp [hij, pow_two]

/-- Exact second moment of a weighted iid sum. The observations can be signed;
boundedness is used solely to justify finite sums of Bochner integrals. -/
theorem integral_iid_weighted_sum_sq (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) (w : I → ℝ) :
    (∫ y : I → S, (∑ i, w i * f (y i)) ^ 2 ∂Measure.pi (fun _ ↦ ν)) =
      (∫ x, f x ∂ν) ^ 2 * (∑ i, w i) ^ 2 +
        ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2) * ∑ i, (w i) ^ 2 := by
  classical
  have hp (i j : I) : Integrable (fun y : I → S ↦ f (y i) * f (y j))
      (Measure.pi (fun _ ↦ ν)) := by
    apply Integrable.of_bound (by fun_prop) (B * B)
    exact Filter.Eventually.of_forall fun y ↦ by
      simpa only [Real.norm_eq_abs, abs_mul] using
        mul_le_mul (hbound (y i)) (hbound (y j)) (abs_nonneg _) hB
  have hexpand : (fun y : I → S ↦ (∑ i, w i * f (y i)) ^ 2) =
      (fun y ↦ ∑ i, ∑ j, (w i * w j) * (f (y i) * f (y j))) := by
    funext y
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand, integral_finsetSum _ (fun i _ ↦
    integrable_finsetSum _ (fun j _ ↦ (hp i j).const_mul (w i * w j)))]
  simp_rw [integral_finsetSum _ (fun j _ ↦ (hp _ j).const_mul _),
    integral_const_mul, integral_iid_coordinate_mul ν hf]
  let a : ℝ := ∫ x, f x ∂ν
  let b : ℝ := (∫ x, (f x) ^ 2 ∂ν) - a ^ 2
  change (∑ i, ∑ j, (w i * w j) * (a ^ 2 + if i = j then b else 0)) =
    a ^ 2 * (∑ i, w i) ^ 2 + b * ∑ i, (w i) ^ 2
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hdiag (i : I) : (∑ j, (w i * w j) * (if i = j then b else 0)) =
      b * (w i) ^ 2 := by
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    ring
  simp_rw [hdiag]
  rw [← Finset.mul_sum]
  congr 1
  simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  ring

/-- Indicator observations give the exact local-mass second moment for any
deterministic weights and any measurable target event. -/
theorem integral_iid_weighted_indicator_sum_sq (ν : Measure S) [IsProbabilityMeasure ν]
    {A : Set S} (hA : MeasurableSet A) (w : I → ℝ) :
    (∫ y : I → S, (∑ i, w i * A.indicator (fun _ ↦ (1 : ℝ)) (y i)) ^ 2
      ∂Measure.pi (fun _ ↦ ν)) =
      (ν.real A) ^ 2 * (∑ i, w i) ^ 2 +
        (ν.real A - (ν.real A) ^ 2) * ∑ i, (w i) ^ 2 := by
  have hm : Measurable (A.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hA
  have hbound : ∀ x, |A.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have hsq : (fun x ↦ (A.indicator (fun _ ↦ (1 : ℝ)) x) ^ 2) =
      A.indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hmean : (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x ∂ν) = ν.real A := by
    simpa using (integral_indicator_const (μ := ν) (1 : ℝ) hA)
  rw [integral_iid_weighted_sum_sq ν hm (by norm_num) hbound w, hsq, hmean]

end OTSelector.Probability
