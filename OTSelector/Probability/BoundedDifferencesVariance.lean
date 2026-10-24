import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance
import OTSelector.Probability.BoundedProductVariance

/-!
Conditions: An actual finite iid product probability law, measurable globally bounded observable and explicit coordinate replacement oscillation bounds.

Objects: Variance at most the sum of squared coordinate oscillation bounds, with an exact measure-preserving coordinate-splitting lemma.

Proof detail: Recursively split the original finite product, decompose conditional variance and bound each one-coordinate fluctuation by its oscillation. Integrate the resulting finite recursion.

References: Roman Vershynin: Section 5.7, Theorem 5.7.1, p. 166; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: The oscillation hypotheses are the standard bounded-differences structure. Lean proves this variance consequence directly by recursion; the stronger McDiarmid exponential theorem is a comparison, not the local conclusion.
-/


/-!
# Variance from coordinatewise bounded differences

A bounded measurable observable of independent coordinates has variance at most
the sum of the squared coordinate oscillation bounds. The proof recursively
splits the actual finite product measure and uses variance decomposition.
No optimizer selection or regularity of the coordinate laws is required.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace OTSelector.Probability

variable {X : Type*} [MeasurableSpace X]

/-- Insertion of the first coordinate preserves the actual product probability. -/
theorem measurePreserving_finCons (μ : Measure X) [SigmaFinite μ] (n : ℕ) :
    MeasurePreserving (fun z : X × (Fin n → X) ↦ (Fin.cons z.1 z.2 : Fin (n + 1) → X))
      (μ.prod (Measure.pi fun _ : Fin n ↦ μ)) (Measure.pi fun _ : Fin (n + 1) ↦ μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ μ) 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ X) 0)
  simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv] using h

/-- Coordinate replacement bounds give a variance bound under the true finite
product law. The constant is sufficient for the high-dimensional pressure scale. -/
theorem variance_pi_le_sum_sq_of_bounded_differences
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    {f : (Fin n → X) → ℝ} (hf : Measurable f) {M : ℝ} (hbound : ∀ x, |f x| ≤ M)
    (c : Fin n → ℝ)
    (hosc : ∀ i x y, |f (Function.update x i y) - f x| ≤ c i) :
    variance f (Measure.pi fun _ : Fin n ↦ μ) ≤ ∑ i, c i ^ 2 := by
  induction n with
  | zero =>
    have hc : f = fun _ ↦ f (fun i ↦ Fin.elim0 i) := by
      funext x
      exact congrArg f (Subsingleton.elim _ _)
    rw [hc, variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let P : Measure (Fin n → X) := Measure.pi fun _ ↦ μ
    let F : X × (Fin n → X) → ℝ := fun z ↦ f (Fin.cons z.1 z.2)
    let g : X → ℝ := fun a ↦ ∫ x, F (a, x) ∂P
    have hpres := measurePreserving_finCons μ n
    have hF : Measurable F := hf.comp hpres.measurable
    have hFb (z : X × (Fin n → X)) : |F z| ≤ M := hbound _
    have hslice (a : X) : Integrable (fun x ↦ F (a, x)) P := by
      apply Integrable.mono' (integrable_const M)
        (hF.comp measurable_prodMk_left).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x ↦ by
        change ‖F (a, x)‖ ≤ M
        simpa only [Real.norm_eq_abs] using hFb (a, x)
    have htail (a : X) : variance (fun x ↦ F (a, x)) P ≤ ∑ i : Fin n, c i.succ ^ 2 := by
      apply ih (hF.comp measurable_prodMk_left) (fun x ↦ hFb (a, x)) (fun i ↦ c i.succ)
      intro i x y
      change |f (Fin.cons a (Function.update x i y)) - f (Fin.cons a x)| ≤ c i.succ
      rw [Fin.cons_update]
      exact hosc i.succ (Fin.cons a x) y
    have hg : Measurable g := hF.stronglyMeasurable.integral_prod_right'.measurable
    have hgosc (a b : X) : |g a - g b| ≤ c 0 := by
      change |(∫ x, F (a, x) ∂P) - ∫ x, F (b, x) ∂P| ≤ c 0
      rw [← integral_sub (hslice a) (hslice b)]
      have hh : ∀ᵐ x ∂P, ‖F (a, x) - F (b, x)‖ ≤ c 0 := by
        apply Filter.Eventually.of_forall
        intro x
        simpa only [F, Real.norm_eq_abs, Fin.update_cons_zero] using
          hosc 0 (Fin.cons b x) a
      simpa using norm_integral_le_of_norm_le_const hh
    have hgvar := variance_le_sq_of_oscillation μ hg hgosc
    obtain ⟨hvarint, hv⟩ := variance_prod_of_bounded μ P hF hFb
    have htailint : (∫ a, variance (fun x ↦ F (a, x)) P ∂μ) ≤
        ∑ i : Fin n, c i.succ ^ 2 := by
      calc
        _ ≤ ∫ _ : X, ∑ i : Fin n, c i.succ ^ 2 ∂μ :=
          integral_mono_ae hvarint (integrable_const _)
            (Filter.Eventually.of_forall htail)
        _ = _ := by simp
    have hvpres := hpres.variance_fun_comp hf.aemeasurable
    change variance F (μ.prod P) = variance f (Measure.pi fun _ : Fin (n + 1) ↦ μ) at hvpres
    rw [← hvpres, hv]
    calc
      _ ≤ (∑ i : Fin n, c i.succ ^ 2) + c 0 ^ 2 := add_le_add htailint hgvar
      _ = _ := by rw [Fin.sum_univ_succ]; ring

end OTSelector.Probability
