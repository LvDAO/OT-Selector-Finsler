import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Independence.Integration
import OTSelector.Probability.DirichletQuadraticMoments
import OTSelector.Probability.DirichletReference
import OTSelector.Probability.IIDWeightedSecondMoment

/-!
Conditions: Actual independent Dirichlet reference weights and n+1 iid targets, a measurable target event and an optional bound on its original unweighted mean count.

Objects: The genuine weighted target mass, boundedness/integrability and its exact second moment, followed by the uniform local bound 2V+V².

Proof detail: Expand the finite squared weighted count. Independent target indicators and the genuine Dirichlet coordinate moments evaluate diagonal and off-diagonal terms; the supplied mean-count bound simplifies the result.

References: Thomas P. Minka: Section 1, equations (1)–(3), p. 1; equations (19)–(20), p. 2; Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163.
Relation: A locally derived weighted empirical-mass moment formula. The weights are the actual independent Dirichlet law, not arbitrary simplex weights with an assumed variance estimate.
-/


/-!
# Local masses of the actual Dirichlet-weighted target cloud

For n+1 iid targets and independent original Dirichlet weights p, the target
mass in A is (n+1) times the sum of p_j over targets in A. Its exact second
moment yields a local bound depending only on the original unweighted mean
mass, uniformly in sample size.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {S : Type*} [MeasurableSpace S]

/-- Local mass of the original target cloud with weights (n+1)p_j. -/
def dirichletWeightedTargetMass (n : ℕ) (A : Set S)
    (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → S)) : ℝ :=
  ((n : ℝ) + 1) * ∑ j, z.1 j * A.indicator (fun _ ↦ (1 : ℝ)) (z.2 j)

theorem measurable_dirichletWeightedTargetMass (n : ℕ) {A : Set S}
    (hA : MeasurableSet A) : Measurable (dirichletWeightedTargetMass n A) := by
  have hm : Measurable (A.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hA
  unfold dirichletWeightedTargetMass
  fun_prop

omit [MeasurableSpace S] in
/-- On its actual simplex support, local target mass lies between zero and
the exact total cloud mass n+1. -/
theorem dirichletWeightedTargetMass_bounds (n : ℕ) (A : Set S)
    {p : Fin (n + 1) → ℝ} (hp : p ∈ stdSimplex ℝ (Fin (n + 1)))
    (y : Fin (n + 1) → S) :
    0 ≤ dirichletWeightedTargetMass n A (p, y) ∧
      dirichletWeightedTargetMass n A (p, y) ≤ (n : ℝ) + 1 := by
  have hobs (j : Fin (n + 1)) :
      0 ≤ A.indicator (fun _ ↦ (1 : ℝ)) (y j) ∧
      A.indicator (fun _ ↦ (1 : ℝ)) (y j) ≤ 1 := by
    by_cases hj : y j ∈ A <;> simp [hj]
  have hnonneg : 0 ≤ ∑ j, p j * A.indicator (fun _ ↦ (1 : ℝ)) (y j) :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hp.1 j) (hobs j).1
  have hle : (∑ j, p j * A.indicator (fun _ ↦ (1 : ℝ)) (y j)) ≤ 1 := by
    calc
      _ ≤ ∑ j, p j := Finset.sum_le_sum fun j _ ↦
        mul_le_of_le_one_right (hp.1 j) (hobs j).2
      _ = 1 := hp.2
  unfold dirichletWeightedTargetMass
  exact ⟨mul_nonneg (by positivity) hnonneg,
    mul_le_of_le_one_right (by positivity) hle⟩

/-- Polynomial moments of the actual local mass are Bochner integrable. -/
theorem integrable_dirichletWeightedTargetMass_pow (n : ℕ) (ν : Measure S)
    [IsProbabilityMeasure ν] {A : Set S} (hA : MeasurableSet A) (k : ℕ) :
    Integrable (fun z ↦ (dirichletWeightedTargetMass n A z) ^ k)
      ((dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) := by
  have hs : ∀ᵐ z ∂(dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)),
      z.1 ∈ stdSimplex ℝ (Fin (n + 1)) := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    simpa only [Measure.map_fst_prod, measure_univ, one_smul] using
      ae_mem_stdSimplex_dirichletOne n
  have hm := measurable_dirichletWeightedTargetMass n hA
  have hmk : Measurable (fun z ↦ (dirichletWeightedTargetMass n A z) ^ k) := by fun_prop
  apply Integrable.of_bound hmk.aestronglyMeasurable (((n : ℝ) + 1) ^ k)
  filter_upwards [hs] with z hz
  have hb := dirichletWeightedTargetMass_bounds n A hz z.2
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hb.1]
  exact pow_le_pow_left₀ hb.1 hb.2 k

/-- Exact second moment, with the correct diagonal and off-diagonal factors for
the original probability target law. -/
theorem integral_dirichletWeightedTargetMass_sq (n : ℕ) (ν : Measure S)
    [IsProbabilityMeasure ν] {A : Set S} (hA : MeasurableSet A) :
    (∫ z, (dirichletWeightedTargetMass n A z) ^ 2
      ∂(dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) =
      ((n : ℝ) + 1) ^ 2 * (2 * ν.real A + (n : ℝ) * (ν.real A) ^ 2) /
        ((n : ℝ) + 2) := by
  rw [integral_prod _ (integrable_dirichletWeightedTargetMass_pow n ν hA 2)]
  have hinner : (∫ p, ∫ y, (dirichletWeightedTargetMass n A (p, y)) ^ 2
      ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν) ∂dirichletOne n) =
      ∫ p, ((n : ℝ) + 1) ^ 2 * ((ν.real A) ^ 2 +
        (ν.real A - (ν.real A) ^ 2) * ∑ i, (p i) ^ 2) ∂dirichletOne n := by
    apply integral_congr_ae
    filter_upwards [ae_mem_stdSimplex_dirichletOne n] with p hp
    simp only [dirichletWeightedTargetMass, mul_pow]
    rw [integral_const_mul, integral_iid_weighted_indicator_sum_sq ν hA p, hp.2]
    ring
  rw [hinner, integral_const_mul,
    integral_add (integrable_const _) ((integrable_finsetSum _
      (fun i _ ↦ integrable_dirichletOne_coordinate_pow n i 2)).const_mul _),
    integral_const_mul, integral_dirichletOne_sum_sq]
  simp only [integral_const, probReal_univ, one_smul]
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- A bound on the original unweighted mean local mass gives a sample-size
independent second-moment bound for the actual weighted target mass. -/
theorem integral_dirichletWeightedTargetMass_sq_le (n : ℕ) (ν : Measure S)
    [IsProbabilityMeasure ν] {A : Set S} (hA : MeasurableSet A)
    {V : ℝ} (hV : 0 ≤ V) (hmass : ((n : ℝ) + 1) * ν.real A ≤ V) :
    (∫ z, (dirichletWeightedTargetMass n A z) ^ 2
      ∂(dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) ≤ 2 * V + V ^ 2 := by
  rw [integral_dirichletWeightedTargetMass_sq n ν hA]
  let m := ((n : ℝ) + 1) * ν.real A
  have hm : 0 ≤ m := mul_nonneg (by positivity) measureReal_nonneg
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hfirst : 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hsecond : (n : ℝ) / ((n : ℝ) + 2) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  calc
    _ = (2 * ((n : ℝ) + 1) / ((n : ℝ) + 2)) * m +
        ((n : ℝ) / ((n : ℝ) + 2)) * m ^ 2 := by dsimp [m]; ring
    _ ≤ 2 * m + m ^ 2 := by
      simpa only [one_mul] using add_le_add
        (mul_le_mul_of_nonneg_right hfirst hm)
        (mul_le_mul_of_nonneg_right hsecond (sq_nonneg m))
    _ ≤ 2 * V + V ^ 2 := by
      have hmv : m ≤ V := hmass
      nlinarith

end OTSelector.Probability
