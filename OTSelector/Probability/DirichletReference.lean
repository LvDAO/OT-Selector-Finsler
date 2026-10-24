import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import OTSelector.Probability.BetaMixedMoments

/-!
Conditions: Natural dimension n and the actual recursive law built from an independent Beta(1,n+1) split and the smaller simplex law; zero dimension is included.

Objects: A constructed Dirichlet(1,…,1) reference probability with a.e. simplex membership and strictly positive coordinates.

Proof detail: Start at the one-coordinate Dirac law and recursively prepend a beta coordinate while scaling the old vector by its complementary mass. Product probability and the beta support establish the stated support.

References: Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163; Thomas P. Minka: Section 1, equations (1)–(3), p. 1; equations (19)–(20), p. 2.
Relation: The standard Dirichlet reference is constructed by beta splitting. This is separate from identifying any application-specific random simplex vector with that reference law.
-/


/-!
# The standard Dirichlet reference probability

The reference law with all parameters equal to one is constructed by its usual
beta splitting: a Beta(1,n+1) first coordinate and an independent smaller
Dirichlet vector, scaled by the remaining mass. This is an explicit probability
measure on the standard simplex, separate from the actual cavity law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- Split off the first coordinate and distribute the remaining mass. -/
def dirichletSplit (n : ℕ) (z : ℝ × (Fin (n + 1) → ℝ)) : Fin (n + 2) → ℝ :=
  Fin.cons z.1 (fun j ↦ (1 - z.1) * z.2 j)

theorem measurable_dirichletSplit (n : ℕ) : Measurable (dirichletSplit n) := by
  apply measurable_pi_lambda
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · exact measurable_fst
  · exact (measurable_const.sub measurable_fst).mul
      ((measurable_pi_apply k).comp measurable_snd)

/-- The usual recursive beta construction of Dirichlet(1,...,1) on n+1 labels. -/
noncomputable def dirichletOne : (n : ℕ) → Measure (Fin (n + 1) → ℝ)
  | 0 => Measure.dirac (fun _ ↦ 1)
  | n + 1 => ((betaMeasure 1 (n + 1)).prod (dirichletOne n)).map (dirichletSplit n)

instance isProbabilityMeasure_dirichletOne (n : ℕ) : IsProbabilityMeasure (dirichletOne n) := by
  induction n with
  | zero =>
    dsimp [dirichletOne]
    infer_instance
  | succ n ih =>
    let := ih
    let := isProbabilityMeasureBeta (α := 1) (β := (n : ℝ) + 1) (by norm_num) (by positivity)
    exact Measure.isProbabilityMeasure_map (measurable_dirichletSplit n).aemeasurable

/-- Beta splitting preserves nonnegative coordinates and total mass one. -/
theorem dirichletSplit_mem_stdSimplex {n : ℕ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    {p : Fin (n + 1) → ℝ} (hp : p ∈ stdSimplex ℝ (Fin (n + 1))) :
    dirichletSplit n (x, p) ∈ stdSimplex ℝ (Fin (n + 2)) := by
  constructor
  · intro j
    refine Fin.cases hx.1 (fun k ↦ ?_) j
    exact mul_nonneg (sub_nonneg.mpr hx.2) (hp.1 k)
  · change ∑ j, Fin.cons x (fun k ↦ (1 - x) * p k) j = 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Finset.mul_sum, hp.2]
    ring

/-- The explicitly constructed reference law is carried by the standard simplex. -/
theorem ae_mem_stdSimplex_dirichletOne (n : ℕ) :
    ∀ᵐ p ∂dirichletOne n, p ∈ stdSimplex ℝ (Fin (n + 1)) := by
  induction n with
  | zero =>
    rw [dirichletOne]
    apply (ae_dirac_iff (isClosed_stdSimplex ℝ (Fin 1)).measurableSet).mpr
    exact ⟨fun _ ↦ by norm_num, by simp⟩
  | succ n ih =>
    let := isProbabilityMeasureBeta (α := 1) (β := (n : ℝ) + 1) (by norm_num) (by positivity)
    have hm := (isClosed_stdSimplex ℝ (Fin (n + 2))).measurableSet
    rw [dirichletOne]
    apply (ae_map_iff (measurable_dirichletSplit n).aemeasurable hm).mpr
    apply (Measure.ae_prod_iff_ae_ae (hm.preimage (measurable_dirichletSplit n))).mpr
    filter_upwards [ae_mem_Ioo_betaMeasure 1 ((n : ℝ) + 1)] with x hx
    filter_upwards [ih] with p hp
    exact dirichletSplit_mem_stdSimplex ⟨hx.1.le, hx.2.le⟩ hp

/-- All coordinates of the standard Dirichlet vector are strictly positive
almost surely, including the one-label base case. -/
theorem ae_pos_dirichletOne (n : ℕ) :
    ∀ᵐ p ∂dirichletOne n, ∀ j, 0 < p j := by
  induction n with
  | zero =>
    rw [dirichletOne]
    exact ae_dirac_iff (by measurability) |>.mpr (by intro j; norm_num)
  | succ n ih =>
    let := isProbabilityMeasureBeta (α := 1) (β := (n : ℝ) + 1)
      (by norm_num) (by positivity)
    have hm : MeasurableSet {p : Fin (n + 2) → ℝ | ∀ j, 0 < p j} := by measurability
    rw [dirichletOne]
    apply (ae_map_iff (measurable_dirichletSplit n).aemeasurable hm).mpr
    apply (Measure.ae_prod_iff_ae_ae (hm.preimage (measurable_dirichletSplit n))).mpr
    filter_upwards [ae_mem_Ioo_betaMeasure 1 ((n : ℝ) + 1)] with x hx
    filter_upwards [ih] with p hp
    intro j
    refine Fin.cases hx.1 (fun k ↦ ?_) j
    exact mul_pos (sub_pos.mpr hx.2) (hp k)

end OTSelector.Probability
