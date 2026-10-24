import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import OTSelector.MeasureTheory.SimplexCoordinateVolume
import OTSelector.Probability.BetaMixedMoments
import OTSelector.Probability.DirichletReference

/-!
Conditions: Natural simplex dimension, measurable nonnegative coordinate tests and the actual beta-recursive reference probability.

Objects: The coordinate projection law equals n! times Lebesgue restriction to the open n-dimensional unit simplex.

Proof detail: Induct through the beta split, substitute its Beta(1,n+1) density and rescale the smaller simplex with the proved volume factor; the recursion telescopes to n!.

References: Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163; Thomas P. Minka: Section 1, equations (1)–(3), p. 1; equations (19)–(20), p. 2.
Relation: An actual density theorem for independent coordinates of Dirichlet(1,…,1), including dimension zero. The normalizing simplex measure is the specified coordinate Lebesgue measure.
-/


/-!
# The uniform simplex density of the Dirichlet reference law

Dropping the last barycentric coordinate identifies Dirichlet(1,...,1) with
`n!` times Lebesgue measure on the open simplex in `n` independent coordinates.
The proof uses the actual beta recursion and scalar changes of variables.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- Independent simplex coordinates, obtained by dropping the last entry. -/
def simplexCoordinates (n : ℕ) (p : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i ↦ p i.castSucc

theorem measurable_simplexCoordinates (n : ℕ) : Measurable (simplexCoordinates n) := by
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply i.castSucc

theorem simplexCoordinates_split (n : ℕ) (x : ℝ) (p : Fin (n + 1) → ℝ) :
    simplexCoordinates (n + 1) (dirichletSplit n (x, p)) =
      Fin.cons x ((1 - x) • simplexCoordinates n p) := by
  ext i
  refine Fin.cases rfl (fun j ↦ ?_) i
  rfl

theorem betaPDF_one_nat_succ (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    betaPDF 1 ((n : ℝ) + 1) x =
      ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((1 - x) ^ n) := by
  have hbase : beta 1 ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by
    have h := beta_nat_succ_eq_factorial 0 n
    simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one, one_mul,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add] at h
    rw [h]
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  simp only [betaPDF, betaPDFReal, ite_eq_left (show 0 < x ∧ x < 1 from hx), sub_self, Real.rpow_zero,
    mul_one, add_sub_cancel_right, Real.rpow_natCast, hbase, one_div_one_div]
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_add (Nat.cast_nonneg n) (by norm_num), ENNReal.ofReal_natCast,
    ENNReal.ofReal_one, Nat.cast_add, Nat.cast_one]

/-- The beta recursion has exactly the constant coordinate density `n!`. -/
theorem lintegral_dirichletOne_simplexCoordinates (n : ℕ)
    (f : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f (simplexCoordinates n p) ∂dirichletOne n) =
      (n.factorial : ℝ≥0∞) * ∫⁻ q in openSimplexCoordinates n 1, f q := by
  induction n with
  | zero =>
    have hD : openSimplexCoordinates 0 1 = univ := by
      ext q
      simp [openSimplexCoordinates]
    rw [dirichletOne, lintegral_dirac' (f := fun p ↦ f (simplexCoordinates 0 p)) _
        (hf.comp (measurable_simplexCoordinates 0)),
      hD, Measure.restrict_univ, Measure.volume_pi_eq_dirac
        (simplexCoordinates 0 (fun _ ↦ 1)), lintegral_dirac' _ hf]
    simp
  | succ n ih =>
    let := isProbabilityMeasureBeta (α := 1) (β := (n : ℝ) + 1)
      (by norm_num) (by positivity)
    have hfcons (x : ℝ) : Measurable (fun q : Fin n → ℝ ↦ f (Fin.cons x q)) := by
      apply hf.comp
      apply measurable_pi_lambda
      intro j
      exact Fin.cases measurable_const (fun k ↦ measurable_pi_apply k) j
    have hscaled (x : ℝ) :
        Measurable (fun q : Fin n → ℝ ↦ f (Fin.cons x ((1 - x) • q))) :=
      (hfcons x).comp (measurable_const_smul (1 - x))
    rw [dirichletOne, lintegral_map (f := fun p ↦ f (simplexCoordinates (n + 1) p))
      (hf.comp (measurable_simplexCoordinates (n + 1)))
      (measurable_dirichletSplit n)]
    have hsplit (z : ℝ × (Fin (n + 1) → ℝ)) :
        simplexCoordinates (n + 1) (dirichletSplit n z) =
          Fin.cons z.1 ((1 - z.1) • simplexCoordinates n z.2) :=
      simplexCoordinates_split n z.1 z.2
    simp_rw [hsplit]
    have hpair : Measurable (fun z : ℝ × (Fin (n + 1) → ℝ) ↦
        f (Fin.cons z.1 ((1 - z.1) • simplexCoordinates n z.2))) := by
      apply hf.comp
      apply measurable_pi_lambda
      intro j
      refine Fin.cases measurable_fst (fun k ↦ ?_) j
      exact (measurable_const.sub measurable_fst).mul
        ((measurable_pi_apply k.castSucc).comp measurable_snd)
    rw [lintegral_prod _ hpair.aemeasurable]
    simp_rw [ih _ (hscaled _)]
    have hpair' : Measurable (fun z : ℝ × (Fin n → ℝ) ↦
        f (Fin.cons z.1 ((1 - z.1) • z.2))) := by
      apply hf.comp
      apply measurable_pi_lambda
      intro j
      refine Fin.cases measurable_fst (fun k ↦ ?_) j
      exact (measurable_const.sub measurable_fst).mul
        ((measurable_pi_apply k).comp measurable_snd)
    have hinner : Measurable (fun x : ℝ ↦ (n.factorial : ℝ≥0∞) *
        ∫⁻ q in openSimplexCoordinates n 1, f (Fin.cons x ((1 - x) • q))) :=
      hpair'.lintegral_prod_right'.const_mul _
    have hpdf : Measurable (betaPDF 1 ((n : ℝ) + 1)) :=
      (measurable_betaPDFReal 1 ((n : ℝ) + 1)).ennreal_ofReal
    rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ hpdf hinner]
    simp only [Pi.mul_apply]
    calc
      _ = ∫⁻ x, (Ioo (0 : ℝ) 1).indicator
          (fun x ↦ ((n + 1).factorial : ℝ≥0∞) *
            ∫⁻ q in openSimplexCoordinates n (1 - x), f (Fin.cons x q)) x := by
        apply lintegral_congr
        intro x
        by_cases hx : x ∈ Ioo (0 : ℝ) 1
        · rw [indicator_of_mem hx, betaPDF_one_nat_succ n hx]
          calc
            _ = (((n + 1 : ℕ) : ℝ≥0∞) * n.factorial) *
                (ENNReal.ofReal ((1 - x) ^ n) *
                  ∫⁻ q in openSimplexCoordinates n 1,
                    f (Fin.cons x ((1 - x) • q))) := by ring
            _ = _ := by
              rw [mul_lintegral_smul_openSimplexCoordinates n
                (sub_pos.mpr hx.2) _ (hfcons x), Nat.factorial_succ, Nat.cast_mul]
        · rw [indicator_of_notMem hx]
          simp only [betaPDF, betaPDFReal,
            ite_eq_right (show ¬(0 < x ∧ x < 1) from hx), ENNReal.ofReal_zero, zero_mul]
      _ = _ := by
        rw [lintegral_indicator measurableSet_Ioo,
          lintegral_const_mul' _ _ (by simp),
          ← lintegral_openSimplexCoordinates_succ n f hf]

/-- Exact uniform density in independent simplex coordinates. -/
theorem map_simplexCoordinates_dirichletOne (n : ℕ) :
    (dirichletOne n).map (simplexCoordinates n) =
      (n.factorial : ℝ≥0∞) • volume.restrict (openSimplexCoordinates n 1) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_simplexCoordinates n),
    lintegral_smul_measure, smul_eq_mul]
  exact lintegral_dirichletOne_simplexCoordinates n f hf

end OTSelector.Probability
