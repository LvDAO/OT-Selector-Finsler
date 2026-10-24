import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Moments.Variance

/-!
Conditions: A probability coupling with the supplied two marginals and off-diagonal mass≤η, plus a bounded measurable n-point functional with change bounded by B times the number of changed coordinates.

Objects: Exact product-coupling coordinate laws and a sharp expectation difference bound B n η.

Proof detail: Lift the one-point coupling to its true finite product, project to the two original iid arrays and integrate the deterministic coordinate-count stability using expected mismatch count n times the one-point mismatch probability.

References: David A. Levin and Yuval Peres, with contributions by Elizabeth L. Wilmer: Section 4.2, pp. 49–52, Proposition 4.7, Remark 4.8 and equations (4.8)–(4.13); Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: A measurable-space product-coupling transfer. It directly charges expected changed coordinates rather than multiplying a worst-case n-point range by a product total-variation bound.
-/


/-!
# Transfer of iid functionals across a one-point coupling

Let `μ` and `ν` be probability measures on `X` coupled by a probability `π` on
`X × X` whose off-diagonal mass is at most `η`.  If a functional `F` on `n`
points satisfies the coordinate-count stability
`|F x - F y| ≤ B * #{i | x i ≠ y i}`, then its expectations under the two
`n`-fold product laws differ by at most `B * n * η`.

The proof uses the `n`-fold product coupling: the expected number of coordinates
on which the two samples differ is `n` times the off-diagonal mass of `π`.
This is the sharp per-sample total-variation transfer (in contrast with the
crude product-total-variation bound, which would lose a factor `n`).
-/

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section
namespace OTSelector.Probability

variable {X : Type*} [MeasurableSpace X] [MeasurableEq X]

/-- The coordinate projection of an `n`-tuple. -/
def coordProj (n : ℕ) (b : Bool) : (Fin n → X × X) → (Fin n → X) :=
  fun z i => if b then (z i).1 else (z i).2

/-- The number of coordinates on which the two components of a paired tuple
differ, as a real number. -/
def diffCount (n : ℕ) (z : Fin n → X × X) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun i : Fin n => (z i).1 ≠ (z i).2)).card : ℝ)

/-- The number of coordinates on which two tuples differ, as a real number. -/
def pairDiffCount (n : ℕ) (x y : Fin n → X) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card : ℝ)

theorem measurable_coordProj (n : ℕ) (b : Bool) :
    Measurable (coordProj (X := X) n b) := by
  cases b
  · exact measurable_pi_lambda _ (fun i =>
      measurable_snd.comp (measurable_pi_apply i))
  · exact measurable_pi_lambda _ (fun i =>
      measurable_fst.comp (measurable_pi_apply i))

theorem measurableSet_offDiag : MeasurableSet {z : X × X | z.1 ≠ z.2} := by
  rw [show {z : X × X | z.1 ≠ z.2} = {z : X × X | z.1 = z.2}ᶜ by
    ext z; simp]
  exact MeasurableEq.measurableSet_diagonal.compl

theorem measurable_diffCount (n : ℕ) : Measurable (diffCount (X := X) n) := by
  classical
  have hfun : (fun z : Fin n → X × X => diffCount n z) =
      fun z => ∑ i : Fin n, if (z i).1 ≠ (z i).2 then (1 : ℝ) else 0 := by
    funext z
    unfold diffCount
    rw [Finset.card_filter]
    push_cast
    rfl
  change Measurable (fun z => diffCount n z)
  rw [hfun]
  exact Finset.measurable_sum _ (fun i _ => Measurable.ite
    (MeasurableSet.preimage measurableSet_offDiag (measurable_pi_apply i))
    measurable_const measurable_const)

/-- **Product-coupling transfer.**  A one-point coupling with off-diagonal mass
at most `η` transfers an `n`-point functional with coordinate-count stability
`B` with error `B * n * η`. -/
theorem abs_integral_pi_sub_le_of_coupling
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (X × X)) [IsProbabilityMeasure π]
    (hπ1 : Measure.map Prod.fst π = μ)
    (hπ2 : Measure.map Prod.snd π = ν)
    {n : ℕ} (F : (Fin n → X) → ℝ) (hF : Measurable F)
    {B η C : ℝ} (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hFb : ∀ x, |F x| ≤ C)
    (hoff : π {z : X × X | z.1 ≠ z.2} ≤ ENNReal.ofReal η)
    (hstable : ∀ x y : Fin n → X, |F x - F y| ≤ B * pairDiffCount n x y) :
    |∫ x, F x ∂(Measure.pi (fun _ : Fin n => μ)) -
      ∫ y, F y ∂(Measure.pi (fun _ : Fin n => ν))| ≤ B * (n : ℝ) * η := by
  classical
  -- The product coupling.
  let P : Measure (Fin n → X × X) := Measure.pi (fun _ : Fin n => π)
  haveI hsig1 : ∀ _ : Fin n, SigmaFinite (Measure.map (Prod.fst : X × X → X) π) := by
    intro _
    rw [hπ1]
    infer_instance
  haveI hsig2 : ∀ _ : Fin n, SigmaFinite (Measure.map (Prod.snd : X × X → X) π) := by
    intro _
    rw [hπ2]
    infer_instance
  -- Marginals of the product coupling.
  have hfirst : P.map (coordProj (X := X) n true) = Measure.pi (fun _ : Fin n => μ) := by
    dsimp [P]
    change Measure.map (fun z : Fin n → X × X => fun i => (z i).1)
      (Measure.pi (fun _ : Fin n => π)) = Measure.pi (fun _ : Fin n => μ)
    rw [Measure.pi_map_pi (μ := fun _ : Fin n => π)
      (f := fun _ => (Prod.fst : X × X → X)) (fun _ => measurable_fst.aemeasurable)]
    congr 1
    funext i
    exact hπ1
  have hsecond : P.map (coordProj (X := X) n false) = Measure.pi (fun _ : Fin n => ν) := by
    dsimp [P]
    change Measure.map (fun z : Fin n → X × X => fun i => (z i).2)
      (Measure.pi (fun _ : Fin n => π)) = Measure.pi (fun _ : Fin n => ν)
    rw [Measure.pi_map_pi (μ := fun _ : Fin n => π)
      (f := fun _ => (Prod.snd : X × X → X)) (fun _ => measurable_snd.aemeasurable)]
    congr 1
    funext i
    exact hπ2
  -- Integrability of the two pulled-back functionals.
  have hFint1 : Integrable (fun z : Fin n → X × X => F (coordProj n true z)) P := by
    refine Integrable.of_bound ((hF.comp (measurable_coordProj n true)).aestronglyMeasurable)
      C (Filter.Eventually.of_forall fun z => ?_)
    simpa only [Real.norm_eq_abs] using hFb (coordProj n true z)
  have hFint2 : Integrable (fun z : Fin n → X × X => F (coordProj n false z)) P := by
    refine Integrable.of_bound ((hF.comp (measurable_coordProj n false)).aestronglyMeasurable)
      C (Filter.Eventually.of_forall fun z => ?_)
    simpa only [Real.norm_eq_abs] using hFb (coordProj n false z)
  -- Identify the two integrals with integrals over the coupling.
  have hI1 : ∫ x, F x ∂(Measure.pi (fun _ : Fin n => μ)) =
      ∫ z, F (coordProj n true z) ∂P := by
    rw [← hfirst]
    exact integral_map (measurable_coordProj n true).aemeasurable hF.aestronglyMeasurable
  have hI2 : ∫ y, F y ∂(Measure.pi (fun _ : Fin n => ν)) =
      ∫ z, F (coordProj n false z) ∂P := by
    rw [← hsecond]
    exact integral_map (measurable_coordProj n false).aemeasurable hF.aestronglyMeasurable
  -- The expected number of differing coordinates.
  have hcoord : ∀ i : Fin n, P {z : Fin n → X × X | (z i).1 ≠ (z i).2} =
      π {z : X × X | z.1 ≠ z.2} := by
    intro i
    have hPi : P.map (Function.eval i) = π := by
      dsimp [P]
      rw [Measure.pi_map_eval (μ := fun _ : Fin n => π) i]
      simp
    rw [show {z : Fin n → X × X | (z i).1 ≠ (z i).2} =
        (Function.eval i) ⁻¹' {p : X × X | p.1 ≠ p.2} from rfl]
    rw [← Measure.map_apply (measurable_pi_apply i) measurableSet_offDiag]
    rw [hPi]
  have hcount : ∫ z, diffCount n z ∂P =
      (n : ℝ) * (π {z : X × X | z.1 ≠ z.2}).toReal := by
    unfold diffCount
    have hcard : (fun z : Fin n → X × X =>
        (((Finset.univ.filter (fun i : Fin n => (z i).1 ≠ (z i).2)).card : ℕ) : ℝ)) =
        fun z => ∑ i : Fin n, if (z i).1 ≠ (z i).2 then (1 : ℝ) else 0 := by
      funext z
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [hcard]
    have hInt : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Integrable (fun z : Fin n → X × X =>
          if (z i).1 ≠ (z i).2 then (1 : ℝ) else 0) P := by
      intro i _
      refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun z => ?_)
      · refine Measurable.aestronglyMeasurable ?_
        exact Measurable.ite
          (MeasurableSet.preimage measurableSet_offDiag (measurable_pi_apply i))
          measurable_const measurable_const
      · split_ifs <;> simp
    rw [integral_finsetSum _ hInt]
    have hterm : ∀ i : Fin n,
        ∫ z : Fin n → X × X, (if (z i).1 ≠ (z i).2 then (1 : ℝ) else 0) ∂P =
          (π {z : X × X | z.1 ≠ z.2}).toReal := by
      intro i
      have hind : (fun z : Fin n → X × X => if (z i).1 ≠ (z i).2 then (1 : ℝ) else 0) =
          ({z : Fin n → X × X | (z i).1 ≠ (z i).2}).indicator (fun _ => (1 : ℝ)) := by
        funext z
        by_cases h : (z i).1 ≠ (z i).2 <;> simp [Set.indicator, h]
      rw [hind, integral_indicator_const (μ := P) (1 : ℝ)
        (s := {z : Fin n → X × X | (z i).1 ≠ (z i).2})
        (MeasurableSet.preimage measurableSet_offDiag (measurable_pi_apply i))]
      simp only [Measure.real, smul_eq_mul, mul_one]
      rw [hcoord i]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Assemble.
  have hdiff : ∫ x, F x ∂(Measure.pi (fun _ : Fin n => μ)) -
      ∫ y, F y ∂(Measure.pi (fun _ : Fin n => ν)) =
      ∫ z, (F (coordProj n true z) - F (coordProj n false z)) ∂P := by
    rw [hI1, hI2, integral_sub hFint1 hFint2]
  rw [hdiff]
  have hIntAbs : Integrable
      (fun z : Fin n → X × X => |F (coordProj n true z) - F (coordProj n false z)|) P := by
    refine Integrable.of_bound ?_ (2 * C) (Filter.Eventually.of_forall fun z => ?_)
    · exact (continuous_abs.measurable.comp ((hF.comp (measurable_coordProj n true)).sub
        (hF.comp (measurable_coordProj n false)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_abs]
      have h1 := hFb (coordProj n true z)
      have h2 := hFb (coordProj n false z)
      rw [abs_le] at h1 h2
      rw [abs_le]
      constructor <;> linarith
  have hIntCount : Integrable (fun z : Fin n → X × X => B * diffCount n z) P := by
    refine Integrable.const_mul ?_ B
    refine Integrable.of_bound (measurable_diffCount n).aestronglyMeasurable (n : ℝ)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · unfold diffCount
      have hle := Finset.card_le_univ
        (Finset.univ.filter (fun i : Fin n => (z i).1 ≠ (z i).2))
      have : ((Finset.univ.filter (fun i : Fin n => (z i).1 ≠ (z i).2)).card : ℝ) ≤
          (Fintype.card (Fin n) : ℝ) := by exact_mod_cast hle
      simpa using this
    · unfold diffCount
      positivity
  calc |∫ z, (F (coordProj n true z) - F (coordProj n false z)) ∂P|
      ≤ ∫ z, |F (coordProj n true z) - F (coordProj n false z)| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, B * diffCount n z ∂P := by
        apply integral_mono hIntAbs hIntCount
        intro z
        exact hstable (coordProj n true z) (coordProj n false z)
    _ = B * ∫ z, diffCount n z ∂P := integral_const_mul B _
    _ = B * ((n : ℝ) * (π {z : X × X | z.1 ≠ z.2}).toReal) := by rw [hcount]
    _ ≤ B * ((n : ℝ) * η) := by
        have hπne : π {z : X × X | z.1 ≠ z.2} ≠ ⊤ :=
          ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ _))
        have htoReal : (π {z : X × X | z.1 ≠ z.2}).toReal ≤ η := by
          rw [← ENNReal.toReal_ofReal hη]
          exact ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hoff
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htoReal hn0) hB
    _ = B * (n : ℝ) * η := by ring

end OTSelector.Probability
