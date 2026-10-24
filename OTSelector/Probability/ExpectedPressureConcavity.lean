import OTSelector.Probability.CavitySemidiscretePressureSampling
import OTSelector.Finite.PressureRegularity
import Mathlib.Analysis.Convex.Function

/-!
# Concavity of the expected finite pressure

For a fixed sample the tilted assignment value is concave in the tilt, because it
is the minimum of the affine costs of the finitely many assignments.  Integrating
a pointwise concave function against a probability measure preserves concavity
when the relevant values are integrable.  This gives concavity in the tilt of
the original iid pressure, which is the `hconc` input of
`hasDerivAt_of_concave_supergradient_sequence`.

The integrability of the perturbed assignment value is supplied by
`integrable_assignmentValue`; no atomlessness, measurability of optimizers or
selection of assignments is required.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- The normalized tilted assignment value is integrable at every tilt when all
edge costs are integrable. -/
theorem integrable_perturbedAssignmentValue_div (P : Measure Ω) [IsProbabilityMeasure P]
    (c g : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hc : ∀ i j, Measurable (fun ω => c ω i j))
    (hg : ∀ i j, Measurable (fun ω => g ω i j))
    (hci : ∀ i j, Integrable (fun ω => c ω i j) P)
    (hgi : ∀ i j, Integrable (fun ω => g ω i j) P) (t : ℝ) :
    Integrable (fun ω => perturbedAssignmentValue (c ω) (g ω) t / (n : ℝ)) P := by
  have h := integrable_assignmentValue P (fun ω i j => c ω i j + t * g ω i j)
    (fun i j => (hc i j).add ((hg i j).const_mul t))
    (fun i j => (hci i j).add ((hgi i j).const_mul t))
  refine (h.div_const (n : ℝ)).congr (Filter.Eventually.of_forall fun ω => ?_)
  have hmat : perturbedEdgeCost (fun i j => c ω i j + t * g ω i j) 0 0 =
      perturbedEdgeCost (c ω) (g ω) t := by
    funext i j
    simp [perturbedEdgeCost]
  simp only [perturbedAssignmentValue]
  rw [hmat]

/-- **Concavity of the expected finite pressure.**  The expectation of the
normalized tilted assignment value is concave in the tilt. -/
theorem concaveOn_integral_perturbedAssignmentValue_div
    (P : Measure Ω) [IsProbabilityMeasure P]
    (c g : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hc : ∀ i j, Measurable (fun ω => c ω i j))
    (hg : ∀ i j, Measurable (fun ω => g ω i j))
    (hci : ∀ i j, Integrable (fun ω => c ω i j) P)
    (hgi : ∀ i j, Integrable (fun ω => g ω i j) P) :
    ConcaveOn ℝ univ
      (fun t ↦ ∫ ω, perturbedAssignmentValue (c ω) (g ω) t / (n : ℝ) ∂P) := by
  have hF (t : ℝ) :
      Integrable (fun ω => perturbedAssignmentValue (c ω) (g ω) t / (n : ℝ)) P :=
    integrable_perturbedAssignmentValue_div P c g hc hg hci hgi t
  refine ⟨convex_univ, ?_⟩
  intro t₁ _ t₂ _ a b ha hb hab
  simp only [smul_eq_mul]
  have hpt : ∀ ω,
      a * (perturbedAssignmentValue (c ω) (g ω) t₁ / (n : ℝ)) +
        b * (perturbedAssignmentValue (c ω) (g ω) t₂ / (n : ℝ)) ≤
      perturbedAssignmentValue (c ω) (g ω) (a * t₁ + b * t₂) / (n : ℝ) := by
    intro ω
    exact (concaveOn_perturbedAssignmentValue_div (c ω) (g ω)).2
      (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  calc
    a * (∫ ω, perturbedAssignmentValue (c ω) (g ω) t₁ / (n : ℝ) ∂P) +
        b * (∫ ω, perturbedAssignmentValue (c ω) (g ω) t₂ / (n : ℝ) ∂P)
        = ∫ ω, (a * (perturbedAssignmentValue (c ω) (g ω) t₁ / (n : ℝ)) +
            b * (perturbedAssignmentValue (c ω) (g ω) t₂ / (n : ℝ))) ∂P := by
          rw [integral_add ((hF t₁).const_mul a) ((hF t₂).const_mul b),
            integral_const_mul, integral_const_mul]
    _ ≤ ∫ ω, perturbedAssignmentValue (c ω) (g ω) (a * t₁ + b * t₂) / (n : ℝ) ∂P :=
      integral_mono_ae (((hF t₁).const_mul a).add ((hF t₂).const_mul b)) (hF _)
        (Filter.Eventually.of_forall hpt)

end OTSelector.Probability
