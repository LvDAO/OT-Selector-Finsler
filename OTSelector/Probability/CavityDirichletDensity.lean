import OTSelector.Probability.CavityDirichletOriginal
import OTSelector.Probability.DirichletCoordinateDensity

/-!
# Coordinate densities for the actual iid cavity masses

The actual cavity law, already derived from the original independent samples,
has the uniform simplex coordinate density. With random target parameters this
density factors from their original law; independence is a proved conclusion.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace OTSelector.Probability

variable {m : ℕ} {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]

/-- The actual retained-source cell masses have constant density `m!` in the
first `m` mass coordinates. -/
theorem map_iidCavity_simplexCoordinates
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s))) :
    (Measure.pi (fun _ : Fin m ↦ μ)).map
        (fun w ↦ simplexCoordinates m (iidCavityMassVector μ c w)) =
      (m.factorial : ℝ≥0∞) • volume.restrict (openSimplexCoordinates m 1) := by
  change (Measure.pi (fun _ : Fin m ↦ μ)).map
    (simplexCoordinates m ∘ iidCavityMassVector μ c) = _
  rw [← Measure.map_map (measurable_simplexCoordinates m)
    (measurable_iidCavityMassVector μ c hc),
    map_iidCavityMassVector_eq_dirichletOne μ c hc hatom,
    map_simplexCoordinates_dirichletOne]

/-- Every actual cavity cell has positive population mass almost surely. -/
theorem ae_pos_iidCavityMassVector
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s))) :
    ∀ᵐ w ∂Measure.pi (fun _ : Fin m ↦ μ), ∀ j, 0 < iidCavityMassVector μ c w j := by
  have h := ae_pos_dirichletOne m
  rw [← map_iidCavityMassVector_eq_dirichletOne μ c hc hatom] at h
  exact (ae_map_iff (measurable_iidCavityMassVector μ c hc).aemeasurable
    (by measurability)).mp h

/-- Random target parameters retain their original law and are independent of
the actual mass coordinates, whose density is the explicit simplex density. -/
theorem measurePreserving_parameterizedIidCavityCoordinates
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure B) [SFinite ν]
    (c : B → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : B × S ↦ c z.1 j z.2))
    (hatom : ∀ᵐ b ∂ν, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c b j s - c b l s))) :
    MeasurePreserving (fun q : B × (Fin m → S) ↦
      (q.1, simplexCoordinates m (iidCavityMassVector μ (c q.1) q.2)))
      (ν.prod (Measure.pi (fun _ : Fin m ↦ μ)))
      (ν.prod ((m.factorial : ℝ≥0∞) • volume.restrict (openSimplexCoordinates m 1))) := by
  have hcoords : MeasurePreserving (simplexCoordinates m) (dirichletOne m)
      ((m.factorial : ℝ≥0∞) • volume.restrict (openSimplexCoordinates m 1)) :=
    ⟨measurable_simplexCoordinates m, map_simplexCoordinates_dirichletOne m⟩
  exact ((MeasurePreserving.id ν).prod hcoords).comp
    (measurePreserving_parameterizedIidCavityMassVector μ ν c hc hatom)

end OTSelector.Probability
