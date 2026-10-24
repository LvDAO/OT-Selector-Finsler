import OTSelector.Probability.DirichletTargetCloudMoments

/-!
# Uniform local moments of original spatially marked target clouds

Only the original spatial marginal is needed: marks may depend on position.
Projecting a compact marked window gives a finite-volume spatial window, and
translation invariance supplies the target-count bound uniformly in the root.
-/

open MeasureTheory Set Function Filter TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

variable {ι B : Type*} [Fintype ι] [TopologicalSpace B] [MeasurableSpace B]
  [BorelSpace B] [SecondCountableTopology B]

omit [BorelSpace B] [SecondCountableTopology B] in
/-- The original spatial marginal controls every compact marked window, with
no independence assumption between spatial position and mark. -/
theorem normalized_restrict_marked_translated_mass_le
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (D : Set (ι → ℝ)) {N : ℝ} (hN : 0 < N)
    (hν : ν.map Prod.fst = (ENNReal.ofReal N)⁻¹ • volume.restrict D)
    (K : Set ((ι → ℝ) × B)) (hK : IsCompact K) (z : ι → ℝ) :
    N * ν.real {y | cavitySpatialTranslate z y ∈ interior K} ≤
      volume.real (Prod.fst '' K) := by
  let W : Set (ι → ℝ) := Prod.fst '' K
  have hW : IsCompact W := hK.image continuous_fst
  have hwin : MeasurableSet {x : ι → ℝ | x - z ∈ W} :=
    (measurable_id.sub measurable_const) hW.measurableSet
  have hsub : {y | cavitySpatialTranslate z y ∈ interior K} ⊆
      Prod.fst ⁻¹' {x : ι → ℝ | x - z ∈ W} := by
    intro y hy
    exact ⟨cavitySpatialTranslate z y, interior_subset hy, rfl⟩
  calc
    N * ν.real {y | cavitySpatialTranslate z y ∈ interior K} ≤
        N * ν.real (Prod.fst ⁻¹' {x : ι → ℝ | x - z ∈ W}) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) hN.le
    _ = N * (ν.map Prod.fst).real {x : ι → ℝ | x - z ∈ W} := by
      rw [map_measureReal_apply measurable_fst hwin]
    _ ≤ volume.real W := normalized_restrict_translated_mass_le
      volume (ν.map Prod.fst) D hN hν hW.measurableSet hW.measure_ne_top z

/-- Original marked target measures have the exact uniform 2V+V² local second
moment, where V is the volume of the spatial projection of the compact window. -/
theorem integral_original_markedTargetCloud_sq_le
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (U : Ω → (ι → ℝ)) (p : Ω → Fin (n + 1) → ℝ)
    (y : Fin (n + 1) → Ω → ((ι → ℝ) × B))
    (hscene : MeasurePreserving
      (fun ω ↦ (U ω, (p ω, fun j ↦ y j ω))) P
      (ρ.prod ((dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))))
    (D : Set (ι → ℝ))
    (hν : ν.map Prod.fst = (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ • volume.restrict D)
    (K : Set ((ι → ℝ) × B)) (hK : IsCompact K) :
    Integrable (fun ω ↦ ((semidiscreteTargetCloud (p ω)
      (fun j ↦ cavitySpatialTranslate (U ω) (y j ω)) ((n : ℝ) + 1)).real (interior K)) ^ 2) P ∧
    (∫ ω, ((semidiscreteTargetCloud (p ω)
      (fun j ↦ cavitySpatialTranslate (U ω) (y j ω)) ((n : ℝ) + 1)).real (interior K)) ^ 2 ∂P) ≤
      2 * volume.real (Prod.fst '' K) + (volume.real (Prod.fst '' K)) ^ 2 := by
  apply integral_original_semidiscreteTargetCloud_sq_le P ρ ν U p y hscene
    (fun q ↦ cavitySpatialTranslate q.1 q.2) measurable_cavitySpatialTranslate
    isOpen_interior.measurableSet measureReal_nonneg
  exact Eventually.of_forall (fun z ↦ normalized_restrict_marked_translated_mass_le
    ν D (by positivity) hν K hK z)

end OTSelector.Probability
