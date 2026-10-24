import OTSelector.Finite.FractionalGauge
import OTSelector.Reconstruction.SplicedExpectedPressure

/-!
# Original sampled distance slack has the needed integrability

Compact original carriers and a one-Lipschitz potential produce measurable,
nonnegative, integrable slack edges for every finite sample and deterministic
scale. These inputs feed the global spliced-pressure comparison directly.
-/

open Set MeasureTheory Matrix

noncomputable section
namespace OTSelector.Reconstruction

variable {Ω M : Type*} [MeasurableSpace Ω] [PseudoMetricSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ}

/-- The actual distance slack is measurable on arbitrary measurable sample arrays. -/
theorem measurable_distanceSlackEdgeCost (X Y : Ω → Fin n → M) (u : M → ℝ)
    (hu : LipschitzWith 1 u)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i)) (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j)) :
    ∀ i j, Measurable (fun ξ ↦ distanceSlackEdgeCost (X ξ) (Y ξ) u i j) := by
  intro i j
  exact (((hX i).dist (hY j)).sub (hu.continuous.measurable.comp (hY j))).add
    (hu.continuous.measurable.comp (hX i))

/-- Compact physical carriers imply integrable original distance slack; neither
independence nor an additional sample moment is needed for this fact. -/
theorem integrable_distanceSlackEdgeCost_of_compact_carriers
    {Q : Measure Ω} [IsFiniteMeasure Q] (X Y : Ω → Fin n → M) (u : M → ℝ)
    (hu : LipschitzWith 1 u)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i)) (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hXA : ∀ i, ∀ᵐ ξ ∂Q, X ξ i ∈ A) (hYB : ∀ j, ∀ᵐ ξ ∂Q, Y ξ j ∈ B) :
    ∀ i j, Integrable (fun ξ ↦ distanceSlackEdgeCost (X ξ) (Y ξ) u i j) Q := by
  have hc : Continuous (fun p : M × M ↦ dist p.1 p.2 - u p.2 + u p.1) :=
    (continuous_dist.sub (hu.continuous.comp continuous_snd)).add
      (hu.continuous.comp continuous_fst)
  obtain ⟨R, hR⟩ := (hA.prod hB).exists_bound_of_continuousOn hc.continuousOn
  intro i j
  apply (integrable_const R).mono'
    (measurable_distanceSlackEdgeCost X Y u hu hX hY i j).aestronglyMeasurable
  filter_upwards [hXA i, hYB j] with ξ hx hy
  exact hR (X ξ i, Y ξ j) ⟨hx, hy⟩

/-- Positive scaling of the actual compact-carrier distance problem supplies every
nonnegativity and edge-integrability input of the spliced expected-pressure theorem. -/
theorem scaled_distanceSlack_sampling_data
    {Q : Measure Ω} [IsFiniteMeasure Q] (X Y : Ω → Fin n → M) (u : M → ℝ)
    (hu : LipschitzWith 1 u)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i)) (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hXA : ∀ i, ∀ᵐ ξ ∂Q, X ξ i ∈ A) (hYB : ∀ j, ∀ᵐ ξ ∂Q, Y ξ j ∈ B)
    {scale : ℝ} (hscale : 0 ≤ scale) :
    (∀ i j, Measurable (fun ξ ↦ scale * distanceSlackEdgeCost (X ξ) (Y ξ) u i j)) ∧
      (∀ i j, Integrable (fun ξ ↦ scale * distanceSlackEdgeCost (X ξ) (Y ξ) u i j) Q) ∧
      ∀ ξ i j, 0 ≤ scale * distanceSlackEdgeCost (X ξ) (Y ξ) u i j := by
  exact ⟨fun i j ↦ (measurable_distanceSlackEdgeCost X Y u hu hX hY i j).const_mul scale,
    fun i j ↦ (integrable_distanceSlackEdgeCost_of_compact_carriers
      X Y u hu hX hY hA hB hXA hYB i j).const_mul scale,
    fun ξ i j ↦ mul_nonneg hscale (distanceSlackEdgeCost_nonneg (X ξ) (Y ξ) u hu i j)⟩

end OTSelector.Reconstruction
