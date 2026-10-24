import OTSelector.Geometry.FinslerDistanceLocalizationPhysical
import OTSelector.Reconstruction.AssignmentPressureLocalization
import OTSelector.Reconstruction.DistanceSlackSampling

/-!
# Actual expected pressure controls distant retained physical pairs

The original geometry produces a positive distance-slack gap before any samples
are drawn. This same gap bounds the expected mass of distant pairs for every
measurable fractional optimizer of the original sampled tilted pressure.
-/

open Set Function Matrix MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- One positive actual slack gap, fixed independently of sample size or sample law. -/
structure FarGap (radius : ℝ) where
  value : ℝ
  pos : 0 < value
  bound : ∀ p ∈ D.farPhysicalPairs radius,
    value ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1

/-- The original geometric core produces its positive far-pair gap. -/
theorem nonempty_farGap
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFarPressureMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instFarPressureOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {radius : ℝ} (hradius : 0 < radius) : Nonempty (D.FarGap radius) := by
  obtain ⟨gap, hgap, hb⟩ := D.exists_physical_far_gap hF hcomplete hu ha hinj horder hradius
  exact ⟨⟨gap, hgap, hb⟩⟩

/-- The produced geometric gap bounds the expected distant-pair mass of the
entire original fractional optimal face, with original population marginals.
The estimate never requires all sampled points to belong to the retained core. -/
theorem FarGap.expected_original_mass {radius : ℝ} (G : D.FarGap radius)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFarPressureMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} [IsProbabilityMeasure sample]
    {n : ℕ} (hn : 0 < n) (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i))
    (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j))
    (hXlaw : ∀ i, sample.map (fun ξ ↦ X ξ i) = η₀)
    (hYlaw : ∀ j, sample.map (fun ξ ↦ Y ξ j) = η₁)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hη₀A : ∀ᵐ x ∂η₀, x ∈ A) (hη₁B : ∀ᵐ x ∂η₁, x ∈ B)
    (g W : Ω → Matrix (Fin n) (Fin n) ℝ) (t probeBound scale : ℝ)
    (hscale : 0 < scale)
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hW : ∀ i j, Measurable (fun ξ ↦ W ξ i j))
    (hgb : ∀ᵐ ξ ∂sample, ∀ i j, |g ξ i j| ≤ probeBound)
    (hopt : ∀ᵐ ξ ∂sample, OptimalFractionalAssignment
      (perturbedEdgeCost (fun i j ↦ scale *
        ((F.lengthEDist (X ξ i) (Y ξ j)).toReal - u (Y ξ j) + u (X ξ i))) (g ξ) t) (W ξ)) :
    let c := fun ξ i j ↦ scale *
      ((F.lengthEDist (X ξ i) (Y ξ j)).toReal - u (Y ξ j) + u (X ξ i))
    let Q := fun ξ ↦ {ij | (X ξ ij.1, Y ξ ij.2) ∈ D.farPhysicalPairs radius}
    Integrable (fun ξ ↦ fractionalEdgeMass (Q ξ) (W ξ)) sample ∧
      (∫ ξ, fractionalEdgeMass (Q ξ) (W ξ) ∂sample) ≤
        ((∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t / n ∂sample) +
          |t| * probeBound) / (scale * G.value) := by
  let _instFarPressureMetric : MetricSpace M := F.metricSpace
  let _instFarPressureProper : ProperSpace M := F.properSpace_of_complete hcomplete
  obtain ⟨hcm, hci, hcn⟩ := scaled_distanceSlack_sampling_data X Y u hu hX hY hA hB
    (fun i ↦ ae_of_ae_map (hX i).aemeasurable (by rw [hXlaw i]; exact hη₀A))
    (fun j ↦ ae_of_ae_map (hY j).aemeasurable (by rw [hYlaw j]; exact hη₁B)) hscale.le
  have hQ (i j : Fin n) : MeasurableSet
      {ξ | (X ξ i, Y ξ j) ∈ D.farPhysicalPairs radius} :=
    ((hX i).prodMk (hY j))
      (D.measurableSet_farPhysicalPairs hF hcomplete hu ha hinj radius)
  apply expected_optimalFractionalEdgeMass_le_pressure hn
    (fun ξ i j ↦ scale * distanceSlackEdgeCost (X ξ) (Y ξ) u i j) g W
    (fun ξ ↦ {ij | (X ξ ij.1, Y ξ ij.2) ∈ D.farPhysicalPairs radius})
    t probeBound (scale * G.value) (mul_pos hscale G.pos) hcm hg hW hQ hci hopt
    (Filter.Eventually.of_forall hcn) _ hgb
  exact Filter.Eventually.of_forall fun ξ i j hij ↦
    mul_le_mul_of_nonneg_left (G.bound (X ξ i, Y ξ j) hij) hscale.le

end PopulationLocalPressureCore
end OTSelector.Reconstruction
