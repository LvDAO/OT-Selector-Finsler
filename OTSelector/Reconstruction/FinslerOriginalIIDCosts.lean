import OTSelector.Reconstruction.MarkedStationaryValuePhysicalRepair
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Original Finsler costs on the unchanged independent endpoint samples

Compact physical carriers bound every original slack edge, including edges
used to complete a sample-dependent partial matching. Measurability and absolute
tilted bounds are produced on the original iid law; no orphan law is introduced.
-/

open Set Function Matrix MeasureTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Both independent arrays stay on their original almost-sure carriers. -/
theorem ae_originalIID_carriers {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) [IsFiniteMeasure ν]
    {A : Set X} {B : Set Y} (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (n : ℕ) :
    ∀ᵐ ξ ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
      (Measure.pi (fun _ : Fin n ↦ ν)),
      (∀ i, ξ.1 i ∈ A) ∧ (∀ j, ξ.2 j ∈ B) := by
  have hs : ∀ᵐ x ∂Measure.pi (fun _ : Fin n ↦ μ), ∀ i, x i ∈ A :=
    ae_all_iff.mpr fun _ ↦ Measure.tendsto_eval_ae_ae.eventually hμ
  have ht : ∀ᵐ y ∂Measure.pi (fun _ : Fin n ↦ ν), ∀ j, y j ∈ B :=
    ae_all_iff.mpr fun _ ↦ Measure.tendsto_eval_ae_ae.eventually hν
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hs,
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually ht] with ξ hξs hξt
  exact ⟨hξs, hξt⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- The scaled original length-distance slack on one pair of endpoint arrays. -/
def finslerOriginalSampleCost (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (scale : ℝ) {n : ℕ} (ξ : (Fin n → M) × (Fin n → M)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ scale * ((F.lengthEDist (ξ.1 i) (ξ.2 j)).toReal - u (ξ.2 j) + u (ξ.1 i))

/-- The same physical probe evaluated on the original endpoint arrays. -/
def originalSampleProbe (g : M × M → ℝ) {n : ℕ}
    (ξ : (Fin n → M) × (Fin n → M)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ g (ξ.1 i, ξ.2 j)

theorem measurable_finslerOriginalSampleCost [SecondCountableTopology M]
    (F : ContinuousFinslerNorm E M) {u : M → ℝ}
    (hu : let _instOriginalIIDCostMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) (scale : ℝ) (n : ℕ) (i j : Fin n) :
    Measurable (fun ξ : (Fin n → M) × (Fin n → M) ↦
      finslerOriginalSampleCost F u scale ξ i j) := by
  exact ((F.measurable_distance_slack hu).comp
    (show Measurable (fun ξ : (Fin n → M) × (Fin n → M) ↦ (ξ.1 i, ξ.2 j)) by
      fun_prop)).const_mul scale

omit [TopologicalSpace M] [T2Space M] [PreconnectedSpace M] [BorelSpace M] in
theorem measurable_originalSampleProbe {g : M × M → ℝ} (hg : Measurable g)
    (n : ℕ) (i j : Fin n) :
    Measurable (fun ξ : (Fin n → M) × (Fin n → M) ↦ originalSampleProbe g ξ i j) :=
  hg.comp (by fun_prop)

omit [BorelSpace M] in
/-- One compact-carrier constant bounds all original tilted sample edges, for
every size and every nonnegative scale. -/
theorem exists_finsler_originalIID_edge_bound
    (F : ContinuousFinslerNorm E M)
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) {u : M → ℝ}
    (hu : let _instOriginalIIDBoundMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {g : M × M → ℝ} (G : ℝ≥0)
    (hg : ∀ p, |g p| ≤ G) :
    ∃ D > 0, ∀ n : ℕ, ∀ scale t : ℝ, 0 ≤ scale →
      ∀ᵐ ξ ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
        (Measure.pi (fun _ : Fin n ↦ ν)),
        ∀ i j, |perturbedEdgeCost (finslerOriginalSampleCost F u scale ξ)
          (originalSampleProbe g ξ) t i j| ≤ scale * D + |t| * (G : ℝ) := by
  obtain ⟨D, hD, hbound⟩ := F.exists_uniform_compact_distance_slack_bound hA hB hu
  refine ⟨D, hD, ?_⟩
  intro n scale t hscale
  filter_upwards [ae_originalIID_carriers μ ν hμ hν n] with ξ hξ
  intro i j
  obtain ⟨hc0, hcD⟩ := hbound (ξ.1 i) (hξ.1 i) (ξ.2 j) (hξ.2 j)
  calc
    |perturbedEdgeCost (finslerOriginalSampleCost F u scale ξ)
        (originalSampleProbe g ξ) t i j| ≤
      |scale * ((F.lengthEDist (ξ.1 i) (ξ.2 j)).toReal - u (ξ.2 j) + u (ξ.1 i))| +
        |t * g (ξ.1 i, ξ.2 j)| := abs_add_le _ _
    _ ≤ scale * D + |t| * (G : ℝ) := by
      rw [abs_of_nonneg (mul_nonneg hscale hc0), abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hcD hscale)
        (mul_le_mul_of_nonneg_left (hg _) (abs_nonneg t))

end OTSelector.Reconstruction
