import OTSelector.Reconstruction.FinslerPopulationPressureTiles
import OTSelector.Reconstruction.FinslerPopulationSeedPhysicalRecovery

/-!
# Original population samples and simultaneous geometric pressure freezing

Actual population marginals supply the seed-coordinate identities almost surely.
The finite geometric tiles therefore act directly on the unchanged physical
sample arrays. No reconstruction or local remainder oracle is an input.
-/

open Set Function Matrix MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

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
  [IsFiniteMeasure lambda] {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}

namespace PopulationLocalPressureCore.TaylorTiles

/-- The actual original sample law gives the simultaneous finite-tile pressure
comparison. All reconstruction, small-displacement, measurability and local
Taylor estimates follow from the produced original population core. -/
theorem expected_original_distance_pressure {ε : ℝ} (T : D.TaylorTiles ε)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPopulationSpliceMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instPopulationSpliceOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} [IsProbabilityMeasure sample]
    {n : ℕ} (hn : 0 < n) (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i))
    (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j))
    (hXlaw : ∀ i, sample.map (fun ξ ↦ X ξ i) = η₀)
    (hYlaw : ∀ j, sample.map (fun ξ ↦ Y ξ j) = η₁)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hη₀A : ∀ᵐ x ∂η₀, x ∈ A) (hη₁B : ∀ᵐ x ∂η₁, x ∈ B)
    (g : Ω → Matrix (Fin n) (Fin n) ℝ)
    (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ)
    (t G probeError scale : ℝ) (hε0 : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hscale : 0 ≤ scale) (hprobe : 0 ≤ probeError)
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hh : ∀ k i j, Measurable (fun ξ ↦ h ξ k i j))
    (hgb : ∀ᵐ ξ ∂sample, ∀ i j, |g ξ i j| ≤ G)
    (hhb : ∀ᵐ ξ ∂sample, ∀ k i j,
      (i, j) ∈ T.edgeEvent (X ξ) (Y ξ) k → |h ξ k i j| ≤ G)
    (hgh : ∀ᵐ ξ ∂sample, ∀ k i j,
      (i, j) ∈ T.edgeEvent (X ξ) (Y ξ) k → |g ξ i j - h ξ k i j| ≤ probeError) :
    let c := fun ξ i j ↦ scale *
      ((F.lengthEDist (X ξ i) (Y ξ j)).toReal - u (Y ξ j) + u (X ξ i))
    let d := fun ξ k i j ↦ scale * (T.core k).frozenPhysicalCost (T.reference k) (X ξ i) (Y ξ j)
    let Q := fun ξ k ↦ T.edgeEvent (X ξ) (Y ξ) k
    let dQ := fun ξ ↦ finiteTileSplice (Q ξ) (c ξ) (d ξ)
    let hQ := fun ξ ↦ finiteTileSplice (Q ξ) (g ξ) (h ξ)
    Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t / n) sample ∧
      Integrable (fun ξ ↦ perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n) sample ∧
      |(∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t / n ∂sample) -
        ∫ ξ, perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n ∂sample| ≤
      (2 * ε) * ((∫ ξ, perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n ∂sample) +
        |t| * G) + |t| * probeError := by
  let _instPopulationSpliceMetric : MetricSpace M := F.metricSpace
  let _instPopulationSpliceProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPopulationSplicePolish : PolishSpace M := inferInstance
  obtain ⟨hsource, htarget⟩ := D.haar.physical_endpoints_ae
    hF hcomplete hu ha hinj horder hb hinv hη₀reg hη₁reg
  have hXs : ∀ᵐ ξ ∂sample, ∀ i : Fin n, ∀ k : Fin D.haar.continuous.count,
      a (X ξ i) ∈ (D.haar.continuous.coefficient k).roots →
      let S := (P (D.haar.continuous.coefficient k).seedIndex).seed
      X ξ i = S.curve (populationSeedRootLabelValue S a (a (X ξ i))) (u (X ξ i) - S.level) := by
    rw [ae_all_iff]
    intro i
    exact ae_of_ae_map (hX i).aemeasurable (by rw [hXlaw i]; exact hsource)
  have hYs : ∀ᵐ ξ ∂sample, ∀ j : Fin n, ∀ k : Fin D.haar.continuous.count,
      a (Y ξ j) ∈ (D.haar.continuous.coefficient k).roots →
      let S := (P (D.haar.continuous.coefficient k).seedIndex).seed
      Y ξ j = S.curve (populationSeedRootLabelValue S a (a (Y ξ j))) (u (Y ξ j) - S.level) := by
    rw [ae_all_iff]
    intro j
    exact ae_of_ae_map (hY j).aemeasurable (by rw [hYlaw j]; exact htarget)
  apply expected_finite_finsler_pressure hF hcomplete hu ha hinj T.core
    (fun k ↦ T.cover k.1) hn X Y hX hY hA hB
    (fun i ↦ ae_of_ae_map (hX i).aemeasurable (by rw [hXlaw i]; exact hη₀A))
    (fun j ↦ ae_of_ae_map (hY j).aemeasurable (by rw [hYlaw j]; exact hη₁B))
    (fun ξ k ↦ T.edgeEvent (X ξ) (Y ξ) k) (T.measurable_edgeEvent hu ha X Y hX hY)
    (Filter.Eventually.of_forall (fun ξ ↦ T.edgeEvent_disjoint (X ξ) (Y ξ)))
    (fun _ k _ _ ↦ T.reference k) (fun _ _ _ ↦ measurable_const) _ g h
    t G probeError scale hε0 hε1 hscale hprobe hg hh hgb hhb hgh
  filter_upwards [hXs, hYs] with ξ hXsξ hYsξ
  intro k i j hij
  have hx := (T.partition k.1).cell_subset k.2 hij.1
  have hy := (T.partition k.1).cell_subset k.2 hij.2.1
  exact ⟨(T.partition k.1).center_mem k.2, hx, hy, hij.2.2,
    hXsξ i k.1 hx.1, hYsξ j k.1 hy.1⟩

end PopulationLocalPressureCore.TaylorTiles
end OTSelector.Reconstruction
