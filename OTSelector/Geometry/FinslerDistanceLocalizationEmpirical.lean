import OTSelector.Geometry.FinslerDistanceLocalizationPopulation
import OTSelector.Geometry.DistanceSlackLocalizationFinite

/-!
# Actual finite samples inherit the original geometric distance gap

An edge is near when its endpoints use one retained original root piece and
its two actual seed labels are close. The geometric producer gives one positive
slack gap on every other retained edge, uniformly in sample size and sample lists.
Consequently every nonnegative empirical plan has a quantitative far-mass bound.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Function OTSelector.Geometry
open scoped ENNReal
namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)

/-- A retained pair is near precisely when both endpoints use one original
piece and its actual labels differ by less than the prescribed radius. -/
def nearCorePair (radius : ℝ) (i j : Fin D.haar.continuous.count)
    (x y : (ℚ → M) × ℝ) : Prop :=
  ∃ k : Fin D.haar.continuous.count, i = k ∧ j = k ∧
    ‖populationSeedRootLabelValue (P (D.haar.continuous.coefficient k).seedIndex).seed a y.1 -
      populationSeedRootLabelValue (P (D.haar.continuous.coefficient k).seedIndex).seed a x.1‖ < radius

/-- The finite set of sampled edges outside the actual near-pair relation. -/
def farCoreEdges {n : ℕ} (radius : ℝ) (I J : Fin n → Fin D.haar.continuous.count)
    (X Y : Fin n → (ℚ → M) × ℝ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter (fun p ↦ ¬D.nearCorePair radius (I p.1) (J p.2) (X p.1) (Y p.2))

/-- The original manifold and the retained population core produce one geometric
gap for every distant sampled edge, without a sample-dependent gap assumption. -/
theorem exists_sampled_far_gap (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {radius : ℝ} (hradius : 0 < radius) :
    let _inst : MetricSpace M := F.metricSpace
    ∃ gap > 0, ∀ (n : ℕ) (I J : Fin n → Fin D.haar.continuous.count)
      (X Y : Fin n → (ℚ → M) × ℝ),
      (∀ i, X i ∈ D.corePointDomain (I i)) → (∀ j, Y j ∈ D.corePointDomain (J j)) →
      ∀ p ∈ D.farCoreEdges radius I J X Y,
        gap ≤ distanceSlackEdgeCost (fun i ↦ D.corePoint (I i) (X i))
          (fun j ↦ D.corePoint (J j) (Y j)) u p.1 p.2 := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨gap, hgap, hcross, hsame⟩ := D.exists_uniform_far_distance_slack_gap
    hF hcomplete hu ha hinj horder hradius
  refine ⟨gap, hgap, ?_⟩
  intro n I J X Y hX hY p hp
  have hn : ¬D.nearCorePair radius (I p.1) (J p.2) (X p.1) (Y p.2) :=
    (Finset.mem_filter.mp hp).2
  by_cases hij : I p.1 = J p.2
  · have hx : X p.1 ∈ D.corePointDomain (J p.2) := hij ▸ hX p.1
    have hsep : radius ≤
        ‖populationSeedRootLabelValue (P (D.haar.continuous.coefficient (J p.2)).seedIndex).seed a (Y p.2).1 -
          populationSeedRootLabelValue (P (D.haar.continuous.coefficient (J p.2)).seedIndex).seed a (X p.1).1‖ := by
      by_contra h
      exact hn ⟨J p.2, hij, rfl, lt_of_not_ge h⟩
    simpa only [distanceSlackEdgeCost, hij, F.metricSpace_dist] using
      hsame (J p.2) (X p.1) hx (Y p.2) (hY p.2) hsep
  · simpa only [distanceSlackEdgeCost, F.metricSpace_dist] using
      hcross (I p.1) (J p.2) hij (X p.1) (hX p.1) (Y p.2) (hY p.2)

/-- Every finite nonnegative plan on the retained physical cores has far mass
bounded by its true average distance slack divided by one common geometric gap. -/
theorem exists_sampled_far_mass_bound (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {radius : ℝ} (hradius : 0 < radius) :
    let _inst : MetricSpace M := F.metricSpace
    ∃ gap > 0, ∀ (n : ℕ) (I J : Fin n → Fin D.haar.continuous.count)
      (X Y : Fin n → (ℚ → M) × ℝ),
      (∀ i, X i ∈ D.corePointDomain (I i)) → (∀ j, Y j ∈ D.corePointDomain (J j)) →
      ∀ (P₀ : Matrix (Fin n) (Fin n) ℝ), (∀ i j, 0 ≤ P₀ i j) →
      (∑ p ∈ D.farCoreEdges radius I J X Y, P₀ p.1 p.2) / (n : ℝ) ≤
        (fractionalAssignmentCost (distanceSlackEdgeCost
          (fun i ↦ D.corePoint (I i) (X i)) (fun j ↦ D.corePoint (J j) (Y j)) u) P₀ / n) / gap := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨gap, hgap, hb⟩ := D.exists_sampled_far_gap hF hcomplete hu ha hinj horder hradius
  refine ⟨gap, hgap, ?_⟩
  intro n I J X Y hX hY P₀ hP
  exact fractional_far_mass_le_distance_slack_cost _ _ u hu P₀ hP
    (fun i j ↦ ¬D.nearCorePair radius (I i) (J j) (X i) (Y j)) hgap
    (fun i j hij ↦ hb n I J X Y hX hY (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩))

end PopulationLocalPressureCore
end OTSelector.Reconstruction
