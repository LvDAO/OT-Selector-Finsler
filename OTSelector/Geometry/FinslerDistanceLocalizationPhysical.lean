import OTSelector.Geometry.FinslerDistanceLocalizationEmpirical

/-!
# Distance localization for arbitrary original physical samples

Only the selected edges need belong to the actual retained cores. The original
label-clock injectivity recovers their physical endpoints, and the produced gap
holds on a measurable set of far physical pairs. Samples outside that set keep
their original distance cost throughout the empirical comparison.
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

/-- Actual regular physical points whose original root and clock lie in one
retained compact parameter domain. -/
def physicalCoreDomain (i : Fin D.haar.continuous.count) : Set M :=
  {x | x ∈ F.potentialRegularDomain u ∧ (a x, u x) ∈ D.corePointDomain i}

/-- Near physical pairs use the same original piece and nearby actual seed labels. -/
def nearPhysicalPairs (radius : ℝ) : Set (M × M) :=
  ⋃ i : Fin D.haar.continuous.count,
    (D.physicalCoreDomain i ×ˢ D.physicalCoreDomain i) ∩
      {p | ‖populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a (a p.2) -
        populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a (a p.1)‖ < radius}

/-- Retained physical pairs outside the actual near-pair relation. -/
def farPhysicalPairs (radius : ℝ) : Set (M × M) :=
  ((⋃ i, D.physicalCoreDomain i) ×ˢ (⋃ i, D.physicalCoreDomain i)) \ D.nearPhysicalPairs radius

/-- The original physical point is exactly the actual seed endpoint at its own
root and potential clock. -/
theorem corePoint_eq_of_mem_physicalCoreDomain (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count) {x : M} (hx : x ∈ D.physicalCoreDomain i) :
    D.corePoint i (a x, u x) = x := by
  obtain ⟨hreg, hroot⟩ := D.corePoint_root_data hF hcomplete hu ha hinj horder i hx.2
  have ht := (D.corePoint_seed_data hF hcomplete hu ha hinj i hx.2).2
  have hclock : u (D.corePoint i (a x, u x)) = u x := by
    have hh := interior_subset ht
    change u (D.corePoint i (a x, u x)) =
      ((P (D.haar.continuous.coefficient i).seedIndex).seed.level : ℝ) +
        (u x - (P (D.haar.continuous.coefficient i).seedIndex).seed.level) at hh
    simpa only [add_sub_cancel] using hh
  have heq : (⟨D.corePoint i (a x, u x), hreg⟩ : F.potentialRegularDomain u) = ⟨x, hx.1⟩ :=
    hinj (Prod.ext hroot hclock)
  exact congrArg Subtype.val heq

/-- The produced far-pair gap applies pointwise to original physical points;
there is no premise that other sampled endpoints lie in the retained cores. -/
theorem exists_physical_far_gap (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0, ∀ p ∈ D.farPhysicalPairs radius,
      gap ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1 := by
  obtain ⟨gap, hgap, hcross, hsame⟩ := D.exists_uniform_far_distance_slack_gap
    hF hcomplete hu ha hinj horder hradius
  refine ⟨gap, hgap, ?_⟩
  intro p hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp.1.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp.1.2
  have hxi := D.corePoint_eq_of_mem_physicalCoreDomain hF hcomplete hu ha hinj horder i hi
  have hyj := D.corePoint_eq_of_mem_physicalCoreDomain hF hcomplete hu ha hinj horder j hj
  by_cases hij : i = j
  · subst j
    have hsep : radius ≤
        ‖populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a (a p.2) -
          populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a (a p.1)‖ := by
      by_contra h
      exact hp.2 (mem_iUnion.mpr ⟨i, ⟨hi, hj⟩, lt_of_not_ge h⟩)
    simpa only [hxi, hyj] using hsame i (a p.1, u p.1) hi.2 (a p.2, u p.2) hj.2 hsep
  · simpa only [hxi, hyj] using hcross i j hij (a p.1, u p.1) hi.2 (a p.2, u p.2) hj.2

/-- Membership of the retained original physical domains is measurable. -/
theorem measurableSet_physicalCoreDomain (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a) (i : Fin D.haar.continuous.count) :
    MeasurableSet (D.physicalCoreDomain i) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  exact (hF.measurableSet_potentialRegularDomain hcomplete u).inter
    ((D.isCompact_corePointDomain i).measurableSet.preimage (ha.prodMk hu.continuous.measurable))

/-- The actual near-pair relation is measurable in the original physical points. -/
theorem measurableSet_nearPhysicalPairs (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) (radius : ℝ) :
    MeasurableSet (D.nearPhysicalPairs radius) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  apply MeasurableSet.iUnion
  intro i
  have hR := measurable_populationSeedRootLabelValue
    (P (D.haar.continuous.coefficient i).seedIndex).seed hF hcomplete hu ha hinj
  exact ((D.measurableSet_physicalCoreDomain hF hcomplete hu ha i).prod
    (D.measurableSet_physicalCoreDomain hF hcomplete hu ha i)).inter
      (measurableSet_lt (((hR.comp (ha.comp measurable_snd)).sub
        (hR.comp (ha.comp measurable_fst))).norm) measurable_const)

/-- The far-pair set used in empirical and expected pressure localization is
measurable and uses only the original physical samples and their actual labels. -/
theorem measurableSet_farPhysicalPairs (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) (radius : ℝ) :
    MeasurableSet (D.farPhysicalPairs radius) := by
  have h := MeasurableSet.iUnion (fun i ↦ D.measurableSet_physicalCoreDomain hF hcomplete hu ha i)
  exact (h.prod h).diff (D.measurableSet_nearPhysicalPairs hF hcomplete hu ha hinj radius)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
