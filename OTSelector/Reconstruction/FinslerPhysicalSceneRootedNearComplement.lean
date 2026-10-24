import OTSelector.Reconstruction.FinslerPhysicalSceneRootedClockComplement

/-!
# Complete retained near complements

Every pair in the retained original physical cores outside all masked near
events has a common positive true distance-slack gap. The original global
energy controls its Haar-rooted source-window mass.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)} [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ loss : ℝ≥0∞}
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} [∀ j, SigmaFinite (κ j)]

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Retained physical pairs outside every actual masked near event. -/
def retainedNearComplementEvent (A B : Set M) (radius : ℝ) : Set (M × M) :=
  (((⋃ i, D.physicalCoreDomain i) ×ˢ (⋃ i, D.physicalCoreDomain i)) ∩ (A ×ˢ B)) \
    ⋃ i, D.nearDisplacementEvent i radius

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (horder : let _inst : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)

include hF hcomplete hu ha hinj

/-- The entire actual retained near complement is measurable. -/
theorem measurableSet_retainedNearComplementEvent {A B : Set M}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (radius : ℝ) :
    MeasurableSet (D.retainedNearComplementEvent A B radius) := by
  have hcore := MeasurableSet.iUnion fun i ↦
    D.measurableSet_physicalCoreDomain hF hcomplete hu ha i
  exact ((hcore.prod hcore).inter (hA.prod hB)).diff
    (MeasurableSet.iUnion fun i ↦
      D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj i radius)

include horder

/-- A common positive original slack gap controls all retained mass outside
masked near displacement once the actual screens fit the physical support gap. -/
theorem exists_retainedNearComplement_gap
    {A B : Set M} {gap radius : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hradius : 0 < radius)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ p ∈ D.retainedNearComplementEvent A B radius,
      c ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1 := by
  classical
  choose c hc hb using fun i ↦
    D.exists_sameCore_outsideNear_gap hF hcomplete hu ha hinj horder hgap hdist hradius i
      (hwindow i)
  obtain ⟨q, hq, hle⟩ := (isCompact_univ : IsCompact
    (univ : Set (Fin D.haar.continuous.count))).exists_forall_le'
      (f := c) continuous_of_discreteTopology.continuousOn (fun i _ ↦ hc i)
  obtain ⟨g, hg, hcross⟩ := D.exists_crossPieceDisplacement_gap hF hcomplete hu ha hinj horder
  refine ⟨min q g, lt_min hq hg, ?_⟩
  rintro p ⟨⟨⟨hx, hy⟩, hAB⟩, hn⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  by_cases hij : i = j
  · subst j
    exact ((min_le_left q g).trans (hle i (mem_univ i))).trans
      (hb i p ⟨⟨⟨hi, hj⟩, hAB⟩, fun h ↦ hn (mem_iUnion.mpr ⟨i, h⟩)⟩)
  · exact (min_le_right q g).trans (hcross p ⟨i, j, hij, hi, hj⟩)

/-- The same global physical energy controls the full retained near complement
in each actual Haar source window, uniformly over additional source restrictions. -/
theorem exists_retainedNearComplement_rooted_expected_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {gap radius : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hradius : 0 < radius)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ (ι Ω : Type*) [Fintype ι] [MeasurableSpace Ω]
      (Penv : Measure Ω) (Γ : Ω → Measure (M × M)) [∀ w, IsFiniteMeasure (Γ w)]
      (coord : M → (ι → ℝ)), Measurable coord →
      ∀ (H : Set M) (N scale : ℝ), 0 < N → 0 < scale →
      ∀ (rootDomain U : Set (ι → ℝ)), MeasurableSet U → volume U ≠ ⊤ →
      ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ w ∂Penv) ≤ C →
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((Γ w).restrict (D.retainedNearComplementEvent A B radius ∩ (H ×ˢ univ)))
        coord u N z {e | e.1.1 ∈ U}
          ∂OTSelector.Probability.cavityRootMeasure volume rootDomain N ∂Penv) ≤
        volume U * C / ENNReal.ofReal (scale * c) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨c, hc, hb⟩ := D.exists_retainedNearComplement_gap hF hcomplete hu ha hinj horder
    hgap hdist hradius hwindow
  refine ⟨c, hc, ?_⟩
  intro ι Ω _ _ Penv Γ _ coord hcoord H N scale hN hs rootDomain U hU hUf C henergy
  exact lintegral_event_restricted_rooted_sourceWindow_expected_le_of_gap Penv Γ coord hcoord
    u hu.continuous.measurable N hN rootDomain U hU hUf
    (D.measurableSet_retainedNearComplementEvent hF hcomplete hu ha hinj hA hB radius) H
    (fun p ↦ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) hc hs hb C henergy

end PopulationLocalPressureCore
end OTSelector.Reconstruction
