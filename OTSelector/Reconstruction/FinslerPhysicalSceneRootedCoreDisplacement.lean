import OTSelector.Reconstruction.FinslerPhysicalSceneRootedFarDisplacement

/-!
# Far displacement on the complete retained physical cores

The original compact support gap controls every fixed-basis far pair on the full
same-core physical products and every cross-core pair. This includes every
scalar clock pair in the retained physical intervals. Arbitrary original global
plans therefore pay for this whole explicit far relation through their genuine
scaled slack energy, without imposing a scalar-pair-window screen.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry Filter
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
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Fixed-basis far displacement on the full actual same-core physical product,
without imposing any scalar-pair-window screen. -/
def sameCoreFarDisplacementEvent (i : Fin D.haar.continuous.count) (radius : ℝ) : Set (M × M) :=
  (D.physicalCoreDomain i ×ˢ D.physicalCoreDomain i) ∩ {p | radius ≤ ‖D.basisDisplacement i p‖}

/-- The full retained-core near relation uses the same original basis on each piece. -/
def retainedCoreNearDisplacementEvent (radius : ℝ) : Set (M × M) :=
  ⋃ i, (D.physicalCoreDomain i ×ˢ D.physicalCoreDomain i) ∩
    {p | ‖D.basisDisplacement i p‖ < radius}

/-- All same-core basis-far and cross-core physical edges, with full scalar intervals. -/
def retainedCoreFarDisplacementEvent (radius : ℝ) : Set (M × M) :=
  (⋃ i, D.sameCoreFarDisplacementEvent i radius) ∪ D.crossPieceDisplacementEvent

/-- Every retained physical pair outside the actual same-core near relation
belongs to the explicit full retained far relation. -/
theorem retainedCore_not_near_subset_far (radius : ℝ) :
    ((⋃ i, D.physicalCoreDomain i) ×ˢ (⋃ i, D.physicalCoreDomain i)) \
      D.retainedCoreNearDisplacementEvent radius ⊆ D.retainedCoreFarDisplacementEvent radius := by
  intro p hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp.1.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp.1.2
  by_cases hij : i = j
  · subst j
    left
    apply mem_iUnion.mpr
    refine ⟨i, ⟨hi, hj⟩, ?_⟩
    change radius ≤ ‖D.basisDisplacement i p‖
    by_contra hn
    apply hp.2
    apply mem_iUnion.mpr
    refine ⟨i, ⟨hi, hj⟩, ?_⟩
    exact (lt_of_not_ge hn : ‖D.basisDisplacement i p‖ < radius)
  · exact Or.inr ⟨i, j, hij, hi, hj⟩

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (horder : let _inst : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)

include hF hcomplete hu ha hinj

/-- Full same-core basis-far events retain measurable original physical endpoints. -/
theorem measurableSet_sameCoreFarDisplacementEvent
    (i : Fin D.haar.continuous.count) (radius : ℝ) :
    MeasurableSet (D.sameCoreFarDisplacementEvent i radius) :=
  ((D.measurableSet_physicalCoreDomain hF hcomplete hu ha i).prod
    (D.measurableSet_physicalCoreDomain hF hcomplete hu ha i)).inter
      (measurableSet_le measurable_const
        (D.measurable_basisDisplacement hF hcomplete hu ha hinj i).norm)

/-- The full retained far relation is measurable. -/
theorem measurableSet_retainedCoreFarDisplacementEvent (radius : ℝ) :
    MeasurableSet (D.retainedCoreFarDisplacementEvent radius) :=
  (MeasurableSet.iUnion fun i ↦
    D.measurableSet_sameCoreFarDisplacementEvent hF hcomplete hu ha hinj i radius).union
      (D.measurableSet_crossPieceDisplacementEvent hF hcomplete hu ha hinj)

include horder

/-- Full compact physical cores give a positive original slack gap on every
fixed-basis far edge, without the scalar-pair-window mask. -/
theorem exists_sameCoreFarDisplacement_gap
    (i : Fin D.haar.continuous.count) {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0, ∀ p ∈ D.sameCoreFarDisplacementEvent i radius,
      gap ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1 := by
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let bW := Module.finBasis ℝ S.covector.ker
  let R := populationSeedRootLabelValue S a
  let B : ℝ := ‖bW.equivFunL.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  obtain ⟨gap, hg, hb⟩ := D.exists_samePiece_distance_slack_gap
    hF hcomplete hu ha hinj i (div_pos hradius hB)
  refine ⟨gap, hg, ?_⟩
  intro p hp
  have hnorm : ‖D.basisDisplacement i p‖ ≤ ‖bW.equivFunL.toContinuousLinearMap‖ *
      ‖R (a p.2) - R (a p.1)‖ := bW.equivFunL.toContinuousLinearMap.le_opNorm _
  have hsep : radius / B ≤ ‖R (a p.2) - R (a p.1)‖ := by
    apply (div_le_iff₀ hB).mpr
    have hbB : ‖bW.equivFunL.toContinuousLinearMap‖ ≤ B := by dsimp only [B]; linarith
    exact hp.2.trans (hnorm.trans (by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right hbB (norm_nonneg (R (a p.2) - R (a p.1)))))
  have hx := D.corePoint_eq_of_mem_physicalCoreDomain hF hcomplete hu ha hinj horder i hp.1.1
  have hy := D.corePoint_eq_of_mem_physicalCoreDomain hF hcomplete hu ha hinj horder i hp.1.2
  simpa only [hx, hy] using hb (a p.1, u p.1) hp.1.1.2 (a p.2, u p.2) hp.1.2.2 hsep

/-- One positive original slack gap works for all retained full physical cores,
including cross-core edges and all original scalar clock pairs. -/
theorem exists_retainedCoreFarDisplacement_gap {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0, ∀ p ∈ D.retainedCoreFarDisplacementEvent radius,
      gap ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1 := by
  classical
  choose c hc hb using fun i ↦
    D.exists_sameCoreFarDisplacement_gap hF hcomplete hu ha hinj horder i hradius
  obtain ⟨q, hq, hle⟩ := (isCompact_univ : IsCompact
    (univ : Set (Fin D.haar.continuous.count))).exists_forall_le'
      (f := c) continuous_of_discreteTopology.continuousOn (fun i _ ↦ hc i)
  obtain ⟨g, hg, hcross⟩ := D.exists_crossPieceDisplacement_gap hF hcomplete hu ha hinj horder
  refine ⟨min q g, lt_min hq hg, ?_⟩
  intro p hp
  rcases hp with hs | hs
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact ((min_le_left q g).trans (hle i (mem_univ i))).trans (hb i p hi)
  · exact (min_le_right q g).trans (hcross p hs)

/-- The unrestricted original global energy pays for all retained full-core far
mass in each Haar source window; the physical plan may have arbitrary other edges. -/
theorem exists_retainedCoreFarDisplacement_rooted_expected_bound
    {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0, ∀ (ι Ω : Type*) [Fintype ι] [MeasurableSpace Ω]
      (Penv : Measure Ω) (Γ : Ω → Measure (M × M)) [∀ w, IsFiniteMeasure (Γ w)]
      (coord : M → (ι → ℝ)), Measurable coord →
      ∀ (H : Set M) (N scale : ℝ), 0 < N → 0 < scale →
      ∀ (rootDomain U : Set (ι → ℝ)), MeasurableSet U → volume U ≠ ⊤ →
      ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ w ∂Penv) ≤ C →
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((Γ w).restrict (D.retainedCoreFarDisplacementEvent radius ∩ (H ×ˢ univ)))
        coord u N z {e | e.1.1 ∈ U}
          ∂OTSelector.Probability.cavityRootMeasure volume rootDomain N ∂Penv) ≤
        volume U * C / ENNReal.ofReal (scale * gap) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨gap, hg, hb⟩ := D.exists_retainedCoreFarDisplacement_gap hF hcomplete hu ha hinj horder hradius
  refine ⟨gap, hg, ?_⟩
  intro ι Ω _ _ Penv Γ _ coord hcoord H N scale hN hs rootDomain U hU hUf C henergy
  exact lintegral_event_restricted_rooted_sourceWindow_expected_le_of_gap Penv Γ coord hcoord
    u hu.continuous.measurable N hN rootDomain U hU hUf
    (D.measurableSet_retainedCoreFarDisplacementEvent hF hcomplete hu ha hinj radius) H
    (fun p ↦ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) hg hs hb C henergy

end PopulationLocalPressureCore
end OTSelector.Reconstruction
