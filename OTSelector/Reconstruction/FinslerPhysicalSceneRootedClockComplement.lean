import OTSelector.Reconstruction.FinslerPhysicalSceneRootedFarDisplacement
import OTSelector.Transport.Calibration.CompactClockGap

/-!
# Actual same-core clock complements and their global-energy control

Physical core membership gives exact scene-coordinate reconstruction. On the
same full physical core, the displacement carrier is characterized by its actual
rational clock screen. The near complement is covered by retained far edges and
the explicit bad-clock event. When that rational screen fits the original support
gap, the original global energy controls the whole stated near complement.
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

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (horder : let _inst : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)

include hF hcomplete hu ha hinj horder

/-- The actual physical reconstruction is exact at every point of an original
retained regular physical core, rather than an assumed plan-level identity. -/
theorem physicalSceneCoordinate_physicalCore_reconstruction
    (i : Fin D.haar.continuous.count) {x : M} (hx : x ∈ D.physicalCoreDomain i) :
    populationSeedPhysicalMap (P (D.haar.continuous.coefficient i).seedIndex).seed
      (D.haar.sceneCoordinate i x) = x := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  have hlabel := C.root_label_mem_window hF hcomplete hu ha hinj hx.2.1
  have he := populationSeedPhysicalMap_at_label S
    ⟨populationSeedRootLabelValue S a (a x), hlabel.1⟩ (u x)
  exact he.trans (D.corePoint_eq_of_mem_physicalCoreDomain hF hcomplete hu ha hinj horder i hx)

/-- On the full same-core physical product the only missing scalar-pair-window
condition is the explicit lower clock-gap screen. -/
theorem mem_displacementCarrierEvent_iff_clock_gap
    (i : Fin D.haar.continuous.count) {p : M × M}
    (hx : p.1 ∈ D.physicalCoreDomain i) (hy : p.2 ∈ D.physicalCoreDomain i) :
    p ∈ D.displacementCarrierEvent i ↔
      (((D.haar.continuous.coefficient i).window.val.2.2 : ℚ) : ℝ) ≤ u p.2 - u p.1 := by
  constructor
  · intro hp
    exact hp.2.2.1.2
  · intro hclock
    exact ⟨hx.2.1, hy.2.1, ⟨⟨hx.2.2, hy.2.2⟩, hclock⟩,
      D.physicalSceneCoordinate_physicalCore_reconstruction hF hcomplete hu ha hinj horder i hx,
      D.physicalSceneCoordinate_physicalCore_reconstruction hF hcomplete hu ha hinj horder i hy⟩

/-- Same-core mass outside near displacement is exactly covered by the retained
far-radius event and the explicit bad scalar clock condition. -/
theorem sameCore_not_near_subset_far_union_clockBad
    (i : Fin D.haar.continuous.count) (radius : ℝ) :
    ((D.physicalCoreDomain i ×ˢ D.physicalCoreDomain i) \ D.nearDisplacementEvent i radius) ⊆
      D.farDisplacementEvent i radius ∪
        {p | u p.2 - u p.1 < (((D.haar.continuous.coefficient i).window.val.2.2 : ℚ) : ℝ)} := by
  intro p hp
  by_cases hc : (((D.haar.continuous.coefficient i).window.val.2.2 : ℚ) : ℝ) ≤ u p.2 - u p.1
  · left
    rw [D.farDisplacementEvent_eq_carrier_diff_near]
    exact ⟨(D.mem_displacementCarrierEvent_iff_clock_gap hF hcomplete hu ha hinj horder
      i hp.1.1 hp.1.2).mpr hc, hp.2⟩
  · exact Or.inr (lt_of_not_ge hc)

/-- If the actual rational pair screen is at most half the original support gap,
the entire same-core near complement has a positive true slack gap. -/
theorem exists_sameCore_outsideNear_gap
    {A B : Set M} {gap radius : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hradius : 0 < radius) (i : Fin D.haar.continuous.count)
    (hwindow : (((D.haar.continuous.coefficient i).window.val.2.2 : ℚ) : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ p ∈ ((D.physicalCoreDomain i ×ˢ D.physicalCoreDomain i) ∩ (A ×ˢ B)) \ D.nearDisplacementEvent i radius,
      c ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1 := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨c, hc, hfar⟩ := D.exists_farDisplacement_gap_on_piece hF hcomplete hu ha hinj i hradius
  refine ⟨min c (gap / 2), lt_min hc (half_pos hgap), ?_⟩
  intro p hp
  rcases D.sameCore_not_near_subset_far_union_clockBad hF hcomplete hu ha hinj horder
    i radius ⟨hp.1.1, hp.2⟩ with hf | hb
  · exact (min_le_left c (gap / 2)).trans (hfar p hf)
  · apply (min_le_right c (gap / 2)).trans
    exact originalClockBadEvent_slack_gap hdist hp.1.2.1 hp.1.2.2
      (by exact (le_of_lt hb).trans hwindow)

/-- The full same-core near complement is paid by the original global energy
when its actual rational clock screen fits the original support gap. -/
theorem exists_sameCore_outsideNear_rooted_expected_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {gap radius : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hradius : 0 < radius) (i : Fin D.haar.continuous.count)
    (hwindow : (((D.haar.continuous.coefficient i).window.val.2.2 : ℚ) : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ (ι Ω : Type*) [Fintype ι] [MeasurableSpace Ω]
      (Penv : Measure Ω) (Γ : Ω → Measure (M × M)) [∀ w, IsFiniteMeasure (Γ w)]
      (coord : M → (ι → ℝ)), Measurable coord →
      ∀ (H : Set M) (N scale : ℝ), 0 < N → 0 < scale →
      ∀ (rootDomain U : Set (ι → ℝ)), MeasurableSet U → volume U ≠ ⊤ →
      ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ w ∂Penv) ≤ C →
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((Γ w).restrict (((((D.physicalCoreDomain i ×ˢ D.physicalCoreDomain i) ∩
          (A ×ˢ B)) \ D.nearDisplacementEvent i radius)) ∩ (H ×ˢ univ)))
        coord u N z {e | e.1.1 ∈ U}
          ∂OTSelector.Probability.cavityRootMeasure volume rootDomain N ∂Penv) ≤
        volume U * C / ENNReal.ofReal (scale * c) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨c, hc, hb⟩ := D.exists_sameCore_outsideNear_gap hF hcomplete hu ha hinj horder
    hgap hdist hradius i hwindow
  have hQ : MeasurableSet (((D.physicalCoreDomain i ×ˢ D.physicalCoreDomain i) ∩
      (A ×ˢ B)) \ D.nearDisplacementEvent i radius) :=
    (((D.measurableSet_physicalCoreDomain hF hcomplete hu ha i).prod
      (D.measurableSet_physicalCoreDomain hF hcomplete hu ha i)).inter (hA.prod hB)).diff
      (D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj i radius)
  refine ⟨c, hc, ?_⟩
  intro ι Ω _ _ Penv Γ _ coord hcoord H N scale hN hs rootDomain U hU hUf C henergy
  exact lintegral_event_restricted_rooted_sourceWindow_expected_le_of_gap Penv Γ coord hcoord
    u hu.continuous.measurable N hN rootDomain U hU hUf hQ H
    (fun p ↦ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) hc hs hb C henergy

end PopulationLocalPressureCore
end OTSelector.Reconstruction
