import OTSelector.Reconstruction.FinslerPhysicalSceneDisplacement
import OTSelector.Geometry.FinslerDistanceLocalizationPhysical
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTightness

/-!
# Retained far displacement and actual physical plan mass

Adapters from the existing compact original distance-slack gaps to
the same fixed-basis displacement and exact reconstruction event as the current
physical scene displacement module. Cross-piece and clock-complement edges are
not silently assigned to a same-piece event.
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

/-- The complete actual carrier of the near event, before the radius test. -/
def displacementCarrierEvent (i : Fin D.haar.continuous.count) : Set (M × M) :=
  let C := D.haar.continuous.coefficient i
  let physical := populationSeedPhysicalMap (P C.seedIndex).seed
  {p | a p.1 ∈ C.roots ∧ a p.2 ∈ C.roots ∧ (u p.1, u p.2) ∈ C.window.region ∧
    physical (D.haar.sceneCoordinate i p.1) = p.1 ∧
    physical (D.haar.sceneCoordinate i p.2) = p.2}

/-- The radius complement on exactly the same actual carrier as near displacement. -/
def farDisplacementEvent (i : Fin D.haar.continuous.count) (radius : ℝ) : Set (M × M) :=
  D.displacementCarrierEvent i ∩ {p | radius ≤ ‖D.basisDisplacement i p‖}

/-- The two radius cases partition the same retained actual event exactly. -/
theorem farDisplacementEvent_eq_carrier_diff_near
    (i : Fin D.haar.continuous.count) (radius : ℝ) :
    D.farDisplacementEvent i radius =
      D.displacementCarrierEvent i \ D.nearDisplacementEvent i radius := by
  ext p
  simp only [farDisplacementEvent, displacementCarrierEvent, nearDisplacementEvent,
    mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, ← not_lt]
  tauto

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instSceneMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Every original carrier, reconstruction, and far-radius condition is measurable. -/
theorem measurableSet_farDisplacementEvent
    (i : Fin D.haar.continuous.count) (radius : ℝ) :
    MeasurableSet (D.farDisplacementEvent i radius) := by
  let _instSceneMetric : MetricSpace M := F.metricSpace
  let _instSceneProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  have hroot := C.roots_compact.measurableSet
  have hclock := hu.continuous.measurable
  have hphysical := measurable_populationSeedPhysicalMap (P C.seedIndex).seed
  have hcoord := D.haar.measurable_sceneCoordinate hF hcomplete hu ha hinj i
  have hcarrier : MeasurableSet (D.displacementCarrierEvent i) := by
    exact (hroot.preimage (ha.comp measurable_fst)).inter
      ((hroot.preimage (ha.comp measurable_snd)).inter
        ((C.window.isCompact_region.measurableSet.preimage
          ((hclock.comp measurable_fst).prodMk (hclock.comp measurable_snd))).inter
          ((measurableSet_eq_fun ((hphysical.comp hcoord).comp measurable_fst)
            measurable_fst).inter
            (measurableSet_eq_fun ((hphysical.comp hcoord).comp measurable_snd)
              measurable_snd))))
  exact hcarrier.inter (measurableSet_le measurable_const
    (D.measurable_basisDisplacement hF hcomplete hu ha hinj i).norm)

/-- Compact original active seed domains give a positive far gap in the exact
fixed basis used by current near displacement. No global quadratic bound enters. -/
theorem exists_farDisplacement_gap_on_piece
    (i : Fin D.haar.continuous.count) {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0, ∀ p ∈ D.farDisplacementEvent i radius,
      gap ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1 := by
  let _instSceneMetric : MetricSpace M := F.metricSpace
  let _instSceneProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePolish : PolishSpace M := inferInstance
  let _instSceneRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let bW := Module.finBasis ℝ S.covector.ker
  let R := populationSeedRootLabelValue S a
  let B : ℝ := ‖bW.equivFunL.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  obtain ⟨gap, hgap, hbound⟩ := D.exists_samePiece_distance_slack_gap
    hF hcomplete hu ha hinj i (div_pos hradius hB)
  refine ⟨gap, hgap, ?_⟩
  intro p hp
  obtain ⟨⟨hx, hy, ht, hxread, hyread⟩, hfar⟩ := hp
  have htimes := C.window.region_subset ht
  have hxdom : (a p.1, u p.1) ∈ D.corePointDomain i := ⟨hx, htimes.1⟩
  have hydom : (a p.2, u p.2) ∈ D.corePointDomain i := ⟨hy, htimes.2.1⟩
  have hnorm : ‖D.basisDisplacement i p‖ ≤ ‖bW.equivFunL.toContinuousLinearMap‖ *
      ‖R (a p.2) - R (a p.1)‖ := bW.equivFunL.toContinuousLinearMap.le_opNorm _
  have hsep : radius / B ≤ ‖R (a p.2) - R (a p.1)‖ := by
    apply (div_le_iff₀ hB).mpr
    have hb : ‖bW.equivFunL.toContinuousLinearMap‖ ≤ B := by dsimp only [B]; linarith
    exact hfar.trans (hnorm.trans (by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right hb (norm_nonneg (R (a p.2) - R (a p.1)))))
  have hxwindow := C.root_label_mem_window hF hcomplete hu ha hinj hx
  have hywindow := C.root_label_mem_window hF hcomplete hu ha hinj hy
  have hxpoint : D.corePoint i (a p.1, u p.1) = p.1 :=
    (populationSeedPhysicalMap_at_label S ⟨R (a p.1), hxwindow.1⟩ (u p.1)).symm.trans hxread
  have hypoint : D.corePoint i (a p.2, u p.2) = p.2 :=
    (populationSeedPhysicalMap_at_label S ⟨R (a p.2), hywindow.1⟩ (u p.2)).symm.trans hyread
  simpa only [hxpoint, hypoint] using
    hbound (a p.1, u p.1) hxdom (a p.2, u p.2) hydom hsep

/-- A single positive far gap works for every member of the original finite family. -/
theorem exists_uniform_farDisplacement_gap {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0, ∀ i : Fin D.haar.continuous.count,
      ∀ p ∈ D.farDisplacementEvent i radius,
        gap ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1 := by
  classical
  choose gap hgap hbound using fun i ↦
    D.exists_farDisplacement_gap_on_piece hF hcomplete hu ha hinj i hradius
  obtain ⟨c, hc, hle⟩ := (isCompact_univ : IsCompact
    (univ : Set (Fin D.haar.continuous.count))).exists_forall_le'
      (f := gap) continuous_of_discreteTopology.continuousOn (fun i _ ↦ hgap i)
  exact ⟨c, hc, fun i p hp ↦ (hle i (mem_univ _)).trans (hbound i p hp)⟩

/-- Cross-piece edges retain the actual regular physical core and the full
individual compact clock interval on each side. -/
def crossPieceDisplacementEvent : Set (M × M) :=
  {p | ∃ i j : Fin D.haar.continuous.count,
    i ≠ j ∧ p.1 ∈ D.physicalCoreDomain i ∧ p.2 ∈ D.physicalCoreDomain j}

/-- The retained cross-piece mask is measurable in the unchanged physical endpoints. -/
theorem measurableSet_crossPieceDisplacementEvent :
    MeasurableSet D.crossPieceDisplacementEvent := by
  classical
  unfold crossPieceDisplacementEvent
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hij : i ≠ j
  · convert (D.measurableSet_physicalCoreDomain hF hcomplete hu ha i).prod
        (D.measurableSet_physicalCoreDomain hF hcomplete hu ha j) using 1
    ext p
    exact ⟨fun hp ↦ hp.2, fun hp ↦ ⟨hij, hp⟩⟩
  · simp only [hij, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

/-- Original geometric root separation gives a positive gap on the exact
cross-piece physical carrier, regardless of the rest of a global plan. -/
theorem exists_crossPieceDisplacement_gap
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    ∃ gap > 0, ∀ p ∈ D.crossPieceDisplacementEvent,
      gap ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1 := by
  obtain ⟨gap, hgap, hbound⟩ :=
    D.exists_uniform_crossPiece_distance_slack_gap hF hcomplete hu ha hinj horder
  refine ⟨gap, hgap, ?_⟩
  rintro p ⟨i, j, hij, hx, hy⟩
  have hxp := D.corePoint_eq_of_mem_physicalCoreDomain hF hcomplete hu ha hinj horder i hx
  have hyp := D.corePoint_eq_of_mem_physicalCoreDomain hF hcomplete hu ha hinj horder j hy
  simpa only [hxp, hyp] using hbound i j hij (a p.1, u p.1) hx.2 (a p.2, u p.2) hy.2

/-- All same-piece far events and the exact retained cross-piece event. The
same-piece scalar-pair window test remains visible in this union. -/
def retainedFarDisplacementEvent (radius : ℝ) : Set (M × M) :=
  (⋃ i : Fin D.haar.continuous.count, D.farDisplacementEvent i radius) ∪
    D.crossPieceDisplacementEvent

/-- The combined retained far mask is measurable. -/
theorem measurableSet_retainedFarDisplacementEvent (radius : ℝ) :
    MeasurableSet (D.retainedFarDisplacementEvent radius) :=
  (MeasurableSet.iUnion fun i ↦
    D.measurableSet_farDisplacementEvent hF hcomplete hu ha hinj i radius).union
    (D.measurableSet_crossPieceDisplacementEvent hF hcomplete hu ha hinj)

/-- A common strictly positive original slack gap controls the full explicit
retained far mask, including cross-piece physical edges. -/
theorem exists_retainedFarDisplacement_gap
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0, ∀ p ∈ D.retainedFarDisplacementEvent radius,
      gap ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1 := by
  obtain ⟨c, hc, hsame⟩ := D.exists_uniform_farDisplacement_gap hF hcomplete hu ha hinj hradius
  obtain ⟨d, hd, hcross⟩ := D.exists_crossPieceDisplacement_gap hF hcomplete hu ha hinj horder
  refine ⟨min c d, lt_min hc hd, ?_⟩
  intro p hp
  rcases hp with hs | hc
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact (min_le_left c d).trans (hsame i p hi)
  · exact (min_le_right c d).trans (hcross p hc)

end PopulationLocalPressureCore

/-- Every measure pays at least the fixed positive event gap; no feasibility,
optimality, support, or probability premise is needed. -/
theorem measure_event_le_scaled_energy_of_gap
    {X : Type*} [MeasurableSpace X] (Γ : Measure X) {Q : Set X} (hQ : MeasurableSet Q)
    (f : X → ℝ) {gap scale : ℝ} (hgap : 0 < gap) (hscale : 0 < scale)
    (hbound : ∀ p ∈ Q, gap ≤ f p) :
    Γ Q ≤ (∫⁻ p, ENNReal.ofReal (scale * f p) ∂Γ) / ENNReal.ofReal (scale * gap) := by
  have hpoint : Q.indicator (fun _ ↦ ENNReal.ofReal (scale * gap)) ≤
      fun p ↦ ENNReal.ofReal (scale * f p) := by
    intro p
    by_cases hp : p ∈ Q
    · rw [indicator_of_mem hp]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hbound p hp) hscale.le)
    · rw [indicator_of_notMem hp]
      exact bot_le
  have hmass : ENNReal.ofReal (scale * gap) * Γ Q ≤
      ∫⁻ p, ENNReal.ofReal (scale * f p) ∂Γ := by
    rw [← lintegral_indicator_const hQ]
    exact lintegral_mono hpoint
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hscale hgap)))
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  rwa [mul_comm]

/-- Haar source-window averaging preserves the actual gap bound for the
explicitly event-restricted original plan and any additional source restriction. -/
theorem lintegral_event_restricted_rooted_sourceWindow_le_of_gap
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (Γ : Measure (X × X)) [IsFiniteMeasure Γ]
    (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (clock : X → ℝ) (hclock : Measurable clock)
    (N : ℝ) (hN : 0 < N) (rootDomain U : Set (ι → ℝ)) (hU : MeasurableSet U)
    {Q : Set (X × X)} (hQ : MeasurableSet Q) (H : Set X)
    (f : X × X → ℝ) {gap scale : ℝ} (hgap : 0 < gap) (hscale : 0 < scale)
    (hbound : ∀ p ∈ Q, gap ≤ f p) :
    (∫⁻ z, physicalSceneRootedPlan (Γ.restrict (Q ∩ (H ×ˢ univ))) coord clock N z
      {e | e.1.1 ∈ U} ∂OTSelector.Probability.cavityRootMeasure volume rootDomain N) ≤
      volume U * (∫⁻ p, ENNReal.ofReal (scale * f p) ∂Γ) /
        ENNReal.ofReal (scale * gap) := by
  calc
    _ ≤ volume U * (Γ.restrict (Q ∩ (H ×ˢ univ))) univ :=
      lintegral_physicalSceneRootedPlan_sourceWindow_le _ coord hcoord clock hclock
        N hN rootDomain U hU
    _ ≤ volume U * Γ Q := by
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul_right (measure_mono inter_subset_left) _
    _ ≤ volume U * ((∫⁻ p, ENNReal.ofReal (scale * f p) ∂Γ) /
        ENNReal.ofReal (scale * gap)) :=
      mul_le_mul_right (measure_event_le_scaled_energy_of_gap Γ hQ f hgap hscale hbound) _
    _ = _ := by simp only [div_eq_mul_inv, mul_assoc]

/-- A bound on the original expected scaled slack controls the Haar-window
mass of the same explicit event restriction, with every original environment retained. -/
theorem lintegral_event_restricted_rooted_sourceWindow_expected_le_of_gap
    {ι X Ω : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Ω]
    (Penv : Measure Ω) (Γ : Ω → Measure (X × X)) [∀ env, IsFiniteMeasure (Γ env)]
    (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (clock : X → ℝ) (hclock : Measurable clock)
    (N : ℝ) (hN : 0 < N) (rootDomain U : Set (ι → ℝ))
    (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    {Q : Set (X × X)} (hQ : MeasurableSet Q) (H : Set X)
    (f : X × X → ℝ) {gap scale : ℝ} (hgap : 0 < gap) (hscale : 0 < scale)
    (hbound : ∀ p ∈ Q, gap ≤ f p) (C : ℝ≥0∞)
    (henergy : (∫⁻ env, ∫⁻ p, ENNReal.ofReal (scale * f p) ∂Γ env ∂Penv) ≤ C) :
    (∫⁻ env, ∫⁻ z, physicalSceneRootedPlan
      ((Γ env).restrict (Q ∩ (H ×ˢ univ))) coord clock N z {e | e.1.1 ∈ U}
        ∂OTSelector.Probability.cavityRootMeasure volume rootDomain N ∂Penv) ≤
      volume U * C / ENNReal.ofReal (scale * gap) := by
  let d := ENNReal.ofReal (scale * gap)
  have hd : d ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hscale hgap)
  have hfactor : volume U / d ≠ ⊤ := ENNReal.div_ne_top hUf hd
  calc
    _ ≤ ∫⁻ env, volume U * (∫⁻ p, ENNReal.ofReal (scale * f p) ∂Γ env) / d ∂Penv :=
      lintegral_mono fun env ↦
        lintegral_event_restricted_rooted_sourceWindow_le_of_gap
          (Γ env) coord hcoord clock hclock N hN rootDomain U hU hQ H f hgap hscale hbound
    _ = (volume U / d) *
        (∫⁻ env, ∫⁻ p, ENNReal.ofReal (scale * f p) ∂Γ env ∂Penv) := by
      simp_rw [div_eq_mul_inv, mul_right_comm (volume U)]
      exact lintegral_const_mul' _ _ hfactor
    _ ≤ (volume U / d) * C := by gcongr
    _ = _ := by simp only [d, div_eq_mul_inv]; ac_rfl

/-- A uniformly bounded energy divided by a fixed positive gap and an original
scale tending to infinity forces the controlled mass to vanish. -/
theorem tendsto_zero_of_le_scaled_gap_bound
    {I : Type*} {l : Filter I} (mass : I → ℝ≥0∞) (scale : I → ℝ)
    {gap : ℝ} (hgap : 0 < gap) (hscale : Tendsto scale l atTop)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hmass : ∀ᶠ k in l, mass k ≤ C / ENNReal.ofReal (scale k * gap)) :
    Tendsto mass l (𝓝 0) := by
  have hden : Tendsto (fun k ↦ ENNReal.ofReal (scale k * gap)) l (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_atTop.comp (hscale.atTop_mul_const hgap)
  have hratio : Tendsto (fun k ↦ C / ENNReal.ofReal (scale k * gap)) l (𝓝 0) := by
    simpa only [ENNReal.div_top] using ENNReal.Tendsto.const_div hden (Or.inr hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hratio
    (Eventually.of_forall fun _ ↦ bot_le) hmass

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instSceneMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (horder : let _inst : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)

include hF hcomplete hu ha hinj horder

/-- The original global plan pays for every same-core far or retained cross-core
edge. The plan is arbitrary and may send every other edge outside all cores. -/
theorem exists_retainedFarDisplacement_global_mass_bound
    {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0, ∀ (Γ : Measure (M × M)) (scale : ℝ), 0 < scale →
      Γ (D.retainedFarDisplacementEvent radius) ≤
        (∫⁻ p, ENNReal.ofReal (scale *
          ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ) /
            ENNReal.ofReal (scale * gap) := by
  obtain ⟨gap, hgap, hbound⟩ :=
    D.exists_retainedFarDisplacement_gap hF hcomplete hu ha hinj horder hradius
  refine ⟨gap, hgap, fun Γ scale hscale ↦ ?_⟩
  exact measure_event_le_scaled_energy_of_gap Γ
    (D.measurableSet_retainedFarDisplacementEvent hF hcomplete hu ha hinj radius)
    (fun p ↦ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) hgap hscale hbound

/-- Original expected scaled slack bounds Haar-rooted source-window mass of the
explicit same-core far plus cross-core plan, retaining any actual source restriction. -/
theorem exists_retainedFarDisplacement_rooted_expected_bound
    {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0, ∀ (ι Ω : Type*) [Fintype ι] [MeasurableSpace Ω]
      (Penv : Measure Ω) (Γ : Ω → Measure (M × M)) [∀ env, IsFiniteMeasure (Γ env)]
      (coord : M → (ι → ℝ)), Measurable coord →
      ∀ (H : Set M) (N scale : ℝ), 0 < N → 0 < scale →
      ∀ (rootDomain U : Set (ι → ℝ)), MeasurableSet U → volume U ≠ ⊤ →
      ∀ C : ℝ≥0∞,
      (∫⁻ env, ∫⁻ p, ENNReal.ofReal (scale *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ env ∂Penv) ≤ C →
      (∫⁻ env, ∫⁻ z, physicalSceneRootedPlan
        ((Γ env).restrict (D.retainedFarDisplacementEvent radius ∩ (H ×ˢ univ)))
        coord u N z {e | e.1.1 ∈ U}
          ∂OTSelector.Probability.cavityRootMeasure volume rootDomain N ∂Penv) ≤
        volume U * C / ENNReal.ofReal (scale * gap) := by
  let _instSceneMetric : MetricSpace M := F.metricSpace
  obtain ⟨gap, hgap, hbound⟩ :=
    D.exists_retainedFarDisplacement_gap hF hcomplete hu ha hinj horder hradius
  refine ⟨gap, hgap, ?_⟩
  intro ι Ω _ _ Penv Γ _ coord hcoord H N scale hN hscale rootDomain U hU hUf C henergy
  exact lintegral_event_restricted_rooted_sourceWindow_expected_le_of_gap
    Penv Γ coord hcoord u hu.continuous.measurable N hN rootDomain U hU hUf
    (D.measurableSet_retainedFarDisplacementEvent hF hcomplete hu ha hinj radius) H
    (fun p ↦ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) hgap hscale hbound C henergy

end PopulationLocalPressureCore

end OTSelector.Reconstruction
