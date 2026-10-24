import OTSelector.Reconstruction.FinslerOriginalRefinedAtlasInteriority
import OTSelector.Reconstruction.FinslerOriginalCubeCoverageConditionalMarks
import OTSelector.MeasureTheory.NormalizedIntervalDensity

/-!
# Refined compact-ball-core atlas and the cube-coverage inputs

This file threads the certified compact-ball cores through the finite upper atlas
chain. The producer theorem `exists_ball_core_C11_data` supplies C1,1 chart data on
a compact chart ball; the presentation of a seed carries `core ⊆ E`, a continuous
section `position` and `labels = openLabels cap position^{-1}(core)`. Hence a
presentation whose core contains a closed chart ball around the section point
retains a genuine metric ball of labels around the zero label.

The file then proves:

* `labels_ball_of_ball_core` / `labels_ball_of_core_interior`: a certified ball
  core gives the label ball, i.e. the exact interiority input of the cube
  coverage (the converse direction is in the atlas-interiority module);
* `certified_ball_core_available`: the chart ball core extracted directly from
  the producer theorem `exists_ball_core_C11_data`;
* `hlabelCover_of_labelBall`: the label ball plus the radius condition on the
  normalized basis gives the coverage input `hlabelCover` of the tile model;
* `mem_populationSeedRootPiece_iff_of_ballCore` / `mem_piece_of_owner`: exact membership in
  the owning window piece, so the retention input `hretain` holds as soon as the
  original root has finite-nonzero population reference intensity and is not
  owned by an earlier window (the unique owning window of the disjointification);
* `exists_pos_lower_bound_atlasTheta_on_compact` /
  `exists_pos_lower_bound_atlasTheta_on_cube`: pointwise positive reference
  intensity on a compact label set gives a uniform `theta >= c > 0` bound, which
  is the pointwise finite-nonzero reference-intensity input at retained roots;
* `ballCore_cubeCoverage`: the two coverage inputs hold simultaneously for the
  refined ball-core atlas and yield the actual cube coverage consumed by the
  upper pressure lane.

The one remaining producer sub-gap is recorded at the end: constructing the full
refined `CalibratedSeedWindow` family whose presentation core is the certified
chart ball (i.e. re-building the `position/ambient/curve/level` fields for the
new C1,1 potential on the ball, and making the ball a *core* around the section
point) is producer geometry beyond the chart-level C1,1 data. The conditional
construction and all coverage/retention consequences are proved here.
-/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open MeasureTheory.Measure
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## The refined ball core gives the label ball -/

/-- **A presentation with a ball core around the section point retains a label
ball.**  If the compact core of the C1,1 presentation contains a closed chart
ball around the section point `position 0`, then the labels contain a genuine
metric ball around the zero label.  This is the label-ball interiority input of
the cube coverage, obtained from the certified ball core. -/
theorem labels_ball_of_ball_core
    (A : F.CalibratedLevelSeedPatch u)
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      A.covector A.level A.openLabels A.labels A.curve)
    {y' : E} {σ : ℝ} (hσ : 0 < σ)
    (hcore : closedBall y' σ ⊆ D.core) (hsec : D.position 0 = y') :
    ∃ r : ℝ, 0 < r ∧ ball (0 : A.covector.ker) r ⊆ A.labels := by
  have hcont : ContinuousWithinAt D.position A.openLabels 0 :=
    D.position_contDiff.continuousOn.continuousWithinAt D.zero_mem
  obtain ⟨δ, hδ, hδsub⟩ := Metric.continuousWithinAt_iff.mp hcont σ hσ
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.isOpen_iff.mp A.openLabels_open 0 D.zero_mem
  refine ⟨min δ δ₂, lt_min hδ hδ₂, ?_⟩
  intro w hw
  rw [mem_ball_zero_iff] at hw
  have hwδ : dist w 0 < δ := by
    rw [dist_eq_norm, sub_zero]
    exact lt_of_lt_of_le hw (min_le_left _ _)
  have hwδ₂ : dist w 0 < δ₂ := by
    rw [dist_eq_norm, sub_zero]
    exact lt_of_lt_of_le hw (min_le_right _ _)
  have hwV : w ∈ A.openLabels := hδ₂sub (mem_ball.mpr hwδ₂)
  have hpos : D.position w ∈ closedBall y' σ := by
    rw [mem_closedBall]
    have hdist : dist (D.position w) (D.position 0) < σ := hδsub hwV hwδ
    exact le_of_lt (hsec ▸ hdist)
  rw [D.labels_eq]
  exact ⟨hwV, hcore hpos⟩

/-- **Label ball from a core interior around the section point.**  In particular a
presentation whose core is a chart neighbourhood of the section point retains a
ball of labels. -/
theorem labels_ball_of_core_interior
    (A : F.CalibratedLevelSeedPatch u)
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      A.covector A.level A.openLabels A.labels A.curve)
    (h : ∃ σ : ℝ, 0 < σ ∧ closedBall (D.position 0) σ ⊆ D.core) :
    ∃ r : ℝ, 0 < r ∧ ball (0 : A.covector.ker) r ⊆ A.labels := by
  obtain ⟨σ, hσ, hσcore⟩ := h
  exact labels_ball_of_ball_core A D hσ hσcore rfl

/-- **The certified ball core of the producer theorem.**  The C1,1 producer
`exists_ball_core_C11_data` supplies a genuine compact chart ball inside the
prescribed chart ball, which is the core of the refined presentation. -/
theorem certified_ball_core_available
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {δ : ℝ} (hδ : 0 < δ)
    (hu : let _instBallCoreProducerMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {y : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hyball : closedBall y ρ ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hreach : let _instBallCoreProducerReach : MetricSpace M := F.metricSpace
      ∀ x ∈ closedBall y ρ, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ) :
    ∃ (y' : E) (σ : ℝ) (G : E → ℝ) (L : ℝ≥0), 0 < σ ∧
      closedBall y' σ ⊆ closedBall y ρ ∧ ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        LipschitzWith L (fderiv ℝ G) ∧
        EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (closedBall y' σ) ∧
        EqOn (fderiv ℝ G) (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) (closedBall y' σ) ∧
        ∀ x ∈ closedBall y' σ,
          HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x :=
  exists_ball_core_C11_data hF hcomplete old hδ hu hρ hyball hreach

/-! ## The coverage input `hlabelCover` from the label ball -/

/-- **The seed-label coverage input from the label ball.**  If the retained labels
contain a metric ball of labels of radius `r` and the normalized basis `e` maps
the unit cube into that ball, then the unit cube is contained in the seed-label
image: exactly the `hlabelCover` input of the tile model. -/
theorem hlabelCover_of_labelBall
    (A : F.CalibratedLevelSeedPatch u) {q : ℕ}
    (e : A.covector.ker ≃L[ℝ] (Fin q → ℝ)) {r : ℝ}
    (hball : ball (0 : A.covector.ker) r ⊆ A.labels)
    (hcube : ∀ v ∈ OTSelector.Probability.seedUnitCube q, ‖e.symm v‖ < r) :
    OTSelector.Probability.seedUnitCube q ⊆ e '' A.labels := by
  intro v hv
  refine ⟨e.symm v, hball ?_, e.apply_symm_apply v⟩
  rw [mem_ball_zero_iff]
  exact hcube v hv

/-! ## The retention input `hretain` and the unique owning window -/

/-- **Exact membership in the owning window piece.**  A root belongs to the
selected disjoint piece of window `j` iff it has finite-nonzero reference
intensity for window `j` and is not owned by any earlier window. -/
theorem mem_populationSeedRootPiece_iff_of_ballCore
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    {j : ℕ} {z : Z} :
    z ∈ populationSeedRootPiece P a κ lambda j ↔
      z ∈ populationSeedReferenceRoots (P j).seed a (κ j) lambda ∧
        ∀ i < j, z ∉ populationSeedReferenceRoots (P i).seed a (κ i) lambda := by
  constructor
  · intro hz
    have h' : z ∈ disjointed
        (fun i => populationSeedReferenceRoots (P i).seed a (κ i) lambda) j := hz
    rw [disjointed_eq_inter_compl] at h'
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff] at h'
    exact ⟨h'.1, fun i hi => h'.2 i hi⟩
  · rintro ⟨hroot, hfirst⟩
    have h' : z ∈ disjointed
        (fun i => populationSeedReferenceRoots (P i).seed a (κ i) lambda) j := by
      rw [disjointed_eq_inter_compl]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
      exact ⟨hroot, fun i hi => hfirst i hi⟩
    exact h'

/-- **A finite-nonzero first-owned root is retained in its window's piece.**  This
is the retention input at a retained root, before any choice of label: the root
has finite-nonzero reference intensity and the disjointification makes the owning
window unique. -/
theorem mem_piece_of_owner
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    {j : ℕ} {z : Z}
    (hroot : z ∈ populationSeedReferenceRoots (P j).seed a (κ j) lambda)
    (hfirst : ∀ i < j, z ∉ populationSeedReferenceRoots (P i).seed a (κ i) lambda) :
    z ∈ populationSeedRootPiece P a κ lambda j :=
  (mem_populationSeedRootPiece_iff_of_ballCore P a κ lambda).mpr ⟨hroot, hfirst⟩

/-! ## The reference-intensity input at retained roots -/

section ReferenceIntensity

variable {ι : Type*} [Fintype ι]

/-- **Pointwise positive reference intensity on a compact label set gives a
uniform positive lower bound.**  This is the pointwise finite-nonzero
reference-intensity input at the retained roots: on a compact set of labels, the
common quotient density `theta` is bounded below by a positive constant as soon
as it is positive at every point. -/
theorem exists_pos_lower_bound_atlasTheta_on_compact
    {gA : ℝ → (ι → ℝ) → ℝ} {lo hi : ℝ} (hgA : Continuous (uncurry gA))
    {K : Set (ι → ℝ)} (hK : IsCompact K)
    (hpos : ∀ z ∈ K, 0 < atlasTheta gA lo hi z) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ atlasTheta gA lo hi z := by
  by_cases hne : K.Nonempty
  · obtain ⟨z₀, hz₀, hmin⟩ :=
      hK.exists_isMinOn hne (continuous_atlasTheta hgA).continuousOn
    exact ⟨atlasTheta gA lo hi z₀, hpos z₀ hz₀, fun z hz => (isMinOn_iff.mp hmin) z hz⟩
  · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hne⟩

/-- **The cube form of the positive lower bound.**  Positivity of the common
quotient density at every label of the compact closed cube gives a positive
constant lower bound on the retained cube labels. -/
theorem exists_pos_lower_bound_atlasTheta_on_cube
    {gA : ℝ → (ι → ℝ) → ℝ} {lo hi : ℝ} (hgA : Continuous (uncurry gA)) {q : ℕ}
    (e : (ι → ℝ) ≃L[ℝ] (Fin q → ℝ))
    (hpos : ∀ v ∈ (univ.pi fun _ : Fin q => Icc (0 : ℝ) 1),
      0 < atlasTheta gA lo hi (e.symm v)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ v ∈ (univ.pi fun _ : Fin q => Icc (0 : ℝ) 1),
        c ≤ atlasTheta gA lo hi (e.symm v) := by
  have hK : IsCompact (e.symm '' (univ.pi fun _ : Fin q => Icc (0 : ℝ) 1)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image e.symm.continuous
  have hpos' : ∀ z ∈ e.symm '' (univ.pi fun _ : Fin q => Icc (0 : ℝ) 1),
      0 < atlasTheta gA lo hi z := by
    rintro z ⟨v, hv, rfl⟩
    exact hpos v hv
  obtain ⟨c, hc, hle⟩ := exists_pos_lower_bound_atlasTheta_on_compact hgA hK hpos'
  exact ⟨c, hc, fun v hv => hle (e.symm v) ⟨v, hv, rfl⟩⟩

/-- **The uniform `theta >= c > 0` input at the retained roots.**  Restricted to
the open unit cube of retained labels, the positive lower bound of the closed
cube applies: this is the pointwise finite-nonzero reference intensity at the
retained roots. -/
theorem retainedRoots_theta_ge
    {gA : ℝ → (ι → ℝ) → ℝ} {lo hi : ℝ} (hgA : Continuous (uncurry gA)) {q : ℕ}
    (e : (ι → ℝ) ≃L[ℝ] (Fin q → ℝ))
    (hpos : ∀ v ∈ (univ.pi fun _ : Fin q => Icc (0 : ℝ) 1),
      0 < atlasTheta gA lo hi (e.symm v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ OTSelector.Probability.seedUnitCube q,
      c ≤ atlasTheta gA lo hi (e.symm v) := by
  obtain ⟨c, hc, hle⟩ := exists_pos_lower_bound_atlasTheta_on_cube hgA e hpos
  refine ⟨c, hc, fun v hv => hle v ?_⟩
  exact Set.mem_pi.mpr fun i _ =>
    ⟨le_of_lt (Set.mem_pi.mp hv i (mem_univ i)).1,
      le_of_lt (Set.mem_pi.mp hv i (mem_univ i)).2⟩

end ReferenceIntensity

/-! ## Both coverage inputs for the refined ball-core atlas -/

/-- **The refined ball-core atlas satisfies the coverage inputs and the cube
coverage.**  Assume window `j` of the refined atlas carries the certified chart
ball core around the section point (hence a label ball of radius `r`), the
normalized basis maps the unit cube into that label ball (`hlabelCover`), and the
original roots of the cube labels have finite-nonzero reference intensity for
window `j` and are not owned by any earlier window (the retention input). Then
the unit cube is contained in the seed-label image of the owning window piece,
i.e. the cube coverage hypothesis of the upper pressure lane holds. -/
theorem ballCore_cubeCoverage
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instBallCoreAtlasMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {q : ℕ} (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      (P j).seed.covector (P j).seed.level (P j).seed.openLabels (P j).seed.labels
      (P j).seed.curve)
    {y' : E} {σ : ℝ} (hσ : 0 < σ)
    (hcore : closedBall y' σ ⊆ D.core) (hsec : D.position 0 = y')
    {r : ℝ} (hball : ball (0 : (P j).seed.covector.ker) r ⊆ (P j).seed.labels)
    (hcube : ∀ v ∈ OTSelector.Probability.seedUnitCube q, ‖e.symm v‖ < r)
    (hroot : ∀ w ∈ (P j).seed.labels,
      a ((P j).seed.curve w 0) ∈
        populationSeedReferenceRoots (P j).seed a (κ j) lambda)
    (hfirst : ∀ w ∈ (P j).seed.labels, ∀ i < j,
      a ((P j).seed.curve w 0) ∉
        populationSeedReferenceRoots (P i).seed a (κ i) lambda) :
    OTSelector.Probability.seedUnitCube q ⊆
      e '' (populationSeedRootLabelValue (P j).seed a ''
        populationSeedRootPiece P a κ lambda j) := by
  refine cubeCoverage_of_seedLabelCover_and_retention P a κ lambda
    hF hcomplete hu ha hinj j e
    (hlabelCover_of_labelBall (P j).seed e hball hcube) ?_
  intro w hw _
  exact mem_piece_of_owner P a κ lambda (hroot w hw) (hfirst w hw)

end OTSelector.Reconstruction
