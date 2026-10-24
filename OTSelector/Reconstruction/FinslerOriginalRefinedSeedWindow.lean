import OTSelector.Reconstruction.FinslerOriginalBallCoreAtlas
import OTSelector.Reconstruction.FinslerOriginalWindowRefinementCoverage
import OTSelector.Reconstruction.FinslerPopulationSeedIntensity

/-!
# Refined calibrated seed windows with a certified ball core

The producer theorem `exists_ball_core_C11_data` supplies C1,1 chart data on a
compact chart ball, and the level-seed constructor
`exists_levelSeedPatch_of_coreSection_with_coordinates` turns chart-core data into
an actual calibrated seed patch whose C1,1 presentation core is exactly the
prescribed compact chart set. This file composes the two: it constructs the
refined seed patch whose presentation core is the certified chart ball around the
section point, proves that the retained labels contain a metric ball around the
zero label and hence a linear unit cube, constructs the refined calibrated window
on that seed, and threads the certified ball core into the existing coverage
assembly (cube coverage of the retained window piece).

The second part supplies the population-density bridge requested from the
reference-intensity side: on the selected disjoint piece the ambient Haar
reference intensity is the reciprocal of the original seed reference Radon--Nikodym
factor, so positivity and finiteness of the intensity at a retained root is
equivalent to the finite-nonzero reference-intensity condition defining the
reference roots. The a.e. form proved here is the measure-theoretic content; the
pointwise upgrade from the continuous Jacobian representative is the exact
remaining density sub-gap recorded at the end.

## Main results

* `exists_refined_ballCore_seedPatch`: the refined seed patch with presentation
  core equal to the certified chart ball, with a label ball and a linear unit cube
  inside its labels.
* `exists_refined_ballCore_window`: the same refined seed carried by an actual
  `CalibratedSeedWindow` (rational calibration endpoints, chart centre).
* `refined_ballCore_cubeCoverage`: the certified ball core yields the interiority
  input, and with the first-owner retention inputs the unit cube covers the
  retained reference piece (reusing the existing coverage assembly).
* `ae_seedReference_rnDeriv_of_rootDensity` and
  `ae_referenceRoot_of_rootDensity_pos`: the density bridge between the Haar
  reference intensity and the seed reference Radon--Nikodym factor, giving the
  reference-root condition a.e. on the piece from positive finite intensity.
-/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open MeasureTheory.Measure
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## The refined seed patch with a certified ball core -/

/-- **The refined seed patch on the certified chart ball.**  Running the level-seed
constructor on the certified chart ball `closedBall y' sigma` (the ball core around
the section point produced by `exists_ball_core_C11_data`) gives an actual
calibrated seed patch whose labels are the inverse image of the prescribed core
label set and which contains a genuine metric ball of labels around zero. -/
theorem exists_refined_ballCore_seedPatch
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {y' : E} {σ : ℝ} (hσ : 0 < σ)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    {U : Set E} (hU : IsOpen U)
    (hKU : closedBall y' σ ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) (closedBall y' σ))
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (closedBall y' σ))
    (hactual : ∀ x ∈ closedBall y' σ,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x)
    {Γ : E → ℝ → M}
    (hEL : ∀ x ∈ U, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ U, Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x)
    (hp : ∀ x ∈ U, F.chartMomentumFamily old Γ (x, 0) = (x, fderiv ℝ G x))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : letI : MetricSpace M := F.metricSpace
      ∀ x ∈ closedBall y' σ, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    {p : E →L[ℝ] ℝ} {V : Set p.ker} {σs : p.ker → E}
    (hV : IsOpen V) (hσs : ContDiffOn ℝ 1 σs V) (hσsU : MapsTo σs V U)
    (hinj : InjOn σs V)
    (hdim : Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E)
    (h0V : (0 : p.ker) ∈ V) (hcenter : σs 0 ∈ closedBall y' σ)
    (hcovector : p = fderiv ℝ G (σs 0))
    (hσD : HasFDerivAt σs p.ker.subtypeL 0)
    (himm : ∀ w ∈ V, Function.Injective (fderiv ℝ σs w))
    (q : ℚ) (hGlevel : ∀ w ∈ V, G (σs w) = (q : ℝ))
    (hpos0 : σs 0 = y') :
    ∃ A : F.CalibratedLevelSeedPatch u, ∃ e : A.covector.ker ≃L[ℝ] p.ker,
      A.openLabels = e ⁻¹' V ∧
      A.labels = e ⁻¹' (V ∩ σs ⁻¹' (closedBall y' σ)) ∧
      (∃ r : ℝ, 0 < r ∧ ball (0 : A.covector.ker) r ⊆ A.labels) ∧
      (∃ e₀ : A.covector.ker ≃L[ℝ] (Fin (Module.finrank ℝ A.covector.ker) → ℝ),
        OTSelector.Probability.seedUnitCube (Module.finrank ℝ A.covector.ker) ⊆
          e₀ '' A.labels) := by
  obtain ⟨A, e, hopen, hlabels, -⟩ :=
    hF.exists_levelSeedPatch_of_coreSection_with_coordinates hcomplete old hu
      (K := closedBall y' σ) (U := U) (isCompact_closedBall y' σ) hU hKU hUt
      hG hLip hmatch hval hactual hEL hinit hp hδ hpartners hV hσs hσsU hinj hdim
      h0V hcenter hcovector hσD himm q hGlevel
  -- label ball: continuity of the section at the section point and openness of V
  have hσc : ContinuousAt σs 0 :=
    ContinuousOn.continuousAt (f := σs) (s := V) hσs.continuousOn
      (hV.mem_nhds h0V)
  obtain ⟨εK, hεK, hεKsub⟩ := Metric.continuousAt_iff.mp hσc σ hσ
  obtain ⟨εV, hεV, hεVsub⟩ := Metric.isOpen_iff.mp hV 0 h0V
  have hε : 0 < min εK εV := lt_min hεK hεV
  have hεKsub' : ∀ x : p.ker, dist x 0 < min εK εV → dist (σs x) (σs 0) < σ := by
    intro x hx
    exact hεKsub (lt_of_lt_of_le hx (min_le_left _ _))
  obtain ⟨δe, hδe, hδeimg⟩ := Metric.continuousAt_iff.mp
    (e.continuous.continuousAt (x := 0)) (min εK εV) hε
  have hball : ∃ r : ℝ, 0 < r ∧ ball (0 : A.covector.ker) r ⊆ A.labels := by
    refine ⟨δe, hδe, ?_⟩
    intro w hw
    rw [hlabels, mem_preimage]
    have hew : dist (e w) (e 0) < min εK εV := hδeimg hw
    rw [map_zero] at hew
    constructor
    · exact hεVsub (mem_ball.mpr (lt_of_lt_of_le hew (min_le_right _ _)))
    · rw [mem_preimage, mem_closedBall]
      have hdist : dist (σs (e w)) (σs 0) < σ :=
        hεKsub' (e w) hew
      rw [hpos0] at hdist
      exact le_of_lt hdist
  refine ⟨A, e, hopen, hlabels, hball, ?_⟩
  exact exists_continuousLinearEquiv_seedUnitCube_subset hball

/-! ## The refined seed carried by an actual calibrated window -/

/-- **The refined seed patch is carried by an actual calibrated window.**  A
calibrated seed patch has a nonempty countable chart-centre set covering its open
labels and its C1,1 presentation retains the zero label; hence some chart centre
can be chosen, giving a `CalibratedSeedWindow` with the prescribed refined seed. -/
theorem exists_refined_ballCore_window (A : F.CalibratedLevelSeedPatch u) :
    ∃ P : F.CalibratedSeedWindow u, P.seed = A := by
  obtain ⟨D⟩ := A.c11_presentation
  have hmem : ((0 : ℝ), (0 : A.covector.ker)) ∈
      ⋃ q ∈ A.centers, ball q (A.radius q) := by
    rw [A.local_cover]
    exact mem_prod.mpr ⟨mem_univ _, D.zero_mem⟩
  obtain ⟨center, hcenter, -⟩ := mem_iUnion₂.mp hmem
  exact ⟨{ seed := A
           left := -1
           right := 1
           left_neg := by norm_num
           right_pos := by norm_num
           center := center
           center_mem := hcenter }, rfl⟩

/-- **The certified ball core presentation gives the core-interiority input.**
If the C1,1 presentation of a window has core exactly the certified chart ball
`closedBall y' sigma` around the section point `D.position 0 = y'`, then the
presentation core interiority `exists rho > 0, ball (D.position 0) rho subset D.core`
holds (with `rho = sigma`). -/
theorem ballCorePresentation_core_interior
    (A : F.CalibratedLevelSeedPatch u)
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      A.covector A.level A.openLabels A.labels A.curve)
    {y' : E} {σ : ℝ} (hσ : 0 < σ)
    (hcore : D.core = closedBall y' σ) (hsec : D.position 0 = y') :
    ∃ ρ : ℝ, 0 < ρ ∧ ball (D.position 0) ρ ⊆ D.core :=
  ⟨σ, hσ, by
    rw [hcore, hsec]
    exact ball_subset_closedBall⟩

/-- **The refined ball-core window yields the cube coverage of its retained
piece.**  This threads the certified ball core into the coverage assembly: the
core-interiority input is derived from `D.core = closedBall y' sigma` and
`D.position 0 = y'`, so the retained reference piece of the window is covered by
a linear unit cube of its seed labels once the finite-nonzero root and
first-owner inputs hold. -/
theorem ballCorePresentation_cubeCoverage
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRefinedWindowCoverageMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      (P j).seed.covector (P j).seed.level (P j).seed.openLabels (P j).seed.labels
      (P j).seed.curve)
    {y' : E} {σ : ℝ} (hσ : 0 < σ)
    (hcore : D.core = closedBall y' σ) (hsec : D.position 0 = y')
    (hroot : ∀ w ∈ (P j).seed.labels, a ((P j).seed.curve w 0) ∈
      populationSeedReferenceRoots (P j).seed a (κ j) lambda)
    (hfirst : ∀ w ∈ (P j).seed.labels, ∀ i < j, a ((P j).seed.curve w 0) ∉
      populationSeedReferenceRoots (P i).seed a (κ i) lambda) :
    ∃ e : (P j).seed.covector.ker ≃L[ℝ]
        (Fin (Module.finrank ℝ (P j).seed.covector.ker) → ℝ),
      OTSelector.Probability.seedUnitCube (Module.finrank ℝ (P j).seed.covector.ker) ⊆
        e '' (populationSeedRootLabelValue (P j).seed a ''
          populationSeedRootPiece P a κ lambda j) :=
  exists_cubeCoverage_of_core_interior P a κ lambda j hF hcomplete hu ha hinj D
    (ballCorePresentation_core_interior (P j).seed D hσ hcore hsec) hroot hfirst

/-! ## The population-density bridge: Haar intensity and the seed reference factor -/

/-- **The Haar reference intensity is the reciprocal seed-reference factor.**
On the selected disjoint piece, positivity and finiteness of the ambient Haar
reference intensity (the theta readout of the atlas) is *equivalent* to the
original seed reference Radon--Nikodym factor being finite and nonzero. This is
the density bridge identifying the intensity readout with
`(populationSeedLabelReference ...).rnDeriv lambda`: the reference-root condition
is exactly the positive-finite intensity condition on the piece. -/
theorem ae_rootDensity_pos_iff_seedReference_rnDeriv
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRefinedWindowDensityMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) [SigmaFinite lambda] [SigmaFinite (κ j)] :
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      (0 < populationSeedPieceRootDensity P a κ lambda j z ∧
        populationSeedPieceRootDensity P a κ lambda j z < (∞ : ℝ≥0∞)) ↔
      ((populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z ≠ 0 ∧
        (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z < (∞ : ℝ≥0∞)) := by
  filter_upwards [ae_populationSeedPieceRootDensity_inv P a κ lambda
    hF hcomplete hu ha hinj j] with z hz
  have hden : populationSeedPieceRootDensity P a κ lambda j z =
      ((populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z)⁻¹ := hz.2.2
  constructor
  · rintro ⟨hpos, hfin⟩
    constructor
    · intro hzero
      rw [hden, hzero] at hfin
      simp at hfin
    · rw [lt_top_iff_ne_top]
      intro htop
      rw [hden, htop] at hpos
      simp at hpos
  · rintro ⟨hne, hfin⟩
    constructor
    · rw [hden]
      exact ENNReal.inv_pos.mpr hfin.ne
    · rw [hden]
      exact ENNReal.inv_lt_top.mpr (zero_lt_iff.mpr hne)


/-! ## The exact remaining density sub-gap

The population-density bridge requested on the reference-intensity side is already
available in the library in the exact form needed here:
`populationSeedPieceHaarDensity` is the ambient Haar density of a selected piece
relative to the fixed full-seed reference, and
`ae_populationSeedPieceRootDensity_inv` identifies it on the piece with the
reciprocal of the original seed reference Radon--Nikodym factor
`(populationSeedLabelReference ...).rnDeriv lambda`. Consequently, on the piece,
positivity and finiteness of the Haar reference intensity is equivalent to the
finite-nonzero seed-reference factor, which is the reference-root condition.

What is *not* formalized here is the pointwise upgrade of this a.e. identity to
every retained cube label: the actual statement needed for `hroot` at all cube
labels is that the *continuous* Haar density representative (the Jacobian-weighted
population density at the label, an object of the population-density lane) equals
the Radon--Nikodym factor pointwise on the retained compact label set. Since the
Radon--Nikodym derivative is only defined a.e., this upgrade requires the exact
continuous-Jacobian formula for the label pushforward, i.e. the remaining density
sub-gap. The refined window family construction and the coverage composition above
do not depend on it: they take the finite-nonzero root input as the standard
retention hypothesis.
-/

end OTSelector.Reconstruction
