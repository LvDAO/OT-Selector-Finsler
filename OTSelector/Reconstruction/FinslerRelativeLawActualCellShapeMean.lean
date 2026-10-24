import OTSelector.Reconstruction.FinslerRelativeLawOriginalMicrocellShapeMean
import OTSelector.Reconstruction.FinslerConcreteUpperMicrocellMass

/-! Original coefficient cells supply their literal changing-grid binomial pressure comparison. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry BoxIntegral
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators
  BoundedContinuousFunction Classical unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

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

/-- Actual original Finsler cell data produce a deterministic microscopic
family whose original label loss and missing coordinate volume are small and
whose literal binomial shape means have the actual filling-volume pressure
reference. No shape regularity, conditional-iid or filling-limit premise remains. -/
theorem PopulationLocalPressureCore.exists_actual_cell_binomialShape_pressure_error
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {labelCell : Set (ℚ → M)} (hcell : MeasurableSet labelCell)
    (hsub : labelCell ⊆ (D.haar.continuous.coefficient i).roots)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : ℚ → M) (hz₀ : z₀ ∈ (D.haar.continuous.coefficient i).roots)
    (f : M × M →ᵇ ℝ) (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 0 < Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (e : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker ≃L[ℝ]
      (Fin (Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ)) :
    let C := D.haar.continuous.coefficient i
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    let coord := atlasSeedCoord (P C.seedIndex).seed e a
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    ∃ source target : Fin Q.count → ℝ,
      (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) ∧
      ∀ (density : ℝ≥0) (_hdensity : 0 < density) (L : ℝ) (hL : 0 < L)
        (ε : ℝ≥0∞), 0 < ε →
      ∃ cells : ℕ → Finset (Fin q → ℤ),
        (∀ N, lambda (labelCell \ coord ⁻¹' (⋃ ν ∈ cells N,
          (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ)))) < ε) ∧
        (∀ N, volume ((coord '' labelCell) \ (⋃ ν ∈ cells N,
          (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ)))) < ε) ∧
        Tendsto (fun N ↦ volume ((⋃ ν ∈ cells N,
          (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ))) \ (coord '' labelCell))) atTop (𝓝 0) ∧
        ∀ T : ℝ, 0 ≤ T →
        TendstoUniformlyOn (fun N : ℕ ↦ fun tilt : ℝ ↦
          (∑ ν ∈ cells N, affineClassBinomialShapeExpectation source target
            (α : Measure _) (β : Measure _) N (positiveMicroscopicCubeProbability q density L N)
            ⟨positiveMicroscopicGridSide q L N, positiveMicroscopicGridSide_nonneg q L N⟩
            (fun l ↦ (ν l : ℝ) / positiveMicroscopicGridOrder q L N)
            (originalMicrocellShape (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ))
              (positiveMicroscopicGridOrder q L N) ν (coord '' labelCell))
            (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) / (N : ℝ) -
          volume.real (⋃ ν ∈ cells N,
            (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ))) *
            (finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
              (density * ⟨L ^ q, pow_nonneg hL.le q⟩) (C.densityClockClassKinetic Q z₀ density)
              (C.clockClassProbe Q z₀ hz₀ f) tilt / L ^ q)) (fun _ ↦ 0) atTop (Icc (-T) T) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  let coord := atlasSeedCoord (P C.seedIndex).seed e a
  have hs : MeasurableSet (coord '' labelCell) := by
    have hR := D.haar.measurable_cell_label_image hcomplete i hcell hsub
    have h := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hR
    change MeasurableSet (e '' (R '' labelCell)) at h
    change MeasurableSet ((fun z ↦ e (R z)) '' labelCell)
    simpa only [image_image] using h
  have hsubI : labelCell ⊆ (D.haar.intensity i).roots := by
    rwa [D.haar.intensity_roots]
  have hcompact : IsCompact (e '' (R '' (D.haar.intensity i).roots)) :=
    (D.haar.intensity i).compact_labels.image e.continuous
  have hbounded : Bornology.IsBounded (coord '' labelCell) := hcompact.isBounded.subset (by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_image_of_mem e (mem_image_of_mem R (hsubI hz)))
  obtain ⟨source, target, hcode, hsum⟩ :=
    C.exists_original_microcellShape_pressure_error Q z₀ hz₀ f P₀ hP₀ hmass hq
  refine ⟨source, target, hcode, ?_⟩
  intro density hdensity L hL ε hε
  obtain ⟨cells, _, hloss, hmissing, hadded⟩ :=
    D.exists_cell_microscopic_cubes_with_two_mass_controls hF hcomplete hu ha hinj i hcell hsub e hε
      (positiveMicroscopicGridOrder q L) (tendsto_positiveMicroscopicGridOrder hq hL)
  refine ⟨cells, hloss, hmissing, hadded, ?_⟩
  intro T hT
  exact hsum density hdensity L hL (coord '' labelCell) hs hbounded.measure_lt_top.ne cells hadded T hT

end OTSelector.Reconstruction
