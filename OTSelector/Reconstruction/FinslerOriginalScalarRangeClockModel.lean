import OTSelector.Reconstruction.FinslerOriginalProjectedPressureStability
import OTSelector.Reconstruction.FinslerConcreteUpperClassObservation
import OTSelector.Reconstruction.FinslerConcreteUpperClassMask
import OTSelector.Reconstruction.FinslerExpectedCoefficientFreezing

/-! Original scalar clocks are carried by their actual compact range, with
measurable finite-bin observation and the original geometric kinetic cost.
Only illegal entries are zero-extended; the original legal problem is unchanged. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The unique original bin containing a clock in its actual range. No fallback
or nonempty-bin assumption is required, including an empty overall range. -/
def FiniteScalarBins.rangeClassify {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (x : range) : Fin Q.count :=
  (show ∃ j, x.val ∈ Q.cell j from mem_iUnion.mp (Q.union_eq.symm ▸ x.property)).choose

/-- Every original range clock belongs to the bin reported by its observation. -/
theorem FiniteScalarBins.rangeClassify_mem {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (x : range) : x.val ∈ Q.cell (Q.rangeClassify x) :=
  (show ∃ j, x.val ∈ Q.cell j from mem_iUnion.mp (Q.union_eq.symm ▸ x.property)).choose_spec

/-- The observation reports the unique original bin, with every endpoint tie
resolved by the original measurable partition. -/
theorem FiniteScalarBins.rangeClassify_eq_of_mem {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (j : Fin Q.count) {x : range} (hx : x.val ∈ Q.cell j) :
    Q.rangeClassify x = j := by
  by_contra hne
  exact disjoint_left.mp (Q.disjoint hne) (Q.rangeClassify_mem x) hx

/-- Original range-bin observation is measurable. -/
theorem FiniteScalarBins.measurable_rangeClassify {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) : Measurable Q.rangeClassify := by
  apply measurable_to_countable'
  intro j
  have heq : Q.rangeClassify ⁻¹' {j} = Subtype.val ⁻¹' Q.cell j := by
    ext x
    simp only [mem_preimage,mem_singleton_iff]
    exact ⟨fun hx ↦ hx ▸ Q.rangeClassify_mem x,fun hx ↦ Q.rangeClassify_eq_of_mem j hx⟩
  rw [heq]
  exact (Q.measurable_cell j).preimage measurable_subtype_coe

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The actual original clock-pair quadratic coefficient on the observed legal
mask. Its value is set to zero only on edges excluded from the matching problem. -/
def OriginalPopulationCoefficientCore.originalMaskedClockKinetic
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width) (z₀ : Z)
    (x y : range) (v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) : ℝ :=
  if C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y) then
    matrixQuadratic (C.matrix z₀ (x.val,y.val)) v else 0

/-- The original bounded physical probe at two original range clocks. -/
def OriginalPopulationCoefficientCore.originalRangeClockProbe
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M → ℝ) (x y : range) : ℝ :=
  originalReferenceClockProbe C z₀ hz₀ f (x.val,y.val)

/-- The original masked clock kernel remains genuinely quadratic. -/
theorem OriginalPopulationCoefficientCore.originalMaskedClockKinetic_homogeneous
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width) (z₀ : Z)
    (x y : range) (c : ℝ) (v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) :
    C.originalMaskedClockKinetic Q z₀ x y (c • v) = c ^ 2 * C.originalMaskedClockKinetic Q z₀ x y v := by
  dsimp only [originalMaskedClockKinetic]
  split_ifs
  · exact matrixQuadratic_smul _ _ _
  · exact (mul_zero _).symm

/-- The original physical probe keeps the original bounded continuous norm. -/
theorem OriginalPopulationCoefficientCore.originalRangeClockProbe_abs_le
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ) (x y : range) :
    |C.originalRangeClockProbe z₀ hz₀ f x y| ≤ ‖f‖ := f.norm_coe_le_norm _

/-- The actual original masked coefficient is measurable jointly in both
original scalar marks and the displacement. -/
theorem OriginalPopulationCoefficientCore.measurable_originalMaskedClockKinetic
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width) (z₀ : Z) :
    Measurable (Function.uncurry (fun p : range × range ↦ C.originalMaskedClockKinetic Q z₀ p.1 p.2)) := by
  let Ω := (range × range) × (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
  have hmask : MeasurableSet {x : Ω |
      C.clockClassAllowed Q (Q.rangeClassify x.1.1) (Q.rangeClassify x.1.2)} := by
    exact (Set.to_countable {p : Fin Q.count × Fin Q.count | C.clockClassAllowed Q p.1 p.2}).measurableSet.preimage
      ((Q.measurable_rangeClassify.comp (measurable_fst.comp measurable_fst)).prodMk
        (Q.measurable_rangeClassify.comp (measurable_snd.comp measurable_fst)))
  have hraw : Measurable (fun x : Ω ↦ matrixQuadratic
      (C.matrix z₀ (x.1.1.val,x.1.2.val)) x.2) :=
    C.measurable_quadratic_cost hF hcomplete hu ha hinj measurable_const
      ((measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))) measurable_snd
  exact hraw.ite hmask measurable_const

/-- The original physical range-clock probe is measurable. Its curve is the
same complete original seed curve at the retained root. -/
theorem OriginalPopulationCoefficientCore.measurable_originalRangeClockProbe
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex) {range : Set ℝ}
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ) :
    Measurable (Function.uncurry (C.originalRangeClockProbe (range := range) z₀ hz₀ f)) := by
  let S := (P C.seedIndex).seed
  let w := populationSeedPieceLabel P a κ lambda C.seedIndex ⟨z₀,C.roots_subset_piece hz₀⟩
  have hc : Continuous (S.curve w.val) := continuous_iff_continuousAt.mpr fun t ↦
    (hF.contMDiffAt_of_isEulerLagrangeAt (S.complete w.val w.property t (mem_univ _))).continuousAt
  have hp : Continuous (originalReferenceClockProbe C z₀ hz₀ f) :=
    f.continuous.comp ((hc.comp (continuous_fst.sub continuous_const)).prodMk
      (hc.comp (continuous_snd.sub continuous_const)))
  exact hp.measurable.comp (measurable_subtype_coe.prodMap measurable_subtype_coe)

end OTSelector.Reconstruction
