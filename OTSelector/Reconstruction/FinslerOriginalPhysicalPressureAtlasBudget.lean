import OTSelector.Reconstruction.FinslerOriginalPhysicalRootPressure

/-! Exact countable coordinate-pressure budgets on the unchanged original root.
The global physical pressure needs no full-cover or energy absolute-continuity premise. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

variable {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, (κ j).IsAddHaarMeasure]
  {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {b : Z × ℝ → M} (f : M × M →ᵇ ℝ)

/-- The positive part of the actual glued pressure has its exact countable
original-coordinate integral decomposition, without an integrability assumption.
This includes the genuine cHaar in every original coordinate intensity. -/
theorem lintegral_originalPhysicalFinslerRootPressure_eq_coordinate_tsum
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val))) (t : ℝ) :
    (∫⁻ z, ENNReal.ofReal (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z)
      ∂lambda) =
    ∑' j, ∫⁻ z, ENNReal.ofReal (
      originalSeedCoordinateIntensity P a κ lambda j z ^ (-2/(((finrank ℝ E - 1 : ℕ) : ℝ))) *
      originalSeedRootPressure (P j).seed a η₀ η₁ b f z
        (t * originalSeedCoordinateIntensity P a κ lambda j z ^
          (2/(((finrank ℝ E - 1 : ℕ) : ℝ)))))
      ∂lambda.restrict (populationSeedRootPiece P a κ lambda j) := by
  let piece := populationSeedRootPiece P a κ lambda
  let p := originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t
  have hm j : MeasurableSet (piece j) :=
    measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j
  have heq : (⋃ j, piece j).indicator (fun z ↦ ENNReal.ofReal (p z)) =
      (fun z ↦ ENNReal.ofReal (p z)) := by
    funext z
    by_cases hz : z ∈ ⋃ j, piece j
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      have hp : p z = 0 := disjointRootPressure_eq_zero_of_notMem piece _ hz
      rw [hp,ENNReal.ofReal_zero]
  calc
    _ = ∫⁻ z in ⋃ j, piece j, ENNReal.ofReal (p z) ∂lambda := by
      rw [← lintegral_indicator (MeasurableSet.iUnion hm),heq]
    _ = ∑' j, ∫⁻ z in piece j, ENNReal.ofReal (p z) ∂lambda :=
      lintegral_iUnion hm (pairwiseDisjoint_populationSeedRootPiece P a κ lambda) _
    _ = _ := by
      apply tsum_congr
      intro j
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hm j)] with z hz
      have hh := originalPhysicalFinslerRootPressure_eq_coordinate_on_piece
        (η₀ := η₀) (η₁ := η₁) (b := b) f j t hz
      exact congrArg ENNReal.ofReal hh

variable (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
  (hdim : 6 ≤ finrank ℝ E)
  {gap diameter : ℝ} (hgap : 0 < gap)
  (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diameter)
  (γ : Kernel Z (ℝ × ℝ)) [IsMarkovKernel γ]
  (hγ : ∀ᵐ z ∂lambda, Vlasov.IsCoupling (γ z)
    (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2)
  (hb : Measurable b)

include hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ hb

/-- The exact sum of original coordinate zero-pressure integrals is the only
budget needed for genuine global p0 integrability. A parent Taylor/Palm lower
and the single original global energy budget supply this exact sum. -/
theorem integrable_originalPhysicalFinslerRootPressure_of_coordinate_budget
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbudget : (∑' j, ∫⁻ z, ENNReal.ofReal (
      originalSeedCoordinateIntensity P a κ lambda j z ^ (-2/(((finrank ℝ E - 1 : ℕ) : ℝ))) *
      originalSeedRootPressure (P j).seed a η₀ η₁ b f z 0)
      ∂lambda.restrict (populationSeedRootPiece P a κ lambda j)) ≤ C) :
    Integrable (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0) lambda ∧
      (∫ z, originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0 z ∂lambda) ≤ C.toReal := by
  have hread := originalPhysicalFinslerRootPressure_measurable_nonneg f hlaw hF hcomplete
    hu ha hinj hdim hgap hsep γ hγ hb 0
  have hbound : (∫⁻ z, ENNReal.ofReal
      (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0 z) ∂lambda) ≤ C := by
    rw [lintegral_originalPhysicalFinslerRootPressure_eq_coordinate_tsum f hF hcomplete hu ha hinj 0]
    simpa only [zero_mul] using hbudget
  have hfinite : (∫⁻ z, ENNReal.ofReal
      (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0 z) ∂lambda) ≠ ⊤ :=
    ne_top_of_le_ne_top hC hbound
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hread.1 hread.2).mp hfinite,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hread.2 hread.1]
  exact ENNReal.toReal_mono hC hbound

/-- The same single original coordinate budget gives every signed tilted
actual physical pressure and its global original-atlas integral bound. -/
theorem originalPhysicalFinslerPressure_all_tilts_of_coordinate_budget
    [IsFiniteMeasure lambda] {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbudget : (∑' j, ∫⁻ z, ENNReal.ofReal (
      originalSeedCoordinateIntensity P a κ lambda j z ^ (-2/(((finrank ℝ E - 1 : ℕ) : ℝ))) *
      originalSeedRootPressure (P j).seed a η₀ η₁ b f z 0)
      ∂lambda.restrict (populationSeedRootPiece P a κ lambda j)) ≤ C) (t : ℝ) :
    Integrable (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t) lambda ∧
    |populationAtlasPressure P a κ lambda
      (fun j ↦ originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f)
      ((finrank ℝ E - 1 : ℕ) : ℝ) t| ≤ C.toReal + |t| * ‖f‖ * lambda.real univ := by
  obtain ⟨hp0,hbound0⟩ := integrable_originalPhysicalFinslerRootPressure_of_coordinate_budget f hlaw hF
    hcomplete hu ha hinj hdim hgap hsep γ hγ hb hC hbudget
  obtain ⟨hi,hbound⟩ := integrable_originalPhysicalFinslerRootPressure_of_zero f hlaw hF
    hcomplete hu ha hinj hdim hgap hsep γ hγ hb hp0 t
  exact ⟨hi,by linarith only [hbound,hbound0]⟩

end OTSelector.Reconstruction
