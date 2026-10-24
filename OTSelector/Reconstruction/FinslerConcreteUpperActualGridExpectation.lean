import OTSelector.Reconstruction.FinslerConcreteUpperClassGridExpectation

/-! Original finite clock-class coefficients in the actual active grid mean
bound. All kinetic and probe conditions come from the stored coefficient core. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
local instance actualClassGridOptionMeasurableSpace (T : Type*) : MeasurableSpace (Option T) := ⊤
local instance actualClassGridOptionMeasurableSingleton (T : Type*) :
    MeasurableSingletonClass (Option T) := ⟨fun _ ↦ trivial⟩
variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The original retained class law and original coefficient field produce
an active microscopic grid comparison; no per-cell transport estimate is assumed. -/
theorem OriginalPopulationCoefficientCore.exists_actual_clockClass_active_grid_expectation
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmassP : 0 < ∑ j, ∑ k, P₀ j k)
    (hzero : ∀ j k, ¬C.clockClassAllowed Q j k → P₀ j k = 0) :
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
      (m depth N : ℕ) (_hq : 4 < q) (_hN : 0 < N)
    (hm : 0 < m) (hdepth : m ≤ 2 ^ depth) (_hdepth2 : 2 ^ depth ≤ 2 * m)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (xs ys : Fin N → Ω → X × (Fin Q.count × Fin Q.count))
    (_hx : ∀ i, Measurable (xs i)) (_hy : ∀ i, Measurable (ys i))
    (_hxi : iIndepFun xs P) (_hyi : iIndepFun ys P)
    (_hxl : ∀ i, P.map (xs i) = μ.prod (clockClassJointProbability P₀ hP₀ hmassP : Measure _))
    (_hyl : ∀ i, P.map (ys i) = μ.prod (clockClassJointProbability P₀ hP₀ hmassP : Measure _))
    (_hxy : IndepFun (fun sample i ↦ xs i sample) (fun sample j ↦ ys j sample) P)
    (θ : X → Option Unit) (_hθ : Measurable θ)
    (z : X → Fin q → ℝ) (_hz : Measurable z)
    (_hunit : ∀ᵐ x ∂μ, (θ x).isSome = true → z x ∈ unitCube q)
    {density tilt : ℝ} (_hd : 0 ≤ density)
    (_hmass : μ.real {x | (θ x).isSome = true} ≤ density),
    let graph := fun sample ↦ pairedClassActiveGraph θ (C.clockClassAllowed Q)
      (fun i ↦ xs i sample) (fun j ↦ ys j sample);
    let cost := fun sample i j ↦ pairedClassScaledEdgeCost z (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f)
      (((N : ℝ) * density) ^ (2 / (q : ℝ))) tilt (xs i sample) (ys j sample);
    (∫ (sample : Ω), PartialMatching.legalMaximumValue (graph sample) (cost sample) ∂P) / N ≤
      (∫ (sample : Ω), ∑ b : Fin q → Fin (2 ^ depth + 1), PartialMatching.legalMaximumValue
        (PartialMatching.spatialLegalBlock (graph sample)
          (fun i ↦ gridCellLabel q m depth depth hm hdepth (z (xs i sample).1))
          (fun j ↦ gridCellLabel q m depth depth hm hdepth (z (ys j sample).1)) b)
        (cost sample) ∂P) / N +
      activeGridRepairError q
        (legalGridRepairConstant q (Q.count + 1) (Q.count * Q.count))
        K ‖f‖ tilt density ((N : ℝ) / (m : ℝ) ^ q) := by
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  refine ⟨K, hK, ?_⟩
  intro Ω X _ _ m depth N hq hN hm hdepth hdepth2 Psample _ μ _ xs ys hx hy hxi hyi hxl hyl hxy θ hθ z hz hunit density tilt hd hmass
  simpa only [Fintype.card_fin] using integral_pairedClass_active_grid_value_div_le (tilt := tilt)
    _ m depth N hq hN hm hdepth hdepth2 Psample μ P₀ hP₀ hmassP
    (C.clockClassAllowed Q) hzero xs ys hx hy hxi hyi hxl hyl hxy θ hθ z hz hunit
    (C.clockClassKinetic Q z₀) (C.measurable_clockClassKinetic Q z₀)
    (C.clockClassProbe Q z₀ hz₀ f) (C.measurable_clockClassProbe Q z₀ hz₀ f)
    hd hmass hK (norm_nonneg f) (fun j k _ ↦ hbound j k)
    (fun j k _ ↦ C.clockClassProbe_abs_le Q z₀ hz₀ f j k)

end OTSelector.Reconstruction
