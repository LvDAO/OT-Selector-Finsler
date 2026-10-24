import OTSelector.Reconstruction.FinslerOriginalLegalPressureCoefficientStability
import OTSelector.Reconstruction.FinslerOriginalClassPressureUnitDensity
import OTSelector.Reconstruction.FinslerCoefficientPressureFreezing

/-! The actual original relative coefficient cover produces quantitative
stability of its original finite-class thermodynamic pressures. -/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- A produced relative geometric coefficient cover controls the actual unit
pressure at two retained roots. Both pressure limits are produced internally
for the same original class plan. The remaining probe oscillation is the
ordinary uniform error of the original bounded continuous physical probe. -/
theorem OriginalPopulationCoefficientCore.exists_clockClassPressure_relative_stability
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    {ε η : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    (D : C.RelativeRootCover ε) {z₀ z : Z} (hz₀ : z₀ ∈ D.centers)
    (hz : z ∈ C.roots ∩ D.neighborhood z₀) (f : M × M →ᵇ ℝ)
    (hprobeDiff : ∀ p ∈ C.window.region,
      |originalReferenceClockProbe C z hz.1 f p -
        originalReferenceClockProbe C z₀ (D.subset hz₀) f p| ≤ η)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k)
    (hzero : ∀ j k, ¬C.clockClassAllowed Q j k → P₀ j k = 0)
    (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 4 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    ∃ p pref : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q)
        (α : Measure _) (β : Measure _) (C.clockClassKinetic Q z)
        (C.clockClassProbe Q z hz.1 f) R t) atTop (𝓝 (p t))) ∧
      (∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q)
        (α : Measure _) (β : Measure _) (C.clockClassKinetic Q z₀)
        (C.clockClassProbe Q z₀ (D.subset hz₀) f) R t) atTop (𝓝 (pref t))) ∧
      ∀ t, |p t - pref t| ≤ ε * (pref t + |t| * ‖f‖) + |t| * η := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨p,hp,_,_⟩ := C.exists_clockClassPressure_limit Q z hz.1 f P₀ hP₀ hzero hmass hq
  obtain ⟨pref,hpref,_,_⟩ := C.exists_clockClassPressure_limit Q z₀ (D.subset hz₀) f
    P₀ hP₀ hzero hmass hq
  obtain ⟨K,hK,hbound⟩ := C.exists_clockClassKinetic_bound Q z hz.1
  obtain ⟨Kref,hKref,hrefbound⟩ := C.exists_clockClassKinetic_bound Q z₀ (D.subset hz₀)
  have hnested : ∀ j j', (∀ k, C.clockClassAllowed Q j k → C.clockClassAllowed Q j' k) ∨
      (∀ k, C.clockClassAllowed Q j' k → C.clockClassAllowed Q j k) :=
    C.clockClassAllowed_rows_nested Q
  have hkin (j k : Fin Q.count) (hjk : C.clockClassAllowed Q j k) (v : Fin q → ℝ) :
      |C.clockClassKinetic Q z j k v - C.clockClassKinetic Q z₀ j k v| ≤
        ε * C.clockClassKinetic Q z₀ j k v := by
    simpa only [OriginalPopulationCoefficientCore.clockClassKinetic,
      OriginalPopulationCoefficientCore.clockClassMatrix,hjk,↓reduceIte] using
      D.relative z₀ hz₀ z hz (C.clockClassReference Q j k) (C.clockClassReference_mem Q hjk).1 v
  have hprobe (j k : Fin Q.count) (hjk : C.clockClassAllowed Q j k) :
      |C.clockClassProbe Q z hz.1 f j k - C.clockClassProbe Q z₀ (D.subset hz₀) f j k| ≤ η := by
    simpa only [OriginalPopulationCoefficientCore.clockClassProbe,hjk,↓reduceIte] using
      hprobeDiff (C.clockClassReference Q j k) (C.clockClassReference_mem Q hjk).1
  have hbound' (j k : Fin Q.count) (_hjk : C.clockClassAllowed Q j k) (v : Fin q → ℝ) :
      |C.clockClassKinetic Q z j k v| ≤ (K + Kref) * ∑ l, v l ^ 2 := by
    exact (hbound j k v).trans (mul_le_mul_of_nonneg_right
      (by linarith : K ≤ K + Kref) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
  have hrefbound' (j k : Fin Q.count) (_hjk : C.clockClassAllowed Q j k) (v : Fin q → ℝ) :
      |C.clockClassKinetic Q z₀ j k v| ≤ (K + Kref) * ∑ l, v l ^ 2 := by
    exact (hrefbound j k v).trans (mul_le_mul_of_nonneg_right
      (by linarith : Kref ≤ K + Kref) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
  refine ⟨p,pref,hp,hpref,?_⟩
  intro t
  exact finiteClassLegalPressure_limits_abs_sub_le_relative q (C.clockClassAllowed Q) hnested
    (α : Measure _) (β : Measure _) (kin := C.clockClassKinetic Q z)
    (reference := C.clockClassKinetic Q z₀) (add_nonneg hK hKref) (norm_nonneg f) hε0 hε1 hη
    (C.measurable_clockClassKinetic Q z) (C.measurable_clockClassKinetic Q z₀)
    hbound' hrefbound' (C.clockClassProbe Q z hz.1 f) (C.clockClassProbe Q z₀ (D.subset hz₀) f)
    (fun j k _ ↦ C.clockClassProbe_abs_le Q z hz.1 f j k)
    (fun j k _ ↦ C.clockClassProbe_abs_le Q z₀ (D.subset hz₀) f j k)
    hkin hprobe p pref hp hpref t

end OTSelector.Reconstruction
