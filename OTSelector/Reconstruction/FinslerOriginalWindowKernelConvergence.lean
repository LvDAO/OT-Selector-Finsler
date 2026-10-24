import OTSelector.Reconstruction.FinslerOriginalWindowClockKernel

/-! Actual conditional-law variation on the original Finsler continuity cores
passes exactly through scalar-range lifts and arbitrary retained pairings. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- Actual original local L1 cores give variation convergence of each full
conditional law on any one of their actual coefficient pieces. -/
theorem PopulationLocalPressureCore.original_piece_clock_variation_tendsto
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count)
    (z : ℕ → (D.haar.continuous.coefficient i).roots)
    (ref : (D.haar.continuous.coefficient i).roots) (hz : Tendsto z atTop (𝓝 ref))
    (color : Fin 2) :
    Tendsto (fun n ↦
      ((populationTwoColorClockKernel u a μ ν color (z n).val).toSignedMeasure -
        (populationTwoColorClockKernel u a μ ν color ref.val).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
  let B := D.haar.continuous.population
  have hsub : (D.haar.continuous.coefficient i).roots ⊆ B.roots := fun w hw ↦
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,hw⟩
  let lift : (D.haar.continuous.coefficient i).roots → B.roots := fun w ↦ ⟨w.val,hsub w.property⟩
  have hcont : Continuous lift := continuous_subtype_val.subtype_mk (fun w ↦ hsub w.property)
  have ht := hcont.continuousAt.tendsto.comp hz
  exact B.original_clock_law_variation_tendsto (fun n ↦ lift (z n)) (lift ref) ht color

/-- The actual original manifold geometry produces the global relative
kernel/probe error input of the true continuous pressure theorem. The compact
window extension is identical on both roots and has no finite-bin dependence. -/
theorem PopulationLocalPressureCore.original_window_kernels_eventually
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count)
    (z : ℕ → (D.haar.continuous.coefficient i).roots)
    (ref : (D.haar.continuous.coefficient i).roots) (hz : Tendsto z atTop (𝓝 ref))
    (f : M × M →ᵇ ℝ) {range : Set ℝ} :
    ∀ ε > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ x y : range,
      (∀ w, |(D.haar.continuous.coefficient i).originalWindowClockKinetic (z n).val x y w -
        (D.haar.continuous.coefficient i).originalWindowClockKinetic ref.val x y w| ≤
          ε * (D.haar.continuous.coefficient i).originalWindowClockKinetic ref.val x y w) ∧
      |(D.haar.continuous.coefficient i).originalWindowClockProbe (z n).val (z n).property f x y -
        (D.haar.continuous.coefficient i).originalWindowClockProbe ref.val ref.property f x y| ≤ η := by
  intro ε hε η hη
  filter_upwards [D.original_window_geometry_eventually hF hcomplete hu ha hinj i z ref hz f ε hε η hη]
    with n hn
  intro x y
  by_cases hp : (x.val,y.val) ∈ (D.haar.continuous.coefficient i).window.region
  · simpa only [OriginalPopulationCoefficientCore.originalWindowClockKinetic,
      OriginalPopulationCoefficientCore.originalWindowClockProbe,
      OriginalPopulationCoefficientCore.originalRangeClockProbe,hp,↓reduceIte] using hn _ hp
  · simp only [OriginalPopulationCoefficientCore.originalWindowClockKinetic,
      OriginalPopulationCoefficientCore.originalWindowClockProbe,hp,↓reduceIte,sub_self,abs_zero,mul_zero,
      le_refl,forall_const,true_and]
    exact hη.le

end OTSelector.Reconstruction
