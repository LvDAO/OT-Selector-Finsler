import OTSelector.Reconstruction.FinslerOriginalWindowRetainedPairKernel
import OTSelector.Reconstruction.FinslerOriginalWindowPressureRootCutoffs
import OTSelector.Reconstruction.FinslerOriginalWindowRetainedMeanLoss
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual original geometric core laws choose the window/kernel refinement
and all original loss schedules internally, before any iid sampling. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- A deterministic positive stage accuracy, chosen before all original samples. -/
def originalWindowStageAccuracy (n : ℕ) : ℝ := 1 / ((n:ℝ) + 2)

/-- A summable original root-loss schedule, independent of samples and geometry. -/
def originalWindowStageRootLoss (n : ℕ) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ (n + 1)

/-- The stage accuracy is admissible for both original retention and window loss. -/
theorem originalWindowStageAccuracy_properties :
    (∀ n, 0 < originalWindowStageAccuracy n ∧ originalWindowStageAccuracy n < 1) ∧
    Tendsto originalWindowStageAccuracy atTop (𝓝 0) := by
  have hpos n : 0 < originalWindowStageAccuracy n := by unfold originalWindowStageAccuracy; positivity
  have hlt n : originalWindowStageAccuracy n < 1 := by
    unfold originalWindowStageAccuracy
    apply (div_lt_one (by positivity : (0:ℝ) < (n:ℝ) + 2)).mpr
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith only [hn]
  refine ⟨fun n ↦ ⟨hpos n,hlt n⟩,?_⟩
  have hh := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_natCast_atTop_atTop)
  change Tendsto (fun n : ℕ ↦ 1 / ((n:ℝ) + 2)) atTop (𝓝 0)
  simpa only [one_div,Function.comp_def] using hh

/-- Total original root losses are finite and every stage has positive budget. -/
theorem originalWindowStageRootLoss_properties :
    (∀ n, originalWindowStageRootLoss n ≠ 0) ∧ (∑' n, originalWindowStageRootLoss n) = 1 := by
  refine ⟨fun n ↦ pow_ne_zero _ (by norm_num),?_⟩
  simp only [originalWindowStageRootLoss,ENNReal.tsum_geometric_add_one,
    ENNReal.one_sub_inv_two,inv_inv]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The original local geometric core law produces an actual finite-core/window
kernel refinement with no supplied core sequence, retained kernels, loss rates,
or mass-convergence callback. Bins and all choices precede original iid samples. -/
theorem PopulationLocalPressureCoreLaw.exists_originalWindowRetainedKernel_recovery
    (hcore : PopulationLocalPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (hgap : 0 ≤ gap)
    (hGood : ∀ᵐ z ∂μ.map a,
      originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range z)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) :
    let δn := fun n ↦ ENNReal.ofReal (originalWindowStageAccuracy n)
    ∃ D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      r (δn n) (originalWindowStageRootLoss n),
    ∃ Q : ∀ n, FiniteScalarBins range (originalWindowStageAccuracy n),
      (∀ n z, (D n).originalWindowRetainedPairKernel hcomplete (fun _ ↦ Q n) γ z ≤ γ z) ∧
      ∀ᵐ z ∂μ.map a, Tendsto
        (fun n ↦ ((D n).originalWindowRetainedPairKernel hcomplete (fun _ ↦ Q n) γ z).real univ)
        atTop (𝓝 1) := by
  dsimp only
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  have hacc := originalWindowStageAccuracy_properties
  have hroot := originalWindowStageRootLoss_properties
  let δn := fun n ↦ ENNReal.ofReal (originalWindowStageAccuracy n)
  have hδ0 n : δn n ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (hacc.1 n).1)
  let D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      r (δn n) (originalWindowStageRootLoss n) := fun n ↦ Classical.choice
        (hcore _ hGood (δn n) (hδ0 n) (originalWindowStageRootLoss n) (hroot.1 n))
  let Q : ∀ n, FiniteScalarBins range (originalWindowStageAccuracy n) := fun n ↦
    Classical.choice (exists_finiteScalarBins hrange (hacc.1 n).1)
  have hδreal n : (δn n).toReal = originalWindowStageAccuracy n :=
    ENNReal.toReal_ofReal (hacc.1 n).1.le
  have hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0) := by
    simpa only [hδreal] using hacc.2
  refine ⟨D,Q,?_⟩
  exact originalWindowRetainedPairKernel_ae_mass_recovery hrange.measurableSet γ gap hgap
    (fun _ ↦ r) δn originalWindowStageRootLoss D hcomplete
    (fun n _ ↦ originalWindowStageAccuracy n) (fun n _ ↦ Q n)
    (fun _ ↦ ENNReal.ofReal_ne_top) (fun n ↦ by rw [hδreal]; exact (hacc.1 n).2)
    hδlim (by rw [hroot.2]; norm_num)

end OTSelector.Reconstruction
