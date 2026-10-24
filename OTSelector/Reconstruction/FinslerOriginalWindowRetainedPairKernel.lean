import OTSelector.Reconstruction.OriginalWindowRetainedPairKernel
import OTSelector.Reconstruction.FinslerOriginalWindowContinuousClockLaw
import OTSelector.MeasureTheory.RetainedLawVariation
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! Actual finite original coefficient windows produce their own measurable
retained conditional pair kernels and original-root mass recovery. -/
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

/-- The actual finite original core retains the unchanged conditional pairing
on its literal continuous clock mask; outside the original cores its mass is zero. -/
def PopulationLocalPressureCore.originalWindowRetainedPairKernel
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {range : Set ℝ} {width : Fin D.haar.continuous.count → ℝ}
    (Q : ∀ i, FiniteScalarBins range (width i)) (γ : Kernel (ℚ → M) (ℝ × ℝ)) :
    Kernel (ℚ → M) (ℝ × ℝ) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  exact originalFiniteClockMaskPairKernel (fun i ↦ (D.haar.continuous.coefficient i).roots)
    (fun i ↦ (D.haar.continuous.coefficient i).roots_compact.measurableSet)
    Q (fun i ↦ (D.haar.continuous.coefficient i).clockClassAllowed (Q i)) γ

/-- The actual retained window law is always an original conditional sublaw. -/
theorem PopulationLocalPressureCore.originalWindowRetainedPairKernel_le
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {range : Set ℝ} {width : Fin D.haar.continuous.count → ℝ}
    (Q : ∀ i, FiniteScalarBins range (width i)) (γ : Kernel (ℚ → M) (ℝ × ℝ)) (z : ℚ → M) :
    D.originalWindowRetainedPairKernel hcomplete Q γ z ≤ γ z := by
  exact originalFiniteClockMaskPairKernel_le _ _ D.haar.continuous.disjoint _ _ _ z

instance PopulationLocalPressureCore.originalWindowRetainedPairKernel_finite
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {range : Set ℝ} {width : Fin D.haar.continuous.count → ℝ}
    (Q : ∀ i, FiniteScalarBins range (width i)) (γ : Kernel (ℚ → M) (ℝ × ℝ))
    [IsMarkovKernel γ] (z : ℚ → M) :
    IsFiniteMeasure (D.originalWindowRetainedPairKernel hcomplete Q γ z) :=
  isFiniteMeasure_of_le (γ z) (D.originalWindowRetainedPairKernel_le hcomplete Q γ z)

/-- The retained mass bound is derived from the SAME original clock coupling
and original stored window loss at every retained root, without a callback. -/
theorem PopulationLocalPressureCore.originalWindowRetainedPairKernel_mass_lower
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {width : Fin D.haar.continuous.count → ℝ} (Q : ∀ i, FiniteScalarBins range (width i))
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (i : Fin D.haar.continuous.count) (z : ℚ → M)
    (hz : z ∈ (D.haar.continuous.coefficient i).roots) :
    1 - δ.toReal ≤ (D.originalWindowRetainedPairKernel hcomplete Q γ z).real univ := by
  have heq : D.originalWindowRetainedPairKernel hcomplete Q γ z =
      (γ z).restrict ((Q i).originalClockMaskSet
        ((D.haar.continuous.coefficient i).clockClassAllowed (Q i))) :=
    originalFiniteClockMaskPairKernel_eq_on_cell _ _ D.haar.continuous.disjoint _ _ _ i z hz
  rw [heq]
  obtain ⟨π,hπ,hmap,hlower,_⟩ := D.exists_original_window_continuous_clock_law
    hrange γ gap i ⟨z,hz⟩ (Q i) (by norm_num : (0:ℝ) < 1) hgap hδ hδ1
  have hm := (Q i).real_restrict_originalClockMaskSet_eq
    ((D.haar.continuous.coefficient i).clockClassAllowed (Q i)) π
  rw [hmap] at hm
  rw [hm]
  exact hlower

/-- Actual finite core/window refinements produce retained original kernels
with rootwise full mass recovery. Summable ORIGINAL root losses give eventual
core membership by Borel-Cantelli; the original window losses give the rest.
No uniform conditional density, positive retained mass or fixed geometry is assumed. -/
theorem originalWindowRetainedPairKernel_ae_mass_recovery
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (hgap : 0 ≤ gap)
    (rn : ℕ → ℝ) (δn lossn : ℕ → ℝ≥0∞)
    (D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      (rn n) (δn n) (lossn n))
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (width : ∀ n, Fin (D n).haar.continuous.count → ℝ)
    (Q : ∀ n i, FiniteScalarBins range (width n i))
    (hδ : ∀ n, δn n ≠ ⊤) (hδ1 : ∀ n, (δn n).toReal < 1)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤) :
    (∀ n z, (D n).originalWindowRetainedPairKernel hcomplete (Q n) γ z ≤ γ z) ∧
    ∀ᵐ z ∂μ.map a, Tendsto
      (fun n ↦ ((D n).originalWindowRetainedPairKernel hcomplete (Q n) γ z).real univ)
      atTop (𝓝 1) := by
  refine ⟨fun n z ↦ (D n).originalWindowRetainedPairKernel_le hcomplete (Q n) γ z,?_⟩
  have hsum : (∑' n, (μ.map a) ((D n).haar.continuous.population.roots)ᶜ) ≠ ⊤ :=
    ne_top_of_le_ne_top hloss (ENNReal.tsum_le_tsum fun n ↦
      (D n).haar.continuous.population.complement_small.le)
  filter_upwards [ae_eventually_notMem hsum] with z hz
  apply tendsto_submeasure_mass_of_lost_mass (γ z)
    (fun n ↦ (D n).originalWindowRetainedPairKernel hcomplete (Q n) γ z) atTop
    (fun n ↦ (δn n).toReal) hδlim
  filter_upwards [hz] with n hn
  have hzin : z ∈ (D n).haar.continuous.population.roots := by
    simpa only [mem_compl_iff,not_not] using hn
  have hroot : z ∈ ⋃ i, ((D n).haar.continuous.coefficient i).roots :=
    (D n).haar.continuous.union_eq.symm ▸ hzin
  obtain ⟨i,hi⟩ := mem_iUnion.mp hroot
  exact ⟨(D n).originalWindowRetainedPairKernel_le hcomplete (Q n) γ z,
    (D n).originalWindowRetainedPairKernel_mass_lower hrange γ gap hcomplete (Q n)
      hgap (hδ n) (hδ1 n) i z hi⟩

end OTSelector.Reconstruction
