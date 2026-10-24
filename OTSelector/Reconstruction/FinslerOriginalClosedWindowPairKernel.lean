import OTSelector.Reconstruction.FinslerOriginalFineWindowLawConvergence
import OTSelector.Reconstruction.FinslerOriginalWindowRetainedPairKernel

/-! One canonical original closed-window subkernel is chosen before all fine
bins. The actual original-gap certificate makes every full endpoint mask
exactly this same retained law; later reference partitions cannot change it. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The original conditional gap and full endpoint certificate identify a
fine mask with the SAME closed window, as an exact original joint measure. -/
theorem OriginalPopulationCoefficientCore.original_full_mask_restrict_eq_window
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (π : Measure (ℝ × ℝ))
    (hrange : ∀ᵐ p ∂π, p.1 ∈ range ∧ p.2 ∈ range)
    (hgap : ∀ᵐ p ∂π, (C.window.val.2.2 : ℝ) ≤ p.2 - p.1)
    (hfull : ∀ i j, C.clockClassAllowed Q i j → ∀ x ∈ Q.cell i, ∀ y ∈ Q.cell j,
      x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
      y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y) :
    π.restrict (Q.originalClockMaskSet (C.clockClassAllowed Q)) = π.restrict C.window.region := by
  apply Measure.restrict_congr_set
  filter_upwards [hrange,hgap] with p hp hg
  apply propext
  constructor
  · rintro ⟨i,j,hij,hi,hj⟩
    have hh := hfull i j hij p.1 hi p.2 hj
    exact ⟨⟨hh.1,hh.2.1⟩,hg⟩
  · intro hmem
    change p ∈ Q.originalClockMaskSet (Q.regionClockAllowed C.window.region)
    exact Q.mem_originalClockMaskSet_of_mem_region hp hmem

variable {a : M → (ℚ → M)}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {loss : ℝ≥0∞}

/-- The original fixed closed-window pair law, independent of all cost bins,
reference centers, cutoff choices, and normalized probability conventions. -/
def PopulationLocalPressureCore.originalClosedWindowPairKernel
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) : Kernel (ℚ → M) (ℝ × ℝ) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  exact finiteCellPairKernel (fun i ↦ (D.haar.continuous.coefficient i).roots)
    (fun i ↦ (D.haar.continuous.coefficient i).roots_compact.measurableSet)
    (fun i ↦ γ.restrict (D.haar.continuous.coefficient i).window.isCompact_region.measurableSet)

/-- At every active original root this is exactly its closed-window restriction. -/
theorem PopulationLocalPressureCore.originalClosedWindowPairKernel_eq_on_piece
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (γ : Kernel (ℚ → M) (ℝ × ℝ))
    (i : Fin D.haar.continuous.count) (z : ℚ → M)
    (hz : z ∈ (D.haar.continuous.coefficient i).roots) :
    D.originalClosedWindowPairKernel hcomplete γ z =
      (γ z).restrict (D.haar.continuous.coefficient i).window.region :=
  finiteCellPairKernel_eq _ _ D.haar.continuous.disjoint _ i hz

/-- The fixed canonical retained law always remains a sublaw of the unchanged
original conditional coupling. -/
theorem PopulationLocalPressureCore.originalClosedWindowPairKernel_le
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) (z : ℚ → M) :
    D.originalClosedWindowPairKernel hcomplete γ z ≤ γ z := by
  by_cases hz : z ∈ ⋃ i, (D.haar.continuous.coefficient i).roots
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    rw [D.originalClosedWindowPairKernel_eq_on_piece hcomplete γ i z hi]
    exact Measure.restrict_le_self
  · have heq : D.originalClosedWindowPairKernel hcomplete γ z = 0 :=
      finiteCellPairKernel_eq_zero _ _ _ hz
    rw [heq]
    exact bot_le

instance PopulationLocalPressureCore.originalClosedWindowPairKernel_finite
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (z : ℚ → M) :
    IsFiniteMeasure (D.originalClosedWindowPairKernel hcomplete γ z) :=
  isFiniteMeasure_of_le (γ z) (D.originalClosedWindowPairKernel_le hcomplete γ z)

/-- The stored ORIGINAL coupling-loss bound internally gives positive canonical
window mass. No fine partition or supplied mass lower bound is needed. -/
theorem PopulationLocalPressureCore.originalClosedWindowPairKernel_mass_lower
    {range : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤)
    (i : Fin D.haar.continuous.count) (z : (D.haar.continuous.coefficient i).roots) :
    1 - δ.toReal < (D.originalClosedWindowPairKernel hcomplete γ z.val).real univ := by
  let C := D.haar.continuous.coefficient i
  have hz : z.val ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,z.property⟩
  have hgood := (D.haar.continuous.population.good z.val hz).1
  have horder : ∀ᵐ p ∂γ z.val, p.1 ≤ p.2 :=
    hgood.2.1.mono (fun _ h ↦ sub_nonneg.mp (hgap.trans h))
  have hloss := C.coupling_loss z.val z.property (γ z.val) hgood.1 horder
  have hr : (γ z.val).real C.window.regionᶜ < δ.toReal :=
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) hδ).mpr hloss
  rw [probReal_compl_eq_one_sub C.window.isCompact_region.measurableSet] at hr
  rw [D.originalClosedWindowPairKernel_eq_on_piece hcomplete γ i z.val z.property,
    measureReal_def,Measure.restrict_apply_univ]
  change 1 - δ.toReal < (γ z.val).real C.window.region
  linarith only [hr]

/-- For the gap-certified original core, every actual full endpoint mask
is exactly its canonical window law at that root. Fine bins may be chosen
later at any reference root of the same coefficient piece. -/
theorem PopulationLocalPressureCore.originalWindowRetainedPairKernel_eq_closed_window
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {width : Fin D.haar.continuous.count → ℝ} (Q : ∀ i, FiniteScalarBins range (width i))
    (i : Fin D.haar.continuous.count) (z : (D.haar.continuous.coefficient i).roots)
    (hwindowGap : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q i) j k →
      ∀ x ∈ (Q i).cell j, ∀ y ∈ (Q i).cell k,
        x ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        y ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧ x < y) :
    D.originalWindowRetainedPairKernel hcomplete Q γ z.val =
      D.originalClosedWindowPairKernel hcomplete γ z.val := by
  have hz : z.val ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,z.property⟩
  have hgood := (D.haar.continuous.population.good z.val hz).1
  rw [show D.originalWindowRetainedPairKernel hcomplete Q γ z.val =
      (γ z.val).restrict ((Q i).originalClockMaskSet
        ((D.haar.continuous.coefficient i).clockClassAllowed (Q i))) from
    originalFiniteClockMaskPairKernel_eq_on_cell _ _ D.haar.continuous.disjoint _ _ _ i z.val z.property,
    D.originalClosedWindowPairKernel_eq_on_piece hcomplete γ i z.val z.property]
  exact (D.haar.continuous.coefficient i).original_full_mask_restrict_eq_window (Q i) (γ z.val)
    (D.original_pair_range_support hrange γ gap i z)
    (hgood.2.1.mono (fun _ h ↦ hwindowGap.trans h)) hfull

/-- Actual original window losses and summable root losses produce full-mass
recovery of the canonical kernels, before any fine bins are selected. -/
theorem originalClosedWindowPairKernel_ae_mass_recovery
    {range : Set ℝ}
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (hgap : 0 ≤ gap)
    (rn : ℕ → ℝ) (δn lossn : ℕ → ℝ≥0∞)
    (D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      (rn n) (δn n) (lossn n))
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hδ : ∀ n, δn n ≠ ⊤)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤) :
    (∀ n z, (D n).originalClosedWindowPairKernel hcomplete γ z ≤ γ z) ∧
    ∀ᵐ z ∂μ.map a, Tendsto
      (fun n ↦ ((D n).originalClosedWindowPairKernel hcomplete γ z).real univ)
      atTop (𝓝 1) := by
  refine ⟨fun n z ↦ (D n).originalClosedWindowPairKernel_le hcomplete γ z,?_⟩
  have hsum : (∑' n, (μ.map a) ((D n).haar.continuous.population.roots)ᶜ) ≠ ⊤ :=
    ne_top_of_le_ne_top hloss (ENNReal.tsum_le_tsum fun n ↦
      (D n).haar.continuous.population.complement_small.le)
  filter_upwards [ae_eventually_notMem hsum] with z hz
  apply tendsto_submeasure_mass_of_lost_mass (γ z)
    (fun n ↦ (D n).originalClosedWindowPairKernel hcomplete γ z) atTop
    (fun n ↦ (δn n).toReal) hδlim
  filter_upwards [hz] with n hn
  have hzin : z ∈ (D n).haar.continuous.population.roots := by
    simpa only [mem_compl_iff,not_not] using hn
  have hroot : z ∈ ⋃ i, ((D n).haar.continuous.coefficient i).roots :=
    (D n).haar.continuous.union_eq.symm ▸ hzin
  obtain ⟨i,hi⟩ := mem_iUnion.mp hroot
  exact ⟨(D n).originalClosedWindowPairKernel_le hcomplete γ z,
    ((D n).originalClosedWindowPairKernel_mass_lower γ hcomplete hgap (hδ n) i ⟨z,hi⟩).le⟩

end OTSelector.Reconstruction
