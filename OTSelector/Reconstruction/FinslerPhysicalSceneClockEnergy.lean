import OTSelector.Transport.Calibration.CompactClockGap
import OTSelector.Reconstruction.FinslerPhysicalSceneRestriction
import OTSelector.Probability.CavitySemidiscreteLocalPlan

/-!
# Actual physical clock energy on restricted global allocation plans

The physical target cloud is observed from the same global allocation.  A source
cell restricts that physical plan exactly and retains its actual local column
masses.  The original compact support gap controls forbidden clock mass by
nonnegative slack energy, before any root or limiting scene is introduced.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

section AllocationPlan

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

/-- The original allocation with its actual physical target atoms. -/
def physicalSceneAllocationPlan (μ : Measure M) (a : M → Fin (n + 1) → ℝ)
    (Y : Fin (n + 1) → M) : Measure (M × M) :=
  (semidiscreteAllocationMeasure μ a).map (Prod.map id Y)

/-- Every original nonnegative physical observable has exactly its allocation
integral on the same physical target cloud. -/
theorem lintegral_physicalSceneAllocationPlan
    (μ : Measure M) (a : M → Fin (n + 1) → ℝ) (Y : Fin (n + 1) → M)
    (energy : M × M → ℝ≥0∞) (henergy : Measurable energy) :
    (∫⁻ e, energy e ∂physicalSceneAllocationPlan μ a Y) =
      ∫⁻ e, energy (e.1, Y e.2) ∂semidiscreteAllocationMeasure μ a :=
  lintegral_map henergy (measurable_id.prodMap (measurable_of_finite Y))

/-- Actual allocation feasibility supplies finiteness of the physical plan. -/
theorem finite_physicalSceneAllocationPlan
    {μ : Measure M} [IsFiniteMeasure μ] {p : Fin (n + 1) → ℝ}
    {a : M → Fin (n + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (Y : Fin (n + 1) → M) : IsFiniteMeasure (physicalSceneAllocationPlan μ a Y) := by
  have := ha.isFiniteMeasure_allocationMeasure
  unfold physicalSceneAllocationPlan
  infer_instance

/-- Restricting the original physical source restricts the same physical plan. -/
theorem physicalSceneAllocationPlan_restrict
    (μ : Measure M) (a : M → Fin (n + 1) → ℝ) (Y : Fin (n + 1) → M)
    {H : Set M} (hH : MeasurableSet H) :
    physicalSceneAllocationPlan (μ.restrict H) a Y =
      (physicalSceneAllocationPlan μ a Y).restrict (H ×ˢ univ) := by
  have hm : Measurable (Prod.map (id : M → M) Y) :=
    measurable_id.prodMap (measurable_of_finite Y)
  unfold physicalSceneAllocationPlan
  rw [semidiscreteAllocationMeasure_restrict μ a hH,
    Measure.restrict_map hm (hH.prod MeasurableSet.univ)]
  have heq : (Prod.map id Y) ⁻¹' (H ×ˢ (univ : Set M)) =
      H ×ˢ (univ : Set (Fin (n + 1))) := by ext e; simp
  rw [heq]

/-- The normalized physical cell plan has precisely the inverse actual cell-mass
factor and otherwise keeps the same restricted global plan. -/
theorem physicalSceneAllocationPlan_normalized_restrict
    (μ : Measure M) (a : M → Fin (n + 1) → ℝ) (Y : Fin (n + 1) → M)
    {H : Set M} (hH : MeasurableSet H) :
    physicalSceneAllocationPlan (normalizedFiniteLaw (μ.restrict H)) a Y =
      (((μ.restrict H).real univ)⁻¹.toNNReal : ℝ≥0∞) •
        (physicalSceneAllocationPlan μ a Y).restrict (H ×ˢ univ) := by
  unfold physicalSceneAllocationPlan
  rw [semidiscreteAllocationMeasure_normalized_restrict μ a hH, Measure.map_smul]
  congr 1
  have hm : Measurable (Prod.map (id : M → M) Y) :=
    measurable_id.prodMap (measurable_of_finite Y)
  rw [Measure.restrict_map hm (hH.prod MeasurableSet.univ)]
  congr 2

/-- The actual physical plan keeps the original source carrier and target cloud. -/
theorem ae_physicalSceneAllocationPlan_carried
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (Y : Fin (n + 1) → M)
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hYB : ∀ j, Y j ∈ B) :
    ∀ᵐ e ∂physicalSceneAllocationPlan μ a Y, e.1 ∈ A ∧ e.2 ∈ B := by
  have hm : Measurable (Prod.map (id : M → M) Y) :=
    measurable_id.prodMap (measurable_of_finite Y)
  apply (ae_map_iff hm.aemeasurable (hA.prod hB)).mpr
  have hs : ∀ᵐ e ∂semidiscreteAllocationMeasure μ a, e.1 ∈ A := by
    apply ae_of_ae_map (p := fun x ↦ x ∈ A) measurable_fst.aemeasurable
    simpa only [ha.isCoupling.1] using hμA
  exact hs.mono fun e he ↦ ⟨he, hYB e.2⟩

/-- Any nonnegative source-cell energy is bounded by the unchanged global plan. -/
theorem lintegral_physicalSceneAllocationPlan_restrict_le
    (μ : Measure M) (a : M → Fin (n + 1) → ℝ) (Y : Fin (n + 1) → M)
    {H : Set M} (hH : MeasurableSet H) (energy : M × M → ℝ≥0∞) :
    (∫⁻ e, energy e ∂physicalSceneAllocationPlan (μ.restrict H) a Y) ≤
      ∫⁻ e, energy e ∂physicalSceneAllocationPlan μ a Y := by
  rw [physicalSceneAllocationPlan_restrict μ a Y hH]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

end AllocationPlan

section Metric

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The original positive support gap controls bad-clock mass directly by the
nonnegative physical plan energy, with no real integrability requirement. -/
theorem originalClockBadEvent_mass_mul_le_lintegral
    (Γ : Measure (M × M)) {A B : Set M} {gap scale : ℝ}
    (hscale : 0 ≤ scale) (hgap : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hcarried : ∀ᵐ e ∂Γ, e.1 ∈ A ∧ e.2 ∈ B)
    {u : M → ℝ} (hu : LipschitzWith 1 u) :
    ENNReal.ofReal (scale * (gap / 2)) * Γ (originalClockBadEvent u gap) ≤
      ∫⁻ e, ENNReal.ofReal (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ := by
  have hpoint : (originalClockBadEvent u gap).indicator
      (fun _ ↦ ENNReal.ofReal (scale * (gap / 2))) ≤ᵐ[Γ]
        fun e ↦ ENNReal.ofReal (scale * (dist e.1 e.2 - u e.2 + u e.1)) := by
    filter_upwards [hcarried] with e he
    by_cases hbad : e ∈ originalClockBadEvent u gap
    · rw [indicator_of_mem hbad]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (originalClockBadEvent_slack_gap hgap he.1 he.2 hbad) hscale)
    · rw [indicator_of_notMem hbad]
      exact zero_le
  have h := lintegral_mono_ae hpoint
  rwa [lintegral_indicator_const (measurableSet_originalClockBadEvent hu gap)] at h

/-- Positive scaling gives the original quantitative forbidden-clock tail. -/
theorem originalClockBadEvent_mass_le_lintegral_div
    (Γ : Measure (M × M)) {A B : Set M} {gap scale : ℝ}
    (hscale : 0 < scale) (hgap : 0 < gap)
    (hdist : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hcarried : ∀ᵐ e ∂Γ, e.1 ∈ A ∧ e.2 ∈ B)
    {u : M → ℝ} (hu : LipschitzWith 1 u) :
    Γ (originalClockBadEvent u gap) ≤
      (∫⁻ e, ENNReal.ofReal (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ) /
        ENNReal.ofReal (scale * (gap / 2)) := by
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hscale (half_pos hgap))))
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [mul_comm]
  exact originalClockBadEvent_mass_mul_le_lintegral Γ hscale.le hdist hcarried hu

end Metric
end OTSelector.Reconstruction
