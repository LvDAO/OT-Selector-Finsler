import OTSelector.MeasureTheory.NonproperProbeCutoffLoss
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonproperExhaustion

/-!
# Actual macroscopic clock probes and nonproper target cutoffs

A compact source spatial probe and the two unchanged physical clocks can be
read from the full original plan. Actual target escape pays the cutoff error.
-/
open Set Function MeasureTheory OTSelector.Probability
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]
local notation "V" => (ι → ℝ)
local notation "Point" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Point × Point)

/-- The full macro-clock probe's target cutoff error pays only the same plan's
actual escape over its source spatial support. -/
theorem lintegral_macro_clockProbe_cutoff_error_le_escape
    (π : Measure Edge) (w : V) (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ))
    (χ : Point → ℝ) (hχ : ∀ y, χ y ∈ Icc 0 1)
    (K : Set Point) (hK : MeasurableSet K) (hχK : EqOn χ 1 K) :
    (∫⁻ e, ENNReal.ofReal
      |η e.1.1 * g (w, (e.1.2, e.2.2)) -
        (η e.1.1 * g (w, (e.1.2, e.2.2))) * χ e.2| ∂π) ≤
      ENNReal.ofReal (‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖) *
        π ((tsupport η ×ˢ univ) ×ˢ Kᶜ) := by
  apply lintegral_bounded_probe_cutoff_error_le_escape π
    (fun e ↦ η e.1.1 * g (w, (e.1.2, e.2.2)))
    (‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖)
  · intro e
    rw [abs_mul]
    have hη := η.toBoundedContinuousFunction.norm_coe_le_norm e.1.1
    have hg := g.toBoundedContinuousFunction.norm_coe_le_norm (w, (e.1.2, e.2.2))
    change ‖η e.1.1‖ ≤ _ at hη
    change ‖g (w, (e.1.2, e.2.2))‖ ≤ _ at hg
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hη)
      (by simpa only [Real.norm_eq_abs] using hg) (abs_nonneg _) (norm_nonneg _)
  · exact (isClosed_tsupport η).measurableSet.prod MeasurableSet.univ
  · intro e he
    have hpos : e.1.1 ∉ tsupport η := fun h ↦ he ⟨h, mem_univ _⟩
    rw [image_eq_zero_of_notMem_tsupport hpos, zero_mul]
  · exact hχ
  · exact hK
  · exact hχK

/-- A genuine compact exhaustion removes targets using the actual original
clock carrier. The source radius and clock radius are chosen internally. -/
theorem exists_macro_clockProbe_cutoff_error_le_longTail
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ))
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ W C : ℝ, ∀ (π : Measure Edge), (∀ᵐ e ∂π, e.2.2 ∈ J) →
      ∀ (w : V) (n : ℕ),
      (∫⁻ e, ENNReal.ofReal
        |η e.1.1 * g (w, (e.1.2, e.2.2)) -
          (η e.1.1 * g (w, (e.1.2, e.2.2))) *
            LocalFiniteMeasure.exhaustionCutoff (physicalSceneSpatialClockExhaustion W C) n e.2|
              ∂π) ≤
        ENNReal.ofReal (‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖) *
          π (physicalSceneLongEdgeWindow (tsupport η) (ENNReal.ofReal (((n : ℝ) + 1) ^ 2))) := by
  obtain ⟨W, hW⟩ := η.hasCompactSupport.isCompact.isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := hJ.isBounded.exists_norm_le
  have hclock : ∀ t ∈ J, ‖t‖ ≤ |C| + 1 := fun t ht ↦
    (hC t ht).trans ((le_abs_self C).trans (by linarith))
  have hsp : ∀ v ∈ tsupport η, ‖v‖ ≤ |W| := fun v hv ↦
    (hW v hv).trans (le_abs_self W)
  refine ⟨W, C, ?_⟩
  intro π hπ w n
  have hb := lintegral_macro_clockProbe_cutoff_error_le_escape π w η g
    (LocalFiniteMeasure.exhaustionCutoff (physicalSceneSpatialClockExhaustion W C) n)
    (LocalFiniteMeasure.exhaustionCutoff_bounds _ _) _
    ((physicalSceneSpatialClockExhaustion (ι := ι) W C).isCompact n).measurableSet
    (LocalFiniteMeasure.exhaustionCutoff_eq_one _ _)
  have htail : π ((tsupport η ×ˢ univ) ×ˢ
      (physicalSceneSpatialClockExhaustion (ι := ι) W C n)ᶜ) ≤
      π (physicalSceneLongEdgeWindow (tsupport η) (ENNReal.ofReal (((n : ℝ) + 1) ^ 2))) := by
    have hsub : (tsupport η ×ˢ (univ : Set ℝ)) ×ˢ
        (physicalSceneSpatialClockExhaustion (ι := ι) W C n)ᶜ ⊆
        (tsupport η ×ˢ univ) ×ˢ (physicalSceneSpatialClockCutoff |W| (n + 1) J)ᶜ := by
      intro e he
      exact ⟨he.1, fun h ↦ he.2 (physicalSceneSpatialClockCutoff_subset_exhaustion W C hclock n h)⟩
    exact (measure_mono hsub).trans
      (physicalScene_escape_compact_le_longTail π hsp (by positivity) hπ)
  refine hb.trans ?_
  simpa only [mul_comm] using mul_le_mul_right htail
    (ENNReal.ofReal (‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖))

/-- The target escape can be taken open in the whole edge space. This lets
its actual expected mass pass through both vague weak limits by Portmanteau. -/
theorem exists_open_macro_clockProbe_target_cutoff
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ))
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ W C : ℝ, let U := Metric.ball (0 : V) (|W| + 1)
      let K := physicalSceneSpatialClockExhaustion (ι := ι) (|W| + 1) C
      (∀ n, IsOpen ((U ×ˢ (univ : Set ℝ)) ×ˢ (K n)ᶜ)) ∧
      ∀ (π : Measure Edge) (w : V) (n : ℕ),
      (∫⁻ e, ENNReal.ofReal
        |η e.1.1 * g (w, (e.1.2, e.2.2)) -
          (η e.1.1 * g (w, (e.1.2, e.2.2))) *
            LocalFiniteMeasure.exhaustionCutoff K n e.2| ∂π) ≤
        ENNReal.ofReal (‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖) *
          π ((U ×ˢ univ) ×ˢ (K n)ᶜ) ∧
      ((∀ᵐ e ∂π, e.2.2 ∈ J) →
        π ((U ×ˢ univ) ×ˢ (K n)ᶜ) ≤
          π (physicalSceneLongEdgeWindow U (ENNReal.ofReal (((n : ℝ) + 1) ^ 2)))) := by
  obtain ⟨W, hW⟩ := η.hasCompactSupport.isCompact.isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := hJ.isBounded.exists_norm_le
  have hclock : ∀ t ∈ J, ‖t‖ ≤ |C| + 1 := fun t ht ↦
    (hC t ht).trans ((le_abs_self C).trans (by linarith))
  let U := Metric.ball (0 : V) (|W| + 1)
  let K := physicalSceneSpatialClockExhaustion (ι := ι) (|W| + 1) C
  have hηU : tsupport η ⊆ U := by
    intro v hv
    change dist v 0 < |W| + 1
    rw [dist_zero_right]
    linarith [(hW v hv).trans (le_abs_self W)]
  have hsp : ∀ v ∈ U, ‖v‖ ≤ |(|W| + 1)| := by
    intro v hv
    have hv' : ‖v‖ < |W| + 1 := by simpa only [U, Metric.mem_ball, dist_zero_right] using hv
    exact hv'.le.trans (le_abs_self _)
  refine ⟨W, C, ?_, ?_⟩
  · intro n
    exact (Metric.isOpen_ball.prod isOpen_univ).prod (K.isCompact n).isClosed.isOpen_compl
  · intro π w n
    constructor
    · have hb := lintegral_macro_clockProbe_cutoff_error_le_escape π w η g
        (LocalFiniteMeasure.exhaustionCutoff K n) (LocalFiniteMeasure.exhaustionCutoff_bounds _ _)
        _ (K.isCompact n).measurableSet (LocalFiniteMeasure.exhaustionCutoff_eq_one _ _)
      apply hb.trans
      have hm : π ((tsupport η ×ˢ univ) ×ˢ (K n)ᶜ) ≤ π ((U ×ˢ univ) ×ˢ (K n)ᶜ) :=
        measure_mono (prod_mono (prod_mono hηU subset_rfl) subset_rfl)
      simpa only [mul_comm] using mul_le_mul_right hm
        (ENNReal.ofReal (‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖))
    · intro hπ
      have hsub : (U ×ˢ (univ : Set ℝ)) ×ˢ (K n)ᶜ ⊆
          (U ×ˢ univ) ×ˢ (physicalSceneSpatialClockCutoff |(|W| + 1)| (n + 1) J)ᶜ := by
        intro e he
        exact ⟨he.1, fun h ↦ he.2
          (physicalSceneSpatialClockCutoff_subset_exhaustion (|W| + 1) C hclock n h)⟩
      exact (measure_mono hsub).trans
        (physicalScene_escape_compact_le_longTail π hsp (by positivity) hπ)

end OTSelector.Reconstruction
