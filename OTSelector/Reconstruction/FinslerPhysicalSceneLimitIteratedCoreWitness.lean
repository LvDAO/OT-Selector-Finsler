import OTSelector.Reconstruction.FinslerPhysicalSceneRootedAverageScreenedPacking

/-!
# Core accuracy is removed after both original weak-limit stages

A fixed actual scene is estimated by auxiliary physical cores. Their retained
witness bounds vanish with the tilt while their discarded mass errors vanish
only in a final independent accuracy limit. No scene or tilt/sample diagonal
is selected when choosing these auxiliary estimates.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- Auxiliary core accuracy may depend on its own index. The original sample
limit is taken for each tilt, followed by the tilt limit, and only afterward
are the auxiliary discarded masses sent to zero on the same actual law. -/
theorem ae_eq_zero_of_iterated_weak_lsc_tilt_and_core_accuracy_bounds
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, Tendsto (φ k) atTop atTop)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ k, Tendsto (fun N ↦ Pn k (φ k N)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R))
    (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (accuracy : ℕ → ℝ≥0∞) (haccuracy : Tendsto accuracy atTop (𝓝 0))
    (hbound : ∀ m, ∃ B : ℕ → ℝ≥0∞, Tendsto B atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, ∀ᶠ N in atTop,
        (∫⁻ s, W s ∂(Pn k N : Measure S)) ≤ B k + accuracy m) :
    ∀ᵐ s ∂(R : Measure S), W s = 0 := by
  have hopen (r : ℝ≥0∞) (hr : 0 < r) (hrt : r ≠ ⊤) :
      (R : Measure S) {s | r < W s} = 0 := by
    have hb (m : ℕ) : (R : Measure S) {s | r < W s} ≤ accuracy m / r := by
      obtain ⟨B, hB, hbound⟩ := hbound m
      have hQ : ∀ᶠ k in atTop, (Q k : Measure S) {s | r < W s} ≤ (B k + accuracy m) / r := by
        filter_upwards [hbound] with k hk
        have hb : ∀ᶠ N in atTop,
            (Pn k (φ k N) : Measure S) {s | r < W s} ≤ (B k + accuracy m) / r := by
          filter_upwards [(hφ k).eventually hk] with N hN
          exact ((measure_mono (show {s | r < W s} ⊆ {s | r ≤ W s} from
            fun s hs ↦ le_of_lt (show r < W s from hs))).trans
            (meas_ge_le_lintegral_div hW.measurable.aemeasurable (ne_of_gt hr) hrt)).trans
            (ENNReal.div_le_div_right hN r)
        exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto (hinner k)
          (hW.isOpen_preimage r)).trans (liminf_le_of_frequently_le hb.frequently)
      have hdiv : Tendsto (fun k ↦ (B (ψ k) + accuracy m) / r) atTop (𝓝 (accuracy m / r)) := by
        simpa only [zero_add, Function.comp_apply] using ENNReal.Tendsto.div_const
          ((hB.comp hψ).add tendsto_const_nhds) (Or.inr (ne_of_gt hr))
      have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto houter
        (hW.isOpen_preimage r)
      have hQsub : ∀ᶠ k in atTop,
          (Q (ψ k) : Measure S) {s | r < W s} ≤ (B (ψ k) + accuracy m) / r :=
        hψ.eventually hQ
      exact hle.trans ((liminf_le_liminf hQsub).trans_eq hdiv.liminf_eq)
    have haccdiv : Tendsto (fun m ↦ accuracy m / r) atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa only [ENNReal.zero_div] using
        ENNReal.Tendsto.div_const haccuracy (Or.inr (ne_of_gt hr))
    have hle : (R : Measure S) {s | r < W s} ≤ 0 := by
      calc
        _ = atTop.liminf (fun _ : ℕ ↦ (R : Measure S) {s | r < W s}) := (liminf_const _).symm
        _ ≤ atTop.liminf (fun m ↦ accuracy m / r) := liminf_le_liminf (Eventually.of_forall hb)
        _ = _ := haccdiv.liminf_eq
    exact le_antisymm hle bot_le
  have hzero : ∀ᵐ s ∂(R : Measure S), W s ≤ 0 := by
    apply (ae_le_const_iff_forall_gt_measure_zero W 0).mpr
    intro b hb
    obtain ⟨q, _, hq0, hqb⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hb
    have hs : {s | b ≤ W s} ⊆ {s | ((q : ℝ).toNNReal : ℝ≥0∞) < W s} :=
      fun _ h ↦ hqb.trans_le h
    exact measure_mono_null hs (hopen _ hq0 ENNReal.coe_ne_top)
  exact hzero.mono fun _ h ↦ le_antisymm h bot_le

end OTSelector.Reconstruction
