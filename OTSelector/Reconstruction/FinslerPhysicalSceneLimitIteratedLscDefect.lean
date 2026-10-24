import OTSelector.MeasureTheory.IteratedWeakLscDefect
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedCoreWitness

/-!
Conditions: Two levels of actual weak probability convergence, a nonnegative lower-semicontinuous defect and the stated eventual integral loss/tilt/sample bound.

Objects: A limiting defect-tail bound loss divided by any positive finite level.

Proof detail: Pass to the lower-semicontinuous integral inequality at each weak limit, let both error scales vanish and apply Markov to the limit.

Sources: D. H. Fremlin, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation (https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61); Rick Durrett, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37).
Relation: Iterated Portmanteau/Markov consequence; no exchange of the two limits or uniform-integrability premise is inserted.
-/

/-!
# Separate sample and tilt errors in the same limiting scene

A fixed original core's population loss remains explicit. The original energy
error vanishes first with the sample size at each fixed tilt. The tilt error
vanishes only in the subsequent outer limit. No diagonal law is introduced.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]



/-- A fixed positive physical margin cancels before passing to the two weak
limits. The sample error and the tilt error are still taken separately. -/
theorem measure_lsc_gt_le_of_iterated_weak_weighted_sample_tilt_defect_bounds
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, Tendsto (φ k) atTop atTop)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ k, Tendsto (fun N ↦ Pn k (φ k N)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R))
    (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (weight loss : ℝ≥0∞) (hw0 : weight ≠ 0) (hwt : weight ≠ ⊤)
    (tilt sample : ℕ → ℝ≥0∞)
    (htilt : Tendsto tilt atTop (𝓝 0)) (hsample : Tendsto sample atTop (𝓝 0))
    (hbound : ∀ᶠ k in atTop, ∀ᶠ N in atTop,
      weight * (∫⁻ s, W s ∂(Pn k N : Measure S)) ≤ tilt k + weight * (loss + sample N))
    (r : ℝ≥0∞) (hr : 0 < r) (hrt : r ≠ ⊤) :
    (R : Measure S) {s | r < W s} ≤ loss / r := by
  apply measure_lsc_gt_le_of_iterated_weak_sample_tilt_defect_bounds
    Pn Q R φ hφ ψ hψ hinner houter W hW loss
    (fun k ↦ tilt k / weight) sample ?_ hsample ?_ r hr hrt
  · simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const htilt (Or.inr hw0)
  · filter_upwards [hbound] with k hk
    filter_upwards [hk] with N hN
    apply (ENNReal.mul_le_mul_iff_right hw0 hwt).mp
    simpa only [mul_add, ENNReal.mul_div_cancel hw0 hwt, add_assoc] using hN

/-- Every auxiliary estimate addresses the SAME two-index original scene and
its SAME limiting law. Only afterward does its independent core loss vanish. -/
theorem ae_eq_zero_of_iterated_weak_sample_tilt_core_accuracy_bounds
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, Tendsto (φ k) atTop atTop)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ k, Tendsto (fun N ↦ Pn k (φ k N)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R))
    (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (loss : ℕ → ℝ≥0∞) (hloss : Tendsto loss atTop (𝓝 0))
    (hbound : ∀ m, ∃ tilt sample : ℕ → ℝ≥0∞,
      Tendsto tilt atTop (𝓝 0) ∧ Tendsto sample atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, ∀ᶠ N in atTop,
        (∫⁻ s, W s ∂(Pn k N : Measure S)) ≤ tilt k + loss m + sample N) :
    ∀ᵐ s ∂(R : Measure S), W s = 0 := by
  have hopen (r : ℝ≥0∞) (hr : 0 < r) (hrt : r ≠ ⊤) :
      (R : Measure S) {s | r < W s} = 0 := by
    have hb (m : ℕ) : (R : Measure S) {s | r < W s} ≤ loss m / r := by
      obtain ⟨tilt, sample, ht, hs, hbound⟩ := hbound m
      exact measure_lsc_gt_le_of_iterated_weak_sample_tilt_defect_bounds
        Pn Q R φ hφ ψ hψ hinner houter W hW (loss m) tilt sample ht hs hbound r hr hrt
    have hdiv : Tendsto (fun m ↦ loss m / r) atTop (𝓝 0) := by
      simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hloss (Or.inr hr.ne')
    apply le_antisymm _ bot_le
    calc
      _ = atTop.liminf (fun _ : ℕ ↦ (R : Measure S) {s | r < W s}) := (liminf_const _).symm
      _ ≤ atTop.liminf (fun m ↦ loss m / r) := liminf_le_liminf (Eventually.of_forall hb)
      _ = 0 := hdiv.liminf_eq
  have hz : ∀ᵐ s ∂(R : Measure S), W s ≤ 0 := by
    apply (ae_le_const_iff_forall_gt_measure_zero W 0).mpr
    intro b hb
    obtain ⟨q, _, hq0, hqb⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hb
    have hsub : {s | b ≤ W s} ⊆ {s | ((q : ℝ).toNNReal : ℝ≥0∞) < W s} :=
      fun _ hs ↦ hqb.trans_le hs
    exact measure_mono_null hsub (hopen _ hq0 ENNReal.coe_ne_top)
  exact hz.mono fun _ hs ↦ le_antisymm hs bot_le

end OTSelector.Reconstruction
