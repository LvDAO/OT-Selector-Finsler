import OTSelector.MeasureTheory.ProjectedRetainedAccuracy

/-! Local compact masses make product-cycle errors vanish on one fixed projection. -/
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Each actual auxiliary core may change its retained/lost extension. A local
full-mass cutoff is chosen on the SAME full projection, then core accuracy tends
to zero; exhausting the cutoff removes the full strict-cycle witness. -/
theorem ae_eq_zero_of_projected_cycle_retained_zero_and_lost_accuracy
    (R : ProbabilityMeasure Y) (Raux : ℕ → ProbabilityMeasure X)
    (f : X → Y) (hf : Measurable f)
    (hmap : ∀ m, (Raux m).map hf.aemeasurable = R)
    (W mass : Y → ℝ≥0∞) (hW : Measurable W) (hmass : Measurable mass)
    (hfinite : ∀ᵐ y ∂(R : Measure Y), mass y ≠ ⊤)
    (retained lost : ℕ → X → ℝ≥0∞)
    (hdom : ∀ m, ∀ᵐ s ∂(Raux m : Measure X),
      W (f s) ≤ retained m s + 2 * mass (f s) * lost m s)
    (hretained : ∀ m, ∀ᵐ s ∂(Raux m : Measure X), retained m s = 0)
    (accuracy : ℕ → ℝ≥0∞) (haccuracy : Tendsto accuracy atTop (𝓝 0))
    (hlost : ∀ (m : ℕ) (level : ℝ≥0∞), 0 < level → level ≠ ⊤ →
      (Raux m : Measure X) {s | level < lost m s} ≤ accuracy m / level) :
    ∀ᵐ y ∂(R : Measure Y), W y = 0 := by
  have hcutoff (n : ℕ) : ∀ᵐ y ∂(R : Measure Y),
      (if mass y ≤ (n : ℝ≥0∞) + 1 then W y / (2 * ((n : ℝ≥0∞) + 1)) else 0) = 0 := by
    have hα0 : 2 * ((n : ℝ≥0∞) + 1) ≠ 0 := by positivity
    have hαtop : 2 * ((n : ℝ≥0∞) + 1) ≠ ⊤ := by finiteness
    apply ae_eq_zero_of_projected_retained_zero_and_lost_accuracy
      R Raux f hf hmap _
      (Measurable.ite (measurableSet_le hmass measurable_const) (hW.div_const _) measurable_const)
      (fun _ _ ↦ 0) lost ?_ (fun _ ↦ ae_of_all _ fun _ ↦ rfl) accuracy haccuracy hlost
    intro m
    filter_upwards [hdom m, hretained m] with s hs hr
    rw [hr, zero_add] at hs
    by_cases hcut : mass (f s) ≤ (n : ℝ≥0∞) + 1
    · rw [ite_eq_left hcut, zero_add]
      apply (ENNReal.div_le_iff' hα0 hαtop).mpr
      exact hs.trans (by gcongr)
    · rw [ite_eq_right hcut, zero_add]
      exact bot_le
  have hall : ∀ᵐ y ∂(R : Measure Y), ∀ n : ℕ,
      (if mass y ≤ (n : ℝ≥0∞) + 1 then W y / (2 * ((n : ℝ≥0∞) + 1)) else 0) = 0 :=
    ae_all_iff.mpr hcutoff
  filter_upwards [hall, hfinite] with y hy hfin
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin
  have hle : mass y ≤ (n : ℝ≥0∞) + 1 := hn.le.trans (le_add_right le_rfl)
  have hz := hy n
  rw [ite_eq_left hle] at hz
  exact (ENNReal.div_eq_zero_iff.mp hz).resolve_right (by finiteness)
end OTSelector.Reconstruction
