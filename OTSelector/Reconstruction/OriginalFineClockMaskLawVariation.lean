import OTSelector.Reconstruction.OriginalFineClockMaskConvergence
import OTSelector.MeasureTheory.RetainedLawVariation

/-! Actual original fine-mask laws converge in signed variation before and
after normalization, retaining boundary mass and the original conditional law. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal Classical symmDiff
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Fine mask restrictions contain the original region restriction on its
actual scalar support. This compares the unchanged original measures. -/
theorem originalFineClockMask_restrict_le
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (region : Set (ℝ × ℝ)) (π : Measure (ℝ × ℝ))
    (hrange : ∀ᵐ p ∂π, p.1 ∈ range ∧ p.2 ∈ range) :
    π.restrict region ≤ π.restrict (Q.originalClockMaskSet (Q.regionClockAllowed region)) := by
  apply Measure.restrict_mono_ae
  exact hrange.mono (fun _ hp hmem ↦ Q.mem_originalClockMaskSet_of_mem_region hp hmem)

/-- Larger finite original laws with recovering mass converge in raw variation.
The common submeasure is the unchanged original target law. -/
theorem tendsto_totalVariation_supermeasure_of_mass
    {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)]
    (ν : Measure X) [IsFiniteMeasure ν] (hle : ∀ n, ν ≤ μ n)
    (hmass : Tendsto (fun n ↦ (μ n).real univ) atTop (𝓝 (ν.real univ))) :
    Tendsto (fun n ↦ ((μ n).toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
  have heq n : ((μ n).toSignedMeasure - ν.toSignedMeasure).totalVariation = μ n - ν := by
    rw [SignedMeasure.totalVariation,Measure.toJordanDecomposition_toSignedMeasure_sub]
    change (μ n - ν) + (ν - μ n) = μ n - ν
    rw [Measure.sub_eq_zero_of_le (hle n),add_zero]
  have hreal n : ((μ n).toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ =
      (μ n).real univ - ν.real univ := by
    rw [heq,measureReal_def,Measure.sub_apply MeasurableSet.univ (hle n),
      ENNReal.toReal_sub_of_le (hle n univ) (measure_ne_top _ _)]
    rfl
  simpa only [hreal,sub_self] using hmass.sub_const (ν.real univ)

/-- Normalization preserves convergence of these actual positive retained laws;
its inverse mass is controlled by the fixed nonzero original window mass. -/
theorem tendsto_totalVariation_normalized_supermeasure_of_mass
    {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)]
    (ν : Measure X) [IsFiniteMeasure ν] (hle : ∀ n, ν ≤ μ n)
    (hν : 0 < ν.real univ)
    (hmass : Tendsto (fun n ↦ (μ n).real univ) atTop (𝓝 (ν.real univ))) :
    Tendsto (fun n ↦ ((normalizedFiniteLaw (μ n)).toSignedMeasure -
      (normalizedFiniteLaw ν).toSignedMeasure).totalVariation.real univ) atTop (𝓝 0) := by
  have hpos n : 0 < (μ n).real univ := hν.trans_le
    (ENNReal.toReal_mono (measure_ne_top _ _) (hle n univ))
  have hraw := tendsto_totalVariation_supermeasure_of_mass μ ν hle hmass
  have habs : Tendsto (fun n ↦ |(μ n).real univ - ν.real univ|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (hmass.sub_const (ν.real univ)).abs
  have hb := (hraw.add habs).div hmass hν.ne'
  simp only [zero_add,zero_div] at hb
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦
    totalVariation_normalizedFiniteLaw_le (μ n) ν (hpos n) hν) hb

/-- Fine original masked laws converge in raw signed variation to the closed
window restriction, with no non-atomicity requirement at its boundary. -/
theorem tendsto_originalFineClockMask_raw_variation
    {range : Set ℝ} {width : ℕ → ℝ}
    (Q : ∀ n, FiniteScalarBins range (width n)) (hwidth : Tendsto width atTop (𝓝 0))
    {region : Set (ℝ × ℝ)} (hregion : IsClosed region)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hrange : ∀ᵐ p ∂π, p.1 ∈ range ∧ p.2 ∈ range) :
    Tendsto (fun n ↦
      ((π.restrict ((Q n).originalClockMaskSet ((Q n).regionClockAllowed region))).toSignedMeasure -
        (π.restrict region).toSignedMeasure).totalVariation.real univ) atTop (𝓝 0) := by
  apply tendsto_totalVariation_supermeasure_of_mass _ _
    (fun n ↦ originalFineClockMask_restrict_le (Q n) region π hrange)
  simpa only [measureReal_def,Measure.restrict_apply_univ,Function.comp_def] using
    (ENNReal.tendsto_toReal (measure_ne_top π region)).comp
      (tendsto_originalFineClockMask_mass Q hwidth hregion π hrange)

/-- The true normalized original masked pair laws converge to the same original
closed-window law. Both clocks remain paired as in the original measure. -/
theorem tendsto_originalFineClockMask_normalized_variation
    {range : Set ℝ} {width : ℕ → ℝ}
    (Q : ∀ n, FiniteScalarBins range (width n)) (hwidth : Tendsto width atTop (𝓝 0))
    {region : Set (ℝ × ℝ)} (hregion : IsClosed region)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hrange : ∀ᵐ p ∂π, p.1 ∈ range ∧ p.2 ∈ range)
    (hmass : 0 < π.real region) :
    Tendsto (fun n ↦
      ((normalizedFiniteLaw (π.restrict
        ((Q n).originalClockMaskSet ((Q n).regionClockAllowed region)))).toSignedMeasure -
        (normalizedFiniteLaw (π.restrict region)).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
  apply tendsto_totalVariation_normalized_supermeasure_of_mass _ _
    (fun n ↦ originalFineClockMask_restrict_le (Q n) region π hrange)
    (by simpa only [measureReal_def,Measure.restrict_apply_univ,Function.comp_def] using hmass)
  simpa only [measureReal_def,Measure.restrict_apply_univ,Function.comp_def] using
    (ENNReal.tendsto_toReal (measure_ne_top π region)).comp
      (tendsto_originalFineClockMask_mass Q hwidth hregion π hrange)

end OTSelector.Reconstruction
