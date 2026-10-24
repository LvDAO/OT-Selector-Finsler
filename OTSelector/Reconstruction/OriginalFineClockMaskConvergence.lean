import OTSelector.Reconstruction.OriginalWindowRetainedPairKernel
import Mathlib.MeasureTheory.Integral.Indicator

/-! Fine literal scalar masks recover their closed original pair region,
including boundary atoms. Their retained mass is independent of bin choices
in the limit; no endpoint gap comparison or density lower bound is assumed. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal Classical symmDiff
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- A literal allowed bin rectangle contains one pair in the prescribed region. -/
def FiniteScalarBins.regionClockAllowed {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (region : Set (ℝ × ℝ))
    (i j : Fin Q.count) : Prop :=
  ∃ p ∈ region, p.1 ∈ Q.cell i ∧ p.2 ∈ Q.cell j

/-- Every original pair in its region is retained by every literal mask. -/
theorem FiniteScalarBins.mem_originalClockMaskSet_of_mem_region
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    {region : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hrange : p.1 ∈ range ∧ p.2 ∈ range) (hp : p ∈ region) :
    p ∈ Q.originalClockMaskSet (Q.regionClockAllowed region) := by
  let x : range := ⟨p.1,hrange.1⟩
  let y : range := ⟨p.2,hrange.2⟩
  exact ⟨Q.rangeClassify x,Q.rangeClassify y,
    ⟨p,hp,Q.rangeClassify_mem x,Q.rangeClassify_mem y⟩,
    Q.rangeClassify_mem x,Q.rangeClassify_mem y⟩

/-- Every masked pair is within the actual bin diameter of its original
region witness. No regularity of the pair measure is used. -/
theorem FiniteScalarBins.exists_region_witness_dist_le
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    {region : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hp : p ∈ Q.originalClockMaskSet (Q.regionClockAllowed region)) :
    ∃ w ∈ region, dist w p ≤ width / 4 := by
  obtain ⟨i,j,⟨w,hw,hwi,hwj⟩,hpi,hpj⟩ := hp
  refine ⟨w,hw,?_⟩
  rw [Prod.dist_eq,max_le_iff,Real.dist_eq,Real.dist_eq]
  exact ⟨Q.diameter i w.1 hwi p.1 hpi,Q.diameter j w.2 hwj p.2 hpj⟩

/-- As bins refine, each original pair eventually has exactly its closed
region membership. This also retains atoms on the region boundary. -/
theorem eventually_mem_originalFineClockMask_iff
    {range : Set ℝ} {width : ℕ → ℝ}
    (Q : ∀ n, FiniteScalarBins range (width n))
    (hwidth : Tendsto width atTop (𝓝 0))
    {region : Set (ℝ × ℝ)} (hregion : IsClosed region)
    (p : ℝ × ℝ) (hrange : p.1 ∈ range ∧ p.2 ∈ range) :
    ∀ᶠ n in atTop,
      p ∈ (Q n).originalClockMaskSet ((Q n).regionClockAllowed region) ↔ p ∈ region := by
  by_cases hp : p ∈ region
  · exact Filter.Eventually.of_forall fun n ↦
      ⟨fun _ ↦ hp,fun _ ↦ (Q n).mem_originalClockMaskSet_of_mem_region hrange hp⟩
  · obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hregion.isOpen_compl p hp
    have hsmall : ∀ᶠ n in atTop, width n / 4 < ε :=
      (hwidth.div_const 4).eventually (gt_mem_nhds (by simpa using hε))
    filter_upwards [hsmall] with n hn
    refine ⟨?_,fun h ↦ (hp h).elim⟩
    intro hmask
    obtain ⟨w,hw,hd⟩ := (Q n).exists_region_witness_dist_le hmask
    exact ((hball (by exact hd.trans_lt hn)) hw).elim

/-- The actual original retained masses converge to the closed window mass,
for any finite original law, including singular and atomic pair laws. -/
theorem tendsto_originalFineClockMask_mass
    {range : Set ℝ} {width : ℕ → ℝ}
    (Q : ∀ n, FiniteScalarBins range (width n))
    (hwidth : Tendsto width atTop (𝓝 0))
    {region : Set (ℝ × ℝ)} (hregion : IsClosed region)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hrange : ∀ᵐ p ∂π, p.1 ∈ range ∧ p.2 ∈ range) :
    Tendsto (fun n ↦ π ((Q n).originalClockMaskSet ((Q n).regionClockAllowed region)))
      atTop (𝓝 (π region)) := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hregion.measurableSet
    (fun n ↦ (Q n).measurableSet_originalClockMaskSet _)
  exact hrange.mono (fun p hp ↦ eventually_mem_originalFineClockMask_iff Q hwidth hregion p hp)

/-- The same literal fine masks converge in actual symmetric difference.
No claim of exact invariance at finite bin width is made. -/
theorem tendsto_originalFineClockMask_symmDiff
    {range : Set ℝ} {width : ℕ → ℝ}
    (Q : ∀ n, FiniteScalarBins range (width n))
    (hwidth : Tendsto width atTop (𝓝 0))
    {region : Set (ℝ × ℝ)} (hregion : IsClosed region)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hrange : ∀ᵐ p ∂π, p.1 ∈ range ∧ p.2 ∈ range) :
    Tendsto (fun n ↦ π ((Q n).originalClockMaskSet ((Q n).regionClockAllowed region) ∆ region))
      atTop (𝓝 0) := by
  have hlim : ∀ᵐ p ∂π, ∀ᶠ n in atTop,
      p ∈ (Q n).originalClockMaskSet ((Q n).regionClockAllowed region) ∆ region ↔
        p ∈ (∅ : Set (ℝ × ℝ)) := by
    filter_upwards [hrange] with p hp
    filter_upwards [eventually_mem_originalFineClockMask_iff Q hwidth hregion p hp] with n hn
    simp only [mem_symmDiff,mem_empty_iff_false]
    tauto
  simpa only [measure_empty] using
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
      (fun n ↦ ((Q n).measurableSet_originalClockMaskSet _).symmDiff hregion.measurableSet) hlim

end OTSelector.Reconstruction
