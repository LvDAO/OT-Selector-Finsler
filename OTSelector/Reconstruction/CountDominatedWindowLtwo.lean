import OTSelector.Reconstruction.OriginalCompletePathGoodEventLtwo
import OTSelector.Probability.ExponentialTailSecondMoment

/-! A single count argument supplies the bounded-window square estimate for
both original source and original target traffic. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- An integrable nonnegative traffic dominated on a measurable window by an
original count has a square bound from that count's exponential moment. -/
theorem bounded_count_traffic_memLp_two_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {traffic N : Ω → ℝ} (hT : Measurable traffic) (hT0 : ∀ s, 0 ≤ traffic s)
    (hInt : Integrable traffic P)
    {Small : Set Ω} (hSmall : MeasurableSet Small)
    (hN : Measurable N) (hN0 : ∀ s, 0 ≤ N s)
    (hExp : Integrable (fun s ↦ Real.exp (N s)) P)
    {L B K : ℝ} (hExpBound : (∫ s, Real.exp (N s) ∂P) ≤ Real.exp L)
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hdom : ∀ᵐ s ∂P, s ∈ Small → traffic s ≤ B * N s) :
    let budget := B*K*(∫ s, traffic s ∂P)+8*B^2*Real.exp L*Real.exp (-K/2)
    MemLp (Small.indicator traffic) 2 P ∧
      (∫ s, (Small.indicator traffic s)^2 ∂P) ≤ budget ∧
      eLpNorm (Small.indicator traffic) 2 P ≤ ENNReal.ofReal (Real.sqrt budget) := by
  dsimp only
  let Good := {s | s ∈ Small ∧ N s ≤ K}
  have hGood : MeasurableSet Good := hSmall.inter (measurableSet_le hN measurable_const)
  have hg := goodEvent_memLp_two_of_integrable_majorant hT.aestronglyMeasurable
    hGood.compl (mul_nonneg hB hK) hInt (Filter.Eventually.of_forall hT0) (by
      filter_upwards [hdom] with s hs hsG
      have hsGood : s ∈ Good := not_not.mp hsG
      have hb : traffic s ≤ B*K :=
        (hs hsGood.1).trans (mul_le_mul_of_nonneg_left hsGood.2 hB)
      nlinarith [hT0 s])
  simp only [compl_compl] at hg
  have ht := countTail_traffic_memLp_two_and_exponential_norm P hN hN0 hExp hExpBound
    (hT.indicator hSmall).aestronglyMeasurable hB (K:=K) (by
      filter_upwards [hdom] with s hs _hlarge
      by_cases hsm : s ∈ Small
      · rw [indicator_of_mem hsm, abs_of_nonneg (hT0 s)]
        exact hs hsm
      · rw [indicator_of_notMem hsm, abs_zero]
        exact mul_nonneg hB (hN0 s))
  let Tail := {s | K < N s}.indicator (Small.indicator traffic)
  have hsplit : (fun s ↦ (Small.indicator traffic s)^2) =
      (fun s ↦ (Good.indicator traffic s)^2+(Tail s)^2) := by
    funext s
    by_cases hsm : s ∈ Small
    · by_cases hn : N s ≤ K
      · have hg : s ∈ Good := ⟨hsm, hn⟩
        simp only [Tail, indicator_of_mem hsm, indicator_of_mem hg,
          indicator_of_notMem (show s ∉ {s | K < N s} from not_lt.mpr hn),
          zero_pow (by norm_num : 2 ≠ 0), add_zero]
      · have hg : s ∉ Good := fun hg ↦ hn hg.2
        simp only [Tail, indicator_of_mem hsm, indicator_of_notMem hg,
          indicator_of_mem (show s ∈ {s | K < N s} from lt_of_not_ge hn),
          zero_pow (by norm_num : 2 ≠ 0), zero_add]
    · have hg : s ∉ Good := fun hg ↦ hsm hg.1
      by_cases hn : K < N s <;> simp [Tail, hsm, hg, hn]
  have hI : Integrable (fun s ↦ (Small.indicator traffic s)^2) P := by
    rw [hsplit]
    exact hg.1.integrable_sq.add ht.1.integrable_sq
  have hmean : (∫ s, (Small.indicator traffic s)^2 ∂P) ≤
      B*K*(∫ s, traffic s ∂P)+8*B^2*Real.exp L*Real.exp (-K/2) := by
    rw [hsplit, integral_add hg.1.integrable_sq ht.1.integrable_sq]
    exact add_le_add hg.2 ht.2.1
  have hLp : MemLp (Small.indicator traffic) 2 P :=
    (memLp_two_iff_integrable_sq (hT.indicator hSmall).aestronglyMeasurable).mpr hI
  exact ⟨hLp, hmean, eLpNorm_two_le_sqrt_of_integral_sq_le hLp hmean⟩

end OTSelector.Reconstruction
