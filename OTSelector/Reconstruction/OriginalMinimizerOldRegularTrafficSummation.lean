import OTSelector.MeasureTheory.DyadicClockCells
import OTSelector.Probability.DyadicTrafficTailSummation

/-! One-dimensional dyadic old traffic sums from the actual level norm rate.
The increasing count threshold and its summable majorant are chosen internally. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Positive inward-distance decay and the original exponential count error
produce L2 and AE absolute convergence of the actual single old-shell series. -/
theorem memLp_original_old_single_tsum_of_level_norm_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K₀ q ε E A Btail : ℝ} (hK₀ : 0≤K₀) (hq : 0<q) (hε : 0<ε) (hE : 0≤E)
    (hA : 0≤A) (hBtail : 0≤Btail)
    (level : ℕ→Ω→ℝ) (hLp : ∀n,MemLp (level n) 2 P)
    (hlevel : ∀n:ℕ,∀{K:ℝ},K₀≤K→
      eLpNorm (level n) 2 P≤ENNReal.ofReal
        (A*Real.sqrt (K*E)*(birthDyadicShellScale ε n)^(1/(2*q))+
          Btail*Real.exp (-K/4))) :
    MemLp (fun scene↦∑'n,level n scene) 2 P∧
      Summable (fun n↦(eLpNorm (level n) 2 P).toReal)∧
      ∀ᵐscene∂P,Summable (fun n↦‖level n scene‖) := by
  apply memLp_dyadic_tsum_of_eventual_level_norm_bounds P hK₀ (half_pos hε)
    (show 0<(1/(2*q):ℝ) by positivity) hE hA hBtail level hLp
  intro n _hscale K hK
  have hs : birthDyadicShellScale ε n=(ε/2)/(2:ℝ)^n := by
    unfold birthDyadicShellScale
    rw [pow_succ]
    field_simp
  have hn := hlevel n hK
  rw [hs] at hn
  apply hn.trans (ENNReal.ofReal_le_ofReal ?_)
  apply add_le_add le_rfl
  have hpow : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  have htail := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (-K/4))) hBtail
  simpa only [one_mul] using htail

end OTSelector.Reconstruction
