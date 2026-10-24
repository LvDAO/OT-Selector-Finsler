import OTSelector.Probability.BirthSmallTrafficInterpolatedNorm
import OTSelector.Probability.BirthRankZeroInterpolatedNorm

/-! One rank-unified interface for the two proved finite-band birth traffic
interpolation estimates. The rank-zero coefficient is enlarged to the same
constant used at every positive rank; the analytic estimates are reused. -/
open Set MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency true

/-- The same two actual band-square bounds give a uniform finite-level L2
interface for every natural residue rank, including genuine zero pole energy. -/
theorem birthBand_unified_traffic_interpolated_level_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {E t s C : ℝ} {k : ℕ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s) (hC : 0 ≤ C)
    (hE1 : 1 ≤ E) (hNs : (bands.card : ℝ) * s = 8 * t)
    (hE : (∑ i ∈ bands, e i) ≤ E) (hV : (∑ i ∈ bands, v i) ≤ E)
    (hfirst : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ (3 / 2 : ℝ) *
        (t ^ (((k : ℝ) - 3) / 2) * Real.sqrt (e i) +
          t ^ ((k : ℝ) / 2) * Real.sqrt (v i)))
    (hsecond : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ 2 * (t ^ (-((k : ℝ) + 4)) * e i +
        t ^ (-((k : ℝ) + 3)) * v i))
    (hezero : k = 0 → ∀ i, e i = 0) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤
        ENNReal.ofReal (((2 * (8 : ℝ) ^ (3 / 4 : ℝ) + 2 * Real.sqrt 8) *
          Real.sqrt C * Real.sqrt E) *
          (t ^ (if k=0 then (3/8:ℝ) else (k:ℝ)/8) *
            (s/t) ^ (if k=0 then (3/28:ℝ) else (k:ℝ)/(4*(3*(k:ℝ)+4))))) := by
  by_cases hkzero : k = 0
  · have hezero' := hezero hkzero
    have hfirst' : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
        (C * s ^ (3/2:ℝ)) * Real.sqrt (v i) := by
      simpa only [hkzero,Nat.cast_zero,hezero',Real.sqrt_zero,mul_zero,zero_add,
        zero_div,Real.rpow_zero,one_mul] using hfirst
    have hsecond' : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
        C * s ^ 2 * (t ^ (-3:ℝ) * v i) := by
      simpa only [hkzero,Nat.cast_zero,hezero',mul_zero,zero_add] using hsecond
    have hout := birthBand_rankZero_traffic_interpolated_level_norm P bands T hT v hv
      ht ht1 hs hC hE1 hNs hV hfirst' hsecond'
    refine ⟨hout.1,hout.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    simp only [hkzero,ite_true]
    gcongr
    nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 8) (3/4:ℝ)]
  · have hk : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hkzero
    simpa only [hkzero,ite_false] using
      birthBand_small_traffic_interpolated_level_norm P bands T hT e v he hv
        ht ht1 hs hC hE1 hk hNs hE hV hfirst hsecond

end OTSelector.Probability
