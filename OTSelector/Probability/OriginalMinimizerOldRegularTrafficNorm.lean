import OTSelector.Probability.BirthDyadicTrafficLevelNorm
import OTSelector.Probability.FiniteBandTrafficRemainderLtwo

/-! Both genuine old-focal moment rates have one common positive shell power.
The zero-rank branch uses its actual zero pole energy rather than a fictitious
positive residue rank. -/
open Real
noncomputable section
namespace OTSelector.Probability
set_option maxHeartbeats 800000

/-- The actual old small first moment has `t^(1/q)` decay under its unchanged
finite energy budget, including rank zero when its real pole energy is zero. -/
theorem oldFocal_small_firstMoment_le_common_power
    {t q E e v : ℝ} (ht : 0<t) (ht1 : t≤1) (hq : 2≤q) (hE : 1≤E)
    (he : e≤E) (hv : v≤E) (k : ℕ) (hezero : k=0→e=0) :
    t^((k:ℝ)/2)*Real.sqrt e+t^(((k:ℝ)+3)/2)*Real.sqrt v≤
      2*E*t^(1/q) := by
  have hE0:0≤E:=by linarith
  have hsE:Real.sqrt E≤E:=by
    nlinarith [Real.sq_sqrt hE0,Real.sqrt_nonneg E]
  have hse:Real.sqrt e≤E:=(Real.sqrt_le_sqrt he).trans hsE
  have hsv:Real.sqrt v≤E:=(Real.sqrt_le_sqrt hv).trans hsE
  have hqinv:1/q≤1/2:=one_div_le_one_div_of_le (by norm_num) hq
  have hk0:0≤(k:ℝ):=Nat.cast_nonneg _
  have hsecond:t^(((k:ℝ)+3)/2)≤t^(1/q):=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hsecond':t^(((k:ℝ)+3)/2)*Real.sqrt v≤t^(1/q)*E:=
    mul_le_mul hsecond hsv (Real.sqrt_nonneg _) (by positivity)
  have hfirst:t^((k:ℝ)/2)*Real.sqrt e≤t^(1/q)*E:=by
    by_cases hk:k=0
    · rw [hezero hk,Real.sqrt_zero,mul_zero]
      positivity
    · have hk1:1≤(k:ℝ):=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      exact mul_le_mul (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith))
        hse (Real.sqrt_nonneg _) (by positivity)
  nlinarith [hfirst,hsecond']

/-- The old large-phase original pole and momentum energy coefficients retain
the same `t^(1/q)` decay, with one unchanged finite energy budget. -/
theorem oldFocal_large_energy_le_common_power
    {t q E e v : ℝ} (ht : 0<t) (ht1 : t≤1)
    (he : e≤E) (hv : v≤E) (hv0 : 0≤v) :
    t^(1/q)*e+t^(1+1/q)*v≤2*E*t^(1/q) := by
  have hpower:t^(1+1/q)≤t^(1/q):=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hfirst:t^(1/q)*e≤t^(1/q)*E:=
    mul_le_mul_of_nonneg_left he (by positivity)
  have hsecond:t^(1+1/q)*v≤t^(1/q)*E:=
    mul_le_mul hpower hv hv0 (by positivity)
  nlinarith [hfirst,hsecond]

/-- A genuine old-window moment estimate gives its common norm gain; the
original shifted exponential count error keeps the exact quarter exponent. -/
theorem oldFocal_sqrt_budget_le_common_power
    {t q E K K₀ C R P : ℝ} (ht : 0<t) (hE : 0≤E) (hK : 0≤K)
    (hC : 0≤C) (hR : 0≤R) (hP : P≤2*E*t^(1/q)) :
    Real.sqrt (C*K*P+R*Real.exp (-(K-K₀)/2))≤
      Real.sqrt (2*C)*Real.sqrt (K*E)*t^(1/(2*q))+
        Real.sqrt R*Real.exp (K₀/4)*Real.exp (-K/4) := by
  have hmain:0≤C*K*(2*E*t^(1/q)):=by positivity
  have htail:0≤R*Real.exp (-(K-K₀)/2):=by positivity
  have hscale:Real.sqrt (t^(1/q))=t^(1/(2*q)):=by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul ht.le]
    congr 1
    ring
  have hexp:Real.sqrt (Real.exp (-(K-K₀)/2))=
      Real.exp (K₀/4)*Real.exp (-K/4):=by
    rw [Real.sqrt_eq_rpow,←Real.exp_mul,←Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.sqrt (C*K*(2*E*t^(1/q))+R*Real.exp (-(K-K₀)/2)):=
      Real.sqrt_le_sqrt (add_le_add (mul_le_mul_of_nonneg_left hP (show 0≤C*K by positivity)) le_rfl)
    _ ≤ Real.sqrt (C*K*(2*E*t^(1/q)))+
        Real.sqrt (R*Real.exp (-(K-K₀)/2)):=sqrt_add_energy_le_sqrt_terms hmain htail
    _ = _:=by
      rw [show C*K*(2*E*t^(1/q))=(2*C)*(K*E)*t^(1/q) by ring,
        Real.sqrt_mul (by positivity:0≤(2*C)*(K*E)),
        Real.sqrt_mul (by positivity:0≤2*C),hscale,Real.sqrt_mul hR,hexp]
      ring

end OTSelector.Probability
