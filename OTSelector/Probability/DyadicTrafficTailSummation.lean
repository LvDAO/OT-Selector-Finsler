import OTSelector.MeasureTheory.Lp.FinitePrefixSummation
import OTSelector.Probability.InterleavedDyadicSummability
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Single dyadic traffic sums with finite large-scale prefixes and the true
number-of-bands exponential remainder. Threshold growth is selected internally. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- A positive power of the actual dyadic scale and its full 2^j count error
produce L2 and absolute convergence of the literal series. Only scales at
most one require a rate; every finite prefix level needs its own L2 proof. -/
theorem memLp_dyadic_tsum_of_eventual_level_norm_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {K₀ t a E A Btail : ℝ} (hK₀ : 0≤K₀) (ht : 0<t) (ha : 0<a)
    (hE : 0≤E) (hA : 0≤A) (hBtail : 0≤Btail)
    (level : ℕ→Ω→ℝ) (hLp : ∀j,MemLp (level j) 2 P)
    (hlevel : ∀j : ℕ,t/(2:ℝ)^j≤1→∀{K : ℝ},K₀≤K→
      eLpNorm (level j) 2 P≤ENNReal.ofReal
        (A*Real.sqrt (K*E)*(t/(2:ℝ)^j)^a+Btail*((2:ℝ)^j*Real.exp (-K/4)))) :
    MemLp (fun scene↦∑'j,level j scene) 2 P ∧
      Summable (fun j↦(eLpNorm (level j) 2 P).toReal) ∧
      ∀ᵐscene∂P,Summable (fun j↦‖level j scene‖) := by
  obtain ⟨J,_hJlo,hJhi⟩ := exists_nat_pow_near
    (le_max_left (1:ℝ) t) (by norm_num : (1:ℝ)<2)
  let N := J+1
  have htN : t≤(2:ℝ)^N := (le_max_right (1:ℝ) t).trans hJhi.le
  have hscale (j : ℕ) : t/(2:ℝ)^(j+N)≤1 := by
    apply (div_le_one (by positivity : (0:ℝ)<2^(j+N))).mpr
    exact htN.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega))
  let C : ℝ := 4*(Real.log 2+1)
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0<C := by dsimp [C];linarith
  let K := fun j : ℕ↦interleavedLevelThreshold K₀ C 0 j
  have hK (j : ℕ) : K₀≤K j := by
    dsimp [K,interleavedLevelThreshold]
    exact le_add_of_nonneg_right (mul_nonneg hC.le (by positivity))
  let u := t/(2:ℝ)^N
  have hu : 0<u := by dsimp [u];positivity
  let ρ : ℝ := (2:ℝ)^(-a)
  have hρ : 0≤ρ := Real.rpow_nonneg (by norm_num) _
  have hρ1 : ρ<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgood : Summable (fun j : ℕ↦Real.sqrt (K j*E)*ρ^j) := by
    have h := (summable_sqrt_levelThreshold_geometric hK₀ hC.le hE
      (by norm_num : (0:ℝ)≤1/2) (by norm_num) hρ hρ1).comp_injective
      (fun _ _ h↦congrArg Prod.snd h : Function.Injective (fun j : ℕ↦((0:ℕ),j)))
    simpa only [Function.comp_def,pow_zero,mul_one,K] using h
  have hbad : Summable (fun j : ℕ↦(2:ℝ)^j*Real.exp (-(1/4:ℝ)*K j)) := by
    have hdecay : Real.log 2<(1/4:ℝ)*C := by dsimp [C];linarith
    have h := (summable_interleaved_exceptional (K₀:=K₀) hdecay).comp_injective
      (fun _ _ h↦congrArg Prod.snd h : Function.Injective (fun j : ℕ↦((0:ℕ),j)))
    simpa only [Function.comp_def,K] using h
  let B := fun j : ℕ↦A*u^a*(Real.sqrt (K j*E)*ρ^j)+
    (Btail*(2:ℝ)^N)*((2:ℝ)^j*Real.exp (-(1/4:ℝ)*K j))
  have hsum : Summable B :=
    (hgood.mul_left (A*u^a)).add (hbad.mul_left (Btail*(2:ℝ)^N))
  have hB0 (j : ℕ) : 0≤B j := by dsimp [B];positivity
  have hbound (j : ℕ) : eLpNorm (level (j+N)) 2 P≤ENNReal.ofReal (B j) := by
    apply (hlevel (j+N) (hscale j) (hK j)).trans
    apply ENNReal.ofReal_le_ofReal
    have hs : t/(2:ℝ)^(j+N)=u/(2:ℝ)^j := by
      dsimp [u]
      rw [pow_add]
      field_simp
    have he : -K j/4=-(1/4:ℝ)*K j := by ring
    rw [hs,dyadicScale_rpow_eq_geometric hu.le a j,he,pow_add]
    dsimp only [B,ρ]
    ring_nf
    exact le_rfl
  have htail : Summable (fun j↦(eLpNorm (level (j+N)) 2 P).toReal) :=
    hsum.of_nonneg_of_le (fun _↦ENNReal.toReal_nonneg)
      (fun j↦ENNReal.toReal_le_of_le_ofReal (hB0 j) (hbound j))
  exact memLp_tsum_of_summable_tail_norm P level hLp N htail

end OTSelector.Probability
