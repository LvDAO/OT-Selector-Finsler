import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Analysis.Sobolev.BoxTraceCompactness

Conditions: Smooth scalar functions on a finite coordinate box/collar, with the explicitly stated L2 integrability and normal-derivative bounds.

Objects: Endpoint and face trace inequalities and vanishing face L2 norm from vanishing bulk L2 norm plus bounded normal-derivative energy.

Proof detail: Write the endpoint value using FTC on the normal collar, use Cauchy–Schwarz and (a+b)²≤2a²+2b², integrate over tangential coordinates, and then choose the collar width before passing to the sequence limit.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/realanal.pdf#page=200): Section 5.3.1, Theorem 5.3.1, pp. 200–201.
- [Rick Durrett, Probability](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.3 (Hölder), p. 29.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf): Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).

Source relation: Elementary proved box trace estimates; constants and the compactness corollary are local consequences, not an attribution of a full abstract Sobolev trace theorem.
-/

/-! Actual one-sided collar estimates for smooth cube-face traces. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- The actual endpoint trace of a C1 function is controlled by its value
and derivative L2 energies on an arbitrarily thin original collar. -/
theorem smooth_collar_endpoint_sq_mul_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {ε : ℝ} (hε : 0 < ε) :
    ε * (f 0) ^ 2 ≤ 2 * (∫ t in 0..ε, (f t) ^ 2) +
      ε ^ 2 * (∫ t in 0..ε, (deriv f t) ^ 2) := by
  have hfc := hf.continuous
  have hdc := hf.continuous_deriv (by norm_num)
  let g := fun t : ℝ ↦ ε⁻¹ * (f t) ^ 2 + ε * (deriv f t) ^ 2
  have hgc : Continuous g := (continuous_const.mul (hfc.pow 2)).add
    (continuous_const.mul (hdc.pow 2))
  have hg0 : ∀ t, 0 ≤ g t := by intro t; dsimp only [g]; positivity
  have hpoint : ∀ t ∈ Icc 0 ε, (f 0) ^ 2 ≤ (f t) ^ 2 + ∫ s in 0..ε, g s := by
    intro t ht
    have hFTC : (∫ s in 0..t, 2 * f s * deriv f s) = (f t) ^ 2 - (f 0) ^ 2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro s hs
        simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using!
          ((hf.differentiable (by norm_num) s).hasDerivAt.pow 2)
      · exact ((continuous_const.mul hfc).mul hdc).intervalIntegrable _ _
    have hyoung : ∀ s, -(2 * f s * deriv f s) ≤ g s := by
      intro s
      dsimp only [g]
      apply (mul_le_mul_iff_right₀ hε).1
      have he : ε * (ε⁻¹ * (f s) ^ 2 + ε * (deriv f s) ^ 2) =
          (f s) ^ 2 + ε ^ 2 * (deriv f s) ^ 2 := by
        field_simp [hε.ne']
      rw [he]
      nlinarith [sq_nonneg (f s + ε * deriv f s)]
    have hm := intervalIntegral.integral_mono_on (μ := volume) ht.1
      (((continuous_const.mul hfc).mul hdc).neg.intervalIntegrable 0 t)
      (hgc.intervalIntegrable 0 t) (fun s _ ↦ hyoung s)
    change (∫ s in 0..t, -(2 * f s * deriv f s)) ≤ ∫ s in 0..t, g s at hm
    rw [intervalIntegral.integral_neg, hFTC] at hm
    have hext := intervalIntegral.integral_mono_interval (μ := volume) (le_refl (0 : ℝ)) ht.1 ht.2
      (Filter.Eventually.of_forall hg0) (hgc.intervalIntegrable 0 ε)
    linarith
  have hm := intervalIntegral.integral_mono_on (μ := volume) hε.le
    (continuous_const.intervalIntegrable 0 ε)
    (((hfc.pow 2).add continuous_const).intervalIntegrable 0 ε)
    hpoint
  change (∫ t in 0..ε, (f 0) ^ 2) ≤
    ∫ t in 0..ε, (f t) ^ 2 + ∫ s in 0..ε, g s at hm
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (f := fun t : ℝ ↦ (f t) ^ 2) (g := fun _ ↦ ∫ s in 0..ε, g s)
    ((hfc.pow 2).intervalIntegrable 0 ε) (continuous_const.intervalIntegrable 0 ε),
    intervalIntegral.integral_const] at hm
  simp only [sub_zero, smul_eq_mul] at hm
  have hg : (∫ s in 0..ε, g s) =
      ε⁻¹ * (∫ s in 0..ε, (f s) ^ 2) +
        ε * (∫ s in 0..ε, (deriv f s) ^ 2) := by
    dsimp only [g]
    rw [intervalIntegral.integral_add
      (f := fun s : ℝ ↦ ε⁻¹ * (f s) ^ 2)
      (g := fun s : ℝ ↦ ε * (deriv f s) ^ 2)
      ((continuous_const.mul (hfc.pow 2)).intervalIntegrable 0 ε)
      ((continuous_const.mul (hdc.pow 2)).intervalIntegrable 0 ε),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hg] at hm
  have he : ε * (ε⁻¹ * (∫ s in 0..ε, (f s) ^ 2) +
      ε * (∫ s in 0..ε, (deriv f s) ^ 2)) =
      (∫ s in 0..ε, (f s) ^ 2) + ε ^ 2 * (∫ s in 0..ε, (deriv f s) ^ 2) := by
    field_simp [hε.ne']
  rw [he] at hm
  linarith

/-- The denominator form of the true thin-collar endpoint estimate. -/
theorem smooth_collar_endpoint_sq_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {ε : ℝ} (hε : 0 < ε) :
    (f 0) ^ 2 ≤ (2 / ε) * (∫ t in 0..ε, (f t) ^ 2) +
      ε * (∫ t in 0..ε, (deriv f t) ^ 2) := by
  apply (mul_le_mul_iff_right₀ hε).1
  have h := smooth_collar_endpoint_sq_mul_le hf hε
  have he : ε * ((2 / ε) * (∫ t in 0..ε, (f t) ^ 2) +
      ε * (∫ t in 0..ε, (deriv f t) ^ 2)) =
      2 * (∫ t in 0..ε, (f t) ^ 2) + ε ^ 2 * (∫ t in 0..ε, (deriv f t) ^ 2) := by
    field_simp [hε.ne']
  rw [he]
  exact h

private theorem continuous_integrableOn_box_collar_sq
    {ι : Type*} [Fintype ι] {g : (ι → ℝ) × ℝ → ℝ}
    (hg : Continuous g) (a b : ι → ℝ) (ε : ℝ) :
    IntegrableOn (fun p ↦ (g p) ^ 2) (Icc a b ×ˢ Icc 0 ε)
      ((volume : Measure (ι → ℝ)).prod volume) := by
  rw [← Icc_prod_eq (a, (0 : ℝ)) (b, ε)]
  exact (hg.pow 2).continuousOn.integrableOn_Icc

/-- The actual normal trace on a rectangular face has the same adjustable
collar estimate after Fubini. The energy uses the original directional
Fréchet derivative, with no assumed trace or gradient inequality. -/
theorem smooth_box_face_trace_sq_mul_le
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    {f : (ι → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f) {ε : ℝ} (hε : 0 < ε) :
    ε * (∫ y in Icc a b, (f (y, 0)) ^ 2) ≤
      2 * (∫ p in Icc a b ×ˢ Icc 0 ε, (f p) ^ 2) +
      ε ^ 2 * (∫ p in Icc a b ×ˢ Icc 0 ε,
        (fderiv ℝ f p (0, 1)) ^ 2) := by
  let df := fun p : (ι → ℝ) × ℝ ↦ fderiv ℝ f p (0, 1)
  have hdc : Continuous df :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hbulk : IntegrableOn (fun p ↦ (f p) ^ 2) (Icc a b ×ˢ Icc 0 ε)
      ((volume : Measure (ι → ℝ)).prod volume) :=
    continuous_integrableOn_box_collar_sq hf.continuous a b ε
  have hgrad : IntegrableOn (fun p ↦ (df p) ^ 2) (Icc a b ×ˢ Icc 0 ε)
      ((volume : Measure (ι → ℝ)).prod volume) :=
    continuous_integrableOn_box_collar_sq hdc a b ε
  have hbulk' : Integrable (fun p ↦ (f p) ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc 0 ε))) := by
    rwa [Measure.prod_restrict]
  have hgrad' : Integrable (fun p ↦ (df p) ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc 0 ε))) := by
    rwa [Measure.prod_restrict]
  have htrace : IntegrableOn (fun y ↦ (f (y, 0)) ^ 2) (Icc a b) volume := by
    apply ContinuousOn.integrableOn_Icc
    exact ((hf.continuous.comp (continuous_id.prodMk continuous_const)).pow 2).continuousOn
  have hpoint : ∀ y : ι → ℝ,
      ε * (f (y, 0)) ^ 2 ≤ 2 * (∫ t in Icc 0 ε, (f (y, t)) ^ 2) +
        ε ^ 2 * (∫ t in Icc 0 ε, (df (y, t)) ^ 2) := by
    intro y
    have hslice : ContDiff ℝ 1 (fun t : ℝ ↦ f (y, t)) :=
      hf.comp (contDiff_const.prodMk contDiff_id)
    have hd : ∀ t : ℝ, deriv (fun s : ℝ ↦ f (y, s)) t = df (y, t) := by
      intro t
      exact ((hf.differentiable (by norm_num) (y, t)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))).deriv
    have h := smooth_collar_endpoint_sq_mul_le hslice hε
    simpa only [intervalIntegral.integral_of_le hε.le, ← integral_Icc_eq_integral_Ioc, hd] using h
  have hm := integral_mono_ae (htrace.const_mul ε)
    ((hbulk'.integral_prod_left.const_mul 2).add (hgrad'.integral_prod_left.const_mul (ε ^ 2)))
    (Filter.Eventually.of_forall hpoint)
  change (∫ y in Icc a b, ε * (f (y, 0)) ^ 2) ≤
    ∫ y in Icc a b, 2 * (∫ t in Icc 0 ε, (f (y, t)) ^ 2) +
      ε ^ 2 * (∫ t in Icc 0 ε, (df (y, t)) ^ 2) at hm
  rw [integral_const_mul, integral_add
    (f := fun y ↦ 2 * (∫ t in Icc 0 ε, (f (y, t)) ^ 2))
    (g := fun y ↦ ε ^ 2 * (∫ t in Icc 0 ε, (df (y, t)) ^ 2))
    (hbulk'.integral_prod_left.const_mul 2)
    (hgrad'.integral_prod_left.const_mul (ε ^ 2)), integral_const_mul, integral_const_mul] at hm
  rw [Measure.volume_eq_prod, setIntegral_prod _ hbulk, setIntegral_prod _ hgrad]
  exact hm

/-- The true unit-collar H1 energy bounds the original face L2 trace. -/
theorem smooth_box_face_trace_sq_le_h1
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    {f : (ι → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    (∫ y in Icc a b, (f (y, 0)) ^ 2) ≤
      2 * (∫ p in Icc a b ×ˢ Icc (0 : ℝ) 1, (f p) ^ 2) +
      (∫ p in Icc a b ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ f p (0, 1)) ^ 2) := by
  simpa only [one_mul, one_pow] using
    smooth_box_face_trace_sq_mul_le (a := a) (b := b) hf (ε := 1) (by norm_num)

/-- The actual thin-collar bound also uses the original full unit-collar
energies. This uniform interpolation estimate separates the vanishing bulk
L2 error from the bounded normal derivative energy. -/
theorem smooth_box_face_trace_sq_mul_le_full_collar
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    {f : (ι → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε * (∫ y in Icc a b, (f (y, 0)) ^ 2) ≤
      2 * (∫ p in Icc a b ×ˢ Icc (0 : ℝ) 1, (f p) ^ 2) +
      ε ^ 2 * (∫ p in Icc a b ×ˢ Icc (0 : ℝ) 1,
        (fderiv ℝ f p (0, 1)) ^ 2) := by
  have hsubset : Icc a b ×ˢ Icc (0 : ℝ) ε ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 :=
    Set.prod_mono subset_rfl (Icc_subset_Icc le_rfl hε1)
  have hbulk : (∫ p in Icc a b ×ˢ Icc (0 : ℝ) ε, (f p) ^ 2) ≤
      ∫ p in Icc a b ×ˢ Icc (0 : ℝ) 1, (f p) ^ 2 := by
    rw [Measure.volume_eq_prod]
    exact setIntegral_mono_set (continuous_integrableOn_box_collar_sq hf.continuous a b 1)
      (Filter.Eventually.of_forall fun p ↦ sq_nonneg (f p)) hsubset.eventuallyLE
  have hdc : Continuous (fun p ↦ fderiv ℝ f p (0, 1)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgrad : (∫ p in Icc a b ×ˢ Icc (0 : ℝ) ε, (fderiv ℝ f p (0, 1)) ^ 2) ≤
      ∫ p in Icc a b ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ f p (0, 1)) ^ 2 := by
    rw [Measure.volume_eq_prod]
    exact setIntegral_mono_set (continuous_integrableOn_box_collar_sq hdc a b 1)
      (Filter.Eventually.of_forall fun p ↦ sq_nonneg (fderiv ℝ f p (0, 1))) hsubset.eventuallyLE
  exact (smooth_box_face_trace_sq_mul_le hf hε).trans
    (add_le_add (mul_le_mul_of_nonneg_left hbulk (by norm_num))
      (mul_le_mul_of_nonneg_left hgrad (sq_nonneg ε)))

/-- Genuine bulk L2 convergence and one uniform original normal-gradient
energy bound imply convergence of the actual face L2 trace. No trace limit
or compactness conclusion is assumed. -/
theorem tendsto_smooth_box_face_trace_sq_zero_of_bulk
    {κ ι : Type*} [Fintype ι] {a b : ι → ℝ} (l : Filter κ)
    {f : κ → ((ι → ℝ) × ℝ) → ℝ} (hf : ∀ n, ContDiff ℝ 1 (f n))
    {C : ℝ} (hC : 0 ≤ C)
    (hgrad : ∀ n, (∫ p in Icc a b ×ˢ Icc (0 : ℝ) 1,
      (fderiv ℝ (f n) p (0, 1)) ^ 2) ≤ C)
    (hbulk : Tendsto (fun n ↦ ∫ p in Icc a b ×ˢ Icc (0 : ℝ) 1,
      (f n p) ^ 2) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ y in Icc a b, (f n (y, 0)) ^ 2) l (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro z hz
    exact Filter.Eventually.of_forall fun n ↦
      hz.trans_le (integral_nonneg fun y ↦ sq_nonneg (f n (y, 0)))
  · intro z hz
    have hpos : 0 < min 1 (z / (2 * (C + 1))) :=
      lt_min (by norm_num) (div_pos hz (by positivity))
    obtain ⟨ε, hε, hεsmall⟩ := exists_between hpos
    have hε1 : ε ≤ 1 := (hεsmall.trans_le (min_le_left _ _)).le
    have hεC : ε * C < z / 2 := by
      have h := (lt_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).1
        (hεsmall.trans_le (min_le_right _ _))
      nlinarith
    have htarget : 0 < ε * z / 4 := by positivity
    filter_upwards [hbulk.eventually (gt_mem_nhds htarget)] with n hn
    have hb := smooth_box_face_trace_sq_mul_le_full_collar (a := a) (b := b)
      (hf n) hε hε1
    have he := mul_le_mul_of_nonneg_left (hgrad n) (sq_nonneg ε)
    have hs := mul_lt_mul_of_pos_left hεC hε
    nlinarith

end OTSelector.Reconstruction
