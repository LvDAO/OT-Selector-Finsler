import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import OTSelector.Analysis.Calculus.Whitney.Basic
import OTSelector.Analysis.Calculus.Whitney.Proofs.Cover
import OTSelector.Analysis.Calculus.Whitney.Proofs.Partition

/-!
# Second derivative estimates for the Whitney construction

Main declarations: exists_whitney_partition_secondDerivative; norm_hessian_whitneyBlend_boundary_le.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.SecondDerivative`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Real normed domain for finite differential identities; finite dimension for the uniform bound on the actual scaled bump. C2 and positive normalization denominator are explicit where needed.
* **Objects:** Actual product, sum and rescaled second derivatives; first/Hessian masses of normalized finite weights; inverse-square radius bound for bumps.
* **Proof detail:** Apply genuine Fréchet product/chain rules twice, use the local finite sum identity, and estimate operator norms. A fixed bump’s compact Hessian support supplies a uniform reference bound that rescales by r^-2.

## Mathematical sources

* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
  https://www.jirka.org/ra/realanal2.pdf#page=37

**Relationship to the sources:** Explicit differential estimates supporting the second-order partition scale in Whitney’s construction. The finite normalized-mass formulas are locally derived calculus, not a separate assumed extension theorem.
-/

/-!
# Actual second derivative bounds for Whitney weights

Second derivatives are computed for the actual smooth scaled bumps and normalized
finite weights. The estimates supply the missing inverse-square scale in a C1,1
Whitney construction; they do not assume an extension with Lipschitz derivative.
-/

open Set Filter Metric Function
open scoped Topology ContDiff BigOperators

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance whitneyWeightHessianNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance whitneyWeightHessianNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem fderiv_scaled_translate {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (c : E) (r : ℝ) (x : E) :
    fderiv ℝ (fun y ↦ f (r • (y - c))) x = r • fderiv ℝ f (r • (x - c)) := by
  simp only [sub_eq_add_neg]
  calc
    _ = fderiv ℝ (fun z ↦ f (r • z)) (x + -c) :=
      fderiv_comp_add_right (f := fun z ↦ f (r • z)) (-c)
    _ = _ := fderiv_comp_smul r

private theorem hessian_scaled_translate (f : E → ℝ) (c : E) (r : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f (r • (y - c)))) x =
      (r * r) • fderiv ℝ (fderiv ℝ f) (r • (x - c)) := by
  have he : fderiv ℝ (fun y ↦ f (r • (y - c))) =
      r • (fun y ↦ fderiv ℝ f (r • (y - c))) := by
    funext y
    exact fderiv_scaled_translate f c r y
  rw [he]
  have hh := congrFun (fderiv_const_smul_field (𝕜 := ℝ)
    (f := fun y ↦ fderiv ℝ f (r • (y - c))) r) x
  simpa only [Pi.smul_apply, fderiv_scaled_translate, smul_smul] using hh

/-- The actual Hessian of a product, evaluated on two directions, has both mixed
first-derivative terms. This follows by differentiating the true first derivative. -/
theorem hessian_mul_apply {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (f * g)) x v w =
      f x * fderiv ℝ (fderiv ℝ g) x v w +
        fderiv ℝ f x v * fderiv ℝ g x w +
        g x * fderiv ℝ (fderiv ℝ f) x v w +
        fderiv ℝ g x v * fderiv ℝ f x w := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hpf : HasFDerivAt (fun y ↦ fderiv ℝ f y w)
      ((fderiv ℝ (fderiv ℝ f) x).flip w) x := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using!
      hdf.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hpg : HasFDerivAt (fun y ↦ fderiv ℝ g y w)
      ((fderiv ℝ (fderiv ℝ g) x).flip w) x := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using!
      hdg.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hprod := (hf.mul hg).fderiv_right (m := 1) (by norm_num)
  have hp : HasFDerivAt (fun y ↦ fderiv ℝ (f * g) y w)
      ((fderiv ℝ (fderiv ℝ (f * g)) x).flip w) x := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using!
      (hprod.differentiableAt one_ne_zero).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have he : (fun y ↦ fderiv ℝ (f * g) y w) =ᶠ[𝓝 x]
      (fun y ↦ f y * fderiv ℝ g y w + g y * fderiv ℝ f y w) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    rw [fderiv_mul (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hc := (((hf.differentiableAt (by norm_num)).hasFDerivAt.mul hpg).add
    ((hg.differentiableAt (by norm_num)).hasFDerivAt.mul hpf)).congr_of_eventuallyEq he
  have hh := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) (hp.unique hc)
  simpa only [ContinuousLinearMap.flip_apply, add_apply, smul_apply, smul_eq_mul,
    Pi.mul_apply, Pi.add_apply, add_assoc, mul_comm] using hh


private theorem norm_hessian_le_of_mul {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hf1 : 1 ≤ f x) (hg0 : 0 ≤ g x) :
    ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ ‖fderiv ℝ (fderiv ℝ (f * g)) x‖ +
      g x * ‖fderiv ℝ (fderiv ℝ f) x‖ +
      2 * ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ := by
  have he : f x • fderiv ℝ (fderiv ℝ g) x =
      fderiv ℝ (fderiv ℝ (f * g)) x - g x • fderiv ℝ (fderiv ℝ f) x -
        (fderiv ℝ f x).smulRight (fderiv ℝ g x) -
        (fderiv ℝ g x).smulRight (fderiv ℝ f x) := by
    ext v w
    simp only [sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    linarith [hessian_mul_apply hf hg v w]
  have h := norm_sub_le
    (fderiv ℝ (fderiv ℝ (f * g)) x - g x • fderiv ℝ (fderiv ℝ f) x -
      (fderiv ℝ f x).smulRight (fderiv ℝ g x))
    ((fderiv ℝ g x).smulRight (fderiv ℝ f x))
  have h' := (norm_sub_le (fderiv ℝ (fderiv ℝ (f * g)) x)
      (g x • fderiv ℝ (fderiv ℝ f) x))
  have h'' := norm_sub_le
    (fderiv ℝ (fderiv ℝ (f * g)) x - g x • fderiv ℝ (fderiv ℝ f) x)
    ((fderiv ℝ f x).smulRight (fderiv ℝ g x))
  rw [← he, norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ f x)] at h
  rw [norm_smul, Real.norm_of_nonneg hg0] at h'
  have hfg := ContinuousLinearMap.norm_smulRight_apply (fderiv ℝ f x) (fderiv ℝ g x)
  have hgf := ContinuousLinearMap.norm_smulRight_apply (fderiv ℝ g x) (fderiv ℝ f x)
  have hh : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ f x * ‖fderiv ℝ (fderiv ℝ g) x‖ :=
    le_mul_of_one_le_left (norm_nonneg _) hf1
  nlinarith

private theorem hessian_fun_sum {ι : Type*} (s : Finset ι) (b : ι → E → ℝ) {x : E}
    (hb : ∀ i ∈ s, ContDiffAt ℝ 2 (b i) x) :
    fderiv ℝ (fderiv ℝ (fun y ↦ ∑ i ∈ s, b i y)) x =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (b i)) x := by
  have he : fderiv ℝ (fun y ↦ ∑ i ∈ s, b i y) =ᶠ[𝓝 x]
      fun y ↦ ∑ i ∈ s, fderiv ℝ (b i) y := by
    have hnb : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, ContDiffAt ℝ 2 (b i) y :=
      (eventually_all_finset s).mpr fun i hi ↦ (hb i hi).eventually (by norm_num)
    filter_upwards [hnb] with y hy
    exact (HasFDerivAt.fun_sum fun i hi ↦
      (hy i hi).differentiableAt (by norm_num) |>.hasFDerivAt).fderiv
  rw [he.fderiv_eq]
  exact (HasFDerivAt.fun_sum fun i hi ↦
    ((hb i hi).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero |>.hasFDerivAt).fderiv

private theorem norm_fderiv_div_le {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hf0 : 0 ≤ f x) (hg0 : 0 < g x) :
    ‖fderiv ℝ (fun y ↦ f y / g y) x‖ ≤
      (f x / (g x) ^ 2) * ‖fderiv ℝ g x‖ + (g x)⁻¹ * ‖fderiv ℝ f x‖ := by
  have hi := (hasDerivAt_inv hg0.ne').comp_hasFDerivAt x hg.hasFDerivAt
  have hd := hf.hasFDerivAt.mul hi
  have heq : fderiv ℝ (fun y ↦ f y / g y) x =
      f x • (-(g x ^ 2)⁻¹ • fderiv ℝ g x) + (g x)⁻¹ • fderiv ℝ f x := by
    have hfun : (fun y ↦ f y / g y) = f * ((fun y ↦ y⁻¹) ∘ g) := by
      funext y
      simp only [Pi.mul_apply, Function.comp_apply, div_eq_mul_inv]
    rw [hfun]
    exact hd.fderiv
  rw [heq]
  calc
    _ ≤ ‖f x • (-(g x ^ 2)⁻¹ • fderiv ℝ g x)‖ +
        ‖(g x)⁻¹ • fderiv ℝ f x‖ := norm_add_le _ _
    _ = _ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf0, abs_neg,
        abs_inv, abs_pow, abs_of_pos hg0, div_eq_mul_inv, mul_assoc]

/-- A locally normalized finite family has first-derivative mass at most twice
the mass of the original nonnegative family, when its sum is at least one. -/
theorem normalized_finite_derivative_mass {ι : Type*} (s : Finset ι)
    (b : ι → E → ℝ) (S : E → ℝ) {x : E}
    (hb : ∀ i ∈ s, DifferentiableAt ℝ (b i) x)
    (hb0 : ∀ i ∈ s, 0 ≤ b i x) (hS : 1 ≤ S x)
    (he : S =ᶠ[𝓝 x] fun y ↦ ∑ i ∈ s, b i y) :
    ∑ i ∈ s, ‖fderiv ℝ (fun y ↦ b i y / S y) x‖ ≤
      2 * ∑ i ∈ s, ‖fderiv ℝ (b i) x‖ := by
  have hS0 : 0 < S x := lt_of_lt_of_le zero_lt_one hS
  have hd0 := HasFDerivAt.fun_sum (fun i hi ↦ (hb i hi).hasFDerivAt)
  have hd := hd0.congr_of_eventuallyEq he
  have hnorm : ‖fderiv ℝ S x‖ ≤ ∑ i ∈ s, ‖fderiv ℝ (b i) x‖ := by
    rw [hd.fderiv]
    exact norm_sum_le _ _
  have hsum : S x = ∑ i ∈ s, b i x := he.self_of_nhds
  calc
    _ ≤ ∑ i ∈ s, (b i x / S x ^ 2 * ‖fderiv ℝ S x‖ +
        (S x)⁻¹ * ‖fderiv ℝ (b i) x‖) :=
      Finset.sum_le_sum fun i hi ↦ norm_fderiv_div_le (hb i hi) hd.differentiableAt
        (hb0 i hi) hS0
    _ = (2 * (S x)⁻¹) * (∑ i ∈ s, ‖fderiv ℝ (b i) x‖) +
        (S x)⁻¹ * (‖fderiv ℝ S x‖ - ∑ i ∈ s, ‖fderiv ℝ (b i) x‖) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        ← Finset.sum_div, ← hsum]
      field_simp
      ring
    _ ≤ (2 * (S x)⁻¹) * (∑ i ∈ s, ‖fderiv ℝ (b i) x‖) := by
      have hn : (S x)⁻¹ *
          (‖fderiv ℝ S x‖ - ∑ i ∈ s, ‖fderiv ℝ (b i) x‖) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hS0.le) (sub_nonpos.mpr hnorm)
      linarith
    _ ≤ _ := by
      have hi : (S x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS
      exact mul_le_mul_of_nonneg_right (by linarith)
        (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)


/-- Normalizing a finite nonnegative smooth family whose sum is at least one controls
its actual Hessian mass by the original Hessian and first-derivative masses. -/
theorem normalized_finite_hessian_mass {ι : Type*} (s : Finset ι)
    (b : ι → E → ℝ) (S : E → ℝ) {x : E}
    (hb : ∀ i ∈ s, ContDiffAt ℝ 2 (b i) x)
    (hb0 : ∀ i ∈ s, 0 ≤ b i x) (hS : 1 ≤ S x)
    (he : S =ᶠ[𝓝 x] fun y ↦ ∑ i ∈ s, b i y) :
    ∑ i ∈ s, ‖fderiv ℝ (fderiv ℝ (fun y ↦ b i y / S y)) x‖ ≤
      2 * (∑ i ∈ s, ‖fderiv ℝ (fderiv ℝ (b i)) x‖) +
        4 * (∑ i ∈ s, ‖fderiv ℝ (b i) x‖) ^ 2 := by
  let ψ : ι → E → ℝ := fun i y ↦ b i y / S y
  have hS0 : 0 < S x := lt_of_lt_of_le zero_lt_one hS
  have hSc : ContDiffAt ℝ 2 S x := (ContDiffAt.sum hb).congr_of_eventuallyEq he
  have hc (i) (hi : i ∈ s) : ContDiffAt ℝ 2 (ψ i) x :=
    (hb i hi).div hSc hS0.ne'
  have hp0 (i) (hi : i ∈ s) : 0 ≤ ψ i x := div_nonneg (hb0 i hi) hS0.le
  have hone : ∑ i ∈ s, ψ i x = 1 := by
    simp only [ψ, ← Finset.sum_div, ← he.self_of_nhds, div_self hS0.ne']
  have hprod (i) : fderiv ℝ (fderiv ℝ (S * ψ i)) x =
      fderiv ℝ (fderiv ℝ (b i)) x := by
    have hlocal : S * ψ i =ᶠ[𝓝 x] b i := by
      filter_upwards [hSc.continuousAt.eventually_ne hS0.ne'] with y hy
      simp only [Pi.mul_apply, ψ]
      exact mul_div_cancel₀ (b i y) hy
    exact hlocal.fderiv.fderiv_eq
  have hpoint (i) (hi : i ∈ s) :
      ‖fderiv ℝ (fderiv ℝ (ψ i)) x‖ ≤
        ‖fderiv ℝ (fderiv ℝ (b i)) x‖ +
          ψ i x * ‖fderiv ℝ (fderiv ℝ S) x‖ +
          2 * ‖fderiv ℝ S x‖ * ‖fderiv ℝ (ψ i) x‖ := by
    simpa only [hprod] using norm_hessian_le_of_mul hSc (hc i hi) hS (hp0 i hi)
  have hD : ‖fderiv ℝ S x‖ ≤ ∑ i ∈ s, ‖fderiv ℝ (b i) x‖ := by
    have hd := (HasFDerivAt.fun_sum fun i hi ↦
      (hb i hi).differentiableAt (by norm_num) |>.hasFDerivAt).congr_of_eventuallyEq he
    rw [hd.fderiv]
    exact norm_sum_le _ _
  have hH : ‖fderiv ℝ (fderiv ℝ S) x‖ ≤
      ∑ i ∈ s, ‖fderiv ℝ (fderiv ℝ (b i)) x‖ := by
    rw [he.fderiv.fderiv_eq, hessian_fun_sum s b hb]
    exact norm_sum_le _ _
  have hpD := normalized_finite_derivative_mass s b S
    (fun i hi ↦ (hb i hi).differentiableAt (by norm_num)) hb0 hS he
  have hmass := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hone,
    one_mul] at hmass
  have hD0 : 0 ≤ ∑ i ∈ s, ‖fderiv ℝ (b i) x‖ :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hmul := mul_le_mul hD hpD
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hD0
  change ∑ i ∈ s, ‖fderiv ℝ (fderiv ℝ (ψ i)) x‖ ≤ _
  change ∑ i ∈ s, ‖fderiv ℝ (ψ i) x‖ ≤ _ at hpD
  nlinarith

variable [FiniteDimensional ℝ E]

/-- One constructed constant controls the actual Hessians of the same scaled bumps
used by the Whitney partition, uniformly over centers and positive radii. -/
theorem exists_hessian_whitneyScaledBump_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : E) (r : ℝ), 0 < r → ∀ x : E,
      ‖fderiv ℝ (fderiv ℝ (whitneyScaledBump c r)) x‖ ≤ C / r ^ 2 := by
  let b : E → ℝ := whitneyScaledBump 0 1
  have hb : HasCompactSupport b := by
    change IsCompact (closure (support b))
    apply (isCompact_closedBall (0 : E) 2).of_isClosed_subset isClosed_closure
    have hs : support b = ball (0 : E) 2 := by
      simpa only [b, mul_one] using support_whitneyScaledBump (c := (0 : E)) zero_lt_one
    rw [hs]
    exact closure_minimal ball_subset_closedBall isClosed_closedBall
  have hbc : ContDiff ℝ 2 b := (contDiff_whitneyScaledBump 0 1).of_le (by simp)
  have hD : Continuous (fderiv ℝ (fderiv ℝ b)) :=
    (hbc.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := ((hb.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hD
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, hC0, fun c r hr x ↦ ?_⟩
  have he : whitneyScaledBump c r = fun y ↦ b (r⁻¹ • (y - c)) := by
    funext y
    simp only [b, whitneyScaledBump, inv_one, sub_zero, one_smul]
  rw [he, hessian_scaled_translate, norm_smul,
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (inv_nonneg.mpr hr.le))]
  calc
    _ ≤ (r⁻¹ * r⁻¹) * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
    _ = C / r ^ 2 := by rw [div_eq_mul_inv, ← inv_pow]; ring

end OTSelector.Geometry

end
end

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.PartitionSecondDerivative`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional real normed domain and nonempty closed K; the quantitative helper additionally exposes cover, local finiteness and enlarged-overlap assumptions.
* **Objects:** The very same normalized weights with locally finite Hessian support, first derivative mass O(r^-1) and true Hessian mass O(r^-2).
* **Proof detail:** Reduce to a finite local weight family, show absent weights vanish as germs with all derivatives, and combine actual normalized-weight differentiation with the constructed bump bounds and overlap number.

## Mathematical sources

* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
  https://www.jirka.org/ra/realanal2.pdf#page=37

**Relationship to the sources:** The second-order instance of Whitney’s all-order partition estimate. The local norm estimates and actual finite-sum constants are proved directly.
-/

/-!
# Second derivative mass of the constructed Whitney partition

The same actual scaled bumps and normalized weights have locally finite derivative
support and an inverse-square bound for the sum of their true Hessian norms. The cover
and its overlap constant are constructed from the original nonempty closed set.
-/

open Set Metric Filter Function
open scoped Topology BigOperators ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance whitneyPartitionHessianNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance whitneyPartitionHessianNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem partition_local_data {K C : Set E} (hK : IsClosed K) (hne : K.Nonempty)
    (hC : C ⊆ Kᶜ)
    (hcover : Kᶜ ⊆ ⋃ c ∈ C, ball c (whitneyCoverRadius K c))
    (hLF : LocallyFinite (fun c : C ↦
      {y : ↥(Kᶜ) | (y : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)}))
    {x : E} (hx : x ∉ K) :
    ∃ s : Finset C,
      (∀ c ∈ s, x ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)) ∧
      (whitneyBumpSum K C =ᶠ[𝓝 x] fun y ↦
        ∑ c ∈ s, whitneyScaledBump (c : E) (whitneyCoverRadius K c) y) ∧
      (∀ᶠ y in 𝓝 x, ∀ c ∉ s, whitneyPartitionWeight K C c y = 0) ∧
      1 ≤ whitneyBumpSum K C x := by
  classical
  obtain ⟨s, hs, he⟩ := exists_whitney_support_finset hK hLF hx
  have hz : ∀ᶠ y in 𝓝 x, ∀ c ∉ s,
      whitneyScaledBump (c : E) (whitneyCoverRadius K c) y = 0 := by
    filter_upwards [he] with y hy c hc
    apply notMem_support.mp
    rw [support_whitneyScaledBump (whitneyCoverRadius_pos hK hne (hC c.property))]
    exact fun h ↦ hy c hc (ball_subset_closedBall h)
  have hsum : whitneyBumpSum K C =ᶠ[𝓝 x] fun y ↦
      ∑ c ∈ s, whitneyScaledBump (c : E) (whitneyCoverRadius K c) y := by
    filter_upwards [hz] with y hy
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hnot
    exact hc (hy c hnot)
  refine ⟨s, hs, hsum, ?_, ?_⟩
  · filter_upwards [hz] with y hy c hc
    simp only [whitneyPartitionWeight, hy c hc, zero_div]
  · obtain ⟨c, hc, hball⟩ := by simpa only [mem_iUnion] using hcover hx
    let j : C := ⟨c, hc⟩
    have hj : whitneyScaledBump (j : E) (whitneyCoverRadius K j) x = 1 :=
      whitneyScaledBump_eq_one (whitneyCoverRadius_pos hK hne (hC hc))
        (ball_subset_closedBall hball)
    have hjs : j ∈ s := by
      by_contra hn
      exact one_ne_zero (hj.symm.trans (hz.self_of_nhds j hn))
    rw [hsum.self_of_nhds]
    calc
      1 = whitneyScaledBump (j : E) (whitneyCoverRadius K j) x := hj.symm
      _ ≤ _ := Finset.single_le_sum (s := s)
        (f := fun i : C ↦ whitneyScaledBump (i : E) (whitneyCoverRadius K i) x)
        (fun i _ ↦ (whitneyScaledBump_mem_Icc (i : E) _ x).1) hjs

private theorem partition_weight_tsupport_subset {K C : Set E}
    (hK : IsClosed K) (hne : K.Nonempty) (hC : C ⊆ Kᶜ) (c : C) :
    tsupport (whitneyPartitionWeight K C c) ⊆
      closedBall (c : E) (2 * whitneyCoverRadius K c) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hb : x ∈ support (whitneyScaledBump (c : E) (whitneyCoverRadius K c)) := by
    contrapose! hx
    simp only [mem_support, not_not] at hx ⊢
    simp only [whitneyPartitionWeight, hx, zero_div]
  rw [support_whitneyScaledBump (whitneyCoverRadius_pos hK hne (hC c.property))] at hb
  exact ball_subset_closedBall hb

omit [FiniteDimensional ℝ E] in
private theorem local_hessian_support {C : Set E} (ψ : C → E → ℝ)
    {x : E} (s : Finset C) (hz : ∀ᶠ y in 𝓝 x, ∀ c ∉ s, ψ c y = 0) :
    support (fun c ↦ fderiv ℝ (fderiv ℝ (ψ c)) x) ⊆ (s : Set C) := by
  intro c hc
  by_contra hn
  have he : ψ c =ᶠ[𝓝 x] fun _ ↦ 0 := hz.mono fun _ hy ↦ hy c hn
  have hd := (he.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  exact hc (by simpa only [fderiv_fun_const, fderiv_zero, Pi.zero_apply] using hd)


/-- For the actual normalized weights of a Whitney cover, both derivative masses
are bounded at the natural scale. The derivative bounds are derived from scaled bumps
and the cover multiplicity, rather than supplied as hypotheses. -/
theorem whitneyPartitionWeight_derivative_bounds {K C : Set E}
    (hK : IsClosed K) (hne : K.Nonempty) (hC : C ⊆ Kᶜ)
    (hcover : Kᶜ ⊆ ⋃ c ∈ C, ball c (whitneyCoverRadius K c))
    (hLF : LocallyFinite (fun c : C ↦
      {y : ↥(Kᶜ) | (y : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)}))
    {M : ℕ} (hM : ∀ (x : E), x ∉ K →
      {c ∈ C | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}.Finite ∧
      {c ∈ C | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}.ncard ≤ M) :
    ∃ A₁ A₂ : ℝ, 0 ≤ A₁ ∧ 0 ≤ A₂ ∧ ∀ x : E, x ∉ K →
      (∀ c : C, 0 ≤ whitneyPartitionWeight K C c x) ∧
      HasFiniteSupport (fun c : C ↦ whitneyPartitionWeight K C c x) ∧
      (∑ᶠ c : C, whitneyPartitionWeight K C c x) = 1 ∧
      (∀ c : C, ContDiffAt ℝ ∞ (whitneyPartitionWeight K C c) x) ∧
      HasFiniteSupport (fun c : C ↦ fderiv ℝ (whitneyPartitionWeight K C c) x) ∧
      HasFiniteSupport (fun c : C ↦
        fderiv ℝ (fderiv ℝ (whitneyPartitionWeight K C c)) x) ∧
      (∑ᶠ c : C, ‖fderiv ℝ (whitneyPartitionWeight K C c) x‖) ≤
        A₁ / whitneyCoverRadius K x ∧
      (∑ᶠ c : C, ‖fderiv ℝ (fderiv ℝ (whitneyPartitionWeight K C c)) x‖) ≤
        A₂ / (whitneyCoverRadius K x) ^ 2 := by
  classical
  obtain ⟨C₁, hC₁, hbound₁⟩ := exists_fderiv_whitneyScaledBump_bound (E := E)
  obtain ⟨C₂, hC₂, hbound₂⟩ := exists_hessian_whitneyScaledBump_bound (E := E)
  refine ⟨4 * M * C₁, 8 * M * C₂ + 16 * ((M : ℝ) * C₁) ^ 2,
    by positivity, by positivity, ?_⟩
  intro x hx
  let b : C → E → ℝ := fun c ↦ whitneyScaledBump (c : E) (whitneyCoverRadius K c)
  let S : E → ℝ := whitneyBumpSum K C
  let ψ : C → E → ℝ := whitneyPartitionWeight K C
  obtain ⟨s, hs, he, hz, hS⟩ := partition_local_data hK hne hC hcover hLF hx
  have hS0 : 0 < S x := zero_lt_one.trans_le hS
  have hb (c : C) : ContDiff ℝ ∞ (b c) := contDiff_whitneyScaledBump (c : E) _
  have hb0 (c : C) : 0 ≤ b c x := (whitneyScaledBump_mem_Icc (c : E) _ x).1
  have hSc : ContDiffAt ℝ ∞ S x :=
    (ContDiffAt.sum fun c (_ : c ∈ s) ↦ (hb c).contDiffAt).congr_of_eventuallyEq he
  have hzero (c : C) (hc : c ∉ s) : ψ c =ᶠ[𝓝 x] fun _ ↦ 0 :=
    hz.mono fun _ hy ↦ hy c hc
  have hval : support (fun c ↦ ψ c x) ⊆ (s : Set C) := by
    intro c hc
    by_contra hn
    exact hc ((hzero c hn).self_of_nhds)
  have hder : support (fun c ↦ fderiv ℝ (ψ c) x) ⊆ (s : Set C) := by
    intro c hc
    by_contra hn
    exact hc (by simpa only [fderiv_const_apply] using (hzero c hn).fderiv_eq (𝕜 := ℝ))
  have hhess := local_hessian_support ψ s hz
  have hnorm₁ : support (fun c ↦ ‖fderiv ℝ (ψ c) x‖) ⊆ (s : Set C) := by
    simpa only [support, norm_ne_zero_iff] using hder
  have hnorm₂ : support (fun c ↦ ‖fderiv ℝ (fderiv ℝ (ψ c)) x‖) ⊆ (s : Set C) := by
    intro c hc
    apply hhess
    intro hh
    apply hc
    change ‖fderiv ℝ (fderiv ℝ (ψ c)) x‖ = 0
    change fderiv ℝ (fderiv ℝ (ψ c)) x = 0 at hh
    rw [hh, norm_zero]
  have hr := whitneyCoverRadius_pos hK hne hx
  have hinc (c : C) (hc : c ∈ s) :
      x ∈ closedBall (c : E) ((5 / 2 : ℝ) * whitneyCoverRadius K c) := by
    have hrc := whitneyCoverRadius_pos hK hne (hC c.property)
    exact (closedBall_subset_closedBall (by linarith)) (hs c hc)
  have hactive := hM x hx
  have hsub : s.image (fun c : C ↦ (c : E)) ⊆ hactive.1.toFinset := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    exact hactive.1.mem_toFinset.mpr ⟨z.property, hinc z hz⟩
  have hcard : s.card ≤ M := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
      ← Set.ncard_eq_toFinset_card _ hactive.1] at hh
    exact hh.trans hactive.2
  have hgrad (c : C) (hc : c ∈ s) :
      ‖fderiv ℝ (b c) x‖ ≤ 2 * C₁ / whitneyCoverRadius K x := by
    have hrc := whitneyCoverRadius_pos hK hne (hC c.property)
    have hcomp := (whitneyCoverRadius_comparable (hinc c hc)).1
    calc
      _ ≤ C₁ / whitneyCoverRadius K c := hbound₁ (c : E) _ hrc x
      _ ≤ _ := (div_le_div_iff₀ hrc hr).mpr (by nlinarith)
  have hhesspoint (c : C) (hc : c ∈ s) :
      ‖fderiv ℝ (fderiv ℝ (b c)) x‖ ≤ 4 * C₂ / (whitneyCoverRadius K x) ^ 2 := by
    have hrc := whitneyCoverRadius_pos hK hne (hC c.property)
    have hcomp := (whitneyCoverRadius_comparable (hinc c hc)).1
    have hscale : (whitneyCoverRadius K x) ^ 2 ≤
        4 * (whitneyCoverRadius K c) ^ 2 := by nlinarith
    calc
      _ ≤ C₂ / (whitneyCoverRadius K c) ^ 2 := hbound₂ (c : E) _ hrc x
      _ ≤ _ := (div_le_div_iff₀ (sq_pos_of_pos hrc) (sq_pos_of_pos hr)).mpr (by nlinarith)
  have hsum₁ : ∑ c ∈ s, ‖fderiv ℝ (b c) x‖ ≤
      (M : ℝ) * (2 * C₁ / whitneyCoverRadius K x) := by
    calc
      _ ≤ (s.card : ℝ) * (2 * C₁ / whitneyCoverRadius K x) :=
        (Finset.sum_le_sum hgrad).trans_eq (by simp)
      _ ≤ _ := by gcongr
  have hsum₂ : ∑ c ∈ s, ‖fderiv ℝ (fderiv ℝ (b c)) x‖ ≤
      (M : ℝ) * (4 * C₂ / (whitneyCoverRadius K x) ^ 2) := by
    calc
      _ ≤ (s.card : ℝ) * (4 * C₂ / (whitneyCoverRadius K x) ^ 2) :=
        (Finset.sum_le_sum hhesspoint).trans_eq (by simp)
      _ ≤ _ := by gcongr
  refine ⟨fun c ↦ div_nonneg (hb0 c) hS0.le, s.finite_toSet.subset hval, ?_, ?_,
    s.finite_toSet.subset hder, s.finite_toSet.subset hhess, ?_, ?_⟩
  · rw [finsum_eq_sum_of_support_subset _ hval]
    change (∑ c ∈ s, b c x / S x) = 1
    have hsum : S x = ∑ c ∈ s, b c x := he.self_of_nhds
    rw [← Finset.sum_div, ← hsum, div_self hS0.ne']
  · intro c
    exact (hb c).contDiffAt.div hSc hS0.ne'
  · rw [finsum_eq_sum_of_support_subset _ hnorm₁]
    have hm := normalized_finite_derivative_mass s b S
      (fun c _ ↦ (hb c).differentiable (by simp) x) (fun c _ ↦ hb0 c) hS he
    calc
      _ ≤ 2 * ∑ c ∈ s, ‖fderiv ℝ (b c) x‖ := hm
      _ ≤ 2 * ((M : ℝ) * (2 * C₁ / whitneyCoverRadius K x)) := by gcongr
      _ = (4 * M * C₁) / whitneyCoverRadius K x := by ring
  · rw [finsum_eq_sum_of_support_subset _ hnorm₂]
    have hm := normalized_finite_hessian_mass s b S
      (fun c _ ↦ (hb c).contDiffAt.of_le (by simp)) (fun c _ ↦ hb0 c) hS he
    calc
      _ ≤ 2 * (∑ c ∈ s, ‖fderiv ℝ (fderiv ℝ (b c)) x‖) +
          4 * (∑ c ∈ s, ‖fderiv ℝ (b c) x‖) ^ 2 := hm
      _ ≤ 2 * ((M : ℝ) * (4 * C₂ / (whitneyCoverRadius K x) ^ 2)) +
          4 * ((M : ℝ) * (2 * C₁ / whitneyCoverRadius K x)) ^ 2 := by
        gcongr
      _ = (8 * M * C₂ + 16 * ((M : ℝ) * C₁) ^ 2) /
          (whitneyCoverRadius K x) ^ 2 := by field_simp; ring

/-- The original closed set alone determines a genuine smooth normalized partition
with locally finite doubled supports and both inverse-scale derivative mass bounds.
No cover, partition or derivative estimate is supplied. -/
theorem exists_whitney_partition_secondDerivative {K : Set E}
    (hK : IsClosed K) (hne : K.Nonempty) :
    ∃ (C : Set E) (A₁ A₂ : ℝ), 0 ≤ A₁ ∧ 0 ≤ A₂ ∧ C ⊆ Kᶜ ∧
      (Kᶜ ⊆ ⋃ c ∈ C, ball c (whitneyCoverRadius K c)) ∧
      (∀ c : C, tsupport (whitneyPartitionWeight K C c) ⊆
        closedBall (c : E) (2 * whitneyCoverRadius K c)) ∧
      LocallyFinite (fun c : C ↦
        {x : ↥(Kᶜ) | (x : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)}) ∧
      ∀ x : E, x ∉ K →
        (∀ c : C, 0 ≤ whitneyPartitionWeight K C c x) ∧
        HasFiniteSupport (fun c : C ↦ whitneyPartitionWeight K C c x) ∧
        (∑ᶠ c : C, whitneyPartitionWeight K C c x) = 1 ∧
        (∀ c : C, ContDiffAt ℝ ∞ (whitneyPartitionWeight K C c) x) ∧
        HasFiniteSupport (fun c : C ↦ fderiv ℝ (whitneyPartitionWeight K C c) x) ∧
        HasFiniteSupport (fun c : C ↦
          fderiv ℝ (fderiv ℝ (whitneyPartitionWeight K C c)) x) ∧
        (∑ᶠ c : C, ‖fderiv ℝ (whitneyPartitionWeight K C c) x‖) ≤
          A₁ / whitneyCoverRadius K x ∧
        (∑ᶠ c : C, ‖fderiv ℝ (fderiv ℝ (whitneyPartitionWeight K C c)) x‖) ≤
          A₂ / (whitneyCoverRadius K x) ^ 2 := by
  obtain ⟨M, C, hC, hcover, _, hLF, hM⟩ := exists_locallyFinite_whitney_cover hK hne
  obtain ⟨A₁, A₂, hA₁, hA₂, hb⟩ :=
    whitneyPartitionWeight_derivative_bounds hK hne hC hcover hLF hM
  exact ⟨C, A₁, A₂, hA₁, hA₂, hC, hcover,
    partition_weight_tsupport_subset hK hne hC, hLF, hb⟩

end OTSelector.Geometry

end
end

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.AffineSecondDerivative`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Real normed spaces; C2 finite weights with local sum one, prescribed affine jets and explicitly stated first-jet/value errors. No derivative of the prescribed jet field is assumed.
* **Objects:** The actual second Fréchet derivative of a finite affine blend, reference-jet cancellation and a uniform boundary Hessian estimate from quadratic compatibility.
* **Proof detail:** Differentiate the finite affine blend twice; affine second derivatives vanish and the first/second weight sums cancel. Bound the remaining patch errors by Hessian weight mass and jet errors by twice the first derivative mass.

## Mathematical sources

* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 4, Theorem I, p. 65; Section 11, Lemma 2 and proof, pp. 69–71, equations (11.1)–(11.8).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=3
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
  https://www.jirka.org/ra/realanal2.pdf#page=37

**Relationship to the sources:** A quantitative second-derivative consequence of the same Whitney interpolation. The numerical constants 15 and 6 are local estimates, not claimed as constants from the cited paper.
-/

/-!
# Actual Hessian cancellation for affine Whitney blends

Differentiating the same finite affine blend twice gives cancellation against one
reference jet. Consequently patch errors cost the Hessian mass of the weights and
jet errors cost their first-derivative mass. No derivative of the prescribed jet
field, or preexisting second derivative of an extension, is assumed.
-/

open Set Filter
open scoped Topology ContDiff BigOperators

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance whitneyBlendHessianNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance whitneyBlendHessianNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedSpace

private theorem hessian_smul_apply {f : E → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (f • g)) x v w =
      f x • fderiv ℝ (fderiv ℝ g) x v w +
        fderiv ℝ f x v • fderiv ℝ g x w +
        fderiv ℝ f x w • fderiv ℝ g x v +
        fderiv ℝ (fderiv ℝ f) x v w • g x := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hpf : HasFDerivAt (fun y ↦ fderiv ℝ f y w)
      ((fderiv ℝ (fderiv ℝ f) x).flip w) x := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using!
      hdf.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hpg : HasFDerivAt (fun y ↦ fderiv ℝ g y w)
      ((fderiv ℝ (fderiv ℝ g) x).flip w) x := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using!
      hdg.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hprod := (hf.smul hg).fderiv_right (m := 1) (by norm_num)
  have hp : HasFDerivAt (fun y ↦ fderiv ℝ (f • g) y w)
      ((fderiv ℝ (fderiv ℝ (f • g)) x).flip w) x := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using!
      (hprod.differentiableAt one_ne_zero).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have he : (fun y ↦ fderiv ℝ (f • g) y w) =ᶠ[𝓝 x]
      (fun y ↦ f y • fderiv ℝ g y w + fderiv ℝ f y w • g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    rw [fderiv_smul (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have hc := (((hf.differentiableAt (by norm_num)).hasFDerivAt.smul hpg).add
    (hpf.smul (hg.differentiableAt (by norm_num)).hasFDerivAt)).congr_of_eventuallyEq he
  have hh := congrArg (fun L : E →L[ℝ] F ↦ L v) (hp.unique hc)
  simpa only [ContinuousLinearMap.flip_apply, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.smul_apply, Pi.add_apply, add_assoc] using hh

private theorem hessian_sum {ι : Type*} (s : Finset ι) (b : ι → E → F) {x : E}
    (hb : ∀ i ∈ s, ContDiffAt ℝ 2 (b i) x) :
    fderiv ℝ (fderiv ℝ (fun y ↦ ∑ i ∈ s, b i y)) x =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (b i)) x := by
  have he : fderiv ℝ (fun y ↦ ∑ i ∈ s, b i y) =ᶠ[𝓝 x]
      fun y ↦ ∑ i ∈ s, fderiv ℝ (b i) y := by
    have hnb : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, ContDiffAt ℝ 2 (b i) y :=
      (eventually_all_finset s).mpr fun i hi ↦ (hb i hi).eventually (by norm_num)
    filter_upwards [hnb] with y hy
    exact (HasFDerivAt.fun_sum fun i hi ↦
      (hy i hi).differentiableAt (by norm_num) |>.hasFDerivAt).fderiv
  rw [he.fderiv_eq]
  exact (HasFDerivAt.fun_sum fun i hi ↦
    ((hb i hi).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero |>.hasFDerivAt).fderiv

private theorem contDiff_whitneyAffineJet (f : E → F) (D : E → E →L[ℝ] F) (a : E) :
    ContDiff ℝ ∞ (whitneyAffineJet f D a) := by
  unfold whitneyAffineJet
  fun_prop

private theorem fderiv_whitneyAffineJet (f : E → F) (D : E → E →L[ℝ] F) (a : E) :
    fderiv ℝ (whitneyAffineJet f D a) = fun _ ↦ D a := by
  funext x
  exact (hasFDerivAt_whitneyAffineJet f D a x).fderiv

/-- The actual Hessian of the original affine Whitney blend. Only the weights need
C2 regularity: the values and linear maps at the anchors are arbitrary prescribed data. -/
theorem hessian_whitneyBlend_apply (s : Finset ι) (φ : ι → E → ℝ)
    (f : E → F) (D : E → E →L[ℝ] F) (a : ι → E) {x : E}
    (hφ : ∀ i ∈ s, ContDiffAt ℝ 2 (φ i) x) (v w : E) :
    fderiv ℝ (fderiv ℝ (whitneyBlend s φ f D a)) x v w =
      ∑ i ∈ s, (fderiv ℝ (fderiv ℝ (φ i)) x v w • whitneyAffineJet f D (a i) x +
        fderiv ℝ (φ i) x v • D (a i) w + fderiv ℝ (φ i) x w • D (a i) v) := by
  have hc i : ContDiffAt ℝ 2 (whitneyAffineJet f D (a i)) x :=
    (contDiff_whitneyAffineJet f D (a i)).contDiffAt.of_le (by simp)
  change fderiv ℝ (fderiv ℝ (fun y ↦ ∑ i ∈ s,
    (φ i • whitneyAffineJet f D (a i)) y)) x v w = _
  have hsum := hessian_sum s _ (fun i hi ↦ (hφ i hi).smul (hc i))
  have hv := congrArg (fun L : E →L[ℝ] E →L[ℝ] F ↦ L v w) hsum
  rw [hv]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hh := hessian_smul_apply (hφ i hi) (hc i) v w
  have hz : fderiv ℝ (fun _ : E ↦ D (a i)) x = 0 :=
    (hasFDerivAt_const (D (a i)) x).fderiv
  simp only [fderiv_whitneyAffineJet, hz, zero_apply, smul_zero, zero_add] at hh
  convert hh using 1
  abel

/-- Local partition normalization forces the actual second derivatives of the
weights to sum to zero. -/
theorem sum_hessian_eq_zero_of_eventually_sum_one (s : Finset ι) (φ : ι → E → ℝ)
    {x : E} (hφ : ∀ i ∈ s, ContDiffAt ℝ 2 (φ i) x)
    (hone : (fun y ↦ ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ)) :
    ∑ i ∈ s, fderiv ℝ (fderiv ℝ (φ i)) x = 0 := by
  rw [← hessian_sum s φ hφ, hone.fderiv.fderiv_eq]
  have hc : fderiv ℝ (fun _ : E ↦ (1 : ℝ)) = fun _ ↦ (0 : E →L[ℝ] ℝ) := by
    funext y
    exact (hasFDerivAt_const (1 : ℝ) y).fderiv
  rw [hc]
  exact (hasFDerivAt_const (0 : E →L[ℝ] ℝ) x).fderiv

/-- The actual Hessian cancels against any one reference affine jet. The required
zero sums of the first and second derivatives follow from the local sum-one identity. -/
theorem hessian_whitneyBlend_cancel_apply (s : Finset ι) (φ : ι → E → ℝ)
    (f : E → F) (D : E → E →L[ℝ] F) (a : ι → E) {x b : E}
    (hφ : ∀ i ∈ s, ContDiffAt ℝ 2 (φ i) x)
    (hone : (fun y ↦ ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ)) (v w : E) :
    fderiv ℝ (fderiv ℝ (whitneyBlend s φ f D a)) x v w =
      ∑ i ∈ s, (fderiv ℝ (fderiv ℝ (φ i)) x v w •
          (whitneyAffineJet f D (a i) x - whitneyAffineJet f D b x) +
        fderiv ℝ (φ i) x v • (D (a i) - D b) w +
        fderiv ℝ (φ i) x w • (D (a i) - D b) v) := by
  have hz := sum_fderiv_eq_zero_of_eventually_sum_one s φ
    (fun i hi ↦ (hφ i hi).differentiableAt (by norm_num)) hone
  have hzv : ∑ i ∈ s, fderiv ℝ (φ i) x v = 0 := by
    simpa only [sum_apply, zero_apply] using congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hz
  have hzw : ∑ i ∈ s, fderiv ℝ (φ i) x w = 0 := by
    simpa only [sum_apply, zero_apply] using congrArg (fun L : E →L[ℝ] ℝ ↦ L w) hz
  have hz2 : ∑ i ∈ s, fderiv ℝ (fderiv ℝ (φ i)) x v w = 0 := by
    simpa only [sum_apply, zero_apply] using congrArg
      (fun L : E →L[ℝ] E →L[ℝ] ℝ ↦ L v w)
      (sum_hessian_eq_zero_of_eventually_sum_one s φ hφ hone)
  rw [hessian_whitneyBlend_apply s φ f D a hφ v w]
  simp only [sub_apply, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hzv, hzw, hz2, zero_smul, sub_zero]


/-- The norm of the true blend Hessian is controlled by patch and jet errors against
one reference anchor. The inverse powers in the weight masses can therefore cancel
quadratic and linear Whitney errors, respectively. -/
theorem norm_hessian_whitneyBlend_le (s : Finset ι) (φ : ι → E → ℝ)
    (f : E → F) (D : E → E →L[ℝ] F) (a : ι → E) {x b : E} {M η : ℝ}
    (hM : 0 ≤ M) (hη : 0 ≤ η) (hφ : ∀ i ∈ s, ContDiffAt ℝ 2 (φ i) x)
    (hone : (fun y ↦ ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ))
    (hpatch : ∀ i ∈ s, ‖whitneyAffineJet f D (a i) x -
      whitneyAffineJet f D b x‖ ≤ M)
    (hjet : ∀ i ∈ s, ‖D (a i) - D b‖ ≤ η) :
    ‖fderiv ℝ (fderiv ℝ (whitneyBlend s φ f D a)) x‖ ≤
      M * (∑ i ∈ s, ‖fderiv ℝ (fderiv ℝ (φ i)) x‖) +
        2 * η * (∑ i ∈ s, ‖fderiv ℝ (φ i) x‖) := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [hessian_whitneyBlend_cancel_apply s φ f D a hφ hone v w]
  calc
    _ ≤ ∑ i ∈ s, ‖fderiv ℝ (fderiv ℝ (φ i)) x v w •
        (whitneyAffineJet f D (a i) x - whitneyAffineJet f D b x) +
        fderiv ℝ (φ i) x v • (D (a i) - D b) w +
        fderiv ℝ (φ i) x w • (D (a i) - D b) v‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (M * ‖fderiv ℝ (fderiv ℝ (φ i)) x‖ +
        2 * η * ‖fderiv ℝ (φ i) x‖) * ‖v‖ * ‖w‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have hfirst : ‖fderiv ℝ (fderiv ℝ (φ i)) x v w •
          (whitneyAffineJet f D (a i) x - whitneyAffineJet f D b x)‖ ≤
          (‖fderiv ℝ (fderiv ℝ (φ i)) x‖ * ‖v‖ * ‖w‖) * M := by
        rw [norm_smul]
        exact mul_le_mul (ContinuousLinearMap.le_opNorm₂ _ v w) (hpatch i hi)
          (norm_nonneg _) (by positivity)
      have hsecond : ‖fderiv ℝ (φ i) x v • (D (a i) - D b) w‖ ≤
          (‖fderiv ℝ (φ i) x‖ * ‖v‖) * (η * ‖w‖) := by
        rw [norm_smul]
        exact mul_le_mul ((fderiv ℝ (φ i) x).le_opNorm v)
          (((D (a i) - D b).le_opNorm w).trans
            (mul_le_mul_of_nonneg_right (hjet i hi) (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
      have hthird : ‖fderiv ℝ (φ i) x w • (D (a i) - D b) v‖ ≤
          (‖fderiv ℝ (φ i) x‖ * ‖w‖) * (η * ‖v‖) := by
        rw [norm_smul]
        exact mul_le_mul ((fderiv ℝ (φ i) x).le_opNorm w)
          (((D (a i) - D b).le_opNorm v).trans
            (mul_le_mul_of_nonneg_right (hjet i hi) (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
      have ht := norm_add_le
        (fderiv ℝ (fderiv ℝ (φ i)) x v w •
          (whitneyAffineJet f D (a i) x - whitneyAffineJet f D b x) +
          fderiv ℝ (φ i) x v • (D (a i) - D b) w)
        (fderiv ℝ (φ i) x w • (D (a i) - D b) v)
      have ht' := norm_add_le
        (fderiv ℝ (fderiv ℝ (φ i)) x v w •
          (whitneyAffineJet f D (a i) x - whitneyAffineJet f D b x))
        (fderiv ℝ (φ i) x v • (D (a i) - D b) w)
      nlinarith
    _ = _ := by
      simp only [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]


/-- Linear closeness of the anchors, a Lipschitz first jet and a quadratic Whitney
remainder turn the actual inverse-scale weight bounds into a scale-independent
Hessian bound. The anchors and reference may be chosen on any original contact set. -/
theorem norm_hessian_whitneyBlend_boundary_le (s : Finset ι)
    (φ : ι → E → ℝ) (f : E → F) (D : E → E →L[ℝ] F) (a : ι → E)
    {x b : E} {δ L A₁ A₂ : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hφ : ∀ i ∈ s, ContDiffAt ℝ 2 (φ i) x)
    (hone : (fun y ↦ ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ))
    (hbase : ‖x - b‖ ≤ δ) (hanchor : ∀ i ∈ s, ‖x - a i‖ ≤ 2 * δ)
    (hrem : ∀ i ∈ s, ‖f (a i) - f b - D b (a i - b)‖ ≤ L * ‖a i - b‖ ^ 2)
    (hjet : ∀ i ∈ s, ‖D (a i) - D b‖ ≤ L * ‖a i - b‖)
    (hmass₁ : (∑ i ∈ s, ‖fderiv ℝ (φ i) x‖) ≤ A₁ / δ)
    (hmass₂ : (∑ i ∈ s, ‖fderiv ℝ (fderiv ℝ (φ i)) x‖) ≤ A₂ / δ ^ 2) :
    ‖fderiv ℝ (fderiv ℝ (whitneyBlend s φ f D a)) x‖ ≤
      15 * L * A₂ + 6 * L * A₁ := by
  have hab (i) (hi : i ∈ s) : ‖a i - b‖ ≤ 3 * δ := by
    calc
      _ = ‖(a i - x) + (x - b)‖ := by congr 1; abel
      _ ≤ ‖a i - x‖ + ‖x - b‖ := norm_add_le _ _
      _ ≤ 3 * δ := by rw [norm_sub_rev (a i) x]; linarith [hanchor i hi]
  have hjet' (i) (hi : i ∈ s) : ‖D (a i) - D b‖ ≤ 3 * L * δ :=
    (hjet i hi).trans (by nlinarith [mul_le_mul_of_nonneg_left (hab i hi) hL])
  have hpatch (i) (hi : i ∈ s) :
      ‖whitneyAffineJet f D (a i) x - whitneyAffineJet f D b x‖ ≤ 15 * L * δ ^ 2 := by
    have hr : ‖f (a i) - f b - D b (a i - b)‖ ≤
        (L * ‖a i - b‖) * ‖a i - b‖ := by
      simpa only [pow_two, mul_assoc] using hrem i hi
    have hp := norm_whitneyAffineJet_sub_le (x := x) hr (hjet i hi)
    have hLnorm : L * ‖a i - b‖ ≤ L * (3 * δ) :=
      mul_le_mul_of_nonneg_left (hab i hi) hL
    have hq := mul_le_mul hLnorm (hab i hi) (norm_nonneg _) (by positivity)
    have hl := mul_le_mul hLnorm (hanchor i hi) (norm_nonneg _) (by positivity)
    nlinarith
  have hh := norm_hessian_whitneyBlend_le s φ f D a
    (by positivity : 0 ≤ 15 * L * δ ^ 2) (by positivity : 0 ≤ 3 * L * δ)
    hφ hone hpatch hjet'
  calc
    _ ≤ (15 * L * δ ^ 2) * (∑ i ∈ s, ‖fderiv ℝ (fderiv ℝ (φ i)) x‖) +
        2 * (3 * L * δ) * (∑ i ∈ s, ‖fderiv ℝ (φ i) x‖) := hh
    _ ≤ (15 * L * δ ^ 2) * (A₂ / δ ^ 2) + 2 * (3 * L * δ) * (A₁ / δ) :=
      add_le_add (mul_le_mul_of_nonneg_left hmass₂ (by positivity))
        (mul_le_mul_of_nonneg_left hmass₁ (by positivity))
    _ = _ := by field_simp; ring

end OTSelector.Geometry

end
end
