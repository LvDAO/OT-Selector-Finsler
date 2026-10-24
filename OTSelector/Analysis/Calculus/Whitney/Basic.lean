import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Affine Whitney jets and scaled smooth bumps

Main declarations: whitneyAffineJet; whitneyBlend; whitneyScaledBump; hasFDerivAt_whitneyBlend.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.Affine`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Real normed domain and target; finite weights, affine first jets, pointwise remainder/jet errors and local sum-one identity as required by each formula.
* **Objects:** Actual affine jets, their finite weighted blend, true first derivatives, partition-derivative cancellation and quantitative error bounds.
* **Proof detail:** Differentiate finite scalar-weighted affine sums. Subtract one reference affine jet; the derivative of the local sum-one identity cancels the common terms, leaving controlled value and derivative discrepancies.

## Mathematical sources

* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 4, Theorem I, p. 65; Section 11, Lemma 2 and proof, pp. 69–71, equations (11.1)–(11.8).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=3
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
  https://www.jirka.org/ra/realanal2.pdf#page=37

**Relationship to the sources:** The first-order vector-valued form of Whitney’s Taylor-polynomial interpolation and cancellation; finite algebra helpers use only their displayed local hypotheses.
-/

/-!
# Quantitative affine-jet gluing for Whitney extension

Finite local pieces of a Whitney extension are actual weighted affine jets. This module
computes their true Frechet derivatives, derives the partition derivative cancellation
from a local sum-one identity, and bounds value and derivative errors. It does not assert
existence of a Whitney cover or of a global C1 extension.
-/

open Set Filter
open scoped Topology BigOperators

noncomputable section
namespace OTSelector.Geometry

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The affine polynomial prescribed by a first jet at an anchor. -/
def whitneyAffineJet (f : E → F) (D : E → E →L[ℝ] F) (a x : E) : F :=
  f a + D a (x - a)

/-- The affine polynomial has exactly the prescribed first derivative. -/
theorem hasFDerivAt_whitneyAffineJet (f : E → F) (D : E → E →L[ℝ] F) (a x : E) :
    HasFDerivAt (whitneyAffineJet f D a) (D a) x := by
  change HasFDerivAt (fun y ↦ f a + D a (y - a)) (D a) x
  simpa only [ContinuousLinearMap.comp_id, Function.comp_apply, id_eq] using
    ((D a).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)).const_add (f a)

/-- The difference of affine patches is controlled by the original Whitney remainder
and the difference of prescribed derivatives, evaluated at their actual anchors. -/
theorem norm_whitneyAffineJet_sub_le {f : E → F} {D : E → E →L[ℝ] F}
    {a b x : E} {ε η : ℝ}
    (hrem : ‖f a - f b - D b (a - b)‖ ≤ ε * ‖a - b‖)
    (hD : ‖D a - D b‖ ≤ η) :
    ‖whitneyAffineJet f D a x - whitneyAffineJet f D b x‖ ≤
      ε * ‖a - b‖ + η * ‖x - a‖ := by
  have heq : whitneyAffineJet f D a x - whitneyAffineJet f D b x =
      (f a - f b - D b (a - b)) + (D a - D b) (x - a) := by
    simp only [whitneyAffineJet, sub_apply, map_sub]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hrem
    (((D a - D b).le_opNorm _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))))

/-- A finite weighted family of actual affine first jets. -/
def whitneyBlend (s : Finset ι) (φ : ι → E → ℝ) (f : E → F)
    (D : E → E →L[ℝ] F) (a : ι → E) (x : E) : F :=
  ∑ i ∈ s, φ i x • whitneyAffineJet f D (a i) x

/-- The true derivative of the weighted affine-jet formula. -/
theorem hasFDerivAt_whitneyBlend (s : Finset ι) (φ : ι → E → ℝ)
    (f : E → F) (D : E → E →L[ℝ] F) (a : ι → E) {x : E}
    (hφ : ∀ i ∈ s, DifferentiableAt ℝ (φ i) x) :
    HasFDerivAt (whitneyBlend s φ f D a)
      (∑ i ∈ s, (φ i x • D (a i) +
        (fderiv ℝ (φ i) x).smulRight (whitneyAffineJet f D (a i) x))) x := by
  change HasFDerivAt (fun y ↦ ∑ i ∈ s, φ i y • whitneyAffineJet f D (a i) y) _ x
  convert HasFDerivAt.fun_sum (fun i hi ↦
      (hφ i hi).hasFDerivAt.smul (hasFDerivAt_whitneyAffineJet f D (a i) x)) using 1
  rfl

/-- Local partition normalization forces the actual derivatives of its weights to sum
to zero; this cancellation is derived, not independently assumed. -/
theorem sum_fderiv_eq_zero_of_eventually_sum_one (s : Finset ι) (φ : ι → E → ℝ)
    {x : E} (hφ : ∀ i ∈ s, DifferentiableAt ℝ (φ i) x)
    (hone : (fun y ↦ ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ)) :
    ∑ i ∈ s, fderiv ℝ (φ i) x = 0 := by
  have hd := HasFDerivAt.fun_sum (fun i hi ↦ (hφ i hi).hasFDerivAt)
  have hz := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).congr_of_eventuallyEq hone
  exact hd.unique hz

/-- The derivative error of an actual blend has the cancellation formula used at a
Whitney boundary. All derivatives here are ordinary Frechet derivatives. -/
theorem fderiv_whitneyBlend_sub (s : Finset ι) (φ : ι → E → ℝ)
    (f : E → F) (D : E → E →L[ℝ] F) (a : ι → E) {x b : E}
    (hφ : ∀ i ∈ s, DifferentiableAt ℝ (φ i) x)
    (hone : (fun y ↦ ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ)) :
    fderiv ℝ (whitneyBlend s φ f D a) x - D b =
      ∑ i ∈ s, (φ i x • (D (a i) - D b) +
        (fderiv ℝ (φ i) x).smulRight
          (whitneyAffineJet f D (a i) x - whitneyAffineJet f D b x)) := by
  have hsum : ∑ i ∈ s, φ i x = 1 := hone.self_of_nhds
  have hzero := sum_fderiv_eq_zero_of_eventually_sum_one s φ hφ hone
  rw [(hasFDerivAt_whitneyBlend s φ f D a hφ).fderiv]
  ext v
  have hz : ∑ i ∈ s, fderiv ℝ (φ i) x v = 0 := by
    simpa only [sum_apply, zero_apply] using
      congrArg (fun T : E →L[ℝ] ℝ ↦ T v) hzero
  simp only [sub_apply, sum_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, smul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul,
    hz, zero_smul, sub_zero]
  abel

/-- The value error of an actual normalized nonnegative affine blend. -/
theorem norm_whitneyBlend_sub_le (s : Finset ι) (φ : ι → E → ℝ)
    (f : E → F) (D : E → E →L[ℝ] F) (a : ι → E) {x b : E} {M : ℝ}
    (hφ : ∀ i ∈ s, 0 ≤ φ i x) (hone : ∑ i ∈ s, φ i x = 1)
    (hpatch : ∀ i ∈ s, ‖whitneyAffineJet f D (a i) x -
      whitneyAffineJet f D b x‖ ≤ M) :
    ‖whitneyBlend s φ f D a x - whitneyAffineJet f D b x‖ ≤ M := by
  have heq : whitneyBlend s φ f D a x - whitneyAffineJet f D b x =
      ∑ i ∈ s, φ i x • (whitneyAffineJet f D (a i) x -
        whitneyAffineJet f D b x) := by
    simp only [whitneyBlend, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      hone, one_smul]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ s, ‖φ i x • (whitneyAffineJet f D (a i) x -
        whitneyAffineJet f D b x)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, φ i x * M := Finset.sum_le_sum fun i hi ↦ by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ i hi)]
      exact mul_le_mul_of_nonneg_left (hpatch i hi) (hφ i hi)
    _ = M := by rw [← Finset.sum_mul, hone, one_mul]

/-- The quantitative derivative estimate retains the actual derivative mass of the
partition. Constructing a Whitney partition with controlled mass is a separate step. -/
theorem norm_fderiv_whitneyBlend_sub_le (s : Finset ι) (φ : ι → E → ℝ)
    (f : E → F) (D : E → E →L[ℝ] F) (a : ι → E) {x b : E} {M η : ℝ}
    (hφ : ∀ i ∈ s, DifferentiableAt ℝ (φ i) x)
    (hpos : ∀ i ∈ s, 0 ≤ φ i x)
    (hone : (fun y ↦ ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ))
    (hpatch : ∀ i ∈ s, ‖whitneyAffineJet f D (a i) x -
      whitneyAffineJet f D b x‖ ≤ M)
    (hD : ∀ i ∈ s, ‖D (a i) - D b‖ ≤ η) :
    ‖fderiv ℝ (whitneyBlend s φ f D a) x - D b‖ ≤
      η + M * ∑ i ∈ s, ‖fderiv ℝ (φ i) x‖ := by
  rw [fderiv_whitneyBlend_sub s φ f D a hφ hone]
  calc
    _ ≤ ∑ i ∈ s, ‖φ i x • (D (a i) - D b) +
        (fderiv ℝ (φ i) x).smulRight
          (whitneyAffineJet f D (a i) x - whitneyAffineJet f D b x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (φ i x * η + M * ‖fderiv ℝ (φ i) x‖) := by
      apply Finset.sum_le_sum
      intro i hi
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hpos i hi)]
        exact mul_le_mul_of_nonneg_left (hD i hi) (hpos i hi)
      · rw [ContinuousLinearMap.norm_smulRight_apply, mul_comm]
        exact mul_le_mul_of_nonneg_right (hpatch i hi) (norm_nonneg _)
    _ = η + M * ∑ i ∈ s, ‖fderiv ℝ (φ i) x‖ := by
      have hsum : ∑ i ∈ s, φ i x = 1 := hone.self_of_nhds
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        hsum, one_mul]

end OTSelector.Geometry

end
end

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.Bump`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** A finite-dimensional real normed domain; positive radius for the support, plateau and radius-bound conclusions.
* **Objects:** One fixed compactly supported smooth bump and all translated/scaled ball bumps, with a common reciprocal-radius actual derivative bound.
* **Proof detail:** Use a smooth unit bump with inner/outer radii 1 and 2, translate/rescale it, and transfer its bounded compactly supported derivative by the chain rule.

## Mathematical sources

* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
  https://www.jirka.org/ra/realanal2.pdf#page=37

**Relationship to the sources:** A ball-based normed-space replacement for the smooth localization used by Whitney. The particular bump formula and exact support balls are Lean constructions, not the original cube formula.
-/

/-!
# Uniformly scaled smooth bumps for Whitney extension

A single compactly supported smooth bump on a finite-dimensional real normed space
produces bumps on every ball, with one common constant controlling the true derivative
by the reciprocal radius. No inner product is chosen in the resulting statements.
This is a quantitative building block; a Whitney covering is not constructed here.
-/

open Set Metric Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private def whitneyUnitBump : ContDiffBump (0 : E) where
  rIn := 1
  rOut := 2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := one_lt_two

/-- A radius-scaled copy of one fixed smooth bump. -/
def whitneyScaledBump (c : E) (r : ℝ) (x : E) : ℝ :=
  (whitneyUnitBump (E := E) : E → ℝ) (r⁻¹ • (x - c))

/-- Every scaled bump is genuinely smooth. -/
theorem contDiff_whitneyScaledBump (c : E) (r : ℝ) :
    ContDiff ℝ ∞ (whitneyScaledBump c r) := by
  change ContDiff ℝ ∞ (fun x ↦ (whitneyUnitBump (E := E) : E → ℝ) (r⁻¹ • (x - c)))
  exact ((whitneyUnitBump (E := E)).contDiff).comp ((contDiff_id.sub contDiff_const).const_smul _)

/-- The scaled bump takes values in the unit interval. -/
theorem whitneyScaledBump_mem_Icc (c : E) (r : ℝ) (x : E) :
    whitneyScaledBump c r x ∈ Icc (0 : ℝ) 1 :=
  show 0 ≤ (whitneyUnitBump (E := E) : E → ℝ) (r⁻¹ • (x - c)) ∧
    (whitneyUnitBump (E := E) : E → ℝ) (r⁻¹ • (x - c)) ≤ 1 from
    ⟨(whitneyUnitBump (E := E)).nonneg, (whitneyUnitBump (E := E)).le_one⟩

/-- The scaled bump equals one on the entire closed inner ball. -/
theorem whitneyScaledBump_eq_one {c x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ closedBall c r) : whitneyScaledBump c r x = 1 := by
  change (whitneyUnitBump (E := E) : E → ℝ) (r⁻¹ • (x - c)) = 1
  apply (whitneyUnitBump (E := E)).one_of_mem_closedBall
  rw [mem_closedBall_iff_norm]
  change ‖r⁻¹ • (x - c) - 0‖ ≤ 1
  rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  rw [← div_eq_inv_mul, div_le_one hr]
  exact mem_closedBall_iff_norm.mp hx

/-- The actual support is exactly the doubled open ball. -/
theorem support_whitneyScaledBump {c : E} {r : ℝ} (hr : 0 < r) :
    Function.support (whitneyScaledBump c r) = ball c (2 * r) := by
  ext x
  change (whitneyUnitBump (E := E) : E → ℝ) (r⁻¹ • (x - c)) ≠ 0 ↔ x ∈ ball c (2 * r)
  rw [← Function.mem_support, (whitneyUnitBump (E := E)).support_eq]
  rw [mem_ball_iff_norm, mem_ball_iff_norm]
  change ‖r⁻¹ • (x - c) - 0‖ < 2 ↔ ‖x - c‖ < 2 * r
  rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    ← div_eq_inv_mul, div_lt_iff₀ hr]

/-- One constant controls the derivatives of all centers and positive scales.
The bound is obtained from the actual compactly supported unit bump and the chain rule. -/
theorem exists_fderiv_whitneyScaledBump_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : E) (r : ℝ), 0 < r → ∀ x : E,
      ‖fderiv ℝ (whitneyScaledBump c r) x‖ ≤ C / r := by
  have hb : ContDiff ℝ 1 (whitneyUnitBump (E := E) : E → ℝ) := (whitneyUnitBump (E := E)).contDiff
  obtain ⟨C, hC⟩ :=
    ((whitneyUnitBump (E := E)).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv one_ne_zero)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, hC0, fun c r hr x ↦ ?_⟩
  have hi : HasFDerivAt (fun y : E ↦ r⁻¹ • (y - c))
      (r⁻¹ • ContinuousLinearMap.id ℝ E) x := by
    convert ((hasFDerivAt_id x).sub_const c).const_smul r⁻¹ using 1
    rfl
  have hd := (hb.differentiable one_ne_zero (r⁻¹ • (x - c))).hasFDerivAt.comp x hi
  have heq : fderiv ℝ (whitneyScaledBump c r) x =
      (fderiv ℝ (whitneyUnitBump (E := E) : E → ℝ) (r⁻¹ • (x - c))).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ E) := by
    convert hd.fderiv using 1
    rfl
  rw [heq]
  calc
    _ ≤ ‖fderiv ℝ (whitneyUnitBump (E := E) : E → ℝ) (r⁻¹ • (x - c))‖ *
        ‖r⁻¹ • ContinuousLinearMap.id ℝ E‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * r⁻¹ := by
      apply mul_le_mul (hC _) ?_ (norm_nonneg _) hC0
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      exact mul_le_of_le_one_right (inv_nonneg.mpr hr.le) ContinuousLinearMap.norm_id_le
    _ = C / r := (div_eq_mul_inv C r).symm

end OTSelector.Geometry

end
end
