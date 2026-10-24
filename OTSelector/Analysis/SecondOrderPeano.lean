import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue

/-!
## Lemma skeleton

* **Conditions:** The first derivative exists near the point and is differentiable at that point.
* **Objects:** The second-order quadratic polynomial with little-o squared-distance remainder.
* **Proof detail:** Use the derivative definition and a segment mean-value estimate; apply symmetry of the actual second derivative.

## Mathematical sources

* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder).
  https://www.jirka.org/ra/html/sec_taylor.html
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** The single-point second-derivative hypothesis and normed-space form are explicit formal generalizations of the Peano remainder principle; C2 on a neighborhood is not assumed.
-/

/-!
# Second-order Peano expansion at a single twice differentiable point

The first derivative need only exist near the center and be differentiable at that
center. The actual second derivative is symmetric by Schwarz's theorem. The mean
value little-o estimate integrates its first-order error to a quadratic remainder.
-/

open Set Filter Asymptotics
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiability of the actual first-derivative field at the center suffices for
a second-order Peano expansion. No neighborhood C2 or C3 hypothesis is required. -/
theorem second_order_peano_of_hasFDerivAt {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hsecond : HasFDerivAt f' B x) :
    (fun y ↦ f y - f x - f' x (y - x) - (1 / 2 : ℝ) * B (y - x) (y - x))
      =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2) := by
  have hsym := second_derivative_symmetric_of_eventually_of_real hfirst hsecond
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hfirst
  let R : E → ℝ := fun y ↦
    f y - f x - f' x (y - x) - (1 / 2 : ℝ) * B (y - x) (y - x)
  let R' : E → E →L[ℝ] ℝ := fun y ↦ f' y - f' x - B (y - x)
  have hd (y : E) (hy : y ∈ Metric.ball x r) : HasFDerivAt R (R' y) y := by
    have hshift : HasFDerivAt (fun z : E ↦ z - x) (ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).sub_const x
    have hlin := (f' x).hasFDerivAt.comp y hshift
    have hB := B.hasFDerivAt.comp y hshift
    have hquad := (hB.clm_apply hshift).const_mul (1 / 2 : ℝ)
    have h := (((hball hy).sub_const (f x)).sub hlin).sub hquad
    convert h using 1 <;> try rfl
    ext v
    change f' y v - f' x v - B (y - x) v =
      f' y v - f' x v - (1 / 2 : ℝ) * (B (y - x) v + B v (y - x))
    rw [hsym v (y - x)]
    ring
  have ho : R' =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 1) := by
    simpa only [pow_one, R', isLittleO_norm_right] using hsecond.isLittleO
  have h := (convex_ball x r).isLittleO_pow_succ (Metric.mem_ball_self hr)
    (fun y hy ↦ (hd y hy).hasFDerivWithinAt) (ho.mono nhdsWithin_le_nhds)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds x hr)] at h
  simpa only [R, sub_self, map_zero, mul_zero, sub_zero] using h

/-- The actual first and second Frechet derivatives give the same pointwise expansion. -/
theorem second_order_peano_of_differentiableAt {f : E → ℝ} {x : E}
    (hfirst : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hsecond : DifferentiableAt ℝ (fderiv ℝ f) x) :
    (fun y ↦ f y - f x - fderiv ℝ f x (y - x) -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) x (y - x) (y - x))
      =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2) :=
  second_order_peano_of_hasFDerivAt (hfirst.mono fun _ h ↦ h.hasFDerivAt)
    hsecond.hasFDerivAt

end OTSelector.Geometry
