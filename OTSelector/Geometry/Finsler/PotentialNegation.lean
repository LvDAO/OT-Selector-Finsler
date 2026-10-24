import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Finsler.TimeReversal

/-!
# Geometry.Finsler.PotentialNegation

* **Conditions:** The original reversible fiber energy and any real potential.
* **Objects:** Odd actual energy derivative and equality of the intrinsic regular domains of u and −u.
* **Proof detail:** Differentiate even fiber energy and negate the witnessing nonzero actual tangent.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Uses the original reversibility; no additional potential regularity is required.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialNegation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialNegation`; the selected original proof blocks follow. -/
section

/-!
# Negation preserves the original intrinsic potential domain

The original reversible fiber energy is even, hence its actual derivative is odd.
Negating a potential therefore negates the witnessing nonzero tangent vector in its
intrinsic regular domain and leaves that domain unchanged. No additional symmetry or
geometric regularity hypothesis is imposed.
-/

open Set Manifold Bundle
open scoped ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The derivative of the original reversible fiber energy is odd, including the
usual derivative convention at zero or a nondifferentiable point. -/
theorem fderiv_fiberEnergy_neg (F : ContinuousFinslerNorm E M) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    fderiv ℝ (F.fiberEnergy x) (-v) = -fderiv ℝ (F.fiberEnergy x) v := by
  let L : E → ℝ := F.fiberEnergy x
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.neg ℝ
  have heq : L ∘ e = L := funext (F.fiberEnergy_neg x)
  have hd := e.comp_right_fderiv (f := L) (x := v)
  rw [heq] at hd
  change fderiv ℝ L (-v) = -fderiv ℝ L v
  ext w
  have hw := congrArg (fun p : E →L[ℝ] ℝ ↦ p w) hd
  change (fderiv ℝ L v) w = (fderiv ℝ L (-v)) (-w) at hw
  rw [map_neg] at hw
  simpa using (neg_eq_iff_eq_neg.mpr hw).symm

/-- Negating the original potential preserves its intrinsic regular domain exactly.
The actual inverse-energy witness changes from v to -v in the same tangent fiber. -/
theorem potentialRegularDomain_neg (F : ContinuousFinslerNorm E M) (u : M → ℝ) :
    F.potentialRegularDomain (-u) = F.potentialRegularDomain u := by
  have hneg : ∀ f : M → ℝ, F.potentialRegularDomain f ⊆ F.potentialRegularDomain (-f) := by
    intro f x hx
    obtain ⟨hd, v, hv, hp⟩ := hx
    refine ⟨hd.neg, -v, neg_ne_zero.mpr hv, ?_⟩
    rw [F.fderiv_fiberEnergy_neg, mfderiv_neg, hp]
  exact Subset.antisymm (by simpa only [neg_neg] using hneg (-u)) (hneg u)

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
