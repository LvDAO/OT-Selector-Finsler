import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Variation.First
import OTSelector.Geometry.Manifold.TangentChartCurve
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerChartActionAE.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerChartActionAE`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Energy.ChartActionAE

* **Conditions:** Actual chart membership and almost-everywhere coordinate derivatives on the time interval; equality-on-interval assumptions for action congruence.
* **Objects:** Equality between intrinsic Finsler action and the coordinate energy integral, including additive coordinate variations.
* **Proof detail:** Apply the chart chain rule almost everywhere, identify tangent energy pointwise on that full-measure set, and use integral congruence and locality.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): The chart reconstruction and AE-locality formulas are formal adapters of the classical coordinate expression of energy.
-/

/-!
# Actual Finsler energy actions with almost-everywhere coordinate derivatives

Chart reconstruction identifies the original action with its coordinate integral
using derivatives only almost everywhere. Local equality on the time interval
preserves the action. These statements do not require a smooth central curve.
-/

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff Interval

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] (F : ContinuousFinslerNorm E M)

/-- Almost-everywhere coordinate differentiability and chart membership suffice
to identify the original Finsler action with the coordinate energy integral. -/
theorem curveEnergyAction_chart_eq_of_ae (old : M) {x : ℝ → E} {a b : ℝ}
    (hbase : ∀ᵐ t ∂volume.restrict (uIoc a b),
      x t ∈ (extChartAt 𝓘(ℝ, E) old).target)
    (hx : ∀ᵐ t ∂volume.restrict (uIoc a b), DifferentiableAt ℝ x t) :
    F.curveEnergyAction ((extChartAt 𝓘(ℝ, E) old).symm ∘ x) a b =
      ∫ t in a..b, F.chartEnergy old (x t, deriv x t) := by
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hbase, hx] with t ht hxt
  exact congrArg F.energy (tangentMap_chart_symm_curve old ht hxt.hasDerivAt)

/-- Equality of curves on the whole time interval preserves their actual energy
action, even when their derivatives only exist almost everywhere. -/
theorem curveEnergyAction_congr {c d : ℝ → M} {a b : ℝ}
    (heq : EqOn c d (uIcc a b)) :
    F.curveEnergyAction c a b = F.curveEnergyAction d a b := by
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  have hlocal : c =ᶠ[𝓝 t] d := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact heq (Ioo_subset_Icc_self hs)
  simp only [energy, F.speed_eq_of_eventuallyEq hlocal]

/-- Actual chart coordinates identify the action of an arbitrary curve whenever
those coordinates are differentiable almost everywhere on the time interval. -/
theorem curveEnergyAction_eq_chart_of_ae (old : M) {c : ℝ → M} {a b : ℝ}
    (hsource : MapsTo c (uIcc a b) (extChartAt 𝓘(ℝ, E) old).source)
    (hx : ∀ᵐ t ∂volume.restrict (uIoc a b),
      DifferentiableAt ℝ (extChartAt 𝓘(ℝ, E) old ∘ c) t) :
    F.curveEnergyAction c a b = ∫ t in a..b,
      F.chartEnergy old ((extChartAt 𝓘(ℝ, E) old ∘ c) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) := by
  have heq : EqOn c
      ((extChartAt 𝓘(ℝ, E) old).symm ∘ (extChartAt 𝓘(ℝ, E) old ∘ c))
      (uIcc a b) := fun t ht ↦ ((extChartAt 𝓘(ℝ, E) old).left_inv (hsource ht)).symm
  rw [F.curveEnergyAction_congr heq]
  apply F.curveEnergyAction_chart_eq_of_ae old _ hx
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  exact (extChartAt 𝓘(ℝ, E) old).map_source (hsource (uIoc_subset_uIcc ht))

/-- An additive coordinate variation of an almost-everywhere differentiable center
has exactly its expected original action integral. No time smoothness of the center
or jointly smooth variation is assumed. -/
theorem curveEnergyAction_chart_add_eq_of_ae (old : M) {x η : ℝ → E} {a b s : ℝ}
    (hbase : ∀ᵐ t ∂volume.restrict (uIoc a b),
      x t + s • η t ∈ (extChartAt 𝓘(ℝ, E) old).target)
    (hx : ∀ᵐ t ∂volume.restrict (uIoc a b), DifferentiableAt ℝ x t)
    (hη : ∀ᵐ t ∂volume.restrict (uIoc a b), DifferentiableAt ℝ η t) :
    F.curveEnergyAction
      ((extChartAt 𝓘(ℝ, E) old).symm ∘ (fun t ↦ x t + s • η t)) a b =
      ∫ t in a..b, F.chartEnergy old (x t + s • η t, deriv x t + s • deriv η t) := by
  have hdiff : ∀ᵐ t ∂volume.restrict (uIoc a b),
      DifferentiableAt ℝ (fun t ↦ x t + s • η t) t := by
    filter_upwards [hx, hη] with t hxt hηt
    exact hxt.add (hηt.const_smul s)
  rw [F.curveEnergyAction_chart_eq_of_ae old hbase hdiff]
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hx, hη] with t hxt hηt
  rw [(hxt.hasDerivAt.fun_add (hηt.hasDerivAt.fun_const_smul s)).deriv]

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
