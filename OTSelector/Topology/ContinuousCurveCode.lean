import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Rat

/-!
# Topology.ContinuousCurveCode

Conditions: Continuous real-parameter curves in a Hausdorff target, or a jointly measurable family with a measurable clock; the injectivity result assumes injective starting points.

Objects: A countable rational evaluation code, measurable shifted codes, and injectivity of code plus clock.

Proof detail: Dense rational evaluations determine continuous curves. Compose each rational evaluation with the measurable clock shift. Equal shifted codes and clocks recover the same starting point.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4, Appendix 4A](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6): Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products).
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106): Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.

Source relation: Direct dense-equality and product-sigma consequences; this particular clocked code is a local encoding, not a standard named book construction.
-/

/-!
# Countable codes for actual continuous curves

Rational-time evaluations determine a continuous curve into a Hausdorff space. A
measurable family evaluated at a measurable clock gives a measurable countable code.
The code and the clock recover each marked starting point, so their pair is injective
when the original family starts at its actual input point.
-/

open Set MeasureTheory
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

/-- A curve's countable code records its actual values at all rational times. -/
def rationalCurveCode {M : Type*} (c : ℝ → M) : ℚ → M := fun q ↦ c q

/-- Equal rational-time codes identify the entire actual continuous curves. -/
theorem eq_of_rationalCurveCode_eq {M : Type*} [TopologicalSpace M] [T2Space M]
    {c d : ℝ → M} (hc : Continuous c) (hd : Continuous d)
    (heq : rationalCurveCode c = rationalCurveCode d) : c = d := by
  exact Rat.denseRange_cast.equalizer hc hd heq

/-- Curves related by the corresponding change of origin have identical shifted codes. -/
theorem rationalCurveCode_clock_eq_of_timeShift {M : Type*} {c d : ℝ → M}
    {a b : ℝ} (h : c = fun t ↦ d (t + a - b)) :
    rationalCurveCode (fun t ↦ c (t - a)) = rationalCurveCode (fun t ↦ d (t - b)) := by
  funext q
  change c ((q : ℝ) - a) = d ((q : ℝ) - b)
  rw [h]
  simp only [sub_add_cancel]

/-- A measurable actual curve family and clock give a measurable shifted rational code. -/
theorem measurable_rationalCurveCode_clock {A M : Type*}
    [MeasurableSpace A] [MeasurableSpace M]
    {G : A → ℝ → M} (hG : Measurable (Function.uncurry G))
    {u : A → ℝ} (hu : Measurable u) :
    Measurable (fun x ↦ rationalCurveCode (fun t ↦ G x (t - u x))) := by
  apply measurable_pi_lambda
  intro q
  exact hG.comp (measurable_id.prodMk (measurable_const.sub hu))

/-- The shifted curve code and the original clock together retain the original point. -/
theorem injective_rationalCurveCode_clock {A M : Type*} [TopologicalSpace M] [T2Space M]
    (G : A → ℝ → M) (hG : ∀ x, Continuous (G x))
    (b : A → M) (hb : Function.Injective b) (hzero : ∀ x, G x 0 = b x)
    (u : A → ℝ) :
    Function.Injective (fun x ↦ (rationalCurveCode (fun t ↦ G x (t - u x)), u x)) := by
  intro x y hxy
  have hu : u x = u y := congrArg Prod.snd hxy
  have he := eq_of_rationalCurveCode_eq
    ((hG x).comp (continuous_id.sub continuous_const))
    ((hG y).comp (continuous_id.sub continuous_const)) (congrArg Prod.fst hxy)
  have h := congrFun he (u x)
  change G x (u x - u x) = G y (u x - u y) at h
  apply hb
  simpa only [hu, sub_self, hzero] using h

end OTSelector.Geometry
