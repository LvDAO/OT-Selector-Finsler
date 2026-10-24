import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.IntrinsicLabelHessian
import OTSelector.Geometry.Finsler.SeedKernelMeasurability
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerSeedKernelMeasurabilityIntegral.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerSeedKernelMeasurabilityIntegral`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.SeedKernelMeasurabilityIntegral

* **Conditions:** A jointly strongly measurable parameterized integrand and measurable endpoint maps; geometric corollaries use the actual Borel seed inverse-Hessian kernel.
* **Objects:** Measurable variable-endpoint interval integrals, compliance matrices, inverse coefficients and primitive differences with offsets.
* **Proof detail:** Encode endpoint indicators in one product-measurable integrand, use parameterized integration and compose with measurable maps and totalized matrix inversion.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46): Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition prop:rough-ray-quadratic, lines 1188–1205; equation eq:rough-ray-quadratic, integral inverse-Hessian coefficient.

Source relation (derived): The no-integrability-premise form relies on Lean totalizing nonintegrable Bochner integrals to zero; it claims measurability only, not an analytic finite compliance value.
-/

/-!
# Measurable original compliance and quadratic coefficients

The original jointly Borel inverse label Hessian can be integrated over arbitrary
measurable endpoint parameters. This yields a measurable compliance matrix and
its actual matrix inverse, including arbitrary reference times and scalar offsets.
The measurability proof uses the ordinary parameterized Bochner integral and does
not require an ordering of the endpoints or an integrability assumption.
-/

open Set MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry

/-- A jointly strongly measurable function has strongly measurable oriented
interval integrals with arbitrary measurable endpoints. -/
theorem stronglyMeasurable_intervalIntegral_with_endpoints
    {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Ω × ℝ → V} (hf : StronglyMeasurable f)
    {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b) :
    StronglyMeasurable (fun p ↦ ∫ t in a p..b p, f (p, t)) := by
  have hIoc {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b) :
      StronglyMeasurable (fun p ↦ ∫ t in Ioc (a p) (b p), f (p, t)) := by
    let s := {q : Ω × ℝ | a q.1 < q.2 ∧ q.2 ≤ b q.1}
    have hs : MeasurableSet s :=
      (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hb.comp measurable_fst))
    have hi := (hf.indicator hs).integral_prod_right' (ν := volume)
    convert hi using 1
    funext p
    have heq : (fun t ↦ s.indicator f (p, t)) =
        (Ioc (a p) (b p)).indicator (fun t ↦ f (p, t)) := by
      funext t
      rfl
    rw [heq, integral_indicator measurableSet_Ioc]
  convert (hIoc ha hb).sub (hIoc hb ha) using 1
  funext p
  rfl

/-- Measurable changes of the label parameter preserve measurable interval integrals. -/
theorem stronglyMeasurable_intervalIntegral_comp
    {Ω P V : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : P × ℝ → V} (hf : StronglyMeasurable f)
    {w : Ω → P} (hw : Measurable w) {a b : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    StronglyMeasurable (fun p ↦ ∫ t in a p..b p, f (w p, t)) := by
  have hcomp : StronglyMeasurable (fun p : Ω × ℝ ↦ f (w p.1, p.2)) :=
    hf.comp_measurable ((hw.comp measurable_fst).prodMk measurable_snd)
  exact stronglyMeasurable_intervalIntegral_with_endpoints hcomp ha hb

namespace ContinuousFinslerNorm.CalibratedLevelSeedPatch

set_option backward.isDefEq.respectTransparency false

variable {E M ι Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Original compliance is jointly Borel in any measurable label and two original
time endpoints, with all geometric data coming from the original seed. -/
theorem measurable_familyLabelCompliance (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    {w : Ω → S.labels} (hw : Measurable w) {a b : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p ↦ ∫ t in a p..b p,
      (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w p, t))⁻¹) := by
  have hK := (S.measurable_familyLabelKernel hF bW).stronglyMeasurable
  have hi := stronglyMeasurable_intervalIntegral_comp hK hw ha hb
  exact hi.measurable

/-- The inverse original compliance matrix is a jointly Borel quadratic coefficient. -/
theorem measurable_familyLabelCoefficient (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    {w : Ω → S.labels} (hw : Measurable w) {a b : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p ↦ (∫ t in a p..b p,
      (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w p, t))⁻¹)⁻¹) :=
  measurable_real_matrix_inverse.comp (S.measurable_familyLabelCompliance hF bW hw ha hb)

/-- Subtracting two original compliance primitives with the same arbitrary
measurable reference time remains jointly Borel. -/
theorem measurable_familyLabelPrimitiveDifference (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    {w : Ω → S.labels} (hw : Measurable w) {r x y : Ω → ℝ}
    (hr : Measurable r) (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun p ↦
      (∫ t in r p..(y p - S.level),
        (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w p, t))⁻¹) -
      (∫ t in r p..(x p - S.level),
        (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w p, t))⁻¹)) :=
  (S.measurable_familyLabelCompliance hF bW hw hr (hy.sub_const _)).sub
    (S.measurable_familyLabelCompliance hF bW hw hr (hx.sub_const _))

/-- Scalar population coordinates are converted to original time using the seed's
actual potential level; the resulting inverse compliance is jointly Borel. -/
theorem measurable_familyLabelScalarCoefficient (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    {w : Ω → S.labels} (hw : Measurable w) {x y : Ω → ℝ}
    (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun p ↦ (∫ t in (x p - S.level)..(y p - S.level),
      (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w p, t))⁻¹)⁻¹) :=
  S.measurable_familyLabelCoefficient hF bW hw (hx.sub_const _) (hy.sub_const _)

end ContinuousFinslerNorm.CalibratedLevelSeedPatch
end OTSelector.Geometry

end
end
