import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.Calibration.SeedLabelReference
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.IntrinsicLabelHessian
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Finsler.SeedKernelMeasurability
import OTSelector.Geometry.Finsler.SeedKernelMeasurabilityIntegral
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerSeedRootCoefficient.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerSeedRootCoefficient`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.RootCoefficient

* **Conditions:** An actual calibrated seed with its measurable injective population label embedding and a chosen transverse basis; the stated inherited measurability assumptions govern the inverse and integral theorems.
* **Objects:** The seed-root image, its inverse seed label, a zero-extended inverse-Hessian kernel and the inverse of its actual time integral in the original basis.
* **Proof detail:** Use Lusin–Souslin to invert the Borel label embedding, extend the seed kernel by zero, integrate its measurable parameterized entries and evaluate the extension on genuine seed labels.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46): Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition prop:rough-ray-quadratic, lines 1188–1205; equation eq:rough-ray-quadratic, integral inverse-Hessian coefficient.

Source relation (derived): Borel inverse and parameterized integration justify measurability; the inverse-Hessian interval coefficient is the project construction, not a classical-book theorem.
-/

/-!
# Actual population roots read the original seed coefficient

The unscreened seed embeds measurably into the given population root labels.
Its inverse reads the original seed label on the image. Extending the original
kernel by zero gives a jointly Borel function on all roots, and its actual
interval integral defines the population quadratic coefficient in the same basis.
-/

open Set Function MeasureTheory Matrix Module Manifold OTSelector.Geometry
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

variable {E M Z ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual population roots reached by this unscreened original seed. -/
def populationSeedRootDomain (S : F.CalibratedLevelSeedPatch u) (a : M → Z) : Set Z :=
  range (fun w : S.labels ↦ a (S.curve w 0))

/-- The original seed label over an actual population root in the seed image. -/
def populationSeedRootLabel (S : F.CalibratedLevelSeedPatch u) (a : M → Z) :
    populationSeedRootDomain S a → S.labels :=
  rangeSplitting (fun w : S.labels ↦ a (S.curve w 0))

variable [Fintype ι] [DecidableEq ι]

/-- The original inverse label Hessian, read on actual population roots and
extended by zero away from this seed's image. -/
def populationSeedRootKernel (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (bW : Basis ι ℝ S.covector.ker) : Z × ℝ → Matrix ι ι ℝ :=
  extend (fun q : S.labels × ℝ ↦ (a (S.curve q.1 0), q.2))
    (fun q ↦ (F.familyLabelHessianMatrix bW (fun p ↦ S.curve p.1 p.2) (q.1, q.2))⁻¹)
    (fun _ ↦ 0)

/-- The actual inverse compliance coefficient in population scalar coordinates. -/
def populationSeedRootCoefficient (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (bW : Basis ι ℝ S.covector.ker) (q : Z × (ℝ × ℝ)) : Matrix ι ι ℝ :=
  (∫ t in (q.2.1 - S.level)..(q.2.2 - S.level),
    populationSeedRootKernel S a bW (q.1, t))⁻¹

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instSeedRootMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  {a : M → Z} (ha : Measurable a)
  (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

omit [Fintype ι] [DecidableEq ι] in
/-- The actual root image is measurable. -/
theorem measurableSet_populationSeedRootDomain :
    MeasurableSet (populationSeedRootDomain S a) :=
  (measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj).measurableSet_range

omit [Fintype ι] [DecidableEq ι] in
/-- The actual inverse from a population root to its original seed label is measurable. -/
theorem measurable_populationSeedRootLabel : Measurable (populationSeedRootLabel S a) :=
  (measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj).measurable_rangeSplitting

omit [Fintype ι] [DecidableEq ι] in
/-- Reading an actual root recovers its original seed label exactly. -/
theorem populationSeedRootLabel_at_label (w : S.labels) :
    populationSeedRootLabel S a ⟨a (S.curve w 0), mem_range_self w⟩ = w :=
  rightInverse_rangeSplitting
    (measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj).injective w

/-- The original kernel is Borel jointly in the actual population root and time. -/
theorem measurable_populationSeedRootKernel (bW : Basis ι ℝ S.covector.ker) :
    Measurable (populationSeedRootKernel S a bW) := by
  have he : MeasurableEmbedding (fun q : S.labels × ℝ ↦
      (a (S.curve q.1 0), q.2)) :=
    (measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj).prodMap
      MeasurableEmbedding.id
  exact he.measurable_extend (S.measurable_familyLabelKernel hF bW) measurable_const

/-- At every root in the seed image, the population kernel is the literal original kernel. -/
theorem populationSeedRootKernel_at_label (bW : Basis ι ℝ S.covector.ker)
    (w : S.labels) (t : ℝ) :
    populationSeedRootKernel S a bW (a (S.curve w 0), t) =
      (F.familyLabelHessianMatrix bW (fun p ↦ S.curve p.1 p.2) (w, t))⁻¹ := by
  have he : MeasurableEmbedding (fun q : S.labels × ℝ ↦
      (a (S.curve q.1 0), q.2)) :=
    (measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj).prodMap
      MeasurableEmbedding.id
  exact he.injective.extend_apply _ _ (w, t)

/-- Actual inverse compliance is Borel jointly in the population root and both scalar endpoints. -/
theorem measurable_populationSeedRootCoefficient (bW : Basis ι ℝ S.covector.ker) :
    Measurable (populationSeedRootCoefficient S a bW) := by
  have hK := (measurable_populationSeedRootKernel S hF hcomplete hu ha hinj bW).stronglyMeasurable
  have hi := stronglyMeasurable_intervalIntegral_comp hK measurable_fst
    ((measurable_fst.comp measurable_snd).sub_const (S.level : ℝ))
    ((measurable_snd.comp measurable_snd).sub_const (S.level : ℝ))
  exact ContinuousFinslerNorm.measurable_real_matrix_inverse.comp hi.measurable

/-- The root coefficient is exactly the original seed compliance inverse at the same scalar pair. -/
theorem populationSeedRootCoefficient_at_label (bW : Basis ι ℝ S.covector.ker)
    (w : S.labels) (x y : ℝ) :
    populationSeedRootCoefficient S a bW (a (S.curve w 0), x, y) =
      (∫ t in (x - S.level)..(y - S.level),
        (F.familyLabelHessianMatrix bW (fun p ↦ S.curve p.1 p.2) (w, t))⁻¹)⁻¹ := by
  apply congrArg Inv.inv
  apply intervalIntegral.integral_congr
  intro t ht
  exact populationSeedRootKernel_at_label S hF hcomplete hu ha hinj bW w t

end OTSelector.Reconstruction

end
end
