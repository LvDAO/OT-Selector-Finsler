import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Sequences
import OTSelector.Probability.StationaryL2Foundation

/-!
Conditions: Finite weakly regular Borel measure on a normal scene space, a sequential parameter space, pointwise-continuous measurable measure-preserving scene transformations and any original L2 observable.

Objects: Strong L2 continuity of the actual pullback/Koopman orbit of that observable.

Proof detail: First prove L2 continuity for bounded continuous probes by dominated convergence along parameter sequences. Their L2 density and the common isometry norm bound extend continuity to every L2 vector.

References: Rick Durrett: Section 1.6.2, Theorems 1.6.5–1.6.7, p. 30; D. H. Fremlin: 415Y(i), p. 65.
Relation: A direct strong-continuity extension from pointwise scene continuity and dense probes. Strong continuity is proved for the whole given Koopman representation rather than assumed for a selected dense set.
-/


/-! Strong continuity of the whole actual Koopman representation from
pointwise continuous scene translations and dense bounded continuous readouts. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Probability

/-- A pointwise continuous, measure-preserving scene family acts strongly
continuously on every scalar L² observable. Bounded continuous functions are
dense, and the exact pullbacks are isometries; no continuity of an arbitrary
measurable representative is assumed. -/
theorem continuous_compMeasurePreserving_of_continuous_scene
    {X Ω : Type*} [TopologicalSpace X] [SequentialSpace X]
    [TopologicalSpace Ω] [NormalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] [P.WeaklyRegular]
    (T : X → Ω → Ω) (hT : ∀ x, MeasurePreserving (T x) P P)
    (hc : ∀ ω, Continuous (fun x ↦ T x ω)) (f : Lp ℝ 2 P) :
    Continuous (fun x ↦ Lp.compMeasurePreserving (T x) (hT x) f) := by
  have hbounded (g : Ω →ᵇ ℝ) : Continuous (fun x ↦
      Lp.compMeasurePreserving (T x) (hT x)
        (BoundedContinuousFunction.toLp 2 P ℝ g)) := by
    have hg : MemLp g 2 P :=
      (memLp_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 P ℝ g)).1
        (Lp.memLp (BoundedContinuousFunction.toLp 2 P ℝ g))
    have hJ (x : X) : MemLp (fun ω ↦ g (T x ω)) 2 P :=
      hg.comp_measurePreserving (hT x)
    have hlaw (x : X) : P.map (fun ω ↦ g (T x ω)) = P.map g := by
      change P.map (g ∘ T x) = P.map g
      rw [← Measure.map_map g.continuous.measurable (hT x).measurable, (hT x).map_eq]
    have hd (x y : X) : ProbabilityTheory.IdentDistrib
        (fun ω ↦ g (T x ω)) (fun ω ↦ g (T y ω)) P P :=
      ⟨(hJ x).aestronglyMeasurable.aemeasurable,
        (hJ y).aestronglyMeasurable.aemeasurable, (hlaw x).trans (hlaw y).symm⟩
    have heq (x : X) : (hJ x).toLp (fun ω ↦ g (T x ω)) =
        Lp.compMeasurePreserving (T x) (hT x)
          (BoundedContinuousFunction.toLp 2 P ℝ g) := by
      apply Lp.ext
      exact (hJ x).coeFn_toLp.trans
        ((Lp.coeFn_compMeasurePreserving _ (hT x)).trans
          ((hT x).quasiMeasurePreserving.ae_eq_comp
            (BoundedContinuousFunction.coeFn_toLp 2 P ℝ g))).symm
    simpa only [heq] using continuous_toLp_of_ae_continuous_identDistrib
      P _ hJ hd (Filter.Eventually.of_forall fun ω ↦ g.continuous.comp (hc ω))
  have hequi : Equicontinuous (fun x (g : Lp ℝ 2 P) ↦
      Lp.compMeasurePreserving (T x) (hT x) g) := by
    apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
    intro g h x
    exact ((Lp.isometry_compMeasurePreserving (hT x)).dist_eq g h).le
  apply continuous_iff_continuousAt.2
  intro x₀
  have hdense : Dense (Set.range
      (BoundedContinuousFunction.toLp 2 P ℝ : (Ω →ᵇ ℝ) →L[ℝ] Lp ℝ 2 P)) :=
    BoundedContinuousFunction.toLp_denseRange ℝ P ℝ (by norm_num)
  refine hdense.induction (P := fun g ↦ ContinuousAt
    (fun x ↦ Lp.compMeasurePreserving (T x) (hT x) g) x₀) ?_ ?_ f
  · rintro g ⟨h, rfl⟩
    exact (hbounded h).continuousAt
  · exact hequi.isClosed_setOfPred_tendsto
      (Lp.isometry_compMeasurePreserving (hT x₀)).continuous

end OTSelector.Probability
