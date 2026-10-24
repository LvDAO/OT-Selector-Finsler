import OTSelector.MeasureTheory.PositiveQuadraticDifference
import OTSelector.Probability.CavitySemidiscreteSpatialRooting
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Restricted atomlessness for the actual marked quadratic cost

For each source mark, distinct target positions give an atomless difference of
positive quadratic costs. Fubini transfers this fact to the original Haar times
mark law, and absolute continuity permits intensities and spatial restrictions.
Positivity is required only on the common legal source set.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {ι α β : Type*} [Fintype ι] [MeasurableSpace α]

/-- Measurability of the literal spatial-difference quadratic cost at one target. -/
theorem measurable_marked_matrixQuadratic_cost
    (A : α → β → Matrix ι ι ℝ) (y : (ι → ℝ) × β)
    (hA : Measurable (fun s ↦ A s y.2)) :
    Measurable (fun x : (ι → ℝ) × α ↦ Probability.cavitySpatialDifferenceCost
      (fun s t v ↦ Reconstruction.matrixQuadratic (A s t) v) x y) :=
  Reconstruction.continuous_matrixQuadratic.measurable.comp
    ((hA.comp measurable_snd).prodMk (measurable_const.sub measurable_fst))

/-- Distinct spatial targets give atomless cost differences after restriction
to any measurable common legal source set. Both target matrices may depend on
the source mark, and no finiteness of the source spatial law is assumed. -/
theorem nullSingletonClass_map_marked_matrixQuadratic_sub
    (m : Measure (ι → ℝ)) [m.IsAddHaarMeasure]
    (κ : Measure α) [SFinite κ] {μ : Measure ((ι → ℝ) × α)} (hμ : μ ≪ m.prod κ)
    (A : α → β → Matrix ι ι ℝ) {y z : (ι → ℝ) × β}
    (hy : Measurable (fun s ↦ A s y.2)) (hz : Measurable (fun s ↦ A s z.2))
    (hyz : y.1 ≠ z.1) {D : Set ((ι → ℝ) × α)} (hD : MeasurableSet D)
    (hpos : ∀ x ∈ D, (A x.2 y.2).PosDef ∧ (A x.2 z.2).PosDef) :
    NullSingletonClass ((μ.restrict D).map (fun x ↦
      Probability.cavitySpatialDifferenceCost
        (fun s t v ↦ Reconstruction.matrixQuadratic (A s t) v) x y -
      Probability.cavitySpatialDifferenceCost
        (fun s t v ↦ Reconstruction.matrixQuadratic (A s t) v) x z)) := by
  let f : ((ι → ℝ) × α) → ℝ := fun x ↦
    Probability.cavitySpatialDifferenceCost
      (fun s t v ↦ Reconstruction.matrixQuadratic (A s t) v) x y -
    Probability.cavitySpatialDifferenceCost
      (fun s t v ↦ Reconstruction.matrixQuadratic (A s t) v) x z
  have hf : Measurable f := (measurable_marked_matrixQuadratic_cost A y hy).sub
    (measurable_marked_matrixQuadratic_cost A z hz)
  refine ⟨fun r ↦ ?_⟩
  change (μ.restrict D).map f {r} = 0
  rw [Measure.map_apply hf (measurableSet_singleton _),
    Measure.restrict_apply (hf (measurableSet_singleton _))]
  apply hμ
  rw [Measure.prod_apply_symm ((hf (measurableSet_singleton _)).inter hD)]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Eventually.of_forall
  intro s
  change m ((fun x : ι → ℝ ↦ (x, s)) ⁻¹' (f ⁻¹' {r} ∩ D)) = 0
  by_cases hs : ∃ x : ι → ℝ, (x, s) ∈ D
  · obtain ⟨x, hx⟩ := hs
    have hatom : NullSingletonClass (m.map (fun v ↦
        Reconstruction.matrixQuadratic (A s y.2) (y.1 - v) -
          Reconstruction.matrixQuadratic (A s z.2) (z.1 - v))) :=
      nullSingletonClass_map_matrixQuadratic_sub m Measure.AbsolutelyContinuous.rfl
        (hpos (x, s) hx).1 (hpos (x, s) hx).2 hyz
    have hnull := measure_singleton (μ := m.map (fun v ↦
      Reconstruction.matrixQuadratic (A s y.2) (y.1 - v) -
        Reconstruction.matrixQuadratic (A s z.2) (z.1 - v))) r
    have hm : Measurable (fun v : ι → ℝ ↦ f (v, s)) :=
      hf.comp (measurable_id.prodMk measurable_const)
    change m.map (fun v ↦ f (v, s)) {r} = 0 at hnull
    rw [Measure.map_apply hm (measurableSet_singleton _)] at hnull
    exact measure_mono_null (fun v hv ↦ hv.1) hnull
  · have hempty : (fun x : ι → ℝ ↦ (x, s)) ⁻¹' (f ⁻¹' {r} ∩ D) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hs ⟨x, hx.2⟩
    rw [hempty, measure_empty]

end OTSelector.Geometry
