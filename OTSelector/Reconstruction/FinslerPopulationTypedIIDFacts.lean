import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Probability.TypedPopulationSampling
import Mathlib.Probability.Independence.Basic

/-!
# Independence of the original RN-marked type-coordinate samples

The exact original two-array product law supplies the iid and cross-color
independence facts used by tagged dyadic matching. No new sample law is assumed.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- An exact two-array product law supplies all iid and cross-color independence
facts required by the original-sample matching estimates. -/
theorem iid_facts_of_array_product_law
    {Ω Z I J : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] [Fintype I] [Fintype J]
    (P : Measure Ω) [IsProbabilityMeasure P] (L : Measure Z) [IsProbabilityMeasure L]
    (xs : Ω → I → Z) (ys : Ω → J → Z) (hx : Measurable xs) (hy : Measurable ys)
    (hjoint : P.map (fun ω ↦ (xs ω, ys ω)) =
      (Measure.pi (fun _ : I ↦ L)).prod (Measure.pi (fun _ : J ↦ L))) :
    iIndepFun (fun i ω ↦ xs ω i) P ∧ iIndepFun (fun j ω ↦ ys ω j) P ∧
      (∀ i, P.map (fun ω ↦ xs ω i) = L) ∧ (∀ j, P.map (fun ω ↦ ys ω j) = L) ∧
        IndepFun xs ys P := by
  have hp : MeasurePreserving (fun ω ↦ (xs ω, ys ω)) P
      ((Measure.pi (fun _ : I ↦ L)).prod (Measure.pi (fun _ : J ↦ L))) :=
    ⟨hx.prodMk hy, hjoint⟩
  have hxs : MeasurePreserving xs P (Measure.pi (fun _ : I ↦ L)) :=
    measurePreserving_fst.comp hp
  have hys : MeasurePreserving ys P (Measure.pi (fun _ : J ↦ L)) :=
    measurePreserving_snd.comp hp
  have hxl (i : I) : P.map (fun ω ↦ xs ω i) = L :=
    ((measurePreserving_eval (fun _ : I ↦ L) i).comp hxs).map_eq
  have hyl (j : J) : P.map (fun ω ↦ ys ω j) = L :=
    ((measurePreserving_eval (fun _ : J ↦ L) j).comp hys).map_eq
  refine ⟨?_, ?_, hxl, hyl, ?_⟩
  · apply (iIndepFun_iff_map_fun_eq_pi_map
      (fun i ↦ ((measurable_pi_apply i).comp hx).aemeasurable)).mpr
    change P.map xs = Measure.pi (fun i ↦ P.map (fun ω ↦ xs ω i))
    simp only [hxl]
    exact hxs.map_eq
  · apply (iIndepFun_iff_map_fun_eq_pi_map
      (fun j ↦ ((measurable_pi_apply j).comp hy).aemeasurable)).mpr
    change P.map ys = Measure.pi (fun j ↦ P.map (fun ω ↦ ys ω j))
    simp only [hyl]
    exact hys.map_eq
  · apply (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable).mpr
    rw [hjoint, hxs.map_eq, hys.map_eq]

namespace PopulationSubcouplingTypes
variable {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  (D : PopulationSubcouplingTypes π T)
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The original RN-marked experiment automatically has all common-law iid
hypotheses needed by the tagged hierarchy matching consumer. -/
theorem iid_type_coordinate_facts {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν)
    (a : T → X → Z) (b : T → Y → Z) (z₀ : Z)
    (ha : ∀ t, Measurable (a t)) (hb : ∀ t, Measurable (b t))
    (hlabel : ∀ t, (D.source t).map (a t) = (D.target t).map (b t)) :
    let P := (Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν))
    let L := D.typeCoordinateLaw μ a z₀
    let xs := fun i (ω : (I → X × Option T) × (J → Y × Option T)) ↦
      populationTypedCoordinate a z₀ (ω.1 i)
    let ys := fun j (ω : (I → X × Option T) × (J → Y × Option T)) ↦
      populationTypedCoordinate b z₀ (ω.2 j)
    IsProbabilityMeasure P ∧ IsProbabilityMeasure L ∧
      (∀ i, Measurable (xs i)) ∧ (∀ j, Measurable (ys j)) ∧
      iIndepFun xs P ∧ iIndepFun ys P ∧
      (∀ i, P.map (xs i) = L) ∧ (∀ j, P.map (ys j) = L) ∧
        IndepFun (fun ω i ↦ xs i ω) (fun ω j ↦ ys j ω) P := by
  have hprob := D.marked_probabilities hπ
  let : IsProbabilityMeasure (D.sourceMarkedLaw μ) := hprob.1
  let : IsProbabilityMeasure (D.targetMarkedLaw ν) := hprob.2.1
  let : IsProbabilityMeasure (D.typeCoordinateLaw μ a z₀) :=
    D.typeCoordinateLaw_isProbability hπ a z₀ ha
  have has := measurable_populationTypedCoordinate a z₀ ha
  have hbt := measurable_populationTypedCoordinate b z₀ hb
  have hxs : Measurable (fun ω : (I → X × Option T) × (J → Y × Option T) ↦
      fun i ↦ populationTypedCoordinate a z₀ (ω.1 i)) := by fun_prop
  have hys : Measurable (fun ω : (I → X × Option T) × (J → Y × Option T) ↦
      fun j ↦ populationTypedCoordinate b z₀ (ω.2 j)) := by fun_prop
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro i
    exact (measurable_pi_apply i).comp hxs
  · intro j
    exact (measurable_pi_apply j).comp hys
  · exact iid_facts_of_array_product_law _ _ _ _ hxs hys
      (D.iid_type_coordinate_law hπ a b z₀ ha hb hlabel)

end PopulationSubcouplingTypes
end OTSelector.Reconstruction
