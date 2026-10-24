import OTSelector.Probability.RadonNikodymMarking
import OTSelector.Probability.SubcouplingTypeMarking
import OTSelector.Probability.SubcouplingTypedIID

/-!
Conditions: Finite actual typed subcouplings, measurable type-specific coordinate maps and equal original coordinate submarginals for both colors; the unused type uses a fixed coordinate.

Objects: One genuine common joint type-coordinate law, its exact component masses and iid two-color pushforwards, retaining the original physical sample in the marked law.

Proof detail: Expand the finite marked mixture including the residual none component, apply each original coordinate map and use equality of each retained component and residual total mass; transport the exact marginal identity through finite products.

References: Günter Last and Mathew Penrose: Section 5.2, Definition 5.3 and equations (5.5)–(5.6), pp. 40–41; D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
Relation: A local finite-mixture law-identification interface. The common type-coordinate law is an actual pushforward, not a newly postulated population law.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationTypeCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationTypeCoordinates`; the selected original proof blocks follow. -/
section

/-!
# Common original type and coordinate law for the two iid colors

Each retained type reads its actual chart coordinate; the unused type receives a
fixed coordinate. The original physical point remains part of the marked sample.
Equality of the original type-coordinate submarginals therefore gives a common
joint type-coordinate distribution and independent arrays from that distribution.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Read the actual coordinate assigned to the retained type; unused original
points keep their `none` type and receive a fixed coordinate. -/
def populationTypedCoordinate {X Z T : Type*} (a : T → X → Z) (z₀ : Z)
    (p : X × Option T) : Option T × Z :=
  (p.2, p.2.elim z₀ (fun t ↦ a t p.1))

/-- Reading the retained type's actual coordinate is measurable. -/
theorem measurable_populationTypedCoordinate
    {X Z T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype T]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    (a : T → X → Z) (z₀ : Z) (ha : ∀ t, Measurable (a t)) :
    Measurable (populationTypedCoordinate a z₀) := by
  apply measurable_from_prod_countable_left
  intro tag
  cases tag with
  | none => exact (measurable_const : Measurable (fun _ : X ↦ ((none : Option T), z₀)))
  | some t => exact measurable_const.prodMk (ha t)

/-- The coordinate readout keeps the raw original mass in every retained and
residual type. -/
theorem finiteRNMarkLaw_map_type_coordinate
    {X Z T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype T]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    (μ : Measure X) (m : T → Measure X)
    (a : T → X → Z) (z₀ : Z) (ha : ∀ t, Measurable (a t)) :
    (finiteRNMarkLaw μ m).map (populationTypedCoordinate a z₀) =
      (μ - ∑ t, m t) univ • Measure.dirac (none, z₀) +
        ∑ t, ((m t).map (a t)).map (fun z ↦ (some t, z)) := by
  have hm := measurable_populationTypedCoordinate a z₀ ha
  have hnone : ((μ - ∑ t, m t).map (fun x ↦ (x, (none : Option T)))).map
      (populationTypedCoordinate a z₀) =
        (μ - ∑ t, m t) univ • Measure.dirac (none, z₀) := by
    rw [Measure.map_map hm (show Measurable (fun x : X ↦ (x, (none : Option T))) from
      measurable_id.prodMk measurable_const)]
    change (μ - ∑ t, m t).map (fun _ : X ↦ ((none : Option T), z₀)) = _
    exact Measure.map_const _ _
  have hsome (t : T) : ((m t).map (fun x ↦ (x, some t))).map
      (populationTypedCoordinate a z₀) =
        ((m t).map (a t)).map (fun z ↦ (some t, z)) := by
    rw [Measure.map_map hm (show Measurable (fun x : X ↦ (x, some t)) from
      measurable_id.prodMk measurable_const),
      Measure.map_map (show Measurable (fun z : Z ↦ (some t, z)) from
        measurable_const.prodMk measurable_id) (ha t)]
    rfl
  rw [finiteRNMarkLaw, Measure.map_add _ _ hm, Measure.map_finset_sum' hm.aemeasurable,
    hnone]
  simp only [hsome]

namespace PopulationSubcouplingTypes
variable {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  (D : PopulationSubcouplingTypes π T)
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
/-- Actual equal type-coordinate submarginals give a common joint law of types
and coordinates. The original unused mass is still present. -/
theorem common_type_coordinate_law (hπ : Vlasov.IsCoupling π μ ν)
    (a : T → X → Z) (b : T → Y → Z) (z₀ : Z)
    (ha : ∀ t, Measurable (a t)) (hb : ∀ t, Measurable (b t))
    (hlabel : ∀ t, (D.source t).map (a t) = (D.target t).map (b t)) :
    (D.sourceMarkedLaw μ).map (populationTypedCoordinate a z₀) =
      (D.targetMarkedLaw ν).map (populationTypedCoordinate b z₀) := by
  rw [sourceMarkedLaw, targetMarkedLaw,
    finiteRNMarkLaw_map_type_coordinate μ D.source a z₀ ha,
    finiteRNMarkLaw_map_type_coordinate ν D.target b z₀ hb]
  have hnone := (D.common_type_mass hπ none).1.trans (D.common_type_mass hπ none).2.symm
  simp only [finiteRNMarkComponent] at hnone
  rw [hnone]
  simp only [hlabel]

/-- The common coordinate law is the exact image of the original marked source
population, retaining each original type mass. -/
def typeCoordinateLaw (μ : Measure X) (a : T → X → Z) (z₀ : Z) :
    Measure (Option T × Z) := (D.sourceMarkedLaw μ).map (populationTypedCoordinate a z₀)

instance typeCoordinateLaw_isFinite (a : T → X → Z) (z₀ : Z) :
    IsFiniteMeasure (D.typeCoordinateLaw μ a z₀) := by
  unfold typeCoordinateLaw
  infer_instance

/-- Independently marked original physical arrays yield two independent iid
arrays with the same joint type-coordinate distribution. -/
theorem iid_type_coordinate_law {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν)
    (a : T → X → Z) (b : T → Y → Z) (z₀ : Z)
    (ha : ∀ t, Measurable (a t)) (hb : ∀ t, Measurable (b t))
    (hlabel : ∀ t, (D.source t).map (a t) = (D.target t).map (b t)) :
    ((Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν))).map
        (Prod.map (fun x i ↦ populationTypedCoordinate a z₀ (x i))
          (fun y j ↦ populationTypedCoordinate b z₀ (y j))) =
      (Measure.pi (fun _ : I ↦ D.typeCoordinateLaw μ a z₀)).prod
        (Measure.pi (fun _ : J ↦ D.typeCoordinateLaw μ a z₀)) := by
  have has := measurable_populationTypedCoordinate a z₀ ha
  have hbt := measurable_populationTypedCoordinate b z₀ hb
  rw [← Measure.map_prod_map _ _
    (show Measurable (fun x : I → X × Option T ↦ fun i ↦ populationTypedCoordinate a z₀ (x i)) from
      measurable_pi_lambda _ (fun i ↦ has.comp (measurable_pi_apply i)))
    (show Measurable (fun y : J → Y × Option T ↦ fun j ↦ populationTypedCoordinate b z₀ (y j)) from
      measurable_pi_lambda _ (fun j ↦ hbt.comp (measurable_pi_apply j))),
    Measure.pi_map_pi (fun _ ↦ has.aemeasurable),
    Measure.pi_map_pi (fun _ ↦ hbt.aemeasurable),
    ← D.common_type_coordinate_law hπ a b z₀ ha hb hlabel]
  rfl

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
/-- The common original type-coordinate law is a probability law whenever the
original source population is a probability law. -/
theorem typeCoordinateLaw_isProbability [IsProbabilityMeasure μ]
    (hπ : Vlasov.IsCoupling π μ ν)
    (a : T → X → Z) (z₀ : Z) (ha : ∀ t, Measurable (a t)) :
    IsProbabilityMeasure (D.typeCoordinateLaw μ a z₀) := by
  have : IsProbabilityMeasure (D.sourceMarkedLaw μ) :=
    finiteRNMarkLaw_isProbability μ D.source (D.marginal_domination hπ).1
  exact Measure.isProbabilityMeasure_map (measurable_populationTypedCoordinate a z₀ ha).aemeasurable

/-- Every refined coordinate cell has exactly its original type-subpopulation
mass, with no normalization factor. -/
theorem typeCoordinateLaw_cell (a : T → X → Z) (z₀ : Z)
    (ha : ∀ t, Measurable (a t)) (t : T) {A : Set Z} (hA : MeasurableSet A) :
    D.typeCoordinateLaw μ a z₀ ({some t} ×ˢ A) = (D.source t).map (a t) A := by
  have hpre : populationTypedCoordinate a z₀ ⁻¹' ({some t} ×ˢ A) =
      (a t ⁻¹' A) ×ˢ {some t} := by
    ext p
    rcases p with ⟨x, tag⟩
    cases tag <;> simp +contextual [populationTypedCoordinate, and_comm]
  rw [typeCoordinateLaw, sourceMarkedLaw,
    Measure.map_apply (measurable_populationTypedCoordinate a z₀ ha)
      ((measurableSet_singleton _).prod hA), hpre,
    finiteRNMarkLaw_apply_cell μ D.source (some t) ((ha t) hA),
    Measure.map_apply (ha t) hA]
  rfl

/-- The retained type probability is the mass of its unchanged original
subcoupling. -/
theorem typeCoordinateLaw_type_mass (a : T → X → Z) (z₀ : Z)
    (ha : ∀ t, Measurable (a t)) (t : T) :
    D.typeCoordinateLaw μ a z₀ ({some t} ×ˢ univ) = D.component t univ := by
  rw [D.typeCoordinateLaw_cell a z₀ ha t MeasurableSet.univ,
    Measure.map_apply (ha t) MeasurableSet.univ, preimage_univ,
    source, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]

/-- Forgetting coordinates leaves the same original type distribution. -/
theorem typeCoordinateLaw_map_fst (hπ : Vlasov.IsCoupling π μ ν)
    (a : T → X → Z) (z₀ : Z) (ha : ∀ t, Measurable (a t)) :
    (D.typeCoordinateLaw μ a z₀).map Prod.fst = D.typeLaw := by
  rw [typeCoordinateLaw, Measure.map_map measurable_fst
    (measurable_populationTypedCoordinate a z₀ ha)]
  exact (D.marked_type_laws hπ).1

omit [IsFiniteMeasure π] [IsFiniteMeasure μ] in
/-- Actual type-coordinate support, such as a closed unit cube, transfers to the
common original joint law. The residual type uses the same fixed admissible point. -/
theorem typeCoordinateLaw_ae_coordinate_mem (a : T → X → Z) (z₀ : Z)
    (ha : ∀ t, Measurable (a t)) {C : Set Z} (hC : MeasurableSet C) (hz₀ : z₀ ∈ C)
    (hlabel : ∀ t, ∀ᵐ x ∂D.source t, a t x ∈ C) :
    ∀ᵐ p ∂D.typeCoordinateLaw μ a z₀, p.2 ∈ C := by
  have hm := measurable_populationTypedCoordinate a z₀ ha
  have hp : MeasurableSet {p : X × Option T | (populationTypedCoordinate a z₀ p).2 ∈ C} :=
    hm.snd hC
  apply (ae_map_iff hm.aemeasurable (measurable_snd hC)).mpr
  change ∀ᵐ p ∂finiteRNMarkLaw μ D.source, (populationTypedCoordinate a z₀ p).2 ∈ C
  rw [finiteRNMarkLaw, ae_add_measure_iff]
  constructor
  · apply (ae_map_iff (show Measurable (fun x : X ↦ (x, (none : Option T))) from
      measurable_id.prodMk measurable_const).aemeasurable hp).mpr
    exact Filter.Eventually.of_forall (fun _ ↦ hz₀)
  · rw [← Measure.sum_fintype, Measure.ae_sum_iff]
    intro t
    apply (ae_map_iff (show Measurable (fun x : X ↦ (x, some t)) from
      measurable_id.prodMk measurable_const).aemeasurable hp).mpr
    exact hlabel t

end PopulationSubcouplingTypes
end OTSelector.Reconstruction

end
end
