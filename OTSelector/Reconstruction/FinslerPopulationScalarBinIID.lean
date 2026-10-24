import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.PopulationScalarBinTypes
import OTSelector.Probability.TypedPopulationSampling

/-!
# Actual scalar-bin populations in the original marked iid experiment

The original chart-bin restrictions supply the common type-coordinate law and
the scalar half-gap for every same-type pair in the marked arrays. These claims
hold before choosing a sample-dependent matching, and zero-mass types require no
special assumption.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace J] [MeasurableSingletonClass J] [Fintype J]
  {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ)
  [MeasurableSpace (Option (J × Fin D.count × Fin D.count))]
  [MeasurableSingletonClass (Option (J × Fin D.count × Fin D.count))]
  (chart : X × Y → J) (source : X → ℝ) (target : Y → ℝ)
  (π : Measure (X × Y)) [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (hchart : Measurable chart) (hs : Measurable source) (ht : Measurable target)

/-- Every same-type pair of actual independently marked samples satisfies the
original scalar half-gap, simultaneously for all indices and types. -/
theorem scalarBinPopulationTypes_iid_half_gap
    {NS NT : Type*} [Fintype NS] [Fintype NT]
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1) :
    let Types := scalarBinPopulationTypes D chart source target π hchart hs ht
    ∀ᵐ ω ∂(Measure.pi (fun _ : NS ↦ Types.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : NT ↦ Types.targetMarkedLaw ν)),
      ∀ i j t, (ω.1 i).2 = some t → (ω.2 j).2 = some t →
        δ / 2 ≤ target (ω.2 j).1 - source (ω.1 i).1 := by
  let Types := scalarBinPopulationTypes D chart source target π hchart hs ht
  have hbins := Types.iid_marked_type_properties (μ := μ) (ν := ν) (I := NS) (J := NT)
    (fun t x ↦ source x ∈ D.cell t.2.1) (fun t y ↦ target y ∈ D.cell t.2.2)
    (fun t ↦ (scalarBinPopulationTypes_marginal_bins D chart source target π hchart hs ht t).1)
    (fun t ↦ (scalarBinPopulationTypes_marginal_bins D chart source target π hchart hs ht t).2)
  have hpositive := Types.iid_marked_positive_types (μ := μ) (ν := ν) (I := NS) (J := NT)
  filter_upwards [hbins, hpositive] with ω hωb hωp
  intro i j t hsrc htgt
  exact scalarBinPopulationTypes_gap D chart source target π hchart hs ht hgap t
    (hωp.1 i t hsrc) (source (ω.1 i).1) (hωb.1 i t hsrc)
      (target (ω.2 j).1) (hωb.2 j t htgt)

/-- Actual chart-preserving labels give the same joint chart-bin-coordinate law
for both original marked iid populations. -/
theorem scalarBinPopulationTypes_iid_coordinate_law
    {NS NT Z : Type*} [Fintype NS] [Fintype NT] [MeasurableSpace Z]
    (hπ : Vlasov.IsCoupling π μ ν)
    (left : J → X → Z) (right : J → Y → Z) (z₀ : Z)
    (hleft : ∀ j, Measurable (left j)) (hright : ∀ j, Measurable (right j))
    (hlabel : ∀ᵐ p ∂π, left (chart p) p.1 = right (chart p) p.2) :
    let Types := scalarBinPopulationTypes D chart source target π hchart hs ht
    let a : J × Fin D.count × Fin D.count → X → Z := fun t ↦ left t.1
    let b : J × Fin D.count × Fin D.count → Y → Z := fun t ↦ right t.1
    ((Measure.pi (fun _ : NS ↦ Types.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : NT ↦ Types.targetMarkedLaw ν))).map
        (Prod.map (fun x i ↦ populationTypedCoordinate a z₀ (x i))
          (fun y j ↦ populationTypedCoordinate b z₀ (y j))) =
      (Measure.pi (fun _ : NS ↦ Types.typeCoordinateLaw μ a z₀)).prod
        (Measure.pi (fun _ : NT ↦ Types.typeCoordinateLaw μ a z₀)) := by
  exact (scalarBinPopulationTypes D chart source target π hchart hs ht).iid_type_coordinate_law
    hπ (fun t ↦ left t.1) (fun t ↦ right t.1) z₀ (fun t ↦ hleft t.1)
    (fun t ↦ hright t.1)
    (scalarBinPopulationTypes_common_label D chart source target π hchart hs ht
      left right hleft hright hlabel)

end OTSelector.Reconstruction
