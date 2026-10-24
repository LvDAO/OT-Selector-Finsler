import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.FinslerPopulationTypedIIDFacts
import OTSelector.Reconstruction.FinslerPopulationTypedFullRetention
import OTSelector.Reconstruction.DyadicCubePartition

/-!
# Actual population type data for the original marked matching experiment

Finite original subcouplings retain their full mass, common cube-coordinate laws,
and actual endpoint properties. These data produce the samplewise cost hypotheses
for one tagged hierarchy without assuming a sample law or a balanced type count.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Raw original population data underlying one finite type-and-cube matching. -/
structure PopulationTypedCostData
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (π : Measure (X × Y)) (μ : Measure X) (ν : Measure Y)
    (T : Type*) [Fintype T] (q : ℕ) (cost : X → Y → ℝ) where
  types : PopulationSubcouplingTypes π T
  sum_eq : ∑ t, types.component t = π
  sourceCoordinate : T → X → DyadicUnitCube q
  targetCoordinate : T → Y → DyadicUnitCube q
  measurable_sourceCoordinate : ∀ t, Measurable (sourceCoordinate t)
  measurable_targetCoordinate : ∀ t, Measurable (targetCoordinate t)
  common_coordinate : ∀ t,
    (types.source t).map (sourceCoordinate t) = (types.target t).map (targetCoordinate t)
  paired_coordinate : ∀ t, ∀ᵐ p ∂types.component t,
    sourceCoordinate t p.1 = targetCoordinate t p.2
  quadraticConstant : ℝ
  globalBound : ℝ
  quadratic_nonneg : 0 ≤ quadraticConstant
  bound_nonneg : 0 ≤ globalBound
  measurable_cost : Measurable (Function.uncurry cost)
  global_bounds : ∀ᵐ p ∂μ.prod ν, 0 ≤ cost p.1 p.2 ∧ cost p.1 p.2 ≤ globalBound
  sourceGood : T → X → Prop
  targetGood : T → Y → Prop
  source_good : ∀ t, ∀ᵐ x ∂types.source t, sourceGood t x
  target_good : ∀ t, ∀ᵐ y ∂types.target t, targetGood t y
  quadratic : ∀ t x y, sourceGood t x → targetGood t y →
    cost x y ≤ quadraticConstant *
      ‖dyadicCubePoint (sourceCoordinate t x) - dyadicCubePoint (targetCoordinate t y)‖ ^ 2

namespace PopulationTypedCostData
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y} {q : ℕ} {cost : X → Y → ℝ}
  (D : PopulationTypedCostData π μ ν T q cost)

/-- A fixed cube point completes the irrelevant residual coordinate. -/
def cubeOrigin : DyadicUnitCube q := fun _ ↦ ⟨0, le_rfl, zero_le_one⟩

variable [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]

/-- The actual independent RN-marked original physical arrays. -/
def markedLaw (n : ℕ) : Measure ((Fin n → X × Option T) × (Fin n → Y × Option T)) :=
  (Measure.pi (fun _ : Fin n ↦ D.types.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ D.types.targetMarkedLaw ν))

/-- The common unnormalized type-coordinate law becomes a probability because
its physical marginal is the unchanged original population probability. -/
def coordinateLaw : Measure (Option T × DyadicUnitCube q) :=
  D.types.typeCoordinateLaw μ D.sourceCoordinate (cubeOrigin (q := q))

def sourceSample (n : ℕ) (i : Fin n)
    (ω : (Fin n → X × Option T) × (Fin n → Y × Option T)) :
    Option T × DyadicUnitCube q :=
  populationTypedCoordinate D.sourceCoordinate (cubeOrigin (q := q)) (ω.1 i)

def targetSample (n : ℕ) (i : Fin n)
    (ω : (Fin n → X × Option T) × (Fin n → Y × Option T)) :
    Option T × DyadicUnitCube q :=
  populationTypedCoordinate D.targetCoordinate (cubeOrigin (q := q)) (ω.2 i)

variable [IsFiniteMeasure π] [IsFiniteMeasure μ] [IsFiniteMeasure ν]

omit [MeasurableSingletonClass (Option T)] in
/-- Original raw population bounds hold for all cross-color edges simultaneously. -/
theorem iid_cost_bounds (hπ : Vlasov.IsCoupling π μ ν) (n : ℕ) :
    (∀ᵐ ω ∂D.markedLaw n, ∀ i j, 0 ≤ cost (ω.1 i).1 (ω.2 j).1) ∧
      (∀ᵐ ω ∂D.markedLaw n, ∀ i j, cost (ω.1 i).1 (ω.2 j).1 ≤ D.globalBound) := by
  have hraw : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
      (Measure.pi (fun _ : Fin n ↦ ν)),
      ∀ i j, 0 ≤ cost (ω.1 i) (ω.2 j) ∧ cost (ω.1 i) (ω.2 j) ≤ D.globalBound := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact (MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ μ) i)
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ ν) j)).ae D.global_bounds
  have h := D.types.iid_original_physical_property hπ _ hraw
  exact ⟨h.mono (fun _ hω i j ↦ (hω i j).1), h.mono (fun _ hω i j ↦ (hω i j).2)⟩

/-- All same-type edges of the actual marked sample inherit the original
quadratic estimate; the residual type is absent by full population coverage. -/
theorem iid_quadratic (hπ : Vlasov.IsCoupling π μ ν) (n : ℕ) :
    ∀ tag, ∀ᵐ ω ∂D.markedLaw n, ∀ i j,
      (D.sourceSample n i ω).1 = tag → (D.targetSample n j ω).1 = tag →
      cost (ω.1 i).1 (ω.2 j).1 ≤ D.quadraticConstant *
        ‖dyadicCubePoint (D.sourceSample n i ω).2 -
          dyadicCubePoint (D.targetSample n j ω).2‖ ^ 2 := by
  have hg := D.types.iid_marked_type_properties (μ := μ) (ν := ν)
    (I := Fin n) (J := Fin n) D.sourceGood D.targetGood D.source_good D.target_good
  have hfull := D.types.iid_marked_ae_some_of_sum_eq (I := Fin n) (J := Fin n) hπ D.sum_eq
  intro tag
  filter_upwards [hg, hfull] with ω hgood hretained
  intro i j hi hj
  cases tag with
  | none =>
    obtain ⟨t, ht⟩ := hretained.1 i
    have hnone : (ω.1 i).2 = none := hi
    rw [ht] at hnone
    cases hnone
  | some t =>
    have hsi : (ω.1 i).2 = some t := hi
    have htj : (ω.2 j).2 = some t := hj
    have h := D.quadratic t _ _ (hgood.1 i t hsi) (hgood.2 j t htj)
    simpa only [sourceSample, targetSample, populationTypedCoordinate, hsi, htj,
      Option.elim_some] using h

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
/-- The same raw type-coordinate law supplies all iid and cross-color
independence hypotheses, for every original sample size. -/
theorem iid_facts [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) (n : ℕ) :
    IsProbabilityMeasure (D.markedLaw n) ∧ IsProbabilityMeasure D.coordinateLaw ∧
      (∀ i, Measurable (D.sourceSample n i)) ∧ (∀ j, Measurable (D.targetSample n j)) ∧
      iIndepFun (D.sourceSample n) (D.markedLaw n) ∧
      iIndepFun (D.targetSample n) (D.markedLaw n) ∧
      (∀ i, (D.markedLaw n).map (D.sourceSample n i) = D.coordinateLaw) ∧
      (∀ j, (D.markedLaw n).map (D.targetSample n j) = D.coordinateLaw) ∧
      IndepFun (fun ω i ↦ D.sourceSample n i ω) (fun ω j ↦ D.targetSample n j ω)
        (D.markedLaw n) :=
  D.types.iid_type_coordinate_facts hπ D.sourceCoordinate D.targetCoordinate
    (cubeOrigin (q := q)) D.measurable_sourceCoordinate D.measurable_targetCoordinate
      D.common_coordinate

end PopulationTypedCostData
end OTSelector.Reconstruction
