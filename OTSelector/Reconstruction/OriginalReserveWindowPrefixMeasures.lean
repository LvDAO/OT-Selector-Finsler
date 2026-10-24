import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowCoupling

/-! Original finite prefix point measures commute with actual window restriction. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Restriction enumerates precisely the original prefix indices, including duplicates. -/
theorem originalRestrictedPrefix_sum {X M : Type*} [AddCommMonoid M]
    (S : Set X) (z : ℕ × (ℕ → X)) (f : X → M) :
    (∑ i : Fin (restrictedPrefix S z).1, f ((restrictedPrefix S z).2 i)) =
      ∑ i : Fin z.1, if z.2 i ∈ S then f (z.2 i) else 0 := by
  classical
  let E := Finset.univ.filter fun i : Fin z.1 ↦ restrictionLabel S (z.2 i) = true
  change (∑ i : Fin E.card, f (z.2 (((E.orderIsoOfFin rfl) i).1))) = _
  calc
    _ = ∑ i : E, f (z.2 i.1) :=
      (E.orderIsoOfFin rfl).toEquiv.sum_comp (fun i : E ↦ f (z.2 i.1))
    _ = ∑ i ∈ E, f (z.2 i) := Finset.sum_coe_sort E (fun i : Fin z.1 ↦ f (z.2 i))
    _ = _ := by simp only [E, Finset.sum_filter, restrictionLabel]; congr 1; funext i; split_ifs <;> simp_all

/-- The selected point measure is the restriction of the same original prefix measure. -/
theorem originalRestrictedPrefix_measure {X : Type*} [MeasurableSpace X]
    {S : Set X} (hS : MeasurableSet S) (z : ℕ × (ℕ → X)) :
    legalInputBlockMeasure (restrictedPrefix S z) =
      (∑ i : Fin z.1, Measure.dirac (z.2 i)).restrict S := by
  classical
  rw [legalInputBlockMeasure, originalRestrictedPrefix_sum]
  conv_rhs => rw [← Measure.sum_fintype, Measure.restrict_sum _ hS, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [restrict_dirac' hS]

/-- Physical placement preserves the original finite enumeration before restriction. -/
theorem originalInputWindowPrefix_measure (q : ℕ) (origin : Fin q → ℝ) (side : ℝ≥0)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) (ω : MarkedCloudSpace q ℝ) :
    legalInputBlockMeasure (legalInputWindowPrefix q origin side U ω) =
      (∑ i : Fin ω.1, Measure.dirac
        (legalInputPhysicalPoint q origin side (ω.2 i).1, (ω.2 i).2)).restrict
          (Prod.fst ⁻¹' U) := by
  change legalInputBlockMeasure (mapBlockData
    (Prod.map (legalInputPhysicalPoint q origin side) id)
    (restrictedPrefix ((Prod.map (legalInputPhysicalPoint q origin side) id) ⁻¹'
      (Prod.fst ⁻¹' U)) ω)) = _
  rw [mapBlockData_restrictedPrefix]
  exact originalRestrictedPrefix_measure (hU.preimage measurable_fst) _

/-- Coloring the same original observations also commutes with spatial restriction. -/
theorem originalInputWindowPrefix_coloredMeasure (q : ℕ) (origin : Fin q → ℝ)
    (side : ℝ≥0) {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (c : Fin 2) (ω : MarkedCloudSpace q ℝ) :
    legalInputBlockMeasure (mapBlockData (fun x ↦ (x, c))
      (legalInputWindowPrefix q origin side U ω)) =
      (∑ i : Fin ω.1, Measure.dirac
        ((legalInputPhysicalPoint q origin side (ω.2 i).1, (ω.2 i).2), c)).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' U) := by
  classical
  change (∑ i : Fin (mapBlockData
    (Prod.map (legalInputPhysicalPoint q origin side) id)
    (restrictedPrefix ((Prod.map (legalInputPhysicalPoint q origin side) id) ⁻¹'
      (Prod.fst ⁻¹' U)) ω)).1,
      Measure.dirac (((mapBlockData (Prod.map
        (legalInputPhysicalPoint q origin side) id)
        (restrictedPrefix ((Prod.map (legalInputPhysicalPoint q origin side) id) ⁻¹'
          (Prod.fst ⁻¹' U)) ω)).2 i), c)) = _
  rw [mapBlockData_restrictedPrefix]
  rw [originalRestrictedPrefix_sum (Prod.fst ⁻¹' U)
    (ω.1, fun i ↦ Prod.map (legalInputPhysicalPoint q origin side) id (ω.2 i))
    (fun x ↦ Measure.dirac (x, c))]
  conv_rhs => rw [← Measure.sum_fintype,
    Measure.restrict_sum _ (hU.preimage (measurable_fst.comp measurable_fst)),
    Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [restrict_dirac' (hU.preimage (measurable_fst.comp measurable_fst))]
  rfl

/-- Restricting a containing physical window reads exactly the same original points. -/
theorem originalInputRootWindows_nested_measure (q : ℕ) (side : ℝ≥0)
    {U V : Set (Fin q → ℝ)} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUV : U ⊆ V) (z : Fin q → ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (legalInputTwoBlockMeasure q (legalInputRootWindows q side V (z, ω))).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' U) =
      legalInputTwoBlockMeasure q (legalInputRootWindows q side U (z, ω)) := by
  simp only [legalInputTwoBlockMeasure, legalInputRootWindows,
    legalInputRootWindowPrefix_eq]
  rw [Measure.restrict_add, originalInputWindowPrefix_coloredMeasure q _ _ hV,
    originalInputWindowPrefix_coloredMeasure q _ _ hV,
    Measure.restrict_restrict (hU.preimage (measurable_fst.comp measurable_fst)),
    Measure.restrict_restrict (hU.preimage (measurable_fst.comp measurable_fst))]
  have hsets : ((Prod.fst ∘ Prod.fst) ⁻¹' U ∩
      (Prod.fst ∘ Prod.fst) ⁻¹' V : Set (LegalColoredInputPoint q)) =
      (Prod.fst ∘ Prod.fst) ⁻¹' U := inter_eq_left.mpr (preimage_mono hUV)
  rw [hsets, originalInputWindowPrefix_coloredMeasure q _ _ hU,
    originalInputWindowPrefix_coloredMeasure q _ _ hU]

end OTSelector.Reconstruction
