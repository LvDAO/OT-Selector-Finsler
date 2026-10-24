import OTSelector.Probability.PoissonPrefixMoments
import OTSelector.Probability.PoissonRestriction

/-!
# Actual spatial restrictions of a finite marked Poisson cloud

The retained finite prefix stores the original point positions and marks.
Its canonical embedding and missing-count moment are derived from the original
experiment. No distributional assertion is made about an artificial unused tail.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {q : ℕ} {A : Type*} [MeasurableSpace A]

def shapeCloudLabel (S : Set (Fin q → ℝ)) (p : (Fin q → ℝ) × A) : Bool := by
  classical
  exact if p.1 ∈ S then true else false

theorem measurable_shapeCloudLabel {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    Measurable (shapeCloudLabel (A := A) S) :=
  measurable_const.ite (hS.preimage measurable_fst) measurable_const

/-- Keep exactly the original used points whose spatial coordinate lies in S. -/
def shapeCloud (S : Set (Fin q → ℝ)) (z : MarkedCloudSpace q A) :
    BlockData ((Fin q → ℝ) × A) :=
  blockDataOfPairsGen true (fun i : Fin z.1 ↦ (shapeCloudLabel S (z.2 i), z.2 i))

def shapeCloudIndices (S : Set (Fin q → ℝ)) (z : MarkedCloudSpace q A) :
    Finset (Fin z.1) :=
  Finset.univ.filter fun i ↦ shapeCloudLabel S (z.2 i) = true

/-- Enumerate the retained observations by their original indices. -/
def shapeCloudEmbedding (S : Set (Fin q → ℝ)) (z : MarkedCloudSpace q A) :
    Fin (shapeCloud S z).1 ↪ Fin z.1 where
  toFun i := ((shapeCloudIndices S z).orderIsoOfFin rfl i).1
  inj' := by
    intro i j hij
    exact ((shapeCloudIndices S z).orderIsoOfFin rfl).injective (Subtype.ext hij)

omit [MeasurableSpace A] in
theorem shapeCloud_point (S : Set (Fin q → ℝ)) (z : MarkedCloudSpace q A)
    (i : Fin (shapeCloud S z).1) :
    (shapeCloud S z).2 i = z.2 (shapeCloudEmbedding S z i) := rfl

omit [MeasurableSpace A] in
theorem shapeCloudEmbedding_mem (S : Set (Fin q → ℝ)) (z : MarkedCloudSpace q A)
    (i : Fin (shapeCloud S z).1) : (z.2 (shapeCloudEmbedding S z i)).1 ∈ S := by
  have hi := ((shapeCloudIndices S z).orderIsoOfFin rfl i).2
  have hl := (Finset.mem_filter.mp hi).2
  change shapeCloudLabel S (z.2 (shapeCloudEmbedding S z i)) = true at hl
  simpa [shapeCloudLabel] using hl

theorem measurable_shapeCloud {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    Measurable (shapeCloud (A := A) S) := by
  change Measurable (restrictedPrefix (Prod.fst ⁻¹' S) :
    MarkedCloudSpace q A → BlockData ((Fin q → ℝ) × A))
  exact measurable_restrictedPrefix (hS.preimage measurable_fst)

omit [MeasurableSpace A] in
theorem shapeCloud_count (S : Set (Fin q → ℝ)) (z : MarkedCloudSpace q A) :
    (shapeCloud S z).1 = poissonPrefixCount (Prod.fst ⁻¹' S) z := by
  classical
  have hfilter : (Finset.univ.filter fun i : Fin z.1 ↦ shapeCloudLabel S (z.2 i) = true) =
      Finset.univ.filter (fun i : Fin z.1 ↦ z.2 i ∈ Prod.fst ⁻¹' S) := by
    ext i
    simp [shapeCloudLabel]
  exact congrArg Finset.card hfilter

omit [MeasurableSpace A] in
/-- The omitted count is the actual original prefix count of the spatial holes. -/
theorem shapeCloud_missing_count (S : Set (Fin q → ℝ)) (z : MarkedCloudSpace q A) :
    z.1 - (shapeCloud S z).1 = poissonPrefixCount (Prod.fst ⁻¹' Sᶜ) z := by
  classical
  rw [shapeCloud_count]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin z.1))) (p := fun i ↦ (z.2 i).1 ∈ S)
  have htotal : poissonPrefixCount (Prod.fst ⁻¹' S) z +
      poissonPrefixCount (Prod.fst ⁻¹' Sᶜ) z = z.1 := by
    simpa only [poissonPrefixCount, mem_preimage, mem_compl_iff, Finset.card_univ,
      Fintype.card_fin] using h
  omega

theorem integrable_shapeCloud_missing_count
    (α : Measure A) [IsProbabilityMeasure α] (r : ℝ≥0)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    Integrable (fun z : MarkedCloudSpace q A ↦ ((z.1 - (shapeCloud S z).1 : ℕ) : ℝ))
      (markedPoissonLaw q A α r) := by
  let _inst : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  simpa only [markedPoissonLaw, markedSeqLaw, shapeCloud_missing_count] using
    integrable_poissonPrefixCount ((cubeMeasure (Fin q) 1).prod α) r
      (hS.compl.preimage measurable_fst)

/-- The exact expected number of filled or deleted points is intensity times
the original normalized spatial hole mass. -/
theorem integral_shapeCloud_missing_count
    (α : Measure A) [IsProbabilityMeasure α] (r : ℝ≥0)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    (∫ z : MarkedCloudSpace q A, ((z.1 - (shapeCloud S z).1 : ℕ) : ℝ)
      ∂markedPoissonLaw q A α r) = (r : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal := by
  let _inst : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have h := integral_poissonPrefixCount ((cubeMeasure (Fin q) 1).prod α) r
    (hS.compl.preimage measurable_fst)
  have heval : ((cubeMeasure (Fin q) 1).prod α) (Prod.fst ⁻¹' Sᶜ) =
      (cubeMeasure (Fin q) 1) Sᶜ := by
    rw [show Prod.fst ⁻¹' Sᶜ = Sᶜ ×ˢ (univ : Set A) by ext p; simp,
      Measure.prod_prod, measure_univ, mul_one]
  simpa only [markedPoissonLaw, markedSeqLaw, shapeCloud_missing_count, heval] using h

end OTSelector.Probability
