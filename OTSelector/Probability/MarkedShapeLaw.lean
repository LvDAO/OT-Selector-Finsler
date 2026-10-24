import OTSelector.Probability.PoissonRestriction
import OTSelector.Probability.MarkedShapeCloud

/-! Exact restrictions of original marked cube clouds to arbitrary measurable
spatial shapes, preserving the original conditional spatial law and mark law. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B]

/-- Spatial restriction changes no conditional mark law. This includes null
spatial sets, whose fallback law is unused by the zero-intensity prefix. -/
theorem restrictedPointLaw_prod_fst
    (σ : Measure Z) [IsProbabilityMeasure σ] (α : Measure A) [IsProbabilityMeasure α]
    {S : Set Z} :
    restrictedPointLaw (σ.prod α) (Prod.fst ⁻¹' S) =
      (restrictedPointLaw σ S).prod α := by
  have hset : (Prod.fst ⁻¹' S : Set (Z × A)) = S ×ˢ (univ : Set A) := by ext p; simp
  have hmass : (σ.prod α) (Prod.fst ⁻¹' S) = σ S := by
    rw [hset, Measure.prod_prod, measure_univ, mul_one]
  unfold restrictedPointLaw
  rw [hmass]
  by_cases h : σ S = 0
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, ProbabilityTheory.cond]
    rw [hset, ← Measure.prod_restrict, Measure.restrict_univ, Measure.prod_smul_left,
      Measure.prod_prod, measure_univ, mul_one]

theorem restrictionWeight_prod_fst
    (σ : Measure Z) [IsProbabilityMeasure σ] (α : Measure A) [IsProbabilityMeasure α]
    (S : Set Z) :
    restrictionWeight (σ.prod α) (Prod.fst ⁻¹' S) = restrictionWeight σ S := by
  unfold restrictionWeight
  congr 1
  rw [show (Prod.fst ⁻¹' S : Set (Z × A)) = S ×ˢ (univ : Set A) by ext p; simp,
    Measure.prod_prod, measure_univ, mul_one]

omit [MeasurableSpace A] in
theorem shapeCloud_eq_restrictedPrefix (q : ℕ) (S : Set (Fin q → ℝ))
    (z : MarkedCloudSpace q A) :
    shapeCloud S z = restrictedPrefix (Prod.fst ⁻¹' S) z := rfl

/-- The selected finite-prefix law: original normalized spatial restriction,
unchanged independent marks, and count intensity r times the original shape mass. -/
def shapeBlockLaw (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (r : ℝ≥0) (S : Set (Fin q → ℝ)) :
    Measure (BlockData ((Fin q → ℝ) × A)) := by
  let _inst : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  exact blockDataLaw ((restrictedPointLaw (cubeMeasure (Fin q) 1) S).prod α)
    (fun n ↦ poissonMeasure (r * restrictionWeight (cubeMeasure (Fin q) 1) S) {n})

/-- The selected observations have the exact Poisson-prefix law of the original
normalized spatial restriction, with the original independent marks. -/
theorem map_shapeCloud_markedPoissonLaw (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (r : ℝ≥0)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    (markedPoissonLaw q A α r).map (shapeCloud S) = shapeBlockLaw q α r S := by
  unfold shapeBlockLaw
  let _inst : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have h := map_restrictedPrefix ((cubeMeasure (Fin q) 1).prod α) r
    (hS.preimage measurable_fst)
  have heq : shapeCloud (A := A) S = restrictedPrefix (Prod.fst ⁻¹' S) :=
    funext (shapeCloud_eq_restrictedPrefix q S)
  rw [heq]
  simpa only [markedPoissonLaw, markedSeqLaw, restrictedPointLaw_prod_fst _ _,
    restrictionWeight_prod_fst] using h

/-- The two selected colors remain independent, each with its actual normalized
spatial restriction and unchanged original conditional mark law. -/
theorem map_shapeCloud_twoMarkedCloudLaw (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    (twoMarkedCloudLaw q A B α β r).map (Prod.map (shapeCloud S) (shapeCloud S)) =
      (shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S) := by
  change ((markedPoissonLaw q A α r).prod (markedPoissonLaw q B β r)).map
    (Prod.map (shapeCloud S) (shapeCloud S)) = _
  rw [← Measure.map_prod_map _ _ (measurable_shapeCloud hS) (measurable_shapeCloud hS),
    map_shapeCloud_markedPoissonLaw q α r hS, map_shapeCloud_markedPoissonLaw q β r hS]

/-- Transfer an actual finite-prefix observable to the exact independent shape
laws, keeping integrability and the original expected value. -/
theorem shapeCloud_integrable_integral (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (F : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) → ℝ)
    (hF : Measurable F)
    (hI : Integrable (fun ω : TwoMarkedCloudSpace q A B ↦
      F (shapeCloud S ω.1, shapeCloud S ω.2)) (twoMarkedCloudLaw q A B α β r)) :
    Integrable F ((shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S)) ∧
    (∫ d, F d ∂(shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S)) =
      ∫ ω, F (shapeCloud S ω.1, shapeCloud S ω.2) ∂twoMarkedCloudLaw q A B α β r := by
  let sel : TwoMarkedCloudSpace q A B →
      BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) :=
    Prod.map (shapeCloud S) (shapeCloud S)
  have hsel : Measurable sel :=
    ((measurable_shapeCloud (A := A) hS).comp measurable_fst).prodMk
      ((measurable_shapeCloud (A := B) hS).comp measurable_snd)
  have hlaw : (twoMarkedCloudLaw q A B α β r).map sel =
      (shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S) :=
    map_shapeCloud_twoMarkedCloudLaw q α β r hS
  constructor
  · rw [← hlaw]
    exact (integrable_map_measure hF.aestronglyMeasurable hsel.aemeasurable).mpr hI
  · rw [← hlaw, integral_map hsel.aemeasurable hF.aestronglyMeasurable]
    rfl

end OTSelector.Probability
