import OTSelector.Geometry.FinslerQuadraticCostDifferenceMarkedDistinct
import OTSelector.Transport.CyclicMonotonicity.AmbientLegalTargetRigidity

/-!
# Rigidity on a countable cloud with distinct positions or matrices

The occupied target set itself supplies the measurable target indices. The
existing ambient-plan pullback theorem recovers both original plans exactly,
so no chosen enumeration, lifting identity or indexed-plan hypothesis remains.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {ι α β : Type*} [Fintype ι]
  [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [SecondCountableTopology α]
  [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
  [SecondCountableTopology β] [MeasurableSingletonClass β]

/-- The original full plans agree on any countable occupied cloud whose
positive quadratic rows are distinct by position or by actual matrix.
Spatial injectivity of the cloud is unnecessary. -/
theorem ambient_quadratic_plans_eq_of_countable_distinct_rows
    (m : Measure (ι → ℝ)) [m.IsAddHaarMeasure] (κ : Measure α) [SFinite κ]
    {μ : Measure ((ι → ℝ) × α)} (hμ : μ ≪ m.prod κ)
    (A : α → β → Matrix ι ι ℝ) (hA : ∀ t, Measurable (fun s ↦ A s t))
    {T : Set ((ι → ℝ) × β)} (hT : T.Countable)
    (ν : Measure ((ι → ℝ) × β)) (hν : ∀ᵐ y ∂ν, y ∈ T)
    (π₀ π₁ : Measure (((ι → ℝ) × α) × ((ι → ℝ) × β)))
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (htarget₀ : π₀.map Prod.snd = ν) (htarget₁ : π₁.map Prod.snd = ν)
    (D : Set (((ι → ℝ) × α) × ((ι → ℝ) × β))) (hD : MeasurableSet D)
    (hpos : ∀ p ∈ D, (A p.1.2 p.2.2).PosDef)
    (hseparate : ∀ y ∈ T, ∀ z ∈ T, y ≠ z →
      ∀ x ∈ Reconstruction.commonLegalSource D y z,
        y.1 ≠ z.1 ∨ A x.2 y.2 ≠ A x.2 z.2)
    (hlegal₀ : ∀ᵐ p ∂π₀, p ∈ D) (hlegal₁ : ∀ᵐ p ∂π₁, p ∈ D)
    (hcycle : Reconstruction.IsTwoCycleMonotoneOn
      (Probability.cavitySpatialDifferenceCost
        (fun s t v ↦ Reconstruction.matrixQuadratic (A s t) v)) D
      ((((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)).support) ∩ D)) : π₀ = π₁ := by
  have : Countable T := hT.to_subtype
  let Y : T → (ι → ℝ) × β := Subtype.val
  have hY : MeasurableEmbedding Y := MeasurableEmbedding.subtype_coe hT.measurableSet
  apply Probability.ambient_plan_eq_of_countable_target_legal_average_support
    μ ν π₀ π₁ Y hY (by simpa only [Y, Subtype.range_coe] using hν)
    hsource₀ hsource₁ htarget₀ htarget₁
    (Probability.cavitySpatialDifferenceCost
      (fun s t v ↦ Reconstruction.matrixQuadratic (A s t) v)) D hD
    hlegal₀ hlegal₁ hcycle
  · intro i j
    exact ((measurable_marked_matrixQuadratic_cost A (Y i) (hA _)).sub
      (measurable_marked_matrixQuadratic_cost A (Y j) (hA _))).aemeasurable
  · intro i j hij
    apply nullSingletonClass_map_marked_matrixQuadratic_sub_of_distinct m κ hμ A
      (hA _) (hA _) (Reconstruction.measurableSet_commonLegalSource hD (Y i) (Y j))
    · intro x hx
      exact ⟨hpos (x, Y i) hx.1, hpos (x, Y j) hx.2⟩
    · exact hseparate (Y i) i.property (Y j) j.property
        (fun heq ↦ hij (Subtype.ext heq))

end OTSelector.Geometry
