import OTSelector.Geometry.FinslerQuadraticCostDifferenceMarked
import OTSelector.Transport.CyclicMonotonicity.CountableLegalTargetRigidity

/-!
# Countable legal-target rigidity for frozen Finsler quadratic costs

The actual source law is absolutely continuous with respect to Haar times its
mark law. Positive coefficients on legal edges and distinct spatial target
positions supply restricted atomlessness internally, for infinite source mass
and arbitrary target marks.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {ι α β J : Type*} [Fintype ι] [MeasurableSpace α]
  [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J]

/-- Same-source plans carried by the same legally monotone quadratic relation
agree. The only target separation required here is spatial injectivity. -/
theorem countable_plans_eq_of_marked_matrixQuadratic_legal_twoCycle
    (m : Measure (ι → ℝ)) [m.IsAddHaarMeasure] (κ : Measure α) [SFinite κ]
    {μ : Measure ((ι → ℝ) × α)} (hμ : μ ≪ m.prod κ)
    (A : α → β → Matrix ι ι ℝ) (Y : J → (ι → ℝ) × β)
    (hA : ∀ j, Measurable (fun s ↦ A s (Y j).2))
    (hY : Function.Injective (fun j ↦ (Y j).1))
    (D Γ : Set (((ι → ℝ) × α) × J)) (hD : MeasurableSet D)
    (hΓ : MeasurableSet Γ) (hsub : Γ ⊆ D)
    (hpos : ∀ x j, (x, j) ∈ D → (A x.2 (Y j).2).PosDef)
    (π₀ π₁ : Measure (((ι → ℝ) × α) × J))
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    {r : ℝ≥0∞} (hr : r ≠ 0) (hcarried : ∀ᵐ z ∂r • (π₀ + π₁), z ∈ Γ)
    (hcycle : Reconstruction.IsTwoCycleMonotoneOn
      (fun x j ↦ Probability.cavitySpatialDifferenceCost
        (fun s t v ↦ Reconstruction.matrixQuadratic (A s t) v) x (Y j)) D Γ) :
    π₀ = π₁ := by
  apply hcycle.measure_eq_of_smul_add hD hΓ hsub _ _ hsource₀ hsource₁ hr hcarried
  · intro i j
    exact ((measurable_marked_matrixQuadratic_cost A (Y i) (hA i)).sub
      (measurable_marked_matrixQuadratic_cost A (Y j) (hA j))).aemeasurable
  · intro i j hij
    exact nullSingletonClass_map_marked_matrixQuadratic_sub m κ hμ A (hA i) (hA j)
      (fun h ↦ hij (hY h)) (Reconstruction.measurableSet_commonLegalSource hD i j)
      (fun x hx ↦ ⟨hpos x i hx.1, hpos x j hx.2⟩)

end OTSelector.Geometry
