import OTSelector.Reconstruction.OriginalCoefficientLocalization
import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation

/-!
# Original population coefficient localization

The same original conditional moment witness and the physical support gap give
coefficient control for every legal weakly ordered pairing. All measure, endpoint,
rank and moment inputs are the laws already produced from the physical populations.
-/

open Set Matrix Module Manifold MeasureTheory ProbabilityTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

/-- Integral control for one fixed actual pair coefficient, uniform over all legal
pairings of its original two mark laws. -/
structure ConditionalCoefficientLocalization {n : Type*} [Fintype n] [DecidableEq n]
    (μ ν : Measure ℝ) (A : ℝ × ℝ → Matrix n n ℝ) : Prop where
  measurable : Measurable A
  inverse_integrable : ∀ π, Vlasov.IsCoupling π μ ν → (∀ᵐ p ∂π, p.1 ≤ p.2) →
    Integrable (fun p ↦ (A p)⁻¹) π
  inverse_moments : ∀ π, Vlasov.IsCoupling π μ ν → (∀ᵐ p ∂π, p.1 ≤ p.2) →
    ∀ r : ℝ, 0 < r → r < 2 → Integrable (fun p ↦ ‖(A p)⁻¹‖ ^ r) π
  uniform_small_sets : ∀ ε > 0, ∃ δ > 0, ∀ π, Vlasov.IsCoupling π μ ν →
    (∀ᵐ p ∂π, p.1 ≤ p.2) → ∀ s : Set (ℝ × ℝ), MeasurableSet s → π.real s ≤ δ →
      (∫ p in s, ‖(A p)⁻¹‖ ∂π) < ε
  uniform_core_error : ∀ ε > 0, ∃ δ > 0, ∀ π, Vlasov.IsCoupling π μ ν →
    (∀ᵐ p ∂π, p.1 ≤ p.2) → ∀ s : Set (ℝ × ℝ), MeasurableSet s → π.real sᶜ ≤ δ →
      ‖(∫ p, (A p)⁻¹ ∂π) - ∫ p in s, (A p)⁻¹ ∂π‖ < ε

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The full original moment witness and original positive support gap produce the
coefficient localization contract; legal weak order suffices. -/
theorem OriginalSeedConditionalMoments.coefficient_localization
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diam : ℝ} (hgap : 0 < gap) (hsupport : ConditionalClockSupportBounds μ ν gap diam) :
    ConditionalCoefficientLocalization μ ν (originalSeedPairCoefficient S w) := by
  let root := (D.lo + D.hi) / 2
  have hroot : root ∈ Ioo D.lo D.hi := by
    dsimp [root]
    constructor <;> linarith [D.support.lt]
  refine ⟨measurable_originalSeedPairCoefficient S hF hw, ?_, ?_, ?_, ?_⟩
  · intro π hπ ho
    exact D.integrable_inverse_pair_coefficient hF hw hroot hπ
      (hsupport.ae_strict_order_of_coupling hgap hπ ho)
  · intro π hπ ho r hr0 hr2
    exact (D.paired_inverse_coefficient_moments hF hw hroot hπ
      (hsupport.ae_strict_order_of_coupling hgap hπ ho) hr0 hr2).1
  · intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ :=
      D.uniform_integral_inverse_coefficient_on_small_sets hF hw hroot hε
    exact ⟨δ, hδ, fun π hπ ho ↦
      hsmall π hπ (hsupport.ae_strict_order_of_coupling hgap hπ ho)⟩
  · intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := D.uniform_inverse_coefficient_core_error hF hw hroot hε
    exact ⟨δ, hδ, fun π hπ ho ↦
      hsmall π hπ (hsupport.ae_strict_order_of_coupling hgap hπ ho)⟩

variable {Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- The actual physical atlas gives coefficient localization on almost every original
label, preserving the same seed and both original conditional distributions. -/
theorem PopulationConditionalMomentLaw.coefficient_localization
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (hlaw : PopulationConditionalMomentLaw P a lambda η₀ η₁)
    (hF : F.IsSmoothStronglyConvex)
    {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam) :
    ∀ᵐ z ∂lambda, ∃ (j : ℕ) (w : (P j).seed.covector.ker),
      w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
        Nonempty (OriginalSeedConditionalMoments (P j).seed w
          (condDistrib u a η₀ z) (condDistrib u a η₁ z)) ∧
        ConditionalCoefficientLocalization (condDistrib u a η₀ z) (condDistrib u a η₁ z)
          (originalSeedPairCoefficient (P j).seed w) := by
  filter_upwards [hlaw, hsep] with z hz hsz
  obtain ⟨j, w, hw, hwz, ⟨D⟩⟩ := hz
  exact ⟨j, w, hw, hwz, ⟨D⟩, D.coefficient_localization hF hw hgap hsz⟩

end OTSelector.Reconstruction
