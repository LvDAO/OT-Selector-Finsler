import OTSelector.Reconstruction.SeparatedComplianceBound
import OTSelector.Reconstruction.FinslerPopulationCoefficientLocalization

/-!
# A bounded actual coefficient for every original legal pairing

The original physical support separation and the same full-interval kernel give
one coefficient bound on a conditional label. No endpoint nondegeneracy or global
lower density enters this estimate.
-/

open Set Matrix Module Manifold MeasureTheory ProbabilityTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- The actual original scalar coefficient is bounded by one constant for all legal
pairings of the same conditional populations. -/
theorem OriginalSeedConditionalMoments.exists_uniform_pair_coefficient_bound
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diam : ℝ} (hgap : 0 < gap) (hsupport : ConditionalClockSupportBounds μ ν gap diam) :
    ∃ R ≥ 0, ∀ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π μ ν →
      (∀ᵐ p ∂π, p.1 ≤ p.2) → ∀ᵐ p ∂π, ‖originalSeedPairCoefficient S w p‖ ≤ R := by
  have hK := D.original_kernel_regular hF hw
  obtain ⟨R, hR, hbound⟩ := exists_uniform_inverse_compliance_bound hgap
    (hsupport.span_length_bounds D.support).1 hK.1 hK.2
  refine ⟨R, hR, fun π hπ ho ↦ ?_⟩
  have hx : ∀ᵐ p ∂π, p.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact D.support.source.ae_open)
  have hy : ∀ᵐ p ∂π, p.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact D.support.target.ae_open)
  filter_upwards [hx, hy, hsupport.ae_clock_gap_of_coupling hπ ho] with p hx hy hxy
  exact hbound _ hx _ hy (by linarith)

/-- Boundedness makes the actual coefficient itself integrable under every legal pairing. -/
theorem OriginalSeedConditionalMoments.integrable_pair_coefficient
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diam : ℝ} (hgap : 0 < gap) (hsupport : ConditionalClockSupportBounds μ ν gap diam)
    {π : Measure (ℝ × ℝ)} (hπ : Vlasov.IsCoupling π μ ν) (ho : ∀ᵐ p ∂π, p.1 ≤ p.2) :
    Integrable (originalSeedPairCoefficient S w) π := by
  obtain ⟨R, _, hR⟩ := D.exists_uniform_pair_coefficient_bound hF hw hgap hsupport
  have : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.symm ▸ D.support.source.probability
  have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  exact (integrable_const R).mono'
    (measurable_originalSeedPairCoefficient S hF hw).aestronglyMeasurable (hR π hπ ho)

variable {Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- The same original population seed supplies a bounded actual coefficient together
with its full inverse-moment and core-localization controls. -/
theorem PopulationConditionalMomentLaw.bounded_coefficient_localization
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
          (originalSeedPairCoefficient (P j).seed w) ∧
        ∃ R ≥ 0, ∀ π : Measure (ℝ × ℝ),
          Vlasov.IsCoupling π (condDistrib u a η₀ z) (condDistrib u a η₁ z) →
          (∀ᵐ p ∂π, p.1 ≤ p.2) →
          ∀ᵐ p ∂π, ‖originalSeedPairCoefficient (P j).seed w p‖ ≤ R := by
  filter_upwards [hlaw, hsep] with z hz hsz
  obtain ⟨j, w, hw, hwz, ⟨D⟩⟩ := hz
  exact ⟨j, w, hw, hwz, ⟨D⟩, D.coefficient_localization hF hw hgap hsz,
    D.exists_uniform_pair_coefficient_bound hF hw hgap hsz⟩

end OTSelector.Reconstruction
