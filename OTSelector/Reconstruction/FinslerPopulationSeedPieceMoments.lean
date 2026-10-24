import OTSelector.Reconstruction.FinslerPopulationCoefficientLocalization
import OTSelector.Reconstruction.FinslerSeedRootPartition
import OTSelector.Reconstruction.OriginalSeedCoefficientBound

/-!
# Actual moments on the measurably selected original seed pieces

The fixed original partition selects the seed before its comparison and endpoint
frames. Every piece's actual inverse label retains the original two conditional
laws, their whole active densities, and the resulting coefficient localization.
-/

open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Both original conditional laws have their complete moment witness on the
actual inverse label of every selected seed piece, simultaneously. -/
def PopulationSeedPieceMomentLaw (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] : Prop :=
  ∀ᵐ z ∂lambda, ∀ j, ∀ hz : z ∈ populationSeedRootPiece P a κ lambda j,
    Nonempty (OriginalSeedConditionalMoments (P j).seed
      (populationSeedPieceLabel P a κ lambda j ⟨z, hz⟩)
      (condDistrib u a η₀ z) (condDistrib u a η₁ z))

/-- Every selected original seed piece has coefficient estimates uniform over all
legal pairings of the two original conditional laws. -/
def PopulationSeedPieceCoefficientLaw (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] : Prop :=
  ∀ᵐ z ∂lambda, ∀ j, ∀ hz : z ∈ populationSeedRootPiece P a κ lambda j,
    ConditionalCoefficientLocalization (condDistrib u a η₀ z) (condDistrib u a η₁ z)
      (originalSeedPairCoefficient (P j).seed
        (populationSeedPieceLabel P a κ lambda j ⟨z, hz⟩))

/-- The fixed actual piece coefficient is bounded under every original legal
coupling, alongside its inverse-moment and uniform core-error estimates. -/
def PopulationSeedPieceBoundedCoefficientLaw (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] : Prop :=
  ∀ᵐ z ∂lambda, ∀ j, ∀ hz : z ∈ populationSeedRootPiece P a κ lambda j,
    let A := originalSeedPairCoefficient (P j).seed
      (populationSeedPieceLabel P a κ lambda j ⟨z, hz⟩)
    ConditionalCoefficientLocalization (condDistrib u a η₀ z) (condDistrib u a η₁ z) A ∧
      ∃ R ≥ 0, ∀ π : Measure (ℝ × ℝ),
        Vlasov.IsCoupling π (condDistrib u a η₀ z) (condDistrib u a η₁ z) →
        (∀ᵐ p ∂π, p.1 ≤ p.2) → ∀ᵐ p ∂π, ‖A p‖ ≤ R

/-- The coefficient read in original root coordinates is exactly the actual
coefficient on the same measurably selected original seed label. -/
theorem populationSeedRootCoefficient_eq_pieceCoefficient
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPieceCoefficientMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {z : Z} (hz : z ∈ populationSeedRootPiece P a κ lambda j) (p : ℝ × ℝ) :
    populationSeedRootCoefficient (P j).seed a
      (Module.finBasis ℝ (P j).seed.covector.ker) (z, p) =
        originalSeedPairCoefficient (P j).seed
          (populationSeedPieceLabel P a κ lambda j ⟨z, hz⟩) p := by
  have h := populationSeedRootCoefficient_at_label (P j).seed hF hcomplete hu ha hinj
    (Module.finBasis ℝ (P j).seed.covector.ker)
    (populationSeedPieceLabel P a κ lambda j ⟨z, hz⟩) p.1 p.2
  rw [populationSeedPieceLabel_root P a κ lambda j ⟨z, hz⟩] at h
  exact h

/-- Original support and full-seed physical density producers give moment witnesses
on the fixed measurable seed partition, without reselecting the seed index. -/
theorem populationSeedPieceMomentLaw_of_physical_laws
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    [SigmaFinite lambda] {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : M → E → ℝ}
    (hsupport : PopulationConditionalSupportLaw (F := F) (u := u) a lambda η₀ η₁)
    (hdensity₀ : ∀ j, PopulationSeedChartDensityLaw (P j).seed a (κ j)
      lambda η₀ ρ₀ v (P j).seed.level)
    (hdensity₁ : ∀ j, PopulationSeedChartDensityLaw (P j).seed a (κ j)
      lambda η₁ ρ₁ v (P j).seed.level)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPieceMomentsMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hρ₀ : Continuous ρ₀) (hρ₁ : Continuous ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ x ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old x) :
    PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁ := by
  have hκfinite (j : ℕ) : SigmaFinite (κ j) := by
    let _instPieceMomentsHaar : (κ j).IsAddHaarMeasure := hκ j
    infer_instance
  have hcomparison := ae_populationSeedPieceLabel_property P a κ lambda hF hcomplete hu ha
    hinj hκfinite (fun j ↦ HasActiveSeedComparison (P j).seed) (fun j ↦ by
      let _instPieceComparisonHaar : (κ j).IsAddHaarMeasure := hκ j
      filter_upwards [(P j).seed.ae_exists_comparison_active_jacobian
        (Classical.choice (P j).seed.c11_presentation) hF hcomplete hu (κ j)] with w hw
      exact hw.2)
  filter_upwards [hsupport, hcomparison,
    ae_all_iff.mpr (fun j ↦ (hdensity₀ j).ae_seedClockDensity),
    ae_all_iff.mpr (fun j ↦ (hdensity₁ j).ae_seedClockDensity)] with z hs hc h₀ h₁
  intro j hz
  let w := populationSeedPieceLabel P a κ lambda j ⟨z, hz⟩
  have hwz := populationSeedPieceLabel_root P a κ lambda j ⟨z, hz⟩
  obtain ⟨lo, hi, hspan⟩ := hs (P j).seed w w.property hwz
  exact originalSeedConditionalMoments_of_supported_comparison hF w.property (hc j hz)
    hspan hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg hv hv0
    (h₀ j w w.property hwz) (h₁ j w w.property hwz)

omit [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z] in
/-- The original physical support gap gives all legal-pair coefficient estimates
on the same selected piece and the same original two conditional laws. -/
theorem PopulationSeedPieceMomentLaw.coefficient_localization
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hF : F.IsSmoothStronglyConvex) {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam) :
    PopulationSeedPieceCoefficientLaw P a κ lambda η₀ η₁ := by
  filter_upwards [hlaw, hsep] with z hz hsz
  intro j hj
  obtain ⟨D⟩ := hz j hj
  exact D.coefficient_localization hF
    (populationSeedPieceLabel P a κ lambda j ⟨z, hj⟩).property hgap hsz

omit [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z] in
/-- The same measurable piece index and actual inverse label also have a uniform
actual coefficient bound, derived from the original physical support gap. -/
theorem PopulationSeedPieceMomentLaw.bounded_coefficient_localization
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hF : F.IsSmoothStronglyConvex) {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam) :
    PopulationSeedPieceBoundedCoefficientLaw P a κ lambda η₀ η₁ := by
  filter_upwards [hlaw, hsep] with z hz hsz
  intro j hj
  obtain ⟨D⟩ := hz j hj
  exact ⟨D.coefficient_localization hF
      (populationSeedPieceLabel P a κ lambda j ⟨z, hj⟩).property hgap hsz,
    D.exists_uniform_pair_coefficient_bound hF
      (populationSeedPieceLabel P a κ lambda j ⟨z, hj⟩).property hgap hsz⟩

end OTSelector.Reconstruction
