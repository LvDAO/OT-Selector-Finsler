import OTSelector.Transport.Coupling.FiniteLabelCoreRecovery
import OTSelector.Reconstruction.FinslerPopulationFiniteSeedCore
import OTSelector.Reconstruction.FinslerPopulationSeedPieceMoments

/-!
# Finite actual population cores for local pressure assembly

The original two conditional laws, their selected seed coefficients and their
original label masses are retained on finitely many compact pieces. The omitted
physical mass is exactly the original label complement, and adding it back
recovers both original populations without a new normalization or balance input.
-/

open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- At one original root, every selected piece retains its actual two-color moment
witness and all legal-pair coefficient bounds on that same inverse label. -/
def HasPopulationSeedPiecePressureData (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (z : ℚ → M) : Prop :=
  ∀ j, ∀ hz : z ∈ populationSeedRootPiece P a κ lambda j,
    let w := populationSeedPieceLabel P a κ lambda j ⟨z, hz⟩
    let A := originalSeedPairCoefficient (P j).seed w
    Nonempty (OriginalSeedConditionalMoments (P j).seed w
      (condDistrib u a η₀ z) (condDistrib u a η₁ z)) ∧
    ConditionalCoefficientLocalization (condDistrib u a η₀ z) (condDistrib u a η₁ z) A ∧
    ∃ R ≥ 0, ∀ π : Measure (ℝ × ℝ),
      Vlasov.IsCoupling π (condDistrib u a η₀ z) (condDistrib u a η₁ z) →
      (∀ᵐ p ∂π, p.1 ≤ p.2) → ∀ᵐ p ∂π, ‖A p‖ ≤ R

/-- A finite common original-label core with exact physical recovery, full original
conditional densities, continuous L1/TV laws and actual selected-piece coefficients. -/
structure PopulationPressureCore (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ)
    (b : (ℚ → M) × ℝ → M) (Good : (ℚ → M) → Prop) (ε : ℝ≥0∞) where
  count : ℕ
  roots : Set (ℚ → M)
  densityClass : Fin 2 → (ℚ → M) → Lp ℝ 1 (volume : Measure ℝ)
  measurable_class : ∀ i, @Measurable _ _ _ (borel _) (densityClass i)
  covered : roots ⊆ ⋃ j < count, populationSeedRootPiece P a κ lambda j
  compact : IsCompact roots
  complement_small : lambda rootsᶜ < ε
  pieces_compact : ∀ j, IsCompact (roots ∩ populationSeedRootPiece P a κ lambda j)
  continuous_class : ContinuousOn (fun z i ↦ densityClass i z) roots
  good : ∀ z ∈ roots, Good z ∧ HasPopulationSeedPiecePressureData P a κ lambda η₀ η₁ z
  density : ∀ z ∈ roots, ∀ i,
    (∫⁻ t, populationTwoColorDensity P a κ lambda ρ₀ ρ₁ v i (z, t)) = 1 ∧
    (volume : Measure ℝ).withDensity
        (fun t ↦ populationTwoColorDensity P a κ lambda ρ₀ ρ₁ v i (z, t)) =
      populationTwoColorClockKernel u a η₀ η₁ i z ∧
    (⇑(densityClass i z)) =ᵐ[volume]
      (fun t ↦ (populationTwoColorDensity P a κ lambda ρ₀ ρ₁ v i (z, t)).toReal)
  variation : ∀ i, ∀ z ∈ roots, ∀ z' ∈ roots,
    ((populationTwoColorClockKernel u a η₀ η₁ i z).toSignedMeasure -
      (populationTwoColorClockKernel u a η₀ η₁ i z').toSignedMeasure).totalVariation univ =
        ENNReal.ofReal ‖densityClass i z - densityClass i z'‖
  continuous_variation : ∀ i, ContinuousOn (fun p : (ℚ → M) × (ℚ → M) ↦
    ((populationTwoColorClockKernel u a η₀ η₁ i p.1).toSignedMeasure -
      (populationTwoColorClockKernel u a η₀ η₁ i p.2).toSignedMeasure).totalVariation univ)
    (roots ×ˢ roots)
  recovery : FiniteLabelCoreRecovery u a b lambda η₀ η₁
    (fun j : Fin count ↦ roots ∩ populationSeedRootPiece P a κ lambda j)

/-- Arbitrarily large finite actual pressure cores retain every requested original
almost-everywhere property along with the full physical recovery interface. -/
def PopulationFinitePressureCoreLaw (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ)
    (b : (ℚ → M) × ℝ → M) : Prop :=
  ∀ (Good : (ℚ → M) → Prop), (∀ᵐ z ∂lambda, Good z) →
    ∀ ε : ℝ≥0∞, ε ≠ 0 →
      Nonempty (PopulationPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good ε)

omit [BorelSpace E] in
/-- Finite original seed cores, exact recovery and the actual piece moment producers
assemble the pressure-core inputs while preserving the original masses. -/
theorem PopulationFiniteSeedCompactCoreLaw.pressure_core
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    (hcore : PopulationFiniteSeedCompactCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hmoments : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hcoeff : PopulationSeedPieceBoundedCoefficientLaw P a κ lambda η₀ η₁)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u) :
    PopulationFinitePressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b := by
  let _instPressureCoreMetric : MetricSpace M := F.metricSpace
  let _instPressureCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPressureCorePolish : PolishSpace M := inferInstance
  let _instPressureCoreLabelsBorel : BorelSpace (ℚ → M) := inferInstance
  have hdata : ∀ᵐ z ∂lambda, HasPopulationSeedPiecePressureData P a κ lambda η₀ η₁ z := by
    filter_upwards [hmoments, hcoeff] with z hm hc
    exact fun j hj ↦ ⟨hm j hj, hc j hj⟩
  intro Good hGood ε hε
  obtain ⟨N, L, K, hLm, hKs, hK, hsmall, hKpieces, hLc, hgood, hTV, hTVc⟩ :=
    hcore (fun z ↦ Good z ∧ HasPopulationSeedPiecePressureData P a κ lambda η₀ η₁ z)
      (hGood.and hdata) ε hε
  have hd : Pairwise (Function.onFun Disjoint
      (fun j : Fin N ↦ K ∩ populationSeedRootPiece P a κ lambda j)) := by
    intro i j hij
    exact (pairwiseDisjoint_populationSeedRootPiece P a κ lambda
      (Fin.val_ne_of_ne hij)).mono inter_subset_right inter_subset_right
  exact ⟨{
    count := N
    roots := K
    densityClass := L
    measurable_class := hLm
    covered := hKs
    compact := hK
    complement_small := hsmall
    pieces_compact := hKpieces
    continuous_class := hLc
    good := fun z hz ↦ (hgood z hz).1
    density := fun z hz ↦ (hgood z hz).2
    variation := hTV
    continuous_variation := hTVc
    recovery := hrecovery.finite_recovery ha hu _
      (fun j ↦ (hKpieces j).measurableSet) hd }⟩

variable {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {ε : ℝ≥0∞}

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M] in
/-- The finite selected pieces recover precisely the root core. -/
theorem PopulationPressureCore.iUnion_pieces
    (D : PopulationPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good ε) :
    (⋃ j : Fin D.count, D.roots ∩ populationSeedRootPiece P a κ lambda j) = D.roots := by
  apply subset_antisymm
  · exact iUnion_subset fun _ ↦ inter_subset_left
  · intro z hz
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (D.covered hz)
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hz, hzj⟩

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M] in
/-- The removed physical mass of each original color is exactly the same small
original label mass, with no conditional renormalization. -/
theorem PopulationPressureCore.remainder_mass
    (D : PopulationPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good ε) :
    η₀ (a ⁻¹' D.rootsᶜ) = lambda D.rootsᶜ ∧
      η₁ (a ⁻¹' D.rootsᶜ) = lambda D.rootsᶜ ∧
      η₀ (a ⁻¹' D.rootsᶜ) < ε ∧ η₁ (a ⁻¹' D.rootsᶜ) < ε := by
  have h₀ := D.recovery.source_remainder_mass
  have h₁ := D.recovery.target_remainder_mass
  rw [D.iUnion_pieces] at h₀ h₁
  exact ⟨h₀, h₁, h₀ ▸ D.complement_small, h₁ ▸ D.complement_small⟩

/-- Any further compact root refinement retains the same selected seeds, density
classes, actual coefficient data and exact original physical reconstruction. -/
def PopulationPressureCore.refine
    (D : PopulationPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good ε)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Set (ℚ → M)} (hK : IsCompact K) (hsub : K ⊆ D.roots)
    {ε' : ℝ≥0∞} (hsmall : lambda Kᶜ < ε') :
    PopulationPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good ε' := by
  let _instRefinedCoreMetric : MetricSpace M := F.metricSpace
  let _instRefinedCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instRefinedCorePolish : PolishSpace M := inferInstance
  let _instRefinedCoreLabelsBorel : BorelSpace (ℚ → M) := inferInstance
  have hpieces (j : ℕ) : IsCompact (K ∩ populationSeedRootPiece P a κ lambda j) := by
    have hcompact := (D.pieces_compact j).inter_left hK.isClosed
    convert hcompact using 1
    ext z
    exact ⟨fun hz ↦ ⟨hz.1, hsub hz.1, hz.2⟩, fun hz ↦ ⟨hz.1, hz.2.2⟩⟩
  have hd : Pairwise (Function.onFun Disjoint
      (fun j : Fin D.count ↦ K ∩ populationSeedRootPiece P a κ lambda j)) := by
    intro i j hij
    exact (pairwiseDisjoint_populationSeedRootPiece P a κ lambda
      (Fin.val_ne_of_ne hij)).mono inter_subset_right inter_subset_right
  exact {
    count := D.count
    roots := K
    densityClass := D.densityClass
    measurable_class := D.measurable_class
    covered := hsub.trans D.covered
    compact := hK
    complement_small := hsmall
    pieces_compact := hpieces
    continuous_class := D.continuous_class.mono hsub
    good := fun z hz ↦ D.good z (hsub hz)
    density := fun z hz ↦ D.density z (hsub hz)
    variation := fun i z hz z' hz' ↦ D.variation i z (hsub hz) z' (hsub hz')
    continuous_variation := fun i ↦ (D.continuous_variation i).mono (prod_mono hsub hsub)
    recovery := hrecovery.finite_recovery ha hu _ (fun j ↦ (hpieces j).measurableSet) hd }

end OTSelector.Reconstruction
