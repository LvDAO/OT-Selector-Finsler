import OTSelector.Reconstruction.FinslerPopulationPressureCore
import OTSelector.Reconstruction.FinslerFiniteCoefficientCores

/-!
# Continuous actual coefficient cores with original physical reconstruction

Finite compact scalar-pair regions refine the original finite label core. The same
two conditional laws retain their L1 and total-variation continuity, while the
actual coefficient is jointly continuous and positive definite on every retained
root-pair product. The original masses and complementary physical laws remain exact.
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

/-- Finite actual root-pair coefficient cores, with the original two-color density
core and exact finite physical recovery on precisely those root pieces. -/
structure PopulationContinuousPressureCore (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ)
    (b : (ℚ → M) × ℝ → M) (Good : (ℚ → M) → Prop) (δ ε : ℝ≥0∞) where
  population : PopulationPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good ε
  count : ℕ
  coefficient : Fin count → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ
  disjoint : Pairwise (fun i j ↦ Disjoint (coefficient i).roots (coefficient j).roots)
  union_eq : (⋃ i, (coefficient i).roots) = population.roots
  recovery : FiniteLabelCoreRecovery u a b lambda η₀ η₁ (fun i ↦ (coefficient i).roots)

/-- The original populations admit arbitrarily large finite continuous coefficient
cores, with arbitrarily small conditional pair loss uniformly over legal pairings. -/
def PopulationContinuousPressureCoreLaw (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ)
    (b : (ℚ → M) × ℝ → M) : Prop :=
  ∀ (Good : (ℚ → M) → Prop), (∀ᵐ z ∂lambda, Good z) →
    ∀ δ : ℝ≥0∞, δ ≠ 0 → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      Nonempty (PopulationContinuousPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good δ ε)

/-- The original supported moment, density and recovery laws produce finite joint
coefficient continuity cores without replacing the original label measure. -/
theorem PopulationFinitePressureCoreLaw.continuous_core
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda] {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    (hcore : PopulationFinitePressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hmoments : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instContinuousCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam) :
    PopulationContinuousPressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b := by
  let _instJointCoreMetric : MetricSpace M := F.metricSpace
  let _instJointCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instJointCorePolish : PolishSpace M := inferInstance
  let _instJointCoreLabelsBorel : BorelSpace (ℚ → M) := inferInstance
  intro Good hGood δ hδ ε hε
  obtain ⟨D⟩ := hcore Good hGood (ε / 2) (ENNReal.half_pos hε).ne'
  obtain ⟨N, C, hdisjoint, hcompact, hsub, _, hloss, _⟩ :=
    hmoments.exists_finite_coefficient_cores_within hcover hF hcomplete hu ha hinj
      hgap hsep hGood hδ (ENNReal.half_pos hε).ne' D.compact
  have hsmall : lambda (⋃ i, (C i).roots)ᶜ < ε := by
    apply hloss.trans_le
    calc
      lambda D.rootsᶜ + ε / 2 ≤ ε / 2 + ε / 2 := add_le_add D.complement_small.le le_rfl
      _ = ε := ENNReal.add_halves _
  exact ⟨{
    population := D.refine hrecovery hcomplete ha hu.continuous.measurable hcompact hsub hsmall
    count := N
    coefficient := C
    disjoint := hdisjoint
    union_eq := rfl
    recovery := hrecovery.finite_recovery ha hu.continuous.measurable _
      (fun i ↦ (C i).roots_compact.measurableSet) hdisjoint }⟩

/-- The jointly continuous root coefficient is the same actual coefficient whose
inverse moments and uniform legal-pair bounds are retained by the physical core. -/
theorem PopulationContinuousPressureCore.coefficient_data
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {δ ε : ℝ≥0∞}
    (D : PopulationContinuousPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good δ ε)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instContinuousCoefficientMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.count) {z : ℚ → M} (hz : z ∈ (D.coefficient i).roots) :
    let A := fun p : ℝ × ℝ ↦ populationSeedRootCoefficient
      (P (D.coefficient i).seedIndex).seed a
      (Module.finBasis ℝ (P (D.coefficient i).seedIndex).seed.covector.ker) (z, p)
    ConditionalCoefficientLocalization (condDistrib u a η₀ z) (condDistrib u a η₁ z) A ∧
      ∃ R ≥ 0, ∀ π : Measure (ℝ × ℝ),
        Vlasov.IsCoupling π (condDistrib u a η₀ z) (condDistrib u a η₁ z) →
        (∀ᵐ p ∂π, p.1 ≤ p.2) → ∀ᵐ p ∂π, ‖A p‖ ≤ R := by
  let _instCoefficientDataMetric : MetricSpace M := F.metricSpace
  let _instCoefficientDataProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instCoefficientDataPolish : PolishSpace M := inferInstance
  let _instCoefficientDataBorel : BorelSpace (ℚ → M) := inferInstance
  have hzpop : z ∈ D.population.roots := D.union_eq ▸ mem_iUnion.mpr ⟨i, hz⟩
  have hzpiece := (D.coefficient i).roots_subset_piece hz
  have hdata := (D.population.good z hzpop).2 (D.coefficient i).seedIndex hzpiece
  have heq := funext (populationSeedRootCoefficient_eq_pieceCoefficient P a κ lambda
    hF hcomplete hu ha hinj (D.coefficient i).seedIndex hzpiece)
  dsimp only
  rw [heq]
  refine ⟨hdata.2.1, ?_⟩
  obtain ⟨R, hR, hbound⟩ := hdata.2.2
  refine ⟨R, hR, fun π hπ ho ↦ ?_⟩
  simpa only [populationSeedRootCoefficient_eq_pieceCoefficient P a κ lambda
    hF hcomplete hu ha hinj (D.coefficient i).seedIndex hzpiece] using hbound π hπ ho

end OTSelector.Reconstruction
