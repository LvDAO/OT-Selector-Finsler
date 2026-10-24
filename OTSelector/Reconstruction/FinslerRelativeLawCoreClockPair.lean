import OTSelector.Reconstruction.FinslerRelativeLawReferenceBinFeasibility
import OTSelector.Reconstruction.FinslerPopulationLocalPressureCore

/-!
Original reference-bin feasibility and measurable legal population reconstruction.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- One original conditional pair condition is retained before all later
reference-bin choices. It keeps both literal conditional marginals, the actual
clock gap, and the full original clock range. -/
def originalClockPairGood {Z : Type*} [MeasurableSpace Z]
    (γ : Kernel Z (ℝ × ℝ)) (κ₀ κ₁ : Kernel Z ℝ) (gap : ℝ) (I : Set ℝ) (z : Z) : Prop :=
  Vlasov.IsCoupling (γ z) (κ₀ z) (κ₁ z) ∧
  (∀ᵐ p ∂γ z, gap ≤ p.2 - p.1) ∧
  (∀ᵐ s ∂κ₀ z, s ∈ I) ∧ (∀ᵐ t ∂κ₁ z, t ∈ I)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}

omit [BorelSpace E] in
/-- The actual original population law produces pressure cores retaining one
original pair kernel and full clock range. No finite Hall premise is added. -/
theorem PopulationLocalPressureCoreLaw.exists_original_clockPair_core
    (hcore : PopulationLocalPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    (π : Measure (M × M)) (hπ : Vlasov.IsCoupling π μ ν)
    (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2)
    (gap : ℝ) (hgap : ∀ᵐ p ∂π, gap ≤ u p.2 - u p.1)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hμI : ∀ᵐ x ∂μ, u x ∈ I) (hνI : ∀ᵐ y ∂ν, u y ∈ I) :
    ∃ γ : Kernel (ℚ → M) (ℝ × ℝ), IsMarkovKernel γ ∧
      ∀ (δ loss : ℝ≥0∞), δ ≠ 0 → loss ≠ 0 →
        Nonempty (PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
          (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨γ, hγ, hgood⟩ := exists_original_clockPair_kernel_with_range μ ν π hπ a u ha hu
    hlabel gap hgap I hI hμI hνI
  exact ⟨γ, hγ, fun δ loss hδ hloss ↦ hcore _ hgood δ hδ loss hloss⟩

end OTSelector.Reconstruction
