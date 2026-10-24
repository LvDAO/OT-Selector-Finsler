import OTSelector.Reconstruction.FinslerRootMomentEnvelope
import OTSelector.Reconstruction.FinslerCoefficientPressureFreezing
import OTSelector.Reconstruction.KernelMomentUniformIntegrability

/-!
# Uniform original moments on large compact root cores

The actual measurable marginal envelope is bounded on a compact refinement of
each original coefficient core. Every legal conditional coupling shares this
bound. Integrating the unchanged root law then produces uniform joint tails and
small-event control for arbitrary measurable kernels of legal pairings.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

/-- The original two marginal moments based at this core's fixed scalar left endpoint. -/
def momentEnvelope (r : ℝ) : Z → ℝ :=
  populationSeedRootMomentEnvelope (P C.seedIndex).seed a
    (condDistrib u a η₀) (condDistrib u a η₁) C.window.val.1 r

/-- A compact root refinement with a common bound for its actual marginal envelope. -/
structure UniformMomentCore (r : ℝ) where
  roots : Set Z
  subset : roots ⊆ C.roots
  compact : IsCompact roots
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  envelope_le : ∀ z ∈ roots, C.momentEnvelope r z ≤ bound

/-- Further compact refinements retain the same actual moment envelope and bound. -/
def UniformMomentCore.refine {r : ℝ} (D : C.UniformMomentCore r)
    {K : Set Z} (hK : IsCompact K) (hsub : K ⊆ D.roots) : C.UniformMomentCore r where
  roots := K
  subset := hsub.trans D.subset
  compact := hK
  bound := D.bound
  bound_nonneg := D.bound_nonneg
  envelope_le := fun z hz ↦ D.envelope_le z (hsub hz)

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]

/-- Joint measurability of the actual inverse coefficient uses the original seed producer. -/
theorem measurable_inverse_matrix (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootMomentMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    Measurable (fun q : Z × (ℝ × ℝ) ↦ (C.matrix q.1 q.2)⁻¹) :=
  ContinuousFinslerNorm.measurable_real_matrix_inverse.comp
    (measurable_populationSeedRootCoefficient (P C.seedIndex).seed hF hcomplete hu ha hinj
      (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker))

/-- The uniform envelope core loses arbitrarily little original root mass and
retains the same coefficient window, original seed and two conditional laws. -/
theorem exists_uniformMomentCore [PolishSpace Z] [BorelSpace Z]
    [IsFiniteMeasure lambda] (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootMomentMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (r : ℝ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ D : C.UniformMomentCore r, lambda (C.roots \ D.roots) < ε := by
  obtain ⟨K, hsub, hcompact, hsmall, L, hL, hbound⟩ :=
    exists_compact_rootMomentEnvelope_bound (P C.seedIndex).seed hF hcomplete hu ha hinj
      (condDistrib u a η₀) (condDistrib u a η₁) C.window.val.1 r
      C.roots_compact.measurableSet (measure_ne_top lambda C.roots)
      (Good := fun _ ↦ True) (ae_of_all _ (fun _ ↦ trivial)) hε
  exact ⟨{
    roots := K
    subset := hsub
    compact := hcompact
    bound := L
    bound_nonneg := hL
    envelope_le := fun z hz ↦ (hbound z hz).2 }, hsmall⟩

namespace UniformMomentCore

variable {C} {r : ℝ} (D : C.UniformMomentCore r)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instRootMomentMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The actual common envelope bounds every legal pairing at every retained root. -/
theorem inverse_moment_bound {z : Z} (hz : z ∈ D.roots)
    {π : Measure (ℝ × ℝ)}
    (hπ : Vlasov.IsCoupling π (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    (horder : ∀ᵐ p ∂π, p.1 < p.2) (hr0 : 0 < r) (hr2 : r < 2) :
    Integrable (fun p ↦ ‖(C.matrix z p)⁻¹‖ ^ r) π ∧
      (∫ p, ‖(C.matrix z p)⁻¹‖ ^ r ∂π) ≤ D.bound := by
  have hb := (C.original_window z (D.subset hz)).inverse_moments_le_rootEnvelope
    (P C.seedIndex).seed hF hcomplete hu ha hinj hπ horder hr0 hr2
  exact ⟨hb.1, hb.2.trans (D.envelope_le z hz)⟩

/-- The full original root mass is retained in the joint moment bound; the kernel
may choose any legal pairing separately at each root. -/
theorem joint_inverse_moment_bound [BorelSpace Z] [T2Space Z] [IsFiniteMeasure lambda]
    (k : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel k]
    (hk : ∀ᵐ z ∂lambda.restrict D.roots,
      Vlasov.IsCoupling (k z) (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧
        ∀ᵐ p ∂k z, p.1 < p.2) (hr0 : 0 < r) (hr2 : r < 2) :
    Integrable (fun q : Z × (ℝ × ℝ) ↦ ‖(C.matrix q.1 q.2)⁻¹‖ ^ r)
        (lambda.restrict D.roots ⊗ₘ k) ∧
      (∫ q, ‖(C.matrix q.1 q.2)⁻¹‖ ^ r ∂(lambda.restrict D.roots ⊗ₘ k)) ≤
        D.bound * lambda.real D.roots := by
  have hdata : ∀ᵐ z ∂lambda.restrict D.roots,
      Integrable (fun p ↦ ‖(C.matrix z p)⁻¹‖ ^ r) (k z) ∧
        (∫ p, ‖(C.matrix z p)⁻¹‖ ^ r ∂k z) ≤ D.bound := by
    filter_upwards [ae_restrict_mem D.compact.measurableSet, hk] with z hz hkz
    exact D.inverse_moment_bound hF hcomplete hu ha hinj hz hkz.1 hkz.2 hr0 hr2
  simpa only [measureReal_restrict_apply_univ] using
    integrable_compProd_norm_rpow_of_uniform_moment
      (C.measurable_inverse_matrix hF hcomplete hu ha hinj) (hdata.mono (fun _ hz ↦ hz.1)) (hdata.mono (fun _ hz ↦ hz.2))

/-- One cutoff controls the joint inverse-coefficient tails for every measurable
kernel of legal original pairings over this retained root core. -/
theorem uniform_joint_inverse_tails [BorelSpace Z] [T2Space Z] [IsFiniteMeasure lambda]
    (hr1 : 1 < r) (hr2 : r < 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ R > 0, ∀ k : Kernel Z (ℝ × ℝ), IsSFiniteKernel k →
      (∀ᵐ z ∂lambda.restrict D.roots,
        Vlasov.IsCoupling (k z) (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧
          ∀ᵐ p ∂k z, p.1 < p.2) →
      (∫ q in {q : Z × (ℝ × ℝ) | R < ‖(C.matrix q.1 q.2)⁻¹‖},
        ‖(C.matrix q.1 q.2)⁻¹‖ ∂(lambda.restrict D.roots ⊗ₘ k)) < ε := by
  obtain ⟨R, hR, htail⟩ := exists_uniform_norm_tail_of_rpow_bound
    (C.measurable_inverse_matrix hF hcomplete hu ha hinj) hr1 hε
      (L := D.bound * lambda.real D.roots)
  refine ⟨R, hR, fun k hkfinite hk ↦ ?_⟩
  let : IsSFiniteKernel k := hkfinite
  have hm := D.joint_inverse_moment_bound hF hcomplete hu ha hinj k hk
    (zero_lt_one.trans hr1) hr2
  exact htail _ hm.1 hm.2

/-- Arbitrary small deleted joint events have uniformly small inverse-coefficient
integrals across all legal Markov pairing kernels, with one threshold for the core. -/
theorem uniform_joint_inverse_small_sets [BorelSpace Z] [T2Space Z] [IsFiniteMeasure lambda]
    (hr1 : 1 < r) (hr2 : r < 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ k : Kernel Z (ℝ × ℝ), IsMarkovKernel k →
      (∀ᵐ z ∂lambda.restrict D.roots,
        Vlasov.IsCoupling (k z) (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧
          ∀ᵐ p ∂k z, p.1 < p.2) →
      ∀ Q : Set (Z × (ℝ × ℝ)), MeasurableSet Q →
        (lambda.restrict D.roots ⊗ₘ k).real Q ≤ τ →
        (∫ q in Q, ‖(C.matrix q.1 q.2)⁻¹‖ ∂(lambda.restrict D.roots ⊗ₘ k)) < ε := by
  obtain ⟨τ, hτ, hsmall⟩ := exists_uniform_norm_small_sets_of_rpow_bound
    (C.measurable_inverse_matrix hF hcomplete hu ha hinj) hr1 hε
      (L := D.bound * lambda.real D.roots)
  refine ⟨τ, hτ, fun k hkmarkov hk Q hQ hmass ↦ ?_⟩
  let : IsMarkovKernel k := hkmarkov
  have hm := D.joint_inverse_moment_bound hF hcomplete hu ha hinj k hk
    (zero_lt_one.trans hr1) hr2
  exact hsmall _ inferInstance hm.1 hm.2 Q hQ hmass

/-- The original support gap supplies strict pair order from the usual weak
optimal-face legality, so the joint moment bound needs no extra order hypothesis. -/
theorem joint_inverse_moment_bound_of_original_order
    [BorelSpace Z] [T2Space Z] [IsFiniteMeasure lambda]
    {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam)
    (k : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel k]
    (hk : ∀ᵐ z ∂lambda.restrict D.roots,
      Vlasov.IsCoupling (k z) (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧
        ∀ᵐ p ∂k z, p.1 ≤ p.2) (hr0 : 0 < r) (hr2 : r < 2) :
    Integrable (fun q : Z × (ℝ × ℝ) ↦ ‖(C.matrix q.1 q.2)⁻¹‖ ^ r)
        (lambda.restrict D.roots ⊗ₘ k) ∧
      (∫ q, ‖(C.matrix q.1 q.2)⁻¹‖ ^ r ∂(lambda.restrict D.roots ⊗ₘ k)) ≤
        D.bound * lambda.real D.roots := by
  apply D.joint_inverse_moment_bound hF hcomplete hu ha hinj k _ hr0 hr2
  filter_upwards [hk, ae_restrict_of_ae hsep] with z hkz hsz
  exact ⟨hkz.1, hsz.ae_strict_order_of_coupling hgap hkz.1 hkz.2⟩

/-- Any sufficiently large measurable joint core preserves the integrated original
compliance, uniformly over every legal pairing kernel on this retained root core.
The deleted event may depend on both the root and the paired scalar times. -/
theorem uniform_joint_inverse_recovery_error
    [BorelSpace Z] [T2Space Z] [IsFiniteMeasure lambda]
    {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam)
    (hr1 : 1 < r) (hr2 : r < 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ k : Kernel Z (ℝ × ℝ), IsMarkovKernel k →
      (∀ᵐ z ∂lambda.restrict D.roots,
        Vlasov.IsCoupling (k z) (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧
          ∀ᵐ p ∂k z, p.1 ≤ p.2) →
      ∀ Q : Set (Z × (ℝ × ℝ)), MeasurableSet Q →
        (lambda.restrict D.roots ⊗ₘ k).real Qᶜ ≤ τ →
        ‖(∫ q, (C.matrix q.1 q.2)⁻¹ ∂(lambda.restrict D.roots ⊗ₘ k)) -
          ∫ q in Q, (C.matrix q.1 q.2)⁻¹ ∂(lambda.restrict D.roots ⊗ₘ k)‖ < ε := by
  obtain ⟨τ, hτ, hsmall⟩ := D.uniform_joint_inverse_small_sets hF hcomplete hu ha hinj
    hr1 hr2 hε
  refine ⟨τ, hτ, fun k hkmarkov hk Q hQ hmass ↦ ?_⟩
  let : IsMarkovKernel k := hkmarkov
  have hstrict : ∀ᵐ z ∂lambda.restrict D.roots,
      Vlasov.IsCoupling (k z) (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧
        ∀ᵐ p ∂k z, p.1 < p.2 := by
    filter_upwards [hk, ae_restrict_of_ae hsep] with z hkz hsz
    exact ⟨hkz.1, hsz.ae_strict_order_of_coupling hgap hkz.1 hkz.2⟩
  have hm := D.joint_inverse_moment_bound hF hcomplete hu ha hinj k hstrict
    (zero_lt_one.trans hr1) hr2
  have hf := C.measurable_inverse_matrix hF hcomplete hu ha hinj
  have hnorm : Integrable (fun q : Z × (ℝ × ℝ) ↦ ‖(C.matrix q.1 q.2)⁻¹‖)
      (lambda.restrict D.roots ⊗ₘ k) := by
    have h := integrable_norm_rpow_of_le hf.aestronglyMeasurable
      (show (0 : ℝ) ≤ 1 by norm_num) (zero_lt_one.trans hr1).le hr1.le hm.1
    simpa only [Real.rpow_one] using h
  have hi := (integrable_norm_iff hf.aestronglyMeasurable).mp hnorm
  rw [← integral_add_compl hQ hi, add_sub_cancel_left]
  exact (norm_integral_le_integral_norm _).trans_lt
    (hsmall k hkmarkov hstrict Qᶜ hQ.compl hmass)

end UniformMomentCore
end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
