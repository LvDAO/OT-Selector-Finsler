import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCountable

/-!
# Actual iterated rooted scene limits

Original allocation feasibility controls the entire family of actual rooted
countable scene laws, simultaneously in tilt index and sample size. Compact
closure gives one weak sample-size limit at every fixed tilt and then an outer
weak tilt-index subsequence. Both outer plans keep their same countable integer
target carrier; no diagonal tilt choice or replacement local mass law occurs.
-/

open TopologicalSpace Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Uniform tightness of the full two-index law family gives a genuine outer
weak subsequence of any fixed-tilt inner limits, without a diagonal choice. -/
theorem exists_tendsto_outer_subseq_of_uniform_inner_tightness
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [PseudoMetrizableSpace X] [SeparableSpace X]
    (P : ℕ → ℕ → ProbabilityMeasure X)
    (htight : IsTightMeasureSet (range (fun q : ℕ × ℕ ↦ (P q.1 q.2 : Measure X))))
    (Q : ℕ → ProbabilityMeasure X) (φ : ℕ → ℕ → ℕ)
    (hinner : ∀ k, Tendsto (fun n ↦ P k (φ k n)) atTop (𝓝 (Q k))) :
    ∃ R : ProbabilityMeasure X, ∃ ψ : ℕ → ℕ,
      StrictMono ψ ∧ Tendsto (Q ∘ ψ) atTop (𝓝 R) := by
  have htight' : IsTightMeasureSet
      {((q : ProbabilityMeasure X) : Measure X) | q ∈ range (fun v : ℕ × ℕ ↦ P v.1 v.2)} := by
    convert htight using 1
    ext μ
    simp
  have hc := isCompact_closure_of_isTightMeasureSet htight'
  have hQ (k : ℕ) : Q k ∈ closure (range (fun v : ℕ × ℕ ↦ P v.1 v.2)) := by
    apply isClosed_closure.mem_of_tendsto (hinner k)
    exact Eventually.of_forall fun n ↦ subset_closure ⟨(k, φ k n), rfl⟩
  obtain ⟨R, _, ψ, hψ, hlim⟩ := hc.isSeqCompact hQ
  exact ⟨R, ψ, hψ, hlim⟩

open PointProcess PointProcess.LocalConfiguration

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
variable (base : (ι → ℝ) × ℝ)

local instance physicalSceneIteratedStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance physicalSceneIteratedConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance physicalSceneIteratedConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance physicalSceneIteratedConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance physicalSceneIteratedPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Original feasibility gives uniform tightness jointly in tilt index and
sample size, for the exact original countable rooted scene laws. -/
theorem isTightMeasureSet_all_tilts_actualAllocationRootedCountableSceneLaw
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ (_k n : ℕ), Ω n → M → Fin (m n + 1) → ℝ)
    (hplus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aplus k n z.1 z.2 j))
    (hminus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aminus k n z.1 z.2 j))
    (Y : ∀ n, Ω n → Fin (m n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (hfeasplus : ∀ k n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aplus k n w))
    (hfeasminus : ∀ k n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aminus k n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1)) :
    IsTightMeasureSet (range (fun q : ℕ × ℕ ↦
      (actualAllocationRootedCountableSceneLaw base (P q.2) μ
        (aplus q.1 q.2) (aminus q.1 q.2) (hplus q.1 q.2) (hminus q.1 q.2)
        (Y q.2) (hY q.2) (H q.2) (hH q.2) (coord q.2) (hcoord q.2)
        u hu (D q.2) (hD q.2) : Measure
        (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))) := by
  exact isTightMeasureSet_physicalSceneRootedCountableLocalSceneLaw base
    (fun q : ℕ × ℕ ↦ m q.2) (fun q : ℕ × ℕ ↦ P q.2)
    (fun q : ℕ × ℕ ↦ physicalSceneGlobalAllocationFamily μ (aplus q.1 q.2) (Y q.2))
    (fun q : ℕ × ℕ ↦ physicalSceneGlobalAllocationFamily μ (aminus q.1 q.2) (Y q.2))
    (fun q ↦ measurable_physicalSceneGlobalAllocationFamily μ (aplus q.1 q.2)
      (hplus q.1 q.2) (Y q.2) (hY q.2))
    (fun q ↦ measurable_physicalSceneGlobalAllocationFamily μ (aminus q.1 q.2)
      (hminus q.1 q.2) (Y q.2) (hY q.2))
    (fun q ↦ H q.2) (fun q ↦ hH q.2) (fun q ↦ coord q.2) (fun q ↦ hcoord q.2)
    u hu (fun q ↦ Y q.2) (fun q ↦ hY q.2) (fun q ↦ D q.2) (fun q ↦ hD q.2)
    (μ univ) (measure_ne_top μ univ)
    (fun q ↦ (lintegral_physicalSceneGlobalAllocationFamily_univ (P q.2) μ
      (aplus q.1 q.2) (Y q.2) (p q.2) (hfeasplus q.1 q.2)).le)
    (fun q ↦ (lintegral_physicalSceneGlobalAllocationFamily_univ (P q.2) μ
      (aminus q.1 q.2) (Y q.2) (p q.2) (hfeasminus q.1 q.2)).le)

/-- Iterated actual original scene limits keep the same countable target
carrier after the outer tilt limit, with no diagonal replacement of laws. -/
theorem exists_outer_subseq_actualAllocationRootedCountableSceneLaw
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ (_k n : ℕ), Ω n → M → Fin (m n + 1) → ℝ)
    (hplus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aplus k n z.1 z.2 j))
    (hminus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aminus k n z.1 z.2 j))
    (Y : ∀ n, Ω n → Fin (m n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (hfeasplus : ∀ k n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aplus k n w))
    (hfeasminus : ∀ k n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aminus k n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (Q : ℕ → ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))
    (φ : ℕ → ℕ → ℕ)
    (hinner : ∀ k, Tendsto (fun n ↦
      actualAllocationRootedCountableSceneLaw base (P (φ k n)) μ
        (aplus k (φ k n)) (aminus k (φ k n)) (hplus k (φ k n)) (hminus k (φ k n))
        (Y (φ k n)) (hY (φ k n)) (H (φ k n)) (hH (φ k n))
        (coord (φ k n)) (hcoord (φ k n)) u hu (D (φ k n)) (hD (φ k n)))
        atTop (𝓝 (Q k)))
    (hsupported : ∀ k, ∀ᵐ s ∂(Q k : Measure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.1 ∧
        SupportedOverConfiguration Prod.snd s.2 s.1.2) :
    ∃ R, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (Q ∘ ψ) atTop (𝓝 R) ∧
      ∀ᵐ s ∂(R : Measure
        (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
        (Function.support (LocalConfiguration.multiplicity s.2)).Countable ∧
        (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
          e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2)) ∧
        (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
          e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2)) := by
  let laws := fun k n ↦ actualAllocationRootedCountableSceneLaw base (P n) μ
    (aplus k n) (aminus k n) (hplus k n) (hminus k n)
    (Y n) (hY n) (H n) (hH n) (coord n) (hcoord n) u hu (D n) (hD n)
  have htight := isTightMeasureSet_all_tilts_actualAllocationRootedCountableSceneLaw base
    m P μ aplus aminus hplus hminus Y hY p hfeasplus hfeasminus H hH coord hcoord u hu D hD
  obtain ⟨R, ψ, hψ, houter⟩ :=
    exists_tendsto_outer_subseq_of_uniform_inner_tightness laws htight Q φ hinner
  have hp := ae_supportedOverConfiguration_of_weak_tendsto R (Q ∘ ψ) houter
    Prod.snd continuous_snd Prod.snd (fun s ↦ s.1.1) continuous_snd continuous_fst.fst
    (fun k ↦ (hsupported (ψ k)).mono fun _ h ↦ h.1)
  have hm := ae_supportedOverConfiguration_of_weak_tendsto R (Q ∘ ψ) houter
    Prod.snd continuous_snd Prod.snd (fun s ↦ s.1.2) continuous_snd continuous_fst.snd
    (fun k ↦ (hsupported (ψ k)).mono fun _ h ↦ h.2)
  refine ⟨R, ψ, hψ, houter, ?_⟩
  filter_upwards [hp, hm] with s hs ht
  exact ⟨countable_multiplicity_support s.2,
    (supportedOverConfiguration_iff_ae_mem Prod.snd continuous_snd _ _).mp hs,
    (supportedOverConfiguration_iff_ae_mem Prod.snd continuous_snd _ _).mp ht⟩

/-- Actual original global feasibility produces both the inner sample-size
limits and the outer tilt-index limit, preserving their order. -/
theorem exists_iterated_actualAllocationRootedCountableSceneLaw
    [MeasurableSingletonClass M]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ (_k n : ℕ), Ω n → M → Fin (m n + 1) → ℝ)
    (hplus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aplus k n z.1 z.2 j))
    (hminus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aminus k n z.1 z.2 j))
    (Y : ∀ n, Ω n → Fin (m n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (hfeasplus : ∀ k n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aplus k n w))
    (hfeasminus : ∀ k n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aminus k n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1)) :
    ∃ Q : ℕ → ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base),
    ∃ φ : ℕ → ℕ → ℕ,
      (∀ k, StrictMono (φ k) ∧ Tendsto (fun n ↦
        actualAllocationRootedCountableSceneLaw base (P (φ k n)) μ
          (aplus k (φ k n)) (aminus k (φ k n)) (hplus k (φ k n)) (hminus k (φ k n))
          (Y (φ k n)) (hY (φ k n)) (H (φ k n)) (hH (φ k n))
          (coord (φ k n)) (hcoord (φ k n)) u hu (D (φ k n)) (hD (φ k n)))
          atTop (𝓝 (Q k))) ∧
      ∃ R, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (Q ∘ ψ) atTop (𝓝 R) ∧
        ∀ᵐ s ∂(R : Measure
          (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
          (Function.support (LocalConfiguration.multiplicity s.2)).Countable ∧
          (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
            e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2)) ∧
          (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
            e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2)) := by
  choose Q φ hmono hweak hsupport using fun k ↦
    exists_tendsto_subseq_actualAllocationRootedCountableSceneLaw base m P μ
      (aplus k) (aminus k) (hplus k) (hminus k) Y hY p
      (hfeasplus k) (hfeasminus k) H hH coord hcoord u hu D hD
  refine ⟨Q, φ, fun k ↦ ⟨hmono k, hweak k⟩, ?_⟩
  exact exists_outer_subseq_actualAllocationRootedCountableSceneLaw base m P μ
    aplus aminus hplus hminus Y hY p hfeasplus hfeasminus H hH coord hcoord u hu D hD
    Q φ hweak hsupport


end OTSelector.Reconstruction
