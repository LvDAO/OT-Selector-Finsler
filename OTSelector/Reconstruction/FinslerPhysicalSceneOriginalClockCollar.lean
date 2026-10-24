import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalClockNull
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonNearMass
import Mathlib.Topology.MetricSpace.Thickening

/-! Clock-window endpoint trimming is paid by unchanged original populations.
Finite threshold collars have vanishing mass before any sample, allocation or
weak scene is chosen. No atomlessness of a weak limiting scene is assumed. -/
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

section Collars
variable {M : Type*} [MeasurableSpace M]

/-- Original points whose actual potential clock is close to one of the
finitely many endpoint thresholds of the chosen windows. -/
def originalClockEndpointCollar (u : M → ℝ) (thresholds : Finset ℝ) (ε : ℝ) : Set M :=
  u ⁻¹' Metric.cthickening ε (↑thresholds : Set ℝ)

theorem measurableSet_originalClockEndpointCollar
    {u : M → ℝ} (hu : Measurable u) (thresholds : Finset ℝ) (ε : ℝ) :
    MeasurableSet (originalClockEndpointCollar u thresholds ε) :=
  Metric.isClosed_cthickening.measurableSet.preimage hu

omit [MeasurableSpace M] in
/-- The actual shrinking collars meet only the original finitely many clock
levels; this is an exact set identity, including an empty threshold family. -/
theorem iInter_originalClockEndpointCollar (u : M → ℝ) (thresholds : Finset ℝ) :
    (⋂ n : ℕ, originalClockEndpointCollar u thresholds (1 / ((n : ℝ) + 1))) =
      u ⁻¹' (↑thresholds : Set ℝ) := by
  classical
  ext x
  simp only [mem_iInter, originalClockEndpointCollar, mem_preimage]
  constructor
  · intro hx
    by_contra hnot
    have hclosed : IsClosed (↑thresholds : Set ℝ) := thresholds.finite_toSet.isClosed
    have hnotclosure : u x ∉ closure (↑thresholds : Set ℝ) := by
      simpa only [hclosed.closure_eq] using hnot
    have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Metric.eventually_notMem_cthickening_of_infEDist_pos hnotclosure)
    obtain ⟨n, hn⟩ := hsmall.exists
    exact hn (hx n)
  · intro hx n
    exact Metric.closure_subset_cthickening _ _ (subset_closure hx)

/-- Null original threshold levels give a null finite union of those levels. -/
theorem originalClockFiniteLevels_null (μ : Measure M) (u : M → ℝ) (thresholds : Finset ℝ)
    (hnull : ∀ q ∈ thresholds, μ (u ⁻¹' {q}) = 0) :
    μ (u ⁻¹' (↑thresholds : Set ℝ)) = 0 := by
  classical
  have heq : u ⁻¹' (↑thresholds : Set ℝ) = ⋃ q : thresholds, u ⁻¹' {q.val} := by
    ext x
    simp only [mem_preimage, Finset.mem_coe, mem_iUnion, mem_singleton_iff]
    exact ⟨fun hx ↦ ⟨⟨u x, hx⟩, rfl⟩, fun ⟨q, hq⟩ ↦ hq ▸ q.property⟩
  rw [heq]
  exact measure_iUnion_null fun q ↦ hnull q.val q.property

/-- Original finite-measure clock collars vanish by continuity from above.
Only the actual original thresholds need be null. -/
theorem tendsto_originalClockEndpointCollar
    (μ : Measure M) [IsFiniteMeasure μ] {u : M → ℝ} (hu : Measurable u)
    (thresholds : Finset ℝ) (hnull : ∀ q ∈ thresholds, μ (u ⁻¹' {q}) = 0) :
    Tendsto (fun n : ℕ ↦ μ (originalClockEndpointCollar u thresholds (1 / ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
  have hm : Antitone (fun n : ℕ ↦ originalClockEndpointCollar u thresholds (1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    apply preimage_mono
    apply Metric.cthickening_mono
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1)
    exact add_le_add (Nat.cast_le.mpr hmn) le_rfl
  have h := tendsto_measure_iInter_atTop
    (μ := μ) (fun n ↦ (measurableSet_originalClockEndpointCollar hu thresholds _).nullMeasurableSet)
    hm ⟨0, measure_ne_top _ _⟩
  rw [iInter_originalClockEndpointCollar,
    originalClockFiniteLevels_null μ u thresholds hnull] at h
  exact h

/-- Discard an original edge only when one actual endpoint clock enters a
chosen endpoint collar. Both observations keep their original clocks. -/
def originalClockEndpointBadEdge (u : M → ℝ) (thresholds : Finset ℝ) (ε : ℝ) : Set (M × M) :=
  (originalClockEndpointCollar u thresholds ε ×ˢ univ) ∪
    (univ ×ˢ originalClockEndpointCollar u thresholds ε)

theorem measurableSet_originalClockEndpointBadEdge
    {u : M → ℝ} (hu : Measurable u) (thresholds : Finset ℝ) (ε : ℝ) :
    MeasurableSet (originalClockEndpointBadEdge u thresholds ε) :=
  ((measurableSet_originalClockEndpointCollar hu thresholds ε).prod MeasurableSet.univ).union
    (MeasurableSet.univ.prod (measurableSet_originalClockEndpointCollar hu thresholds ε))

/-- One actual globally feasible allocation pays its collar loss with the
unchanged two original population masses. The bound is uniform in sample size
and allocation, including its original random Dirichlet target columns. -/
theorem lintegral_originalAllocation_clockEndpointCollar_le
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (A : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hA : ∀ j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ A z.1 z.2 j))
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (A z))
    {u : M → ℝ} (hu : Measurable u) (thresholds : Finset ℝ) (ε : ℝ) :
    (∫⁻ z, physicalSceneGlobalAllocationFamily μ A (fun z ↦ z.1) z
      (originalClockEndpointBadEdge u thresholds ε)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      μ (originalClockEndpointCollar u thresholds ε) +
        ν (originalClockEndpointCollar u thresholds ε) := by
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Γ := physicalSceneGlobalAllocationFamily μ A (fun z ↦ z.1)
  let K := originalClockEndpointCollar u thresholds ε
  have hK : MeasurableSet K := measurableSet_originalClockEndpointCollar hu thresholds ε
  have hΓ : Measurable Γ := measurable_physicalSceneGlobalAllocationFamily μ A hA
    (fun z ↦ z.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
  calc
    _ ≤ ∫⁻ z, Γ z (K ×ˢ univ) + Γ z (univ ×ˢ K) ∂Penv :=
      lintegral_mono fun z ↦ measure_union_le _ _
    _ = (∫⁻ z, Γ z (K ×ˢ univ) ∂Penv) + ∫⁻ z, Γ z (univ ×ˢ K) ∂Penv := by
      apply lintegral_add_left
      exact (Measure.measurable_coe (hK.prod MeasurableSet.univ)).comp hΓ
    _ = _ := by
      rw [lintegral_physicalSceneGlobalAllocationFamily_sourceSet_eq μ ν n A hfeas hK,
        lintegral_physicalSceneGlobalAllocationFamily_targetSet_eq μ ν n A hfeas hK]

/-- Endpoint collar loss tends to zero uniformly over every original sample
size and feasible global allocation, before any weak limits are taken. -/
theorem exists_originalClockEndpointCollar_allocation_loss_lt
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] {u : M → ℝ}
    (hu : Measurable u) (thresholds : Finset ℝ)
    (hμnull : ∀ q ∈ thresholds, μ (u ⁻¹' {q}) = 0)
    (hνnull : ∀ q ∈ thresholds, ν (u ⁻¹' {q}) = 0)
    {loss : ℝ≥0∞} (hloss : 0 < loss) :
    ∃ k : ℕ, ∀ n : ℕ,
      ∀ (A : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ),
      (∀ j, Measurable (fun z :
        ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ A z.1 z.2 j)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (A z)) →
      (∫⁻ z, physicalSceneGlobalAllocationFamily μ A (fun z ↦ z.1) z
        (originalClockEndpointBadEdge u thresholds (1 / ((k : ℝ) + 1)))
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) < loss := by
  have hμ := tendsto_originalClockEndpointCollar μ hu thresholds hμnull
  have hν := tendsto_originalClockEndpointCollar ν hu thresholds hνnull
  have hsum : Tendsto (fun k : ℕ ↦
      μ (originalClockEndpointCollar u thresholds (1 / ((k : ℝ) + 1))) +
      ν (originalClockEndpointCollar u thresholds (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
    simpa only [add_zero] using hμ.add hν
  obtain ⟨k, hk⟩ := (hsum.eventually (gt_mem_nhds hloss)).exists
  exact ⟨k, fun n A hA hfeas ↦
    (lintegral_originalAllocation_clockEndpointCollar_le μ ν n A hA hfeas hu thresholds _).trans_lt hk⟩
end Collars
end OTSelector.Reconstruction
