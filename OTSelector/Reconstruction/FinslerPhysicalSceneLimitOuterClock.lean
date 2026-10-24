import OTSelector.Reconstruction.FinslerPhysicalSceneLimitClosedClock
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCountable

/-!
# The original positive clock gap through both scene limits

Uniform actual global energy controls the same physical support-distance gap
at every tilt and sample size. It survives the sample-size weak limits and,
as a closed physical edge constraint, the subsequent tilt-index weak limit.
All laws remain the actual original allocation and integer-target scene laws.
-/

open TopologicalSpace Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

open PointProcess PointProcess.LocalConfiguration

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι] [MetricSpace M] [MeasurableSpace M]
  [BorelSpace M] [SecondCountableTopology M]
variable (base : (ι → ℝ) × ℝ)

local instance physicalSceneOuterClockStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance physicalSceneOuterClockConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance physicalSceneOuterClockConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance physicalSceneOuterClockConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance physicalSceneOuterClockPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

set_option maxHeartbeats 1200000 in
/-- Uniform original energy in both indices retains the same explicit positive
original support gap through the sample-size limit and then the tilt limit. -/
theorem ae_iterated_actualAllocationRootedScene_clock_gap
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ ν : Measure M) [IsFiniteMeasure μ]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (aplus aminus : ∀ (_k n : ℕ), Ω n → M → Fin (m n + 1) → ℝ)
    (hplus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aplus k n z.1 z.2 j))
    (hminus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aminus k n z.1 z.2 j))
    (Y : ∀ n, Ω n → Fin (m n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (hYlaw : ∀ n j, (P n).map (fun w ↦ Y n w j) = ν)
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (hfeasplus : ∀ k n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aplus k n w))
    (hfeasminus : ∀ k n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aminus k n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ k n, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale n * (dist e.1 (Y n w e.2) - u (Y n w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aplus k n w) ∂P n) ≤ C)
    (henergyminus : ∀ k n, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale n * (dist e.1 (Y n w e.2) - u (Y n w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aminus k n w) ∂P n) ≤ C)
    (Q : ℕ → ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, StrictMono (φ k))
    (hinner : ∀ k, Tendsto (fun n ↦
      actualAllocationRootedCountableSceneLaw base (P (φ k n)) μ
        (aplus k (φ k n)) (aminus k (φ k n)) (hplus k (φ k n)) (hminus k (φ k n))
        (Y (φ k n)) (hY (φ k n)) (H (φ k n)) (hH (φ k n))
        (coord (φ k n)) (hcoord (φ k n)) u hu.continuous.measurable
        (D (φ k n)) (hD (φ k n))) atTop (𝓝 (Q k)))
    (R : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))
    (ψ : ℕ → ℕ) (houter : Tendsto (Q ∘ ψ) atTop (𝓝 R)) :
    ∃ gap > 0, ∀ᵐ s ∂(R : Measure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
      (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
        gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
        gap / 2 ≤ e.2.2 - e.1.2) := by
  obtain ⟨gap, hgap, hdist⟩ := exists_original_support_gap hA hB hAB
  let Qpair := fun k ↦ (Q k).map (f := Prod.fst) measurable_fst.aemeasurable
  have hweakpair (k : ℕ) : Tendsto (fun n ↦ actualAllocationRootedSceneLaw
      (P (φ k n)) μ (aplus k (φ k n)) (aminus k (φ k n))
      (hplus k (φ k n)) (hminus k (φ k n)) (Y (φ k n)) (hY (φ k n))
      (H (φ k n)) (hH (φ k n)) (coord (φ k n)) (hcoord (φ k n))
      u hu.continuous.measurable ((m (φ k n) : ℝ) + 1) (by positivity)
      (D (φ k n)) (hD (φ k n))) atTop (𝓝 (Qpair k)) := by
    have hw := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦ actualAllocationRootedCountableSceneLaw base (P (φ k n)) μ
        (aplus k (φ k n)) (aminus k (φ k n)) (hplus k (φ k n)) (hminus k (φ k n))
        (Y (φ k n)) (hY (φ k n)) (H (φ k n)) (hH (φ k n))
        (coord (φ k n)) (hcoord (φ k n)) u hu.continuous.measurable
        (D (φ k n)) (hD (φ k n))) (Q k) (hinner k) continuous_fst
    simpa only [map_actualAllocationRootedCountableSceneLaw_pair] using hw
  have hgappair (k : ℕ) := ae_actualAllocationRootedScene_limit_clock_gap
    (fun n ↦ m (φ k n)) (fun n ↦ P (φ k n)) μ ν hA hB hgap hdist hμA hνB
    (fun n ↦ aplus k (φ k n)) (fun n ↦ aminus k (φ k n))
    (fun n ↦ hplus k (φ k n)) (fun n ↦ hminus k (φ k n))
    (fun n ↦ Y (φ k n)) (fun n ↦ hY (φ k n)) (fun n ↦ hYlaw (φ k n))
    (fun n ↦ p (φ k n)) (fun n ↦ hfeasplus k (φ k n)) (fun n ↦ hfeasminus k (φ k n))
    (fun n ↦ H (φ k n)) (fun n ↦ hH (φ k n))
    (fun n ↦ coord (φ k n)) (fun n ↦ hcoord (φ k n)) hu
    (fun n ↦ scale (φ k n)) (fun n ↦ hscale (φ k n))
    (hscaleTop.comp (hφ k).tendsto_atTop)
    (fun n ↦ (m (φ k n) : ℝ) + 1) (fun _ ↦ by positivity)
    (fun n ↦ D (φ k n)) (fun n ↦ hD (φ k n)) C hC
    (fun n ↦ henergyplus k (φ k n)) (fun n ↦ henergyminus k (φ k n))
    (Qpair k) (hweakpair k)
  have hgapinner (k : ℕ) : ∀ᵐ s ∂(Q k : Measure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
      (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
        gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
        gap / 2 ≤ e.2.2 - e.1.2) :=
    ae_of_ae_map (μ := (Q k : Measure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))
      (f := Prod.fst)
      (p := fun s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
        (∀ᵐ e ∂(s.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
          gap / 2 ≤ e.2.2 - e.1.2) ∧
        (∀ᵐ e ∂(s.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
          gap / 2 ≤ e.2.2 - e.1.2)) measurable_fst.aemeasurable (hgappair k)
  let K : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
    {e | gap / 2 ≤ e.2.2 - e.1.2}
  have hK : IsClosed K := isClosed_le continuous_const (continuous_snd.snd.sub continuous_fst.snd)
  have hp := ae_localFiniteMeasure_carried_of_weak_tendsto R (Q ∘ ψ) houter
    (fun s ↦ s.1.1) continuous_fst.fst hK
    (fun k ↦ (hgapinner (ψ k)).mono fun _ h ↦ h.1)
  have hm := ae_localFiniteMeasure_carried_of_weak_tendsto R (Q ∘ ψ) houter
    (fun s ↦ s.1.2) continuous_fst.snd hK
    (fun k ↦ (hgapinner (ψ k)).mono fun _ h ↦ h.2)
  exact ⟨gap, hgap, hp.and hm⟩

end OTSelector.Reconstruction
