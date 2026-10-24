import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMacroscopic
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutIterated

/-!
# Same original allocation laws with their actual macroscopic root

The original feasible global allocations retain their realized restricted
columns while their actual macroscopic seed root is recorded. Exact projection
recovers the existing actual countable law; compact macroscopic roots and
original total source mass produce uniform joint tightness.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance iteratedMacroscopicPhysicalSceneStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance iteratedMacroscopicPhysicalSceneConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance iteratedMacroscopicPhysicalSceneConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance iteratedMacroscopicPhysicalSceneConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance iteratedMacroscopicPhysicalScenePlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

/-- Actual original feasibility supplies one joint tightness bound uniformly in both indices. -/
theorem isTightMeasureSet_all_tilts_actualAllocationRootedMacroscopicSceneLaw
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (Penv : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (Penv n)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ (_ℓ n : ℕ), Ωn n → M → Fin (m n + 1) → ℝ)
    (hplus : ∀ ℓ n j, Measurable (fun z : Ωn n × M ↦ aplus ℓ n z.1 z.2 j))
    (hminus : ∀ ℓ n j, Measurable (fun z : Ωn n × M ↦ aminus ℓ n z.1 z.2 j))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (hfp : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ (p n w) (aplus ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ (p n w) (aminus ℓ n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (scale : ℕ → ℝ)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hDK : ∀ n z, z ∈ D n → physicalSceneMacroscopicRoot (scale n) z ∈ K) :
    IsTightMeasureSet (range (fun q : ℕ × ℕ ↦
      (actualAllocationRootedMacroscopicSceneLaw base (Penv q.2) μ
        (aplus q.1 q.2) (aminus q.1 q.2) (hplus q.1 q.2) (hminus q.1 q.2)
        (Y q.2) (hY q.2) (H q.2) (hH q.2) (coord q.2) (hcoord q.2) u hu
        (scale q.2) (D q.2) (hD q.2) : Measure ((ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))))) :=
  isTightMeasureSet_actualAllocationRootedMacroscopicSceneLaw base
    (fun q : ℕ × ℕ ↦ m q.2) (fun q : ℕ × ℕ ↦ Penv q.2) μ
    (fun q ↦ aplus q.1 q.2) (fun q ↦ aminus q.1 q.2)
    (fun q ↦ hplus q.1 q.2) (fun q ↦ hminus q.1 q.2)
    (fun q ↦ Y q.2) (fun q ↦ hY q.2) (fun q ↦ p q.2)
    (fun q ↦ hfp q.1 q.2) (fun q ↦ hfm q.1 q.2)
    (fun q ↦ H q.2) (fun q ↦ hH q.2) (fun q ↦ coord q.2) (fun q ↦ hcoord q.2)
    u hu (fun q ↦ scale q.2) (fun q ↦ D q.2) (fun q ↦ hD q.2) K hK
    (fun q ↦ hDK q.2)

/-- Both separate weak-limit stages exist for the same original macro-tagged
allocation scene, without any replacement of its actual restricted columns. -/
theorem exists_iterated_actualAllocationRootedMacroscopicSceneLaw
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (Penv : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (Penv n)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ (_ℓ n : ℕ), Ωn n → M → Fin (m n + 1) → ℝ)
    (hplus : ∀ ℓ n j, Measurable (fun z : Ωn n × M ↦ aplus ℓ n z.1 z.2 j))
    (hminus : ∀ ℓ n j, Measurable (fun z : Ωn n × M ↦ aminus ℓ n z.1 z.2 j))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (hfp : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ (p n w) (aplus ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ (p n w) (aminus ℓ n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (scale : ℕ → ℝ)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hDK : ∀ n z, z ∈ D n → physicalSceneMacroscopicRoot (scale n) z ∈ K) :
    let laws := fun ℓ n ↦ actualAllocationRootedMacroscopicSceneLaw base (Penv n) μ
      (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n)
      (Y n) (hY n) (H n) (hH n) (coord n) (hcoord n) u hu (scale n) (D n) (hD n)
    ∃ Q : ℕ → ProbabilityMeasure ((ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)), ∃ φ : ℕ → ℕ → ℕ,
      (∀ ℓ, StrictMono (φ ℓ) ∧ Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) ∧
      ∃ R : ProbabilityMeasure ((ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)), ∃ ψ : ℕ → ℕ,
        StrictMono ψ ∧ Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R) := by
  let laws := fun ℓ n ↦ actualAllocationRootedMacroscopicSceneLaw base (Penv n) μ
    (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n)
    (Y n) (hY n) (H n) (hH n) (coord n) (hcoord n) u hu (scale n) (D n) (hD n)
  have htight := isTightMeasureSet_all_tilts_actualAllocationRootedMacroscopicSceneLaw
    base m Penv μ aplus aminus hplus hminus Y hY p hfp hfm H hH coord hcoord u hu scale D hD K hK hDK
  have hi (ℓ : ℕ) : ∃ Q : ProbabilityMeasure ((ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun n ↦ laws ℓ (φ n)) atTop (𝓝 Q) := by
    apply exists_tendsto_subseq_probabilityMeasure_of_isTight (laws ℓ)
    apply htight.subset
    rintro _ ⟨n, rfl⟩
    exact ⟨(ℓ, n), rfl⟩
  choose Q φ hφ hinner using hi
  obtain ⟨R, ψ, hψ, houter⟩ := exists_tendsto_outer_subseq_of_uniform_inner_tightness
    laws htight Q φ hinner
  exact ⟨Q, φ, fun ℓ ↦ ⟨hφ ℓ, hinner ℓ⟩, R, ψ, hψ, houter⟩

end OTSelector.Reconstruction
