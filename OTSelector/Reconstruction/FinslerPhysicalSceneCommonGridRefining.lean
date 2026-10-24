import OTSelector.Topology.CommonIteratedRefiningSubsequence
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutMacroscopicIterated
import OTSelector.Reconstruction.FinslerPhysicalSceneRootGrid

/-!
# One original two-stage extraction for every literal root box

Original feasibility supplies coordinate tightness, and countable compactness
selects common sample and tilt subsequences without altering any physical law.
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
local instance refiningGridMacroscopicPhysicalSceneStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance refiningGridMacroscopicPhysicalSceneConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance refiningGridMacroscopicPhysicalSceneConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance refiningGridMacroscopicPhysicalSceneConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance refiningGridMacroscopicPhysicalScenePlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

/-- Every integer root box keeps its original probability law while sharing
both subsequences. Scale normalization and compact root carriers are internal. -/
theorem exists_common_refining_grid_actualAllocationRootedMacroscopicSceneLaw
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
    (hscalePos : ∀ n, 0 < scale n)
    (hpower : ∀ n, scale n ^ Fintype.card ι = (m n : ℝ) + 1)
    (φ₀ : ℕ → ℕ → ℕ) (ψ₀ : ℕ → ℕ) :
    let hD := fun ν n ↦ (volume_physicalSceneRootGridDomain (scale n) (hscalePos n) ν).trans (congrArg ENNReal.ofReal (hpower n))
    let laws := fun ν ℓ n ↦ actualAllocationRootedMacroscopicSceneLaw base (Penv n) μ
      (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n)
      (Y n) (hY n) (H n) (hH n) (coord n) (hcoord n) u hu (scale n)
      (physicalSceneRootGridDomain (scale n) ν) (hD ν n)
    ∃ Q : (ι → ℤ) → ℕ → ProbabilityMeasure ((ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
    ∃ φ : ℕ → ℕ → ℕ,
      (∀ ℓ, StrictMono (φ ℓ)) ∧
      (∀ ν ℓ, Tendsto (fun n ↦ laws ν ℓ (φ₀ ℓ (φ ℓ n))) atTop (𝓝 (Q ν ℓ))) ∧
      ∃ R : (ι → ℤ) → ProbabilityMeasure ((ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ ν, Tendsto (fun ℓ ↦ Q ν (ψ₀ (ψ ℓ))) atTop (𝓝 (R ν)) := by
  intro hD laws
  apply exists_common_iterated_refining_probabilityMeasure_subseq_of_isTight laws ?_ φ₀ ψ₀
  intro ν
  exact isTightMeasureSet_all_tilts_actualAllocationRootedMacroscopicSceneLaw
    base m Penv μ aplus aminus hplus hminus Y hY p hfp hfm H hH coord hcoord u hu scale
    (fun n ↦ physicalSceneRootGridDomain (scale n) ν) (hD ν)
    (BoxIntegral.Box.Icc (BoxIntegral.unitPartition.box 1 ν))
    (BoxIntegral.unitPartition.box 1 ν).isCompact_Icc
    (fun n z hz ↦ by
      have heq : physicalSceneMacroscopicRoot (scale n) z = (scale n)⁻¹ • z := by
        ext i
        simp only [physicalSceneMacroscopicRoot, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
      rw [heq]
      exact physicalSceneRootGridDomain_macro_mem_compact (scale n) ν hz)

end OTSelector.Reconstruction
