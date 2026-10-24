import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedDecomposition
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedJoint
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMacroscopic
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitProjectedExtension

/-!
# Exact original retained/lost decomposition over prescribed full weak limits

The same completed global allocation experiment supplies an actual joint
extension with the closed full = retained + lost identity at every weak stage.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance actualMaskedDecompSceneStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance actualMaskedDecompSceneConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance actualMaskedDecompSceneConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance actualMaskedDecompSceneConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance actualMaskedDecompScenePlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)

/-- Actual finite source/edge restriction supplies the closed exact split
on both weak stages while the prescribed full original laws stay fixed. -/
theorem exists_iterated_actualAllocationRootedMaskedScene_decomposition_over_given_full_limits
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (ap am : ∀ (_ℓ n : ℕ), Ωn n → M → Fin (m n + 1) → ℝ)
    (hp : ∀ ℓ n j, Measurable (fun z : Ωn n × M ↦ ap ℓ n z.1 z.2 j))
    (hm : ∀ ℓ n j, Measurable (fun z : Ωn n × M ↦ am ℓ n z.1 z.2 j))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → M) (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (hfp : ∀ ℓ n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (ap ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (am ℓ n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (scale : ℕ → ℝ)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hDK : ∀ n z, z ∈ D n → physicalSceneMacroscopicRoot (scale n) z ∈ K)
    (Qfull : ℕ → ProbabilityMeasure MacroScene) (Rfull : ProbabilityMeasure MacroScene)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, StrictMono (φ ℓ))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ actualAllocationRootedMacroscopicSceneLaw base
      (P (φ ℓ n)) μ (ap ℓ (φ ℓ n)) (am ℓ (φ ℓ n)) (hp ℓ (φ ℓ n)) (hm ℓ (φ ℓ n))
      (Y (φ ℓ n)) (hY (φ ℓ n)) (H (φ ℓ n)) (hH (φ ℓ n))
      (coord (φ ℓ n)) (hcoord (φ ℓ n)) u hu (scale (φ ℓ n)) (D (φ ℓ n)) (hD (φ ℓ n)))
      atTop (𝓝 (Qfull ℓ)))
    (houter : Tendsto (fun ℓ ↦ Qfull (ψ ℓ)) atTop (𝓝 Rfull)) :
    let laws := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base (P n) μ
      (ap ℓ n) (am ℓ n) (hp ℓ n) (hm ℓ n) (Y n) (hY n)
      (H n) (hH n) E hE (coord n) (hcoord n) u hu (scale n) (D n) (hD n)
    ∃ Q : ℕ → ProbabilityMeasure (MacroScene × (PairScene × PairScene)),
    ∃ θ : ℕ → ℕ → ℕ,
      (∀ ℓ, StrictMono (θ ℓ) ∧ StrictMono (fun n ↦ φ ℓ (θ ℓ n)) ∧
        Tendsto (fun n ↦ laws ℓ (φ ℓ (θ ℓ n))) atTop (𝓝 (Q ℓ)) ∧
        (Q ℓ).map (f := Prod.fst) measurable_fst.aemeasurable = Qfull ℓ ∧
        ∀ᵐ s ∂(Q ℓ : Measure (MacroScene × (PairScene × PairScene))),
          s ∈ physicalSceneMaskedDecompositionCarrier base) ∧
      ∃ R : ProbabilityMeasure (MacroScene × (PairScene × PairScene)), ∃ η : ℕ → ℕ,
        StrictMono η ∧ StrictMono (fun ℓ ↦ ψ (η ℓ)) ∧
        Tendsto (fun ℓ ↦ Q (ψ (η ℓ))) atTop (𝓝 R) ∧
        R.map (f := Prod.fst) measurable_fst.aemeasurable = Rfull ∧
        ∀ᵐ s ∂(R : Measure (MacroScene × (PairScene × PairScene))),
          s ∈ physicalSceneMaskedDecompositionCarrier base := by
  dsimp only
  obtain ⟨Q, θ, hQ, R, η, hη, hψη, hR, hRmap⟩ :=
    exists_iterated_actualAllocationRootedMaskedScene_over_given_full_limits base m P μ
      ap am hp hm Y hY p hfp hfm H hH E hE coord hcoord u hu scale D hD K hK hDK
      Qfull Rfull φ hφ ψ hψ hinner houter
  let laws := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base (P n) μ
    (ap ℓ n) (am ℓ n) (hp ℓ n) (hm ℓ n) (Y n) (hY n)
    (H n) (hH n) E hE (coord n) (hcoord n) u hu (scale n) (D n) (hD n)
  have hfinite (ℓ n : ℕ) : ∀ᵐ s ∂(laws ℓ n : Measure (MacroScene × (PairScene × PairScene))),
      s ∈ physicalSceneMaskedDecompositionCarrier base :=
    ae_physicalSceneRootedMaskedMacroscopicSceneLaw_decomposition base (P n)
      (physicalSceneGlobalAllocationFamily μ (ap ℓ n) (Y n))
      (physicalSceneGlobalAllocationFamily μ (am ℓ n) (Y n))
      (measurable_physicalSceneGlobalAllocationFamily μ (ap ℓ n) (hp ℓ n) (Y n) (hY n))
      (measurable_physicalSceneGlobalAllocationFamily μ (am ℓ n) (hm ℓ n) (Y n) (hY n))
      (H n) (hH n) E hE (coord n) (hcoord n) u hu (scale n) (Y n) (hY n) (D n) (hD n)
  have hd := ae_physicalSceneMaskedDecomposition_of_iterated_weak base laws Q R
    (fun ℓ n ↦ φ ℓ (θ ℓ n)) (fun ℓ ↦ ψ (η ℓ))
    (fun ℓ ↦ (hQ ℓ).2.2.1) hR hfinite
  exact ⟨Q, θ, fun ℓ ↦ ⟨(hQ ℓ).1, (hQ ℓ).2.1, (hQ ℓ).2.2.1,
    (hQ ℓ).2.2.2, hd.1 ℓ⟩, R, η, hη, hψη, hR, hRmap, hd.2⟩

end OTSelector.Reconstruction
