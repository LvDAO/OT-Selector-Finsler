import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedJoint
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutMacroscopicMarginals

/-!
# Exact retained/lost decomposition of the same original physical scene

Vague addition is continuous. The full original pair equals the retained pair
plus its discarded pair as a closed relation, which persists under both weak
stages without changing the prescribed full original scene law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

section Addition
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X]

/-- Sum of two actual locally finite plans on the same physical edge space. -/
def physicalSceneLocalFiniteSum (p : LocalFiniteMeasure X × LocalFiniteMeasure X) :
    LocalFiniteMeasure X := by
  have : IsFiniteMeasureOnCompacts ((p.1 : Measure X) + (p.2 : Measure X)) := by
    constructor
    intro K hK
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩
  exact ⟨(p.1 : Measure X) + (p.2 : Measure X), inferInstance⟩

@[simp]
theorem coe_physicalSceneLocalFiniteSum (p : LocalFiniteMeasure X × LocalFiniteMeasure X) :
    (physicalSceneLocalFiniteSum p : Measure X) = (p.1 : Measure X) + (p.2 : Measure X) := rfl

/-- Adding actual plans adds every compact test integral exactly. -/
theorem testIntegral_physicalSceneLocalFiniteSum
    (p : LocalFiniteMeasure X × LocalFiniteMeasure X) (f : C_c(X, ℝ)) :
    LocalFiniteMeasure.testIntegral (physicalSceneLocalFiniteSum p) f =
      LocalFiniteMeasure.testIntegral p.1 f + LocalFiniteMeasure.testIntegral p.2 f := by
  unfold LocalFiniteMeasure.testIntegral
  exact integral_add_measure f.integrable f.integrable

/-- Addition of the actual locally finite measures is continuous in the vague topology. -/
theorem continuous_physicalSceneLocalFiniteSum :
    Continuous (physicalSceneLocalFiniteSum : LocalFiniteMeasure X × LocalFiniteMeasure X → _) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  change Continuous (fun p ↦ LocalFiniteMeasure.testIntegral (physicalSceneLocalFiniteSum p) f)
  simp only [testIntegral_physicalSceneLocalFiniteSum]
  exact ((LocalFiniteMeasure.continuous_testIntegral f).comp continuous_fst).add
    ((LocalFiniteMeasure.continuous_testIntegral f).comp continuous_snd)
end Addition

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance maskedDecompositionStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance maskedDecompositionConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance maskedDecompositionConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance maskedDecompositionConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance maskedDecompositionPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Componentwise sum of the original plus/minus retained and lost plans. -/
def physicalScenePairSum (p : PairScene × PairScene) : PairScene :=
  (physicalSceneLocalFiniteSum (p.1.1, p.2.1),
    physicalSceneLocalFiniteSum (p.1.2, p.2.2))

/-- Both actual plan sums depend continuously on their vague measures. -/
theorem continuous_physicalScenePairSum : Continuous (physicalScenePairSum (ι := ι)) :=
  (continuous_physicalSceneLocalFiniteSum.comp
    (continuous_fst.fst.prodMk continuous_snd.fst)).prodMk
      (continuous_physicalSceneLocalFiniteSum.comp
        (continuous_fst.snd.prodMk continuous_snd.snd))

/-- Exact full = retained + lost is a closed property of the original joint scene. -/
def physicalSceneMaskedDecompositionCarrier : Set JointScene :=
  {s | s.1.2.1 = physicalScenePairSum s.2}

/-- Vague convergence preserves the actual decomposition, without compact support restrictions. -/
theorem isClosed_physicalSceneMaskedDecompositionCarrier :
    IsClosed (physicalSceneMaskedDecompositionCarrier base) :=
  isClosed_eq continuous_fst.snd.fst
    (continuous_physicalScenePairSum.comp continuous_snd)

/-- The same original plan, source-restricted after the edge split, decomposes exactly. -/
theorem physicalSceneRootedPlan_restricted_mask_split
    (Γ : Measure (M × M)) (H : Set M) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ) :
    physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z =
      physicalSceneRootedPlan ((Γ.restrict E).restrict (H ×ˢ univ)) coord u N z +
      physicalSceneRootedPlan ((Γ.restrict Eᶜ).restrict (H ×ˢ univ)) coord u N z := by
  have hsplit := congrArg (fun m : Measure (M × M) ↦ m.restrict (H ×ˢ univ))
    (Measure.restrict_add_restrict_compl (μ := Γ) hE)
  rw [Measure.restrict_add] at hsplit
  rw [← physicalSceneRootedPlan_add _ _ coord hcoord u hu N z, hsplit]

/-- Every realization decomposes the actual original global plans, keeping the
same environment, actual columns, source cell, macro tag and original target cloud. -/
theorem physicalSceneRootedMaskedMacroscopicObservation_mem_decomposition {n : ℕ}
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (H : Set M) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (v : Ω × (ι → ℝ)) :
    physicalSceneRootedMaskedMacroscopicObservation base Γp Γm H E coord u N scale Y v ∈
      physicalSceneMaskedDecompositionCarrier base := by
  apply Prod.ext <;> apply Subtype.ext
  · exact physicalSceneRootedPlan_restricted_mask_split (Γp v.1) H E hE coord hcoord u hu N v.2
  · exact physicalSceneRootedPlan_restricted_mask_split (Γm v.1) H E hE coord hcoord u hu N v.2

/-- The unchanged original probability experiment has the exact decomposition almost surely. -/
theorem ae_physicalSceneRootedMaskedMacroscopicSceneLaw_decomposition {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ∀ᵐ s ∂(physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hp hm H hH E hE
      coord hcoord u hu scale Y hY D hD : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base := by
  change ∀ᵐ s ∂((Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedMaskedMacroscopicObservation base Γp Γm H E coord u ((n : ℝ) + 1) scale Y)), _
  apply (ae_map_iff
    (measurable_physicalSceneRootedMaskedMacroscopicObservation base Γp Γm hp hm H hH E hE
      coord hcoord u hu ((n : ℝ) + 1) scale Y hY).aemeasurable
    (isClosed_physicalSceneMaskedDecompositionCarrier base).measurableSet).mpr
  exact ae_of_all _ fun v ↦ physicalSceneRootedMaskedMacroscopicObservation_mem_decomposition base
    Γp Γm H E hE coord hcoord u hu ((n : ℝ) + 1) scale Y v

/-- The decomposition persists through each sample limit and then the tilt limit.
The indices remain separate throughout. -/
theorem ae_physicalSceneMaskedDecomposition_of_iterated_weak
    (P : ℕ → ℕ → ProbabilityMeasure JointScene) (Q : ℕ → ProbabilityMeasure JointScene)
    (R : ProbabilityMeasure JointScene) (φ : ℕ → ℕ → ℕ) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ P ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (hP : ∀ ℓ n, ∀ᵐ s ∂(P ℓ n : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base) :
    (∀ ℓ, ∀ᵐ s ∂(Q ℓ : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base) ∧
    ∀ᵐ s ∂(R : Measure JointScene), s ∈ physicalSceneMaskedDecompositionCarrier base := by
  have hQ (ℓ : ℕ) := ae_closed_set_of_physicalScene_weak_tendsto (Q ℓ)
    (fun n ↦ P ℓ (φ ℓ n)) (hinner ℓ) _
    (isClosed_physicalSceneMaskedDecompositionCarrier base) (fun n ↦ hP ℓ (φ ℓ n))
  exact ⟨hQ, ae_closed_set_of_physicalScene_weak_tendsto R (fun ℓ ↦ Q (ψ ℓ)) houter _
    (isClosed_physicalSceneMaskedDecompositionCarrier base) (fun ℓ ↦ hQ (ψ ℓ))⟩

end OTSelector.Reconstruction
