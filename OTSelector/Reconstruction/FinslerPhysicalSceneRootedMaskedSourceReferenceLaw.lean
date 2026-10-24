import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedJoint
import OTSelector.MeasureTheory.IteratedWeakSourceDomination

/-!
# The same masked scene law preserves deterministic source references

An environment-wise source bound holding for every root transfers through the
literal joint masked macroscopic observation. The simultaneous all-open-source
carrier is closed, supplies its own measurability, and survives the prescribed
inner sample limit followed by the outer tilt limit. All targets are retained in
each source test. No source absolute continuity or tail conclusion is asserted.
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
local instance maskedSourceReferenceLawStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) :=
  inferInstance
local instance maskedSourceReferenceLawConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology _
local instance maskedSourceReferenceLawConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance maskedSourceReferenceLawConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance maskedSourceReferenceLawPlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local notation "Endpoint" => (ι → ℝ) × ℝ
local notation "Edge" => Endpoint × Endpoint
local notation "PairScene" => CavityLocalScene Endpoint Endpoint
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Both retained original plans satisfy one deterministic localized source
reference, in their unchanged joint scene. -/
def physicalSceneMaskedRetainedSourceReferenceCarrier
    (U : Set Endpoint) (ref : Measure Endpoint) (error : ℝ≥0∞) : Set JointScene :=
  {s | sourceOpenDominationDefectOn (s.2.1.1 : Measure Edge) U ref error ∧
    sourceOpenDominationDefectOn (s.2.1.2 : Measure Edge) U ref error}

/-- Simultaneous domination over every open source test is a closed carrier
on the same original full/retained/lost macroscopic scene. -/
theorem isClosed_physicalSceneMaskedRetainedSourceReferenceCarrier
    (U : Set Endpoint) (hU : IsOpen U) (ref : Measure Endpoint) (error : ℝ≥0∞) :
    IsClosed (physicalSceneMaskedRetainedSourceReferenceCarrier base U ref error) :=
  ((isClosed_sourceOpenDominationDefectOn U hU ref error).preimage
    continuous_snd.fst.fst).inter
    ((isClosed_sourceOpenDominationDefectOn U hU ref error).preimage
      continuous_snd.fst.snd)

omit base in
/-- The arithmetic mean preserves the same deterministic reference and the
same additive defect when both original plans satisfy that bound. -/
theorem sourceOpenDominationDefectOn_cavityAverage
    (plans : PairScene) (U : Set Endpoint) (ref : Measure Endpoint) (error : ℝ≥0∞)
    (hp : sourceOpenDominationDefectOn (plans.1 : Measure Edge) U ref error)
    (hm : sourceOpenDominationDefectOn (plans.2 : Measure Edge) U ref error) :
    sourceOpenDominationDefectOn (LocalFiniteMeasure.cavityAverage plans : Measure Edge)
      U ref error := by
  intro O hO
  rw [LocalFiniteMeasure.coe_cavityAverage, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ((ref O + error) + (ref O + error)) :=
      mul_le_mul_right (add_le_add (hp O hO) (hm O hO)) _
    _ = ref O + error := by
      rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- An AE environment bound valid at every root transfers through the SAME
joint observation. Its carrier measurability is proved internally from closedness. -/
theorem ae_physicalSceneRootedMaskedMacroscopicSceneLaw_sourceReference {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    (U : Set Endpoint) (hU : IsOpen U) (ref : Measure Endpoint) (error : ℝ≥0∞)
    (hbound : ∀ᵐ w ∂Penv, ∀ root : ι → ℝ,
      sourceOpenDominationDefectOn
        (physicalSceneRootedPlan (((Γp w).restrict E).restrict (H ×ˢ univ))
          coord u ((n : ℝ) + 1) root) U ref error ∧
      sourceOpenDominationDefectOn
        (physicalSceneRootedPlan (((Γm w).restrict E).restrict (H ×ˢ univ))
          coord u ((n : ℝ) + 1) root) U ref error) :
    ∀ᵐ s ∂(physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hp hm H hH E hE
      coord hcoord u hu scale Y hY D hD : Measure JointScene),
      s ∈ physicalSceneMaskedRetainedSourceReferenceCarrier base U ref error := by
  change ∀ᵐ s ∂((Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedMaskedMacroscopicObservation base Γp Γm H E coord u
      ((n : ℝ) + 1) scale Y)), _
  apply (ae_map_iff
    (measurable_physicalSceneRootedMaskedMacroscopicObservation base Γp Γm hp hm H hH E hE
      coord hcoord u hu ((n : ℝ) + 1) scale Y hY).aemeasurable
    (isClosed_physicalSceneMaskedRetainedSourceReferenceCarrier base U hU ref error).measurableSet).mpr
  have hv := (Measure.quasiMeasurePreserving_fst
    (μ := Penv) (ν := cavityRootMeasure volume D ((n : ℝ) + 1))).ae hbound
  filter_upwards [hv] with v hv
  exact hv v.2

/-- The same retained plans and their arithmetic mean preserve one fixed
localized reference through the inner sample and outer tilt limits. -/
theorem ae_maskedRetainedSourceReference_of_iterated_weak
    (laws : ℕ → ℕ → ProbabilityMeasure JointScene) (Q : ℕ → ProbabilityMeasure JointScene)
    (R : ProbabilityMeasure JointScene)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (U : Set Endpoint) (hU : IsOpen U) (ref : Measure Endpoint) (error : ℝ≥0∞)
    (hbound : ∀ ℓ, ∀ᶠ n in atTop, ∀ᵐ s ∂(laws ℓ n : Measure JointScene),
      s ∈ physicalSceneMaskedRetainedSourceReferenceCarrier base U ref error) :
    ∀ᵐ s ∂(R : Measure JointScene),
      sourceOpenDominationDefectOn (s.2.1.1 : Measure Edge) U ref error ∧
      sourceOpenDominationDefectOn (s.2.1.2 : Measure Edge) U ref error ∧
      sourceOpenDominationDefectOn
        (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge) U ref error := by
  have hp : ∀ᵐ s ∂(R : Measure JointScene),
      sourceOpenDominationDefectOn (s.2.1.1 : Measure Edge) U ref error :=
    ae_sourceOpenDominationDefectOn_of_iterated_weak laws Q R φ hφ ψ hinner houter
      (fun s ↦ s.2.1.1) continuous_snd.fst.fst U hU ref error (fun ℓ ↦ by
        filter_upwards [hbound ℓ] with n hn
        exact hn.mono fun s hs ↦ hs.1)
  have hm : ∀ᵐ s ∂(R : Measure JointScene),
      sourceOpenDominationDefectOn (s.2.1.2 : Measure Edge) U ref error :=
    ae_sourceOpenDominationDefectOn_of_iterated_weak laws Q R φ hφ ψ hinner houter
      (fun s ↦ s.2.1.2) continuous_snd.fst.snd U hU ref error (fun ℓ ↦ by
        filter_upwards [hbound ℓ] with n hn
        exact hn.mono fun s hs ↦ hs.2)
  filter_upwards [hp, hm] with s hsp hsm
  exact ⟨hsp, hsm, sourceOpenDominationDefectOn_cavityAverage s.2.1 U ref error hsp hsm⟩

/-- The original two-index experiment supplies its own finite-law carrier
from AE environments and all roots, then passes it through its own weak limits.
No replacement law, test-wise measurability input, or source-tail premise occurs. -/
theorem ae_sourceReference_of_iterated_physicalSceneRootedMaskedMacroscopicSceneLaw
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (Penv : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (Penv n)]
    (Γp Γm : ∀ (_ℓ n : ℕ), Ωn n → Measure (M × M))
    [∀ ℓ n w, IsFiniteMeasure (Γp ℓ n w)]
    [∀ ℓ n w, IsFiniteMeasure (Γm ℓ n w)]
    (hp : ∀ ℓ n, Measurable (Γp ℓ n)) (hm : ∀ ℓ n, Measurable (Γm ℓ n))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (scale : ℕ → ℝ)
    (Y : ∀ n, Ωn n → Fin (m n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (rootDomain : ℕ → Set (ι → ℝ))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (U : Set Endpoint) (hU : IsOpen U) (ref : Measure Endpoint) (error : ℝ≥0∞)
    (hbound : ∀ ℓ, ∀ᶠ n in atTop, ∀ᵐ w ∂Penv n, ∀ root : ι → ℝ,
      sourceOpenDominationDefectOn
        (physicalSceneRootedPlan (((Γp ℓ n w).restrict E).restrict (H n ×ˢ univ))
          (coord n) u ((m n : ℝ) + 1) root) U ref error ∧
      sourceOpenDominationDefectOn
        (physicalSceneRootedPlan (((Γm ℓ n w).restrict E).restrict (H n ×ˢ univ))
          (coord n) u ((m n : ℝ) + 1) root) U ref error) :
    let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
      physicalSceneRootedMaskedMacroscopicSceneLaw base (Penv n) (Γp ℓ n) (Γm ℓ n)
        (hp ℓ n) (hm ℓ n) (H n) (hH n) E hE (coord n) (hcoord n) u hu (scale n)
        (Y n) (hY n) (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (R : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) → ∀ ψ : ℕ → ℕ,
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R) →
      ∀ᵐ s ∂(R : Measure JointScene),
        sourceOpenDominationDefectOn (s.2.1.1 : Measure Edge) U ref error ∧
        sourceOpenDominationDefectOn (s.2.1.2 : Measure Edge) U ref error ∧
        sourceOpenDominationDefectOn
          (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge) U ref error := by
  intro laws Q R φ hφ ψ hinner houter
  apply ae_maskedRetainedSourceReference_of_iterated_weak base laws Q R φ hφ ψ
    hinner houter U hU ref error
  intro ℓ
  filter_upwards [hbound ℓ] with n hn
  exact ae_physicalSceneRootedMaskedMacroscopicSceneLaw_sourceReference base (Penv n)
    (Γp ℓ n) (Γm ℓ n) (hp ℓ n) (hm ℓ n) (H n) (hH n) E hE
    (coord n) (hcoord n) u hu (scale n) (Y n) (hY n) (rootDomain n) (hrootDomain n)
    U hU ref error hn

end OTSelector.Reconstruction
