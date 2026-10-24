import OTSelector.Reconstruction.OriginalIIDMaskedMacroConditionalInput

/-!
# Actual conditional input in any fixed translated original macro frame

A frame c0 uses exactly the original coordinate s_n*(phi-c0). Its original macro tag y
corresponds to the original local center c0+y. Translation transports the entire existing
almost-everywhere actual kernel convergence/profile at once, retaining the original unit-cube
root probability and its unnormalized restriction to centers in K.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal BigOperators CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Probability

/-- Translate a whole almost-everywhere statement on the original core to a frame's original
root restriction. The root measure is only assumed dominated by original Lebesgue measure. -/
theorem ae_translation_preimage_restrict_of_ae_volume
    (q : ℕ) (ρ : Measure (Fin q → ℝ)) (hρ : ρ ≤ volume) (c0 : Fin q → ℝ)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) {P : (Fin q → ℝ) → Prop}
    (hP : ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K, P c) :
    ∀ᵐ y ∂ρ.restrict ((fun y ↦ c0 + y) ⁻¹' K), P (c0 + y) := by
  have hs : Measurable (fun y : Fin q → ℝ ↦ c0 + y) := measurable_const.add measurable_id
  have hmaple : ρ.map (fun y ↦ c0 + y) ≤ (volume : Measure (Fin q → ℝ)) := by
    calc
      _ ≤ (volume : Measure (Fin q → ℝ)).map (fun y ↦ c0 + y) := Measure.map_mono hρ hs
      _ = volume := (measurePreserving_add_left (volume : Measure (Fin q → ℝ)) c0).map_eq
  have hp := ae_mono (Measure.restrict_mono_measure hmaple K) hP
  rw [Measure.restrict_map hs hK] at hp
  exact ae_of_ae_map hs.aemeasurable hp

end OTSelector.Probability

namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000

variable {M : Type*} [MeasurableSpace M] {q : ℕ}
local instance iidTranslatedMacroPointStandardBorel : StandardBorelSpace ((Fin q → ℝ) × ℝ) :=
  inferInstance
local instance iidTranslatedMacroConfigurationTopology (base : (Fin q → ℝ) × ℝ) :
    TopologicalSpace (LocalConfiguration base) := LocalConfiguration.vagueTopology base
local instance iidTranslatedMacroConfigurationBorel (base : (Fin q → ℝ) × ℝ) :
    BorelSpace (LocalConfiguration base) := LocalConfiguration.vagueBorelSpace
local instance iidTranslatedMacroConfigurationPolish (base : (Fin q → ℝ) × ℝ) :
    PolishSpace (LocalConfiguration base) := LocalConfiguration.vaguePolishSpace
local instance iidTranslatedMacroInputPolish :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidTranslatedMacroPlanPolish :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidTranslatedMacroInputNonempty : Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) :=
  ⟨⟨0, inferInstance⟩⟩

set_option quotPrecheck false
local notation "V" => (Fin q → ℝ)
local notation "X" => V × ℝ
local notation "T" => LocalFiniteMeasure X × LocalFiniteMeasure X

/-- The concrete conditional-input conclusion for one original translated frame. The experiment
inside this proposition is the existing original macro law with coordinates s_n*(phi-c0),
unchanged clocks and optimizer. The retained tag y has original center c0+y. The root law
is the same unit-cube Haar probability, restricted without normalization to c0+y in K. -/
def OriginalIIDTranslatedMacroConditionalInput
    (base : X) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < q) {H : Set M} (hH : MeasurableSet H) {φ : M → V} (hφ : Measurable φ)
    {u : M → ℝ} (hu : Measurable u)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (c0 : V) (K : Set V) (Γ : Kernel V T) (profile : V → Measure T → Prop) : Prop :=
  let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
    (physicalScene_centered_unitCube_mass (Fin q))
  let A := (fun y ↦ c0 + y) ⁻¹' K
  ∀ m : ℕ → ℕ, StrictMono m →
    ∀ L : ProbabilityMeasure (OriginalIIDMaskedMacroCarrier base × OriginalIIDMaskedMacroCarrier base),
      Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν (by simpa using hq)
        (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
        (fun x ↦ physicalSceneCanonicalHaarScale q (m n) • (φ x - c0))
        ((hφ.sub measurable_const).const_smul (physicalSceneCanonicalHaarScale q (m n))) u hu)
        atTop (𝓝 L) →
      let Qinput := L.map (measurable_originalIIDMaskedMacroTaggedInputProjection base).aemeasurable
      (Qinput : Measure (V × T)).fst = (η : Measure V) ∧
        (Qinput : Measure (V × T)).restrict (A ×ˢ univ) =
          (η : Measure V).restrict A ⊗ₘ
            Γ.comap (fun y ↦ c0 + y) (measurable_const.add measurable_id) ∧
        ∀ᵐ y ∂(η : Measure V).restrict A,
          (Qinput : Measure (V × T)).condKernel y = Γ (c0 + y) ∧
          profile (c0 + y) ((Qinput : Measure (V × T)).condKernel y)

/-- Reuse actual whole-sequence input convergence to identify the SAME macro weak law in any
fixed translated frame. The generic profile is transported as one statement; it need not be
measurable and is never split into an uncountable family of almost-everywhere assertions. -/
theorem originalIIDTranslatedMacroConditionalInput_of_actual_kernel_limit
    (base : X) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < q) {H : Set M} (hH : MeasurableSet H) {φ : M → V} (hφ : Measurable φ)
    {u : M → ℝ} (hu : Measurable u)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (c0 : V) (K : Set V) (hK : MeasurableSet K)
    (Γ : Kernel V T) [IsMarkovKernel Γ] (profile : V → Measure T → Prop)
    (PN : ℕ → V → ProbabilityMeasure T)
    (hPN : ∀ n c, (PN n c : Measure T) =
      originalIidMaskedLocalInputPairMeasure μ ν (n + 1) base H H
        (fun x ↦ (physicalSceneCanonicalHaarScale q n • (φ x - c), u x))
        (fun x ↦ (physicalSceneCanonicalHaarScale q n • (φ x - c), u x)))
    (hlim : ∀ᵐ c ∂(volume : Measure V).restrict K,
      Tendsto (β := ProbabilityMeasure T) (fun n ↦ PN n c) atTop
        (𝓝 (⟨Γ c, inferInstance⟩ : ProbabilityMeasure T)) ∧ profile c (Γ c)) :
    OriginalIIDTranslatedMacroConditionalInput base μ ν hq hH hφ hu cost hcost k c0 K Γ profile := by
  let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
    (physicalScene_centered_unitCube_mass (Fin q))
  let A := (fun y : V ↦ c0 + y) ⁻¹' K
  have hs : Measurable (fun y : V ↦ c0 + y) := measurable_const.add measurable_id
  have hA : MeasurableSet A := hK.preimage hs
  have hlimShift := ae_translation_preimage_restrict_of_ae_volume q
    (η : Measure V) Measure.restrict_le_self c0 hK hlim
  have hφShift : Measurable (fun x : M ↦ φ x - c0) := hφ.sub measurable_const
  let Ktag := Γ.comap (fun y ↦ c0 + y) hs
  let Kn : ℕ → Kernel V T := fun n ↦ originalIIDMaskedMacroCenteredInputKernel base μ ν n H
    (fun x ↦ φ x - c0) u (physicalSceneCanonicalHaarScale q n)
  let _instKn : ∀ n, IsMarkovKernel (Kn n) := fun n ↦
    isMarkovKernel_originalIIDMaskedMacroCenteredInputKernel base μ ν n hH
      hφShift hu (physicalSceneCanonicalHaarScale q n)
  have hKn (n : ℕ) (y : V) : Kn n y = (PN n (c0 + y) : Measure T) := by
    rw [hPN n (c0 + y)]
    simpa only [sub_sub] using originalIIDMaskedMacroCenteredInputKernel_apply base μ ν n hH
      hφShift hu (physicalSceneCanonicalHaarScale q n) y
  dsimp only [OriginalIIDTranslatedMacroConditionalInput]
  intro m hm L hw
  let Qinput := L.map (measurable_originalIIDMaskedMacroTaggedInputProjection base).aemeasurable
  let Rn : ℕ → ProbabilityMeasure (V × T) := fun n ↦
    (originalIIDMaskedBipartiteMacroLaw base μ ν (by simpa using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (fun x ↦ physicalSceneCanonicalHaarScale q (m n) • (φ x - c0))
      ((hφ.sub measurable_const).const_smul (physicalSceneCanonicalHaarScale q (m n))) u hu).map
      (measurable_originalIIDMaskedMacroTaggedInputProjection base).aemeasurable
  have hwinput : Tendsto Rn atTop (𝓝 Qinput) :=
    ((ProbabilityMeasure.continuous_map
      (continuous_originalIIDMaskedMacroTaggedInputProjection base)).tendsto L).comp hw
  have hfinite (n : ℕ) : (Rn n : Measure (V × T)) = (η : Measure V) ⊗ₘ Kn (m n) :=
    originalIIDMaskedMacroLaw_taggedInput_eq_compProd base μ ν hq (cost (m n)) (hcost (m n))
      (k (m n)) (m n) hH hφShift hu
  have hkernel : ∀ᵐ y ∂(η : Measure V).restrict A,
      Tendsto (β := ProbabilityMeasure T)
        (fun n ↦ (⟨Kn (m n) y, inferInstance⟩ : ProbabilityMeasure T)) atTop
        (𝓝 (⟨Ktag y, inferInstance⟩ : ProbabilityMeasure T)) := by
    filter_upwards [hlimShift] with y hy
    have hvalue n : (⟨Kn (m n) y, inferInstance⟩ : ProbabilityMeasure T) = PN (m n) (c0 + y) :=
      Subtype.ext (hKn (m n) y)
    have htarget : (⟨Ktag y, inferInstance⟩ : ProbabilityMeasure T) =
        (⟨Γ (c0 + y), inferInstance⟩ : ProbabilityMeasure T) := rfl
    simpa only [Function.comp_def, hvalue, htarget] using hy.1.comp hm.tendsto_atTop
  have hrestrict := restrict_joint_weak_limit_eq_compProd_of_ae_kernel_weak η Rn Qinput
    hwinput (fun n ↦ Kn (m n)) Ktag hfinite A hA hkernel
  have hfirst (n : ℕ) : (Rn n).map measurable_fst.aemeasurable = η := by
    apply ProbabilityMeasure.toMeasure_injective
    change (Rn n : Measure (V × T)).fst = (η : Measure V)
    rw [hfinite n, Measure.fst_compProd]
  have hrootweak : Tendsto (fun n ↦ (Rn n).map measurable_fst.aemeasurable) atTop
      (𝓝 (Qinput.map measurable_fst.aemeasurable)) :=
    ((ProbabilityMeasure.continuous_map
      (show Continuous (Prod.fst : V × T → V) from continuous_fst)).tendsto Qinput).comp hwinput
  have hconstant : (fun n ↦ (Rn n).map measurable_fst.aemeasurable) =
      (fun _ : ℕ ↦ η) := funext hfirst
  rw [hconstant] at hrootweak
  have hrootEq : Qinput.map measurable_fst.aemeasurable = η :=
    tendsto_nhds_unique hrootweak tendsto_const_nhds
  have hmarg : (Qinput : Measure (V × T)).fst = (η : Measure V) :=
    congrArg (fun p : ProbabilityMeasure V ↦ (p : Measure V)) hrootEq
  have hcond := ae_condKernel_eq_of_restrict_eq_compProd
    (Qinput : Measure (V × T)) (η : Measure V) hmarg Ktag hA hrestrict
  refine ⟨hmarg, hrestrict, ?_⟩
  filter_upwards [hcond, hlimShift] with y hyy hy
  have heq : (Qinput : Measure (V × T)).condKernel y = Γ (c0 + y) := hyy
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hy.2

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
open Metric Module Manifold OTSelector.Geometry
open scoped ContDiff NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 20000

local instance iidTranslatedMacroCorePointStandardBorel (q : ℕ) :
    StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidTranslatedMacroCoreConfigurationTopology (q : ℕ)
    (base : (Fin q → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueTopology base
local instance iidTranslatedMacroCoreConfigurationBorel (q : ℕ)
    (base : (Fin q → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueBorelSpace
local instance iidTranslatedMacroCoreConfigurationPolish (q : ℕ)
    (base : (Fin q → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) :=
  LocalConfiguration.vaguePolishSpace
local instance iidTranslatedMacroCoreInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidTranslatedMacroCorePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidTranslatedMacroCoreInputNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := ⟨⟨0, inferInstance⟩⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- One unchanged actual D input-limit kernel identifies every fixed translated original
macro frame. No new limit kernel is selected for different c0. Its conditional profile at
tag y uses the original center c0+y and the original intensity theta(c0+y). Covering an
arbitrary K still requires a countable translated-frame cover and common scene subsequence. -/
theorem PopulationLocalPressureCore.original_translated_macro_conditional_input
    [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hdim : 2 ≤ Module.finrank ℝ E) (i : Fin D.haar.continuous.count)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := Module.finrank ℝ S.covector.ker
    let V := Fin q → ℝ
    let X := V × ℝ
    let T := LocalFiniteMeasure X × LocalFiniteMeasure X
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let φ := fun x ↦ e (R (a x))
    let K := e '' (R '' C.roots)
    let mask := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let θ := fun c ↦ originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c)
    let μS := fun c ↦ (volume : Measure V).prod (condDistrib u a η₀ (ref c))
    let μT := fun c ↦ (volume : Measure V).prod (condDistrib u a η₁ (ref c))
    ∃ Γ : Kernel V T, IsMarkovKernel Γ ∧ ∀ c0 : V,
      OriginalIIDTranslatedMacroConditionalInput (0 : X) η₀ η₁
        (original_seed_transverse_finrank_pos S hdim) (H := mask) (φ := φ) (u := u)
        (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex)
        (by
          let _inst : MetricSpace M := F.metricSpace
          let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
          let _instPolish : PolishSpace M := inferInstance
          let _instBorel : BorelSpace (ℚ → M) := inferInstance
          exact e.continuous.measurable.comp
            ((measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj).comp ha))
        (by let _inst : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)
        cost hcost k c0 K Γ
        (fun c L ↦ (∀ H G : LegalNonnegativeInputTest X,
          (∫ z, legalInputMeasureLaplacePair H G z ∂L) =
            Real.exp (-(θ c * ((∫ x, 1 - Real.exp (-H.1 x) ∂μS c) +
              ∫ y, 1 - Real.exp (-G.1 y) ∂μT c)))) ∧ IndepFun Prod.fst Prod.snd L) := by
  dsimp only
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let q := Module.finrank ℝ S.covector.ker
  let V := Fin q → ℝ
  let X := V × ℝ
  let T := LocalFiniteMeasure X × LocalFiniteMeasure X
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let φ := fun x ↦ e (R (a x))
  let K := e '' (R '' C.roots)
  let mask := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
  have hq : 0 < q := original_seed_transverse_finrank_pos S hdim
  have hmask : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj C.seedIndex
  have hφ : Measurable φ := e.continuous.measurable.comp
    ((measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj).comp ha)
  have huM : Measurable u := hu.continuous.measurable
  have hA : MeasurableSet (R '' C.roots) :=
    D.haar.measurable_cell_label_image hcomplete i C.roots_compact.measurableSet Subset.rfl
  have hK : MeasurableSet K := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hA
  let s := physicalSceneCanonicalHaarScale q
  obtain ⟨PN, hPNm, hPN, Q, hQm, Γ, hΓ, hΓQ, hΓlim⟩ :=
    D.original_full_seed_input_limit_kernel hF hcomplete hu ha hinj i s
      (physicalSceneCanonicalHaarScale_pos q) (tendsto_physicalSceneCanonicalHaarScale q hq)
      (fun n ↦ by simpa only [Nat.cast_add, Nat.cast_one] using
        physicalSceneCanonicalHaarScale_pow q hq n)
  let _instΓ : IsMarkovKernel Γ := hΓ
  refine ⟨Γ, hΓ, ?_⟩
  intro c0
  apply originalIIDTranslatedMacroConditionalInput_of_actual_kernel_limit
    (0 : X) η₀ η₁ hq hmask hφ huM cost hcost k c0 K hK Γ _ PN
    (fun n c ↦ hPN c n)
  filter_upwards [hΓlim] with c hc
  have htarget : (⟨Γ c, inferInstance⟩ : ProbabilityMeasure T) = Q c := Subtype.ext (hΓQ c)
  refine ⟨?_, hc.2⟩
  rw [htarget]
  exact hc.1

end OTSelector.Reconstruction
