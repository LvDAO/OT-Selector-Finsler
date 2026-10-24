import OTSelector.Reconstruction.OriginalIIDMaskedMacroInputJointLaw
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalCanonicalSceneScale
import OTSelector.MeasureTheory.WeakKernelIdentification
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Actual conditional inputs of the same original masked macro weak law

The canonical Haar scale identifies the original microscopic root z with the local center
c=z/scale. The SAME finite masked macro law then has fixed centered unit-cube root marginal
and the already-proved actual original iid input laws as its conditional input fibers.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal BigOperators CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Probability

/-- A measurable reparametrization with a left inverse changes only the original root label;
the conditional fiber remains the literal fixed-root pushforward of the same sample law. -/
theorem map_prod_reparameterized_root_readout_eq_compProd
    {Ω W V S : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace V] [MeasurableSpace S]
    (P : Measure Ω) (ρ : Measure W) [SFinite P] [SFinite ρ]
    {f : Ω × W → S} (hf : Measurable f)
    {root : W → V} (hr : Measurable root) {unroot : V → W} (hu : Measurable unroot)
    (hinv : ∀ w, unroot (root w) = w) :
    (P.prod ρ).map (fun v ↦ (root v.2, f v)) =
      (ρ.map root) ⊗ₘ (originalIndependentRootReadoutKernel P f).comap unroot hu := by
  let g : Ω × V → S := fun p ↦ f (p.1, unroot p.2)
  have hg : Measurable g := hf.comp (measurable_fst.prodMk (hu.comp measurable_snd))
  have hm : Measurable (Prod.map (id : Ω → Ω) root) := measurable_id.prodMap hr
  have hchange : (P.prod ρ).map (Prod.map id root) = P.prod (ρ.map root) := by
    rw [← Measure.map_prod_map P ρ measurable_id hr, Measure.map_id]
  calc
    _ = ((P.prod ρ).map (Prod.map id root)).map (fun p ↦ (p.2, g p)) := by
      rw [Measure.map_map (measurable_snd.prodMk hg) hm]
      congr 1
      funext v
      change (root v.2, f v) = (root v.2, f (v.1, unroot (root v.2)))
      rw [hinv]

    _ = (P.prod (ρ.map root)).map (fun p ↦ (p.2, g p)) := by rw [hchange]
    _ = (ρ.map root) ⊗ₘ originalIndependentRootReadoutKernel P g :=
      map_prod_root_readout_eq_compProd P (ρ.map root) hg
    _ = _ := by
      congr 1
      ext v
      rw [originalIndependentRootReadoutKernel_apply P hg, Kernel.comap_apply,
        originalIndependentRootReadoutKernel_apply P hf]

/-- Restricting only the retained root keeps its original mass in the composition product. -/
theorem measure_restrict_compProd_left
    {W S : Type*} [MeasurableSpace W] [MeasurableSpace S]
    (η : Measure W) [SFinite η] (Γ : Kernel W S) [IsSFiniteKernel Γ]
    {A : Set W} (hA : MeasurableSet A) :
    (η.restrict A) ⊗ₘ Γ = (η ⊗ₘ Γ).restrict (A ×ˢ univ) := by
  unfold Measure.compProd
  rw [← Kernel.restrict_const hA, Kernel.compProd_restrict_left hA, Kernel.restrict_apply]

/-- A restricted joint-law identity identifies the original conditional kernel on that same
root set, without normalizing its mass or changing conditional laws elsewhere. -/
theorem ae_condKernel_eq_of_restrict_eq_compProd
    {W S : Type*} [MeasurableSpace W] [MeasurableSpace S]
    [StandardBorelSpace S] [Nonempty S]
    (R : Measure (W × S)) [IsFiniteMeasure R]
    (η : Measure W) [IsFiniteMeasure η] (hmarg : R.fst = η)
    (Γ : Kernel W S) [IsMarkovKernel Γ] {A : Set W} (hA : MeasurableSet A)
    (hjoint : R.restrict (A ×ˢ univ) = η.restrict A ⊗ₘ Γ) :
    ∀ᵐ c ∂η.restrict A, R.condKernel c = Γ c := by
  let RA := R.restrict (A ×ˢ univ)
  have hRA : RA = η.restrict A ⊗ₘ R.condKernel := by
    rw [measure_restrict_compProd_left η R.condKernel hA, ← hmarg,
      R.disintegrate R.condKernel]
  have hfst : RA.fst = η.restrict A := by rw [hRA, Measure.fst_compProd]
  have hΓ := eq_condKernel_of_measure_eq_compProd (ρ := RA) Γ
    (by rw [hfst]; exact hjoint)
  have hOrig := eq_condKernel_of_measure_eq_compProd (ρ := RA) R.condKernel
    (by rw [hfst]; exact hRA)
  rw [hfst] at hΓ hOrig
  filter_upwards [hΓ, hOrig] with c hc ho
  exact ho.trans hc.symm

end OTSelector.Probability

namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 20000

variable {M : Type*} [MeasurableSpace M] {q : ℕ}
local instance iidMaskedMacroConditionalPointStandardBorel :
    StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidMaskedMacroConditionalConfigurationTopology
    (base : (Fin q → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueTopology base

set_option quotPrecheck false
local notation "V" => (Fin q → ℝ)
local notation "X" => V × ℝ
local notation "T" => LocalFiniteMeasure X × LocalFiniteMeasure X

/-- The unchanged macroscopic scene carrier; this abbreviation adds no new data. -/
abbrev OriginalIIDMaskedMacroCarrier (base : X) :=
  V × (CavityLocalScene X X × LocalConfiguration base)

/-- Retain the original macro tag and the two actual masked original inputs. -/
def originalIIDMaskedMacroTaggedInputProjection (base : X)
    (p : OriginalIIDMaskedMacroCarrier base × OriginalIIDMaskedMacroCarrier base) : V × T :=
  (p.1.1, originalIIDMaskedMacroInputProjection base p)

/-- The retained tag and actual input marginal depend continuously on the same macro scene. -/
theorem continuous_originalIIDMaskedMacroTaggedInputProjection (base : X) :
    Continuous (originalIIDMaskedMacroTaggedInputProjection base) :=
  (continuous_fst.comp continuous_fst).prodMk
    (continuous_originalIIDMaskedMacroInputProjection base)

/-- The original tag/input projection is measurable for the unchanged scene structures. -/
theorem measurable_originalIIDMaskedMacroTaggedInputProjection (base : X) :
    Measurable (originalIIDMaskedMacroTaggedInputProjection base) :=
  (measurable_fst.comp measurable_fst).prodMk
    (measurable_originalIIDMaskedMacroInputProjection base)

/-- Reindex the actual microscopic-root kernel by its original local center c=z/scale. -/
def originalIIDMaskedMacroCenteredInputKernel (base : X) (μ ν : Measure M) (n : ℕ)
    (H : Set M) (φ : M → V) (u : M → ℝ) (scale : ℝ) : Kernel V T :=
  (originalIIDMaskedMacroInputKernel base μ ν n H (fun x ↦ scale • φ x) u).comap
    (fun c : V ↦ scale • c) (measurable_id.const_smul scale)

/-- At center c the exact original finite fiber is the actual masked iid law with
observation scale·(φ(x)-c), using the SAME n+1 original observations in each color. -/
theorem originalIIDMaskedMacroCenteredInputKernel_apply
    (base : X) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) {H : Set M} (hH : MeasurableSet H) {φ : M → V} (hφ : Measurable φ)
    {u : M → ℝ} (hu : Measurable u) (scale : ℝ) (c : V) :
    originalIIDMaskedMacroCenteredInputKernel base μ ν n H φ u scale c =
      originalIidMaskedLocalInputPairMeasure μ ν (n + 1) base H H
        (fun x ↦ (scale • (φ x - c), u x)) (fun x ↦ (scale • (φ x - c), u x)) := by
  have hscaled : Measurable (fun x : M ↦ scale • φ x) := hφ.const_smul scale
  rw [originalIIDMaskedMacroCenteredInputKernel, Kernel.comap_apply,
    originalIIDMaskedMacroInputKernel_apply base μ ν n hH
      (coord := fun x ↦ scale • φ x) hscaled hu]
  simp_rw [smul_sub]

/-- The centered original input fiber is an everywhere Markov kernel. -/
theorem isMarkovKernel_originalIIDMaskedMacroCenteredInputKernel
    (base : X) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) {H : Set M} (hH : MeasurableSet H) {φ : M → V} (hφ : Measurable φ)
    {u : M → ℝ} (hu : Measurable u) (scale : ℝ) :
    IsMarkovKernel (originalIIDMaskedMacroCenteredInputKernel base μ ν n H φ u scale) := by
  have := isMarkovKernel_originalIIDMaskedMacroInputKernel base μ ν n hH
    (hφ.const_smul scale) hu
  unfold originalIIDMaskedMacroCenteredInputKernel
  infer_instance

/-- Exact finite-n disintegration of the SAME masked macro optimizer law: the canonical tag
is the local center and its root law is the original unit-mass centered Haar restriction. -/
theorem originalIIDMaskedMacroLaw_taggedInput_eq_compProd
    (base : X) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < q) (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) {H : Set M} (hH : MeasurableSet H)
    {φ : M → V} (hφ : Measurable φ) {u : M → ℝ} (hu : Measurable u) :
    let scale := physicalSceneCanonicalHaarScale q n
    (originalIIDMaskedBipartiteMacroLaw base μ ν (by simpa using hq)
      cost hcost k n H hH (fun x ↦ scale • φ x) (hφ.const_smul scale) u hu : Measure _).map
        (originalIIDMaskedMacroTaggedInputProjection base) =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
        (physicalScene_centered_unitCube_mass (Fin q)) : Measure V) ⊗ₘ
        originalIIDMaskedMacroCenteredInputKernel base μ ν n H φ u scale := by
  let scale := physicalSceneCanonicalHaarScale q n
  let ρ := cavityRootMeasure volume (physicalSceneCanonicalHaarDomain q n) ((n : ℝ) + 1)
  let P := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  have : SFinite ρ := by dsimp [ρ, cavityRootMeasure]; infer_instance
  have hs : scale ≠ 0 := (physicalSceneCanonicalHaarScale_pos q n).ne'
  have htag := (continuous_physicalSceneMacroscopicRoot (ι := Fin q) scale).measurable
  have hunroot : Measurable (fun c : V ↦ scale • c) := measurable_id.const_smul scale
  have hinv (z : V) : scale • physicalSceneMacroscopicRoot scale z = z := by
    ext j
    simp only [physicalSceneMacroscopicRoot, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hroot : ρ.map (physicalSceneMacroscopicRoot scale) =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
        (physicalScene_centered_unitCube_mass (Fin q)) : Measure V) := by
    exact congrArg (fun p : ProbabilityMeasure V ↦ (p : Measure V))
      (physicalSceneMacroscopicRootLaw_canonicalHaarScale q hq n)
  have hinput := measurable_originalIIDMaskedMacroInputReadout base n hH
    (hφ.const_smul scale) hu
  have hm := measurable_originalIIDMaskedBipartiteMacroObservation base cost hcost k n H hH
    (fun x ↦ scale • φ x) (hφ.const_smul scale) u hu scale
  have heq := map_prod_reparameterized_root_readout_eq_compProd P ρ hinput htag hunroot hinv
  rw [hroot] at heq
  have hlaw : (originalIIDMaskedBipartiteMacroLaw base μ ν (by simpa using hq)
      cost hcost k n H hH (fun x ↦ scale • φ x) (hφ.const_smul scale) u hu : Measure _) =
      (P.prod ρ).map (originalIIDMaskedBipartiteMacroObservation base cost k n H
        (fun x ↦ scale • φ x) u scale) := by
    simp only [originalIIDMaskedBipartiteMacroLaw, Fintype.card_fin]
    rfl
  dsimp only
  rw [hlaw, Measure.map_map (measurable_originalIIDMaskedMacroTaggedInputProjection base) hm]
  exact heq

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 20000

local instance iidMaskedMacroConditionalCorePointStandardBorel (q : ℕ) : StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidMaskedMacroConditionalCoreConfigurationTopology
    (q : ℕ) (base : (Fin q → ℝ) × ℝ) :
    TopologicalSpace (LocalConfiguration base) := LocalConfiguration.vagueTopology base
local instance iidMaskedMacroConditionalCoreConfigurationBorel
    (q : ℕ) (base : (Fin q → ℝ) × ℝ) :
    BorelSpace (LocalConfiguration base) := LocalConfiguration.vagueBorelSpace
local instance iidMaskedMacroConditionalCoreConfigurationPolish
    (q : ℕ) (base : (Fin q → ℝ) × ℝ) :
    PolishSpace (LocalConfiguration base) := LocalConfiguration.vaguePolishSpace
local instance iidMaskedMacroConditionalCoreInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidMaskedMacroConditionalCorePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidMaskedMacroConditionalCoreInputNonempty (q : ℕ) : Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) :=
  ⟨⟨0, inferInstance⟩⟩

open Metric Module Manifold OTSelector.Geometry
open scoped ContDiff NNReal

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

/-- On the single original centered macro frame, every weak subsequence of the SAME original
masked iid optimizer law has conditional input law equal to the proved actual Poisson-profile
kernel. The root restriction is η|K, hence volume on K intersect the centered unit cube; it is
never renormalized. The full original geometry still enters only through D's proved kernel.
A later countable translated-frame glue is needed to cover an arbitrary coordinate core K. -/
theorem PopulationLocalPressureCore.original_masked_macro_conditional_input
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
    let s := physicalSceneCanonicalHaarScale q
    let mask := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let θ := fun c ↦ originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c)
    let μS := fun c ↦ (volume : Measure V).prod (condDistrib u a η₀ (ref c))
    let μT := fun c ↦ (volume : Measure V).prod (condDistrib u a η₁ (ref c))
    let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
      (physicalScene_centered_unitCube_mass (Fin q))
    let Macro := OriginalIIDMaskedMacroCarrier (0 : X)
    ∃ Ln : ℕ → ProbabilityMeasure (Macro × Macro),
      (∀ n, (Ln n : Measure (Macro × Macro)) =
        (((Measure.pi (fun _ : Fin (n + 1) ↦ η₀)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ η₁))).prod
          (cavityRootMeasure volume (physicalSceneCanonicalHaarDomain q n) ((n : ℝ) + 1))).map
          (originalIIDMaskedBipartiteMacroObservation (0 : X) (cost n) (k n) n mask
            (fun x ↦ s n • φ x) u (s n))) ∧
      ∃ Γ : Kernel V T, IsMarkovKernel Γ ∧
        ∀ m : ℕ → ℕ, StrictMono m → ∀ L : ProbabilityMeasure (Macro × Macro),
          Tendsto (fun n ↦ Ln (m n)) atTop (𝓝 L) →
          let Qinput := L.map
            (measurable_originalIIDMaskedMacroTaggedInputProjection (0 : X)).aemeasurable
          (Qinput : Measure (V × T)).fst = (η : Measure V) ∧
            (Qinput : Measure (V × T)).restrict (K ×ˢ univ) =
              (η : Measure V).restrict K ⊗ₘ Γ ∧
            ∀ᵐ c ∂(η : Measure V).restrict K,
              (Qinput : Measure (V × T)).condKernel c = Γ c ∧
              (∀ H G : LegalNonnegativeInputTest X,
                (∫ z, legalInputMeasureLaplacePair H G z ∂(Qinput : Measure (V × T)).condKernel c) =
                  Real.exp (-(θ c * ((∫ x, 1 - Real.exp (-H.1 x) ∂μS c) +
                    ∫ y, 1 - Real.exp (-G.1 y) ∂μT c)))) ∧
              IndepFun Prod.fst Prod.snd ((Qinput : Measure (V × T)).condKernel c) := by
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
  let Macro := OriginalIIDMaskedMacroCarrier (0 : X)
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let φ := fun x ↦ e (R (a x))
  let K := e '' (R '' C.roots)
  let s := physicalSceneCanonicalHaarScale q
  let mask := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
  let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
    (physicalScene_centered_unitCube_mass (Fin q))
  have hq : 0 < q := original_seed_transverse_finrank_pos S hdim
  have hmask : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj C.seedIndex
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have hφ : Measurable φ := e.continuous.measurable.comp (hR.comp ha)
  have huM : Measurable u := hu.continuous.measurable
  have hA : MeasurableSet (R '' C.roots) :=
    D.haar.measurable_cell_label_image hcomplete i C.roots_compact.measurableSet Subset.rfl
  have hK : MeasurableSet K := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hA
  let Ln : ℕ → ProbabilityMeasure (Macro × Macro) := fun n ↦
    originalIIDMaskedBipartiteMacroLaw (0 : X) η₀ η₁ (by simpa using hq)
      (cost n) (hcost n) (k n) n mask hmask (fun x ↦ s n • φ x)
        (hφ.const_smul (s n)) u huM
  obtain ⟨PN, hPNm, hPN, Q, hQm, Γ, hΓ, hΓQ, hΓlim⟩ :=
    D.original_full_seed_input_limit_kernel hF hcomplete hu ha hinj i s
      (physicalSceneCanonicalHaarScale_pos q) (tendsto_physicalSceneCanonicalHaarScale q hq)
      (fun n ↦ by simpa only [Nat.cast_add, Nat.cast_one] using
        physicalSceneCanonicalHaarScale_pow q hq n)
  let _instΓ : IsMarkovKernel Γ := hΓ
  let Kn : ℕ → Kernel V T := fun n ↦
    originalIIDMaskedMacroCenteredInputKernel (0 : X) η₀ η₁ n mask φ u (s n)
  let _instKn : ∀ n, IsMarkovKernel (Kn n) := fun n ↦
    isMarkovKernel_originalIIDMaskedMacroCenteredInputKernel (0 : X) η₀ η₁ n
      hmask hφ huM (s n)
  have hKn (n : ℕ) (c : V) : Kn n c = (PN n c : Measure T) := by
    rw [originalIIDMaskedMacroCenteredInputKernel_apply (0 : X) η₀ η₁ n hmask hφ huM]
    exact (hPN c n).symm
  have hηle : (η : Measure V) ≤ volume := Measure.restrict_le_self
  have hΓlimη := ae_mono (Measure.restrict_mono_measure hηle K) hΓlim
  refine ⟨Ln, ?_, Γ, hΓ, ?_⟩
  · intro n
    simp only [Ln, originalIIDMaskedBipartiteMacroLaw, Fintype.card_fin]
    rfl
  · intro m hm L hw
    let Qinput : ProbabilityMeasure (V × T) := L.map
      (measurable_originalIIDMaskedMacroTaggedInputProjection (0 : X)).aemeasurable
    let Rn : ℕ → ProbabilityMeasure (V × T) := fun n ↦ (Ln (m n)).map
      (measurable_originalIIDMaskedMacroTaggedInputProjection (0 : X)).aemeasurable
    have hwinput : Tendsto Rn atTop (𝓝 Qinput) :=
      ((ProbabilityMeasure.continuous_map
        (continuous_originalIIDMaskedMacroTaggedInputProjection (0 : X))).tendsto L).comp hw
    have hfinite (n : ℕ) : (Rn n : Measure (V × T)) = (η : Measure V) ⊗ₘ Kn (m n) :=
      originalIIDMaskedMacroLaw_taggedInput_eq_compProd (0 : X) η₀ η₁ hq
        (cost (m n)) (hcost (m n)) (k (m n)) (m n) hmask hφ huM
    have hkernel : ∀ᵐ c ∂(η : Measure V).restrict K,
        Tendsto (β := ProbabilityMeasure T)
          (fun n ↦ (⟨Kn (m n) c, inferInstance⟩ : ProbabilityMeasure T)) atTop
          (𝓝 (⟨Γ c, inferInstance⟩ : ProbabilityMeasure T)) := by
      filter_upwards [hΓlimη] with c hc
      have hvalue n : (⟨Kn (m n) c, inferInstance⟩ : ProbabilityMeasure T) = PN (m n) c :=
        Subtype.ext (hKn (m n) c)
      have hlimit : (⟨Γ c, inferInstance⟩ : ProbabilityMeasure T) = Q c := Subtype.ext (hΓQ c)
      simpa only [Function.comp_def, hvalue, hlimit] using hc.1.comp hm.tendsto_atTop
    have hrestrict := restrict_joint_weak_limit_eq_compProd_of_ae_kernel_weak η Rn Qinput
      hwinput (fun n ↦ Kn (m n)) Γ hfinite K hK hkernel
    have hfirst (n : ℕ) : (Rn n).map measurable_fst.aemeasurable = η := by
      apply ProbabilityMeasure.toMeasure_injective
      change (Rn n : Measure (V × T)).fst = (η : Measure V)
      rw [hfinite n, Measure.fst_compProd]
    have hrootweak : Tendsto (fun n ↦ (Rn n).map measurable_fst.aemeasurable) atTop
        (𝓝 (Qinput.map measurable_fst.aemeasurable)) :=
      ((ProbabilityMeasure.continuous_map
        (show Continuous (Prod.fst : V × T → V) from continuous_fst)).tendsto Qinput).comp
          hwinput
    have hconstant : (fun n ↦ (Rn n).map measurable_fst.aemeasurable) =
        (fun _ : ℕ ↦ η) := funext hfirst
    rw [hconstant] at hrootweak
    have hrootEq : Qinput.map measurable_fst.aemeasurable = η :=
      tendsto_nhds_unique hrootweak tendsto_const_nhds
    have hmarg : (Qinput : Measure (V × T)).fst = (η : Measure V) :=
      congrArg (fun p : ProbabilityMeasure V ↦ (p : Measure V)) hrootEq
    have hcond := ae_condKernel_eq_of_restrict_eq_compProd
      (Qinput : Measure (V × T)) (η : Measure V) hmarg Γ hK hrestrict
    refine ⟨hmarg, hrestrict, ?_⟩
    filter_upwards [hcond, hΓlimη] with c hcc hc
    refine ⟨hcc, ?_⟩
    rw [hcc]
    exact hc.2

end OTSelector.Reconstruction
