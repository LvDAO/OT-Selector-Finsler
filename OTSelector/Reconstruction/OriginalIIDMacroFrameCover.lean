import OTSelector.Reconstruction.OriginalIIDTranslatedMacroConditionalInput

/-!
# Countable original macro frames over the whole core

Rational translates of the original unit cube cover every transverse coordinate. The first
frame containing a point owns it. These measurable owner cells form an exact partition of
any measurable core, without a boundary-null or compactness assumption. All frames use
one common subsequence of the original masked iid optimizer laws and the same input kernel.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal BigOperators CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 20000

/-- A fixed enumeration of all rational transverse centers, including dimension zero. -/
def originalMacroRationalCenters (q : ℕ) : ℕ → (Fin q → ℚ) :=
  Classical.choose (exists_surjective_nat (Fin q → ℚ))

/-- The original real center of the j-th rational translated macro frame. -/
def originalMacroFrameCenter (q j : ℕ) : Fin q → ℝ :=
  fun i ↦ (originalMacroRationalCenters q j i : ℝ)

/-- The original closed unit cube in the original center coordinates of frame j. -/
def originalMacroFrameCube (q j : ℕ) : Set (Fin q → ℝ) :=
  (fun c ↦ c - originalMacroFrameCenter q j) ⁻¹' physicalSceneCanonicalMacroCarrier q

/-- Every original coordinate belongs to some rational translated original unit cube. -/
theorem iUnion_originalMacroFrameCube (q : ℕ) :
    ⋃ j, originalMacroFrameCube q j = univ := by
  apply eq_univ_of_forall
  intro c
  have hr (i : Fin q) : ∃ r : ℚ, c i - (1 / 2 : ℝ) < r ∧ (r : ℝ) < c i + 1 / 2 :=
    exists_rat_btwn (by linarith)
  choose r hr using hr
  obtain ⟨j, hj⟩ := Classical.choose_spec (exists_surjective_nat (Fin q → ℚ)) r
  refine mem_iUnion.mpr ⟨j, ?_⟩
  change c - originalMacroFrameCenter q j ∈ Icc (fun _ ↦ -(1 / 2 : ℝ)) (fun _ ↦ 1 / 2)
  have hc (i : Fin q) : originalMacroFrameCenter q j i = (r i : ℝ) := by
    change ((originalMacroRationalCenters q j) i : ℝ) = (r i : ℝ)
    rw [originalMacroRationalCenters, hj]
  constructor <;> intro i <;> have hi := hr i <;> simp only [Pi.sub_apply, hc] <;> linarith

/-- Each translated original closed unit cube is measurable. -/
theorem measurableSet_originalMacroFrameCube (q j : ℕ) :
    MeasurableSet (originalMacroFrameCube q j) :=
  measurableSet_Icc.preimage (measurable_id.sub measurable_const)

/-- The first enumerated frame containing a core point owns it. -/
def originalMacroFrameOwner (q : ℕ) (K : Set (Fin q → ℝ)) (j : ℕ) : Set (Fin q → ℝ) :=
  disjointed (fun j ↦ K ∩ originalMacroFrameCube q j) j

/-- The owner rule is exactly core intersect current cube minus all earlier cubes. -/
theorem originalMacroFrameOwner_eq (q : ℕ) (K : Set (Fin q → ℝ)) (j : ℕ) :
    originalMacroFrameOwner q K j =
      (K ∩ originalMacroFrameCube q j) \ (⋃ k < j, originalMacroFrameCube q k) := by
  rw [originalMacroFrameOwner, disjointed_eq_inter_compl]
  ext c
  simp only [mem_inter_iff, mem_iInter, mem_compl_iff, Set.mem_sdiff, mem_iUnion, not_exists]
  tauto

/-- Every owner is measurable whenever the original core is measurable. -/
theorem measurableSet_originalMacroFrameOwner (q : ℕ) {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (j : ℕ) : MeasurableSet (originalMacroFrameOwner q K j) :=
  MeasurableSet.disjointed (fun j ↦ hK.inter (measurableSet_originalMacroFrameCube q j)) j

/-- Owner cells retain their original core and their original frame cube. -/
theorem originalMacroFrameOwner_subset (q : ℕ) (K : Set (Fin q → ℝ)) (j : ℕ) :
    originalMacroFrameOwner q K j ⊆ K ∩ originalMacroFrameCube q j :=
  disjointed_subset _ _

/-- No original root belongs to two different owner cells. -/
theorem pairwiseDisjoint_originalMacroFrameOwner (q : ℕ) (K : Set (Fin q → ℝ)) :
    Pairwise (Disjoint on originalMacroFrameOwner q K) :=
  disjoint_disjointed _

/-- The owners partition the entire original core, including all cube boundaries. -/
theorem iUnion_originalMacroFrameOwner (q : ℕ) (K : Set (Fin q → ℝ)) :
    ⋃ j, originalMacroFrameOwner q K j = K := by
  change (⋃ j, disjointed (fun j ↦ K ∩ originalMacroFrameCube q j) j) = K
  rw [iUnion_disjointed, ← inter_iUnion, iUnion_originalMacroFrameCube, inter_univ]

/-- Owner restrictions sum to the original core measure, without renormalizing any owner. -/
theorem sum_restrict_originalMacroFrameOwner (q : ℕ) {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (ρ : Measure (Fin q → ℝ)) :
    Measure.sum (fun j ↦ ρ.restrict (originalMacroFrameOwner q K j)) = ρ.restrict K := by
  rw [← Measure.restrict_iUnion (pairwiseDisjoint_originalMacroFrameOwner q K)
    (measurableSet_originalMacroFrameOwner q hK), iUnion_originalMacroFrameOwner]


/-- Shifting an owner's original tag back to its original center gives exactly Lebesgue
measure restricted to that owner. Its mass is not rescaled. -/
theorem map_originalMacroFrameOwner_root (q : ℕ) {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (j : ℕ) :
    let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
      (physicalScene_centered_unitCube_mass (Fin q))
    ((η : Measure (Fin q → ℝ)).restrict
      ((fun y ↦ originalMacroFrameCenter q j + y) ⁻¹' originalMacroFrameOwner q K j)).map
        (fun y ↦ originalMacroFrameCenter q j + y) =
      (volume : Measure (Fin q → ℝ)).restrict (originalMacroFrameOwner q K j) := by
  let c0 := originalMacroFrameCenter q j
  let A := originalMacroFrameOwner q K j
  let B := (fun y ↦ c0 + y) ⁻¹' A
  have hA : MeasurableSet A := measurableSet_originalMacroFrameOwner q hK j
  have hs : Measurable (fun y : Fin q → ℝ ↦ c0 + y) := measurable_const.add measurable_id
  have hBU : B ⊆ physicalSceneCanonicalMacroCarrier q := by
    intro y hy
    have hc := (originalMacroFrameOwner_subset q K j hy).2
    change c0 + y - c0 ∈ physicalSceneCanonicalMacroCarrier q at hc
    simpa only [add_sub_cancel_left] using hc
  change (((volume : Measure (Fin q → ℝ)).restrict
    (physicalSceneCanonicalMacroCarrier q)).restrict B).map (fun y ↦ c0 + y) =
      (volume : Measure (Fin q → ℝ)).restrict A
  rw [Measure.restrict_restrict_of_subset hBU, ← Measure.restrict_map hs hA,
    (measurePreserving_add_left (volume : Measure (Fin q → ℝ)) c0).map_eq]

/-- A whole almost-everywhere statement on a frame owner is equivalent to the statement
at original centers under the original Lebesgue restriction. No measurability of the
property is required, so a complete Laplace profile can be transported at once. -/
theorem ae_originalMacroFrameOwner_iff (q : ℕ) {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (j : ℕ) (P : (Fin q → ℝ) → Prop) :
    let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
      (physicalScene_centered_unitCube_mass (Fin q))
    (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict (originalMacroFrameOwner q K j), P c) ↔
      ∀ᵐ y ∂(η : Measure (Fin q → ℝ)).restrict
        ((fun y ↦ originalMacroFrameCenter q j + y) ⁻¹' originalMacroFrameOwner q K j),
          P (originalMacroFrameCenter q j + y) := by
  rw [← map_originalMacroFrameOwner_root q hK j]
  exact (Homeomorph.addLeft (originalMacroFrameCenter q j)).toMeasurableEquiv.measurableEmbedding.ae_map_iff

/-- Countably many owner-wise whole statements glue to one almost-everywhere statement on
all of K. This does not intersect exceptional sets indexed by individual test functions. -/
theorem ae_originalMacroFrameOwner_glue (q : ℕ) (K : Set (Fin q → ℝ))
    (ρ : Measure (Fin q → ℝ)) (P : (Fin q → ℝ) → Prop)
    (hP : ∀ j, ∀ᵐ c ∂ρ.restrict (originalMacroFrameOwner q K j), P c) :
    ∀ᵐ c ∂ρ.restrict K, P c := by
  rw [← iUnion_originalMacroFrameOwner q K]
  exact (ae_restrict_iUnion_iff (originalMacroFrameOwner q K) P).mpr hP

variable {M : Type*} [MeasurableSpace M] {q : ℕ}
local instance iidMacroFrameCoverPointStandardBorel : StandardBorelSpace ((Fin q → ℝ) × ℝ) :=
  inferInstance
local instance iidMacroFrameCoverConfigurationTopology (base : (Fin q → ℝ) × ℝ) :
    TopologicalSpace (LocalConfiguration base) := LocalConfiguration.vagueTopology base
local instance iidMacroFrameCoverConfigurationBorel (base : (Fin q → ℝ) × ℝ) :
    BorelSpace (LocalConfiguration base) := LocalConfiguration.vagueBorelSpace
local instance iidMacroFrameCoverConfigurationPolish (base : (Fin q → ℝ) × ℝ) :
    PolishSpace (LocalConfiguration base) := LocalConfiguration.vaguePolishSpace
local instance iidMacroFrameCoverInputPolish :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidMacroFrameCoverPlanPolish :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidMacroFrameCoverInputNonempty : Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) :=
  ⟨⟨0, inferInstance⟩⟩
set_option quotPrecheck false
local notation "V" => (Fin q → ℝ)
local notation "X" => V × ℝ
local notation "T" => LocalFiniteMeasure X × LocalFiniteMeasure X

/-- Restrict the actual conditional-input conclusion to any measurable smaller original
root set. The restriction keeps its original mass, including positive-mass boundaries. -/
theorem OriginalIIDTranslatedMacroConditionalInput.mono
    (base : X) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < q) {H : Set M} (hH : MeasurableSet H) {φ : M → V} (hφ : Measurable φ)
    {u : M → ℝ} (hu : Measurable u)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (c0 : V) {K A : Set V} (hA : MeasurableSet A) (hAK : A ⊆ K)
    (Γ : Kernel V T) [IsMarkovKernel Γ] (profile : V → Measure T → Prop)
    (hframe : OriginalIIDTranslatedMacroConditionalInput base μ ν hq hH hφ hu
      cost hcost k c0 K Γ profile) :
    OriginalIIDTranslatedMacroConditionalInput base μ ν hq hH hφ hu
      cost hcost k c0 A Γ profile := by
  intro m hm L hw
  obtain ⟨hmarg, hjoint, hcond⟩ := hframe m hm L hw
  let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
    (physicalScene_centered_unitCube_mass (Fin q))
  let Qinput := L.map (measurable_originalIIDMaskedMacroTaggedInputProjection base).aemeasurable
  let B := (fun y : V ↦ c0 + y) ⁻¹' A
  let C := (fun y : V ↦ c0 + y) ⁻¹' K
  let Γshift := Γ.comap (fun y ↦ c0 + y) (measurable_const.add measurable_id)
  have hB : MeasurableSet B := hA.preimage (measurable_const.add measurable_id)
  have hBC : B ⊆ C := preimage_mono hAK
  have hprod : B ×ˢ (univ : Set T) ⊆ C ×ˢ univ := prod_mono hBC Subset.rfl
  refine ⟨hmarg, ?_, ae_restrict_of_ae_restrict_of_subset hBC hcond⟩
  change (Qinput : Measure (V × T)).restrict (B ×ˢ univ) =
    (η : Measure V).restrict B ⊗ₘ Γshift
  calc
    _ = ((Qinput : Measure (V × T)).restrict (C ×ˢ univ)).restrict (B ×ˢ univ) :=
      (Measure.restrict_restrict_of_subset hprod).symm
    _ = ((η : Measure V).restrict C ⊗ₘ Γshift).restrict (B ×ˢ univ) := by rw [hjoint]
    _ = ((η : Measure V).restrict C).restrict B ⊗ₘ Γshift :=
      (measure_restrict_compProd_left _ _ hB).symm
    _ = _ := by rw [Measure.restrict_restrict_of_subset hBC]

/-- One common original sample subsequence and one actual joint weak law for every rational
frame. In frame j the entire original conditional input profile is identified on precisely
its owner cell, using the same Gamma at original center c_j+y. -/
def OriginalIIDMacroFrameOwnerLimits
    (base : X) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < q) {H : Set M} (hH : MeasurableSet H) {φ : M → V} (hφ : Measurable φ)
    {u : M → ℝ} (hu : Measurable u)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (K : Set V) (Γ : Kernel V T) (profile : V → Measure T → Prop) : Prop :=
  let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
    (physicalScene_centered_unitCube_mass (Fin q))
  ∃ m : ℕ → ℕ, StrictMono m ∧
    ∃ Q : ℕ → ProbabilityMeasure (OriginalIIDMaskedMacroCarrier base × OriginalIIDMaskedMacroCarrier base),
      (∀ j,
        Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν (by simpa using hq)
          (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
          (fun x ↦ physicalSceneCanonicalHaarScale q (m n) • (φ x - originalMacroFrameCenter q j))
          ((hφ.sub measurable_const).const_smul (physicalSceneCanonicalHaarScale q (m n))) u hu)
          atTop (𝓝 (Q j)) ∧
        let Qinput := (Q j).map (measurable_originalIIDMaskedMacroTaggedInputProjection base).aemeasurable
        let B := (fun y ↦ originalMacroFrameCenter q j + y) ⁻¹' originalMacroFrameOwner q K j
        (Qinput : Measure (V × T)).fst = (η : Measure V) ∧
          (Qinput : Measure (V × T)).restrict (B ×ˢ univ) =
            (η : Measure V).restrict B ⊗ₘ
              Γ.comap (fun y ↦ originalMacroFrameCenter q j + y) (measurable_const.add measurable_id) ∧
          ∀ᵐ y ∂(η : Measure V).restrict B,
            (Qinput : Measure (V × T)).condKernel y = Γ (originalMacroFrameCenter q j + y) ∧
            profile (originalMacroFrameCenter q j + y) ((Qinput : Measure (V × T)).condKernel y)) ∧
      ∀ᵐ c ∂(volume : Measure V).restrict K, ∃ j,
        c ∈ originalMacroFrameOwner q K j ∧
        let Qinput := (Q j).map (measurable_originalIIDMaskedMacroTaggedInputProjection base).aemeasurable
        (Qinput : Measure (V × T)).condKernel (c - originalMacroFrameCenter q j) = Γ c ∧
          profile c ((Qinput : Measure (V × T)).condKernel (c - originalMacroFrameCenter q j))

/-- Common tightness of all actual frames supplies one sample subsequence; each owner then
consumes the already identified original Gamma. Neither optimizer nor original iid arrays
are selected again when the frame changes. -/
theorem originalIIDMacroFrameOwnerLimits_of_translated_conditional_input
    (base : X) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < q) {H : Set M} (hH : MeasurableSet H) {φ : M → V} (hφ : Measurable φ)
    {u : M → ℝ} (hu : Measurable u)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (K : Set V) (hK : MeasurableSet K)
    (Γ : Kernel V T) [IsMarkovKernel Γ] (profile : V → Measure T → Prop)
    (hframes : ∀ c0, OriginalIIDTranslatedMacroConditionalInput base μ ν hq hH hφ hu
      cost hcost k c0 K Γ profile) :
    OriginalIIDMacroFrameOwnerLimits base μ ν hq hH hφ hu cost hcost k K Γ profile := by
  have hcoord (j n : ℕ) : Measurable (fun x : M ↦
      physicalSceneCanonicalHaarScale q n • (φ x - originalMacroFrameCenter q j)) :=
    (hφ.sub (measurable_const : Measurable (fun _ : M ↦ originalMacroFrameCenter q j))).const_smul
      (physicalSceneCanonicalHaarScale q n)
  obtain ⟨Q, m, hm, hweak⟩ :=
    exists_originalIID_common_masked_bipartite_macro_subsequence_varying_cost
      (fun _ ↦ Fin q) (fun _ ↦ by simpa using hq) (fun _ ↦ base) μ ν cost hcost k
      (fun _ ↦ H) (fun _ ↦ hH)
      (fun j n x ↦ physicalSceneCanonicalHaarScale q n • (φ x - originalMacroFrameCenter q j))
      hcoord u hu
  have howners (j : ℕ) := OriginalIIDTranslatedMacroConditionalInput.mono
    base μ ν hq hH hφ hu cost hcost k
    (originalMacroFrameCenter q j) (measurableSet_originalMacroFrameOwner q hK j)
    (fun c hc ↦ (originalMacroFrameOwner_subset q K j hc).1) Γ profile
    (hframes (originalMacroFrameCenter q j)) m hm (Q j) (hweak j)
  refine ⟨m, hm, Q, (fun j ↦ ⟨hweak j, howners j⟩), ?_⟩
  apply ae_originalMacroFrameOwner_glue q K volume
  intro j
  let Qinput := (Q j).map (measurable_originalIIDMaskedMacroTaggedInputProjection base).aemeasurable
  have hc : ∀ᵐ c ∂(volume : Measure V).restrict (originalMacroFrameOwner q K j),
      (Qinput : Measure (V × T)).condKernel (c - originalMacroFrameCenter q j) = Γ c ∧
        profile c ((Qinput : Measure (V × T)).condKernel (c - originalMacroFrameCenter q j)) := by
    apply (ae_originalMacroFrameOwner_iff q hK j _).mpr
    filter_upwards [(howners j).2.2] with y hy
    simpa only [add_sub_cancel_left] using hy
  filter_upwards [hc, ae_restrict_mem (measurableSet_originalMacroFrameOwner q hK j)] with c hcc hcj
  exact ⟨j, hcj, hcc⟩

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
open Metric Module Manifold OTSelector.Geometry
open scoped ContDiff NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 20000

local instance iidMacroFrameCoverCorePointStandardBorel (q : ℕ) :
    StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidMacroFrameCoverCoreConfigurationTopology (q : ℕ)
    (base : (Fin q → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueTopology base
local instance iidMacroFrameCoverCoreConfigurationBorel (q : ℕ)
    (base : (Fin q → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueBorelSpace
local instance iidMacroFrameCoverCoreConfigurationPolish (q : ℕ)
    (base : (Fin q → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) :=
  LocalConfiguration.vaguePolishSpace
local instance iidMacroFrameCoverCoreInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidMacroFrameCoverCorePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidMacroFrameCoverCoreInputNonempty (q : ℕ) :
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

/-- The actual original D input kernel and a single original sample subsequence cover every
owner of the whole original core. All frames retain the same cost, original optimizer, iid
arrays and intensity at original center c_j+y. Owner masses remain unnormalized. -/
theorem PopulationLocalPressureCore.original_macro_frame_owner_limits
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
    ∃ Γ : Kernel V T, IsMarkovKernel Γ ∧
      OriginalIIDMacroFrameOwnerLimits (0 : X) η₀ η₁
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
        cost hcost k K Γ
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
  obtain ⟨Γ, hΓ, hframes⟩ := D.original_translated_macro_conditional_input
    hF hcomplete hu ha hinj hdim i cost hcost k
  let _instΓ : IsMarkovKernel Γ := hΓ
  refine ⟨Γ, hΓ, ?_⟩
  exact originalIIDMacroFrameOwnerLimits_of_translated_conditional_input
    (0 : X) η₀ η₁ hq hmask hφ huM cost hcost k K hK Γ _ hframes

end OTSelector.Reconstruction
