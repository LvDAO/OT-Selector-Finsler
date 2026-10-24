import OTSelector.MeasureTheory.CountablePartitionKernel
import OTSelector.Reconstruction.OriginalIIDWholeCoreConditionalMatching

/-!
# One measurable actual matching scene kernel over the whole core

The countable disjoint owner partition glues the original conditional scene kernels of
the common actual macro weak limits. On each owner the resulting kernel equals its own
frame conditional law exactly; outside the core it is the fixed empty-scene probability.
The original volume restriction and raw intensity remain unnormalized.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal BigOperators Topology CompactlySupported BoundedContinuousFunction
noncomputable section

namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 20000

variable {q : ℕ}
local instance iidWholeCoreKernelPointStandardBorel : StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidWholeCoreKernelPointPolish : PolishSpace
    (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidWholeCoreKernelPlanPolish : PolishSpace
    (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local instance iidWholeCoreKernelConfigurationTopology :
    TopologicalSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueTopology _
local instance iidWholeCoreKernelConfigurationBorel :
    BorelSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueBorelSpace
local instance iidWholeCoreKernelConfigurationPolish :
    PolishSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vaguePolishSpace
local instance iidWholeCoreKernelPointNonempty : Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) :=
  ⟨⟨0,inferInstance⟩⟩
local instance iidWholeCoreKernelPlanNonempty : Nonempty
    (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩
set_option quotPrecheck false
local notation "V" => (Fin q → ℝ)
local notation "X" => V × ℝ
local notation "T" => LocalFiniteMeasure X × LocalFiniteMeasure X
local notation "Scene" => OriginalIIDMaskedMacroInputScene (Fin q)
local notation "Macro" => OriginalIIDMaskedMacroCarrier (0 : X)

/-- The fixed fallback has no input atoms and no matching edges. -/
def originalIIDEmptyInputScene (q : ℕ) : OriginalIIDMaskedMacroInputScene (Fin q) :=
  ((⟨0,inferInstance⟩,⟨0,inferInstance⟩),(⟨0,inferInstance⟩,⟨0,inferInstance⟩))

/-- Frame j's own original full-scene conditional kernel in original center coordinates. -/
def originalIIDFrameSceneKernel (Q : ℕ → ProbabilityMeasure (Macro × Macro)) (j : ℕ) : Kernel V Scene :=
  let ρ : Measure (V × Scene) := ((Q j).map
    (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable.aemeasurable :
    Measure (V × Scene))
  ρ.condKernel.comap (fun c ↦ c - originalMacroFrameCenter q j) (measurable_id.sub measurable_const)

/-- Each prescribed actual frame conditional law is a probability at every original center. -/
instance iidWholeCoreFrameSceneKernelMarkov (Q : ℕ → ProbabilityMeasure (Macro × Macro)) (j : ℕ) :
    IsMarkovKernel (originalIIDFrameSceneKernel Q j) := by
  unfold originalIIDFrameSceneKernel
  infer_instance

/-- The single actual whole-core scene kernel, formed by measurable owner gluing. -/
def originalIIDWholeCoreSceneKernel (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) : Kernel V Scene :=
  countablePartitionKernel (originalMacroFrameOwner q K) (measurableSet_originalMacroFrameOwner q hK)
    (originalIIDFrameSceneKernel Q)
    (Kernel.deterministic (fun _ : V ↦ originalIIDEmptyInputScene q) measurable_const)

/-- Every original owner uses exactly its actual frame conditional law. -/
theorem originalIIDWholeCoreSceneKernel_eq_on_owner (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) (j : ℕ) {c : V}
    (hc : c ∈ originalMacroFrameOwner q K j) :
    originalIIDWholeCoreSceneKernel K hK Q c = originalIIDFrameSceneKernel Q j c :=
  countablePartitionKernel_eq _ _ (pairwiseDisjoint_originalMacroFrameOwner q K) _ _ j hc

/-- The same fixed empty-scene law is used off K. -/
theorem originalIIDWholeCoreSceneKernel_eq_outside (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) {c : V} (hc : c ∉ K) :
    originalIIDWholeCoreSceneKernel K hK Q c = Measure.dirac (originalIIDEmptyInputScene q) := by
  apply countablePartitionKernel_eq_fallback
  simpa only [iUnion_originalMacroFrameOwner] using hc

/-- The whole-core actual scene family is a measurable Markov kernel. -/
instance iidWholeCoreSceneKernelMarkov (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) : IsMarkovKernel (originalIIDWholeCoreSceneKernel K hK Q) :=
  isMarkovKernel_countablePartitionKernel _ _ (pairwiseDisjoint_originalMacroFrameOwner q K) _ _

/-- The original-center scene joint measure uses unnormalized original volume on K. -/
def originalIIDWholeCoreSceneJoint (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) : Measure (V × Scene) :=
  (volume : Measure V).restrict K ⊗ₘ originalIIDWholeCoreSceneKernel K hK Q

/-- Gluing does not change the original root measure or its total mass. -/
theorem originalIIDWholeCoreSceneJoint_fst (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) :
    (originalIIDWholeCoreSceneJoint K hK Q).fst = (volume : Measure V).restrict K :=
  Measure.fst_compProd _ _

/-- On each original owner the joint measure is exactly the owner measure times its actual
frame conditional kernel, preserving that owner's original mass. -/
theorem originalIIDWholeCoreSceneJoint_restrict_owner (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) (j : ℕ) :
    (originalIIDWholeCoreSceneJoint K hK Q).restrict (originalMacroFrameOwner q K j ×ˢ univ) =
      (volume : Measure V).restrict (originalMacroFrameOwner q K j) ⊗ₘ originalIIDFrameSceneKernel Q j := by
  rw [originalIIDWholeCoreSceneJoint, ← measure_restrict_compProd_left _ _
    (measurableSet_originalMacroFrameOwner q hK j),
    Measure.restrict_restrict_of_subset (fun c hc ↦ (originalMacroFrameOwner_subset q K j hc).1)]
  apply Measure.compProd_congr
  filter_upwards [ae_restrict_mem (measurableSet_originalMacroFrameOwner q hK j)] with c hc
  exact originalIIDWholeCoreSceneKernel_eq_on_owner K hK Q j hc

/-- The complete actual joint measure is the countable sum of its unchanged owner joints. -/
theorem originalIIDWholeCoreSceneJoint_eq_sum (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) :
    originalIIDWholeCoreSceneJoint K hK Q = Measure.sum (fun j ↦
      (volume : Measure V).restrict (originalMacroFrameOwner q K j) ⊗ₘ originalIIDFrameSceneKernel Q j) := by
  rw [originalIIDWholeCoreSceneJoint, ← sum_restrict_originalMacroFrameOwner q hK volume,
    Measure.compProd_sum_left]
  congr 1
  funext j
  apply Measure.compProd_congr
  filter_upwards [ae_restrict_mem (measurableSet_originalMacroFrameOwner q hK j)] with c hc
  exact originalIIDWholeCoreSceneKernel_eq_on_owner K hK Q j hc

/-- An arbitrary whole property of the actual own conditional laws descends to the glued
kernel on all original centers, without a measurable-property or gluing callback. -/
theorem ae_originalIIDWholeCoreSceneKernel_of_ae_owner
    (K : Set V) (hK : MeasurableSet K) (Q : ℕ → ProbabilityMeasure (Macro × Macro))
    (P : V → Measure Scene → Prop)
    (hP : ∀ᵐ c ∂(volume : Measure V).restrict K, ∃ j,
      c ∈ originalMacroFrameOwner q K j ∧ P c (originalIIDFrameSceneKernel Q j c)) :
    ∀ᵐ c ∂(volume : Measure V).restrict K, P c (originalIIDWholeCoreSceneKernel K hK Q c) := by
  filter_upwards [hP] with c hc
  obtain ⟨j,hcj,hpc⟩ := hc
  rwa [originalIIDWholeCoreSceneKernel_eq_on_owner K hK Q j hcj]


end OTSelector.Reconstruction

namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 20000

section WholeCoreKernelSupportedActual
open Metric Module Manifold OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped ContDiff NNReal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

variable
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)

local instance iidWholeCoreKernelSupportedMatchingCorePointStandardBorel (q : ℕ) : StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidWholeCoreKernelSupportedMatchingCoreConfigTopology (q : ℕ) :
    TopologicalSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueTopology _
local instance iidWholeCoreKernelSupportedMatchingCoreConfigBorel (q : ℕ) :
    BorelSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueBorelSpace
local instance iidWholeCoreKernelSupportedMatchingCoreConfigPolish (q : ℕ) :
    PolishSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vaguePolishSpace
local instance iidWholeCoreKernelSupportedMatchingCoreInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidWholeCoreKernelSupportedMatchingCorePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidWholeCoreKernelSupportedMatchingCoreInputNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := ⟨⟨0,inferInstance⟩⟩
local instance iidWholeCoreKernelSupportedMatchingCorePlanNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩

local instance iidWholeCoreKernelSupportedMatchingCoreMacroPairPolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance iidWholeCoreKernelSupportedMatchingCoreSceneBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidWholeCoreKernelSupportedMatchingCoreMacroBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance iidWholeCoreKernelSupportedMatchingCoreMacroPairBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance

local instance iidWholeCoreKernelSupportedMatchingCoreScenePolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidWholeCoreKernelSupportedMatchingCoreSceneStandardBorel (q : ℕ) :
    StandardBorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidWholeCoreKernelSupportedMatchingCoreTaggedSceneBorel (q : ℕ) :
    BorelSpace ((Fin q → ℝ) × OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance

include hcore hrecovery hκ horder hbalance hA hB hμ hν hreg hμreg hface hgap hdist



/-- One actual whole-core Markov scene kernel is glued from the prescribed original frame
conditional laws of one common sample subsequence. It retains the same original input
kernel, complete matching, clocks, profile and all spatial stationarity without an oracle. -/
theorem PopulationLocalPressureCore.original_supported_whole_core_scene_kernel
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (bins : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ)
    (Ksupport : Set M) (hK : IsCompact Ksupport)
    (hμK : ∀ᵐ x ∂μ, x ∈ Ksupport) (hνK : ∀ᵐ y ∂ν, y ∈ Ksupport)
    (f : (Ksupport × Ksupport) →ᵇ ℝ) (g : (M × M) →ᵇ ℝ) (ε probeError : ℝ)
    (hdata : D.originalSupportedWeightUnitDensityPressureData
      (μ := (⟨μ, inferInstance⟩ : ProbabilityMeasure M))
      (ν := (⟨ν, inferInstance⟩ : ProbabilityMeasure M)) γ originalGap bins U
      retentionError splitError Ksupport hK hμK hνK f g ε probeError
      (fun n ↦ canonicalLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure M)
        (⟨ν, inferInstance⟩ : ProbabilityMeasure M) n)
      (fun n ↦ canonicalX n) (fun n ↦ canonicalY n))
    (t : ℝ) (hdim : 2 ≤ finrank ℝ E) (i : Fin D.haar.continuous.count) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let V := Fin q → ℝ
    let X := V × ℝ
    let T := LocalFiniteMeasure X × LocalFiniteMeasure X
    let Scene := OriginalIIDMaskedMacroInputScene (Fin q)
    let Macro := OriginalIIDMaskedMacroCarrier (0 : X)
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let φ := fun x ↦ e (R (a x))
    let K := e '' (R '' C.roots)
    let scale := physicalSceneCanonicalHaarScale q
    let mask := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := μ.map a) C.seedIndex
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let θ := fun c ↦ originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex (ref c)
    let α := fun c ↦ condDistrib u a μ (ref c)
    let β := fun c ↦ condDistrib u a ν (ref c)
    let cost := fun n x y ↦ finslerMeanScale E n *
      ((F.lengthEDist x y).toReal - u y + u x) +
        t * finslerCarrierProbe (⟨μ,inferInstance⟩ : ProbabilityMeasure M)
          (⟨ν,inferInstance⟩ : ProbabilityMeasure M) Ksupport hK.measurableSet hμK hνK f x y
    let hcost : ∀ n, Measurable (Function.uncurry (cost n)) := fun n ↦
      measurable_originalIID_supported_tilt_cost hcomplete
      (⟨μ,inferInstance⟩ : ProbabilityMeasure M) (⟨ν,inferInstance⟩ : ProbabilityMeasure M)
      Ksupport hK.measurableSet hμK hνK u hu f (finslerMeanScale E n) t
    let hm : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex
    let hφ : Measurable φ := by
      have hp := measurable_physicalSceneOriginalSeedScaledPosition
        (P := P) (a := a) hF hcomplete hu ha hinj C.seedIndex (1 : ℝ)
      change Measurable (fun x ↦ (1 : ℝ) • φ x) at hp
      simpa only [one_smul] using hp
    let huM : Measurable u := by
      let _iidWholeCoreKernelMatchingMetric : MetricSpace M := F.metricSpace
      exact hu.continuous.measurable
    ∃ Γ : Kernel V T, IsMarkovKernel Γ ∧
      ∃ m : ℕ → ℕ, StrictMono m ∧ ∃ Q : ℕ → ProbabilityMeasure (Macro × Macro),
        (∀ j, Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw (0 : X) μ ν
          (by simpa using original_seed_transverse_finrank_pos S hdim)
          (cost (m n)) (hcost (m n)) 1 (m n) mask hm
          (fun x ↦ scale (m n) • (φ x - originalMacroFrameCenter q j))
          ((hφ.sub measurable_const).const_smul (scale (m n))) u huM) atTop (𝓝 (Q j))) ∧
        ∃ Λ : Kernel V Scene, IsMarkovKernel Λ ∧
          (∀ j c, c ∈ originalMacroFrameOwner q K j → Λ c = originalIIDFrameSceneKernel Q j c) ∧
          (∀ c, c ∉ K → Λ c = Measure.dirac (originalIIDEmptyInputScene q)) ∧
          (∀ᵐ c ∂(volume : Measure V).restrict K,
            OriginalIIDConditionalMatchingProfile gap (θ c) (α c) (β c) (Γ c) (Λ c)) ∧
          ((volume : Measure V).restrict K ⊗ₘ Λ).fst = (volume : Measure V).restrict K ∧
          (volume : Measure V).restrict K ⊗ₘ Λ = Measure.sum (fun j ↦
            (volume : Measure V).restrict (originalMacroFrameOwner q K j) ⊗ₘ originalIIDFrameSceneKernel Q j) := by
  intro C S q V X T Scene Macro R e φ K scale mask ref θ α β cost hcost hmask hφ huM
  let _iidWholeCoreKernelMetric : MetricSpace M := F.metricSpace
  let _iidWholeCoreKernelProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _iidWholeCoreKernelPolish : PolishSpace M := inferInstance
  let _iidWholeCoreKernelRootBorel : BorelSpace (ℚ → M) := inferInstance
  have hRset : MeasurableSet (R '' C.roots) :=
    D.haar.measurable_cell_label_image hcomplete i C.roots_compact.measurableSet Subset.rfl
  have hKcore : MeasurableSet K :=
    e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hRset
  obtain ⟨Γ,hΓ,m,hm,Q,hweak,_hFrames,hGlobal⟩ :=
    D.original_supported_whole_core_conditional_full_matching
      (hcore := hcore) (hrecovery := hrecovery) (hF := hF) (hcomplete := hcomplete)
      (hu := hu) (ha := ha) (hinj := hinj) (hκ := hκ) (horder := horder)
      (hbalance := hbalance) (hA := hA) (hB := hB) (hμ := hμ) (hν := hν)
      (hreg := hreg) (hμreg := hμreg) (hface := hface) (hgap := hgap) (hdist := hdist)
      γ originalGap bins U retentionError splitError Ksupport hK hμK hνK f g ε probeError hdata t hdim i
  let Λ := originalIIDWholeCoreSceneKernel K hKcore Q
  refine ⟨Γ,hΓ,m,hm,Q,hweak,Λ,inferInstance,?_,?_,?_,?_,?_⟩
  · intro j c hc
    exact originalIIDWholeCoreSceneKernel_eq_on_owner K hKcore Q j hc
  · intro c hc
    exact originalIIDWholeCoreSceneKernel_eq_outside K hKcore Q hc
  · exact ae_originalIIDWholeCoreSceneKernel_of_ae_owner K hKcore Q
      (fun c L ↦ OriginalIIDConditionalMatchingProfile gap (θ c) (α c) (β c) (Γ c) L) hGlobal
  · exact originalIIDWholeCoreSceneJoint_fst K hKcore Q
  · exact originalIIDWholeCoreSceneJoint_eq_sum K hKcore Q

end WholeCoreKernelSupportedActual
end OTSelector.Reconstruction
