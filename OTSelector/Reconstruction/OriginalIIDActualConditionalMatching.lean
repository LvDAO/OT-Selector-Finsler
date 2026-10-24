import OTSelector.Reconstruction.OriginalIIDMaskedMacroConditionalInput
import OTSelector.Reconstruction.OriginalIIDMaskedMacroInputStationarity
import OTSelector.Reconstruction.OriginalIIDMaskedMacroMarginalClosure
import OTSelector.Reconstruction.OriginalIIDMaskedMacroCountingLimit
import OTSelector.Reconstruction.OriginalIIDFullSeedInputSimplicity
import OTSelector.MeasureTheory.MeasurableLocalMeasureEquality
import OTSelector.Reconstruction.OriginalIIDFullMatchingPrimitive

/-!
# Actual conditional full input matchings

The complete matching, original two-color Poisson input and all-translation
stationarity are assembled on the same actual macro weak law and its own
conditional kernel. The single macro frame sees the retained coordinate core
intersected with the centered unit cube; its root measure is not renormalized.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

section Disintegration
variable {A S T : Type*} [MeasurableSpace A] [MeasurableSpace S]
  [MeasurableSpace T] [StandardBorelSpace S] [Nonempty S]
  [StandardBorelSpace T] [Nonempty T]

/-- A projection retaining the same macro root pushes the original full-scene
conditional law to the input-only conditional law, on one common root set. -/
theorem ae_condKernel_map_readout_eq_of_joint_projection
    (ρ : Measure (A × S)) [IsFiniteMeasure ρ] (read : S → T) (hread : Measurable read) :
    let σ := ρ.map (Prod.map id read)
    σ.fst = ρ.fst ∧
      ∀ᵐ c ∂ρ.fst, (ρ.condKernel c).map read = σ.condKernel c := by
  dsimp only
  let σ := ρ.map (Prod.map id read)
  have hfst : σ.fst = ρ.fst := by
    change (ρ.map (Prod.map id read)).map Prod.fst = ρ.map Prod.fst
    rw [Measure.map_map measurable_fst (measurable_id.prodMap hread)]
    rfl
  have hdis : σ = σ.fst ⊗ₘ (ρ.condKernel.map read) := by
    rw [hfst, Measure.compProd_map hread, ρ.disintegrate ρ.condKernel]
  have hcond := eq_condKernel_of_measure_eq_compProd (ρ.condKernel.map read) hdis
  refine ⟨hfst, ?_⟩
  rw [hfst] at hcond
  filter_upwards [hcond] with c hc
  simpa only [Kernel.map_apply _ hread] using hc

/-- Every almost-sure property of one actual joint scene descends to its own
conditional laws. This direction needs no extra measurability callback. -/
theorem ae_ae_condKernel_of_ae_joint
    (ρ : Measure (A × S)) [IsFiniteMeasure ρ] {p : S → Prop}
    (hp : ∀ᵐ z ∂ρ, p z.2) :
    ∀ᵐ c ∂ρ.fst, ∀ᵐ s ∂ρ.condKernel c, p s := by
  have hdis : ρ.fst ⊗ₘ ρ.condKernel = ρ := ρ.disintegrate ρ.condKernel
  exact Measure.ae_ae_of_ae_compProd (by rwa [hdis])
end Disintegration
section ActualScene
variable {q : ℕ} {M : Type*} [MeasurableSpace M]
local instance actualConditionalMatchingPointStandardBorel : StandardBorelSpace (((Fin q) → ℝ) × ℝ) := inferInstance
local instance actualConditionalMatchingPlanPolish : PolishSpace
    (LocalFiniteMeasure ((((Fin q) → ℝ) × ℝ) × (((Fin q) → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local instance actualConditionalMatchingInputPolish : PolishSpace
    (LocalFiniteMeasure (((Fin q) → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance actualConditionalMatchingInputNonempty : Nonempty
    (LocalFiniteMeasure (((Fin q) → ℝ) × ℝ)) := ⟨⟨0,inferInstance⟩⟩
local instance actualConditionalMatchingPlanNonempty : Nonempty
    (LocalFiniteMeasure ((((Fin q) → ℝ) × ℝ) × (((Fin q) → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩
variable (base : ((Fin q) → ℝ) × ℝ)
local instance actualConditionalMatchingConfigurationTopology : TopologicalSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueTopology base
local instance actualConditionalMatchingConfigurationBorel : BorelSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueBorelSpace
local instance actualConditionalMatchingConfigurationPolish : PolishSpace (LocalConfiguration base) :=
  LocalConfiguration.vaguePolishSpace
set_option quotPrecheck false
local notation "Pt" => ((Fin q) → ℝ) × ℝ
local notation "Scene" => OriginalIIDMaskedMacroInputScene (Fin q)
local notation "Macro" => OriginalIIDMaskedMacroCarrier base
local instance actualConditionalMatchingMacroPairPolish : PolishSpace (Macro × Macro) := inferInstance
local instance actualConditionalMatchingSceneBorel : BorelSpace Scene := inferInstance
local instance actualConditionalMatchingMacroBorel : BorelSpace Macro := inferInstance
local instance actualConditionalMatchingMacroPairBorel : BorelSpace (Macro × Macro) := inferInstance

/-- The input-only law is the literal projection of the same tagged full scene. -/
theorem originalMaskedMacro_taggedInput_eq_fullScene_input_projection
    (L : ProbabilityMeasure (Macro × Macro)) :
    (L : Measure (Macro × Macro)).map (originalIIDMaskedMacroTaggedInputProjection base) =
      ((L : Measure (Macro × Macro)).map (originalIIDMaskedMacroInputSceneProjection base)).map
        (Prod.map id (Prod.snd : Scene → LocalFiniteMeasure Pt × LocalFiniteMeasure Pt)) := by
  rw [Measure.map_map (measurable_id.prodMap measurable_snd)
    (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable]
  rfl

/-- Integer edges and complete marginals form a measurable event on the
unchanged pair-plan/two-input scene, even for nonproper endpoint projections. -/
theorem measurableSet_originalMaskedMacro_integer_full_marginals :
    MeasurableSet {s : Scene |
      IsLegalCountingMeasure (base,base) s.1.1 ∧
      (s.1.1 : Measure (Pt × Pt)).fst = (s.2.1 : Measure Pt) ∧
      (s.1.1 : Measure (Pt × Pt)).snd = (s.2.2 : Measure Pt)} := by
  have hsrc : Measurable (fun s : Scene ↦ (s.1.1 : Measure (Pt × Pt)).fst) :=
    (Measure.measurable_map Prod.fst measurable_fst).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst.fst)
  have htgt : Measurable (fun s : Scene ↦ (s.1.1 : Measure (Pt × Pt)).snd) :=
    (Measure.measurable_map Prod.snd measurable_snd).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst.fst)
  exact ((isClosed_isLegalCountingMeasure (base,base)).measurableSet.preimage measurable_fst.fst).inter
    ((measurableSet_measure_eq_localFiniteMeasure _ hsrc (fun s : Scene ↦ s.2.1)
      measurable_snd.fst).inter
      (measurableSet_measure_eq_localFiniteMeasure _ htgt (fun s : Scene ↦ s.2.2) measurable_snd.snd))

/-- Every original macro state retains literal integer configurations in its
input fields. Their full-scene conditional laws inherit those same carriers. -/
theorem ae_conditional_originalMaskedMacro_input_counting
    (L : ProbabilityMeasure (Macro × Macro)) :
    let ρ := (L.map
      (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable :
      Measure (((Fin q) → ℝ) × Scene))
    ∀ᵐ c ∂ρ.fst, ∀ᵐ s ∂ρ.condKernel c,
      IsLegalCountingMeasure base s.2.1 ∧ IsLegalCountingMeasure base s.2.2 := by
  dsimp only
  apply ae_ae_condKernel_of_ae_joint
  have hE : MeasurableSet {z : ((Fin q) → ℝ) × Scene |
      IsLegalCountingMeasure base z.2.2.1 ∧ IsLegalCountingMeasure base z.2.2.2} :=
    ((isClosed_isLegalCountingMeasure base).measurableSet.preimage measurable_snd.snd.fst).inter
      ((isClosed_isLegalCountingMeasure base).measurableSet.preimage measurable_snd.snd.snd)
  exact (ae_map_iff
    (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable hE).mpr
      (.of_forall fun z ↦ ⟨⟨z.1.2.2,rfl⟩,⟨z.2.2.2,rfl⟩⟩)

/-- The exact full-marginal data of one actual macro law pass to the own
conditional kernel of its unchanged tagged full-scene projection. -/
theorem ae_conditional_originalMaskedMacro_integer_full_marginals
    (L : ProbabilityMeasure (Macro × Macro))
    (hc : ∀ᵐ z ∂(L : Measure (Macro × Macro)),
      IsLegalCountingMeasure (base,base) (originalIIDMaskedMacroPlan base z))
    (hm : ∀ᵐ z ∂(L : Measure (Macro × Macro)),
      (originalIIDMaskedMacroPlan base z : Measure (Pt × Pt)).fst =
        (originalIIDMaskedMacroInputProjection base z).1 ∧
      (originalIIDMaskedMacroPlan base z : Measure (Pt × Pt)).snd =
        (originalIIDMaskedMacroInputProjection base z).2) :
    let ρ := (L.map
      (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable :
      Measure (((Fin q) → ℝ) × Scene))
    ∀ᵐ c ∂ρ.fst, ∀ᵐ s ∂ρ.condKernel c,
      IsLegalCountingMeasure (base,base) s.1.1 ∧
      (s.1.1 : Measure (Pt × Pt)).fst = (s.2.1 : Measure Pt) ∧
      (s.1.1 : Measure (Pt × Pt)).snd = (s.2.2 : Measure Pt) := by
  dsimp only
  apply ae_ae_condKernel_of_ae_joint
  have hE := (measurableSet_originalMaskedMacro_integer_full_marginals base).preimage
    (measurable_snd : Measurable (Prod.snd : ((Fin q) → ℝ) × Scene → Scene))
  apply (ae_map_iff
    (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable hE).mpr
  filter_upwards [hc,hm] with z hz hzm
  exact ⟨hz,hzm⟩
/-- Every actual finite observation retains the literal same optimizer in
both coordinates of its first pair scene. -/
theorem ae_originalIIDMaskedMacro_plan_pair_eq
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card (Fin q))
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → ((Fin q) → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) :
    ∀ᵐ s ∂(originalIIDMaskedBipartiteMacroLaw base μ ν hq cost hcost k n H hH
      coord hcoord u hu : Measure (Macro × Macro)), s.1.2.1.1 = s.1.2.1.2 := by
  let R := haarRootRadius (Fintype.card (Fin q)) ((n : ℝ) + 1)
  unfold originalIIDMaskedBipartiteMacroLaw
  apply (ae_map_iff
    (measurable_originalIIDMaskedBipartiteMacroObservation base cost hcost k n H hH
      coord hcoord u hu (2 * R)).aemeasurable
    (isClosed_eq continuous_fst.snd.fst.fst continuous_fst.snd.fst.snd).measurableSet).mpr
  exact ae_of_all _ fun _ ↦ rfl

/-- The closed equality event retains both coordinates of the original
optimizer in every prescribed same-experiment weak limit. -/
theorem ae_originalIIDMaskedMacro_plan_pair_eq_of_tendsto
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card (Fin q))
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → ((Fin q) → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (m : ℕ → ℕ)
    {Q : ProbabilityMeasure (Macro × Macro)}
    (hweak : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (Macro × Macro)), s.1.2.1.1 = s.1.2.1.2 := by
  let K := {s : Macro × Macro | s.1.2.1.1 = s.1.2.1.2}
  have hK : IsClosed K :=
    isClosed_eq continuous_fst.snd.fst.fst continuous_fst.snd.fst.snd
  have hn (n : ℕ) : (originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu : Measure (Macro × Macro)) Kᶜ = 0 :=
    ae_originalIIDMaskedMacro_plan_pair_eq base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hK.isOpen_compl
  change (Q : Measure (Macro × Macro)) Kᶜ ≤ atTop.liminf (fun n ↦
    (originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu : Measure (Macro × Macro)) Kᶜ) at hle
  simp only [hn, liminf_const] at hle
  exact le_antisymm hle bot_le

/-- The actual full-scene root conditional law retains equality of the two
original plan coordinates on one full-measure set of the same original roots. -/
theorem ae_conditional_originalIIDMaskedMacroInputScene_plan_pair_eq_of_tendsto
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card (Fin q))
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → ((Fin q) → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (m : ℕ → ℕ)
    {Q : ProbabilityMeasure (Macro × Macro)}
    (hweak : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu) atTop (𝓝 Q)) :
    let ρ := (Q.map
      (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable :
        Measure (((Fin q) → ℝ) × OriginalIIDMaskedMacroInputScene (Fin q)))
    ∀ᵐ c ∂ρ.fst, ∀ᵐ scene ∂ρ.condKernel c, scene.1.1 = scene.1.2 := by
  intro ρ
  apply Measure.ae_ae_of_ae_compProd (μ := ρ.fst) (κ := ρ.condKernel)
    (p := fun s : ((Fin q) → ℝ) × OriginalIIDMaskedMacroInputScene (Fin q) ↦
      s.2.1.1 = s.2.1.2)
  rw [ρ.disintegrate ρ.condKernel]
  change ∀ᵐ s ∂(Q : Measure (Macro × Macro)).map
    (originalIIDMaskedMacroInputSceneProjection base), s.2.1.1 = s.2.1.2
  apply (ae_map_iff
    (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable
    (isClosed_eq continuous_snd.fst.fst continuous_snd.fst.snd).measurableSet).mpr
  exact ae_originalIIDMaskedMacro_plan_pair_eq_of_tendsto base μ ν hq
    cost hcost k H hH coord hcoord u hu m hweak


end ActualScene

section SupportedActual
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

local instance actualConditionalMatchingCorePointStandardBorel (q : ℕ) : StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance actualConditionalMatchingCoreConfigTopology (q : ℕ) :
    TopologicalSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueTopology _
local instance actualConditionalMatchingCoreConfigBorel (q : ℕ) :
    BorelSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueBorelSpace
local instance actualConditionalMatchingCoreConfigPolish (q : ℕ) :
    PolishSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vaguePolishSpace
local instance actualConditionalMatchingCoreInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance actualConditionalMatchingCorePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance actualConditionalMatchingCoreInputNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := ⟨⟨0,inferInstance⟩⟩
local instance actualConditionalMatchingCorePlanNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩

local instance actualConditionalMatchingCoreMacroPairPolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance actualConditionalMatchingCoreSceneBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance actualConditionalMatchingCoreMacroBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance actualConditionalMatchingCoreMacroPairBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance

local instance actualConditionalMatchingCoreScenePolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance actualConditionalMatchingCoreSceneStandardBorel (q : ℕ) :
    StandardBorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance actualConditionalMatchingCoreTaggedSceneBorel (q : ℕ) :
    BorelSpace ((Fin q → ℝ) × OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance

include hcore hrecovery hκ horder hbalance hA hB hμ hν hreg hμreg hface hgap hdist

set_option maxHeartbeats 1200000 in
/-- The same supported-cost macro weak law has a genuinely full one-to-one
matching in its own stationary conditional scene kernel, with both original
input measures and the original intensity profile. The root measure is eta|K,
namely K intersect the centered unit cube; arbitrary K still needs translated
frames to cover it. It is never normalized by its mass or by theta. -/
theorem PopulationLocalPressureCore.original_supported_conditional_full_matching
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
    let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
      (physicalScene_centered_unitCube_mass (Fin q))
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
      let _actualConditionalMatchingMetric : MetricSpace M := F.metricSpace
      exact hu.continuous.measurable
    ∃ Γ : Kernel V T, IsMarkovKernel Γ ∧
      ∀ m : ℕ → ℕ, StrictMono m → ∀ L : ProbabilityMeasure (Macro × Macro),
        Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw (0 : X) μ ν
          (by simpa using original_seed_transverse_finrank_pos S hdim)
          (cost (m n)) (hcost (m n)) 1 (m n) mask hm
          (fun x ↦ scale (m n) • φ x) (hφ.const_smul (scale (m n))) u huM)
          atTop (𝓝 L) →
        let ρ := (L.map
          (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable.aemeasurable :
          Measure (V × Scene))
        let σ := (L.map
          (measurable_originalIIDMaskedMacroTaggedInputProjection (0 : X)).aemeasurable :
          Measure (V × T))
        ρ.fst = (η : Measure V) ∧
          (∀ w : V, MeasurePreserving (Prod.map id (originalIIDMaskedMacroInputSceneReroot w)) ρ ρ) ∧
          ∀ᵐ c ∂(η : Measure V).restrict K,
            (ρ.condKernel c).map Prod.snd = σ.condKernel c ∧
            σ.condKernel c = Γ c ∧
            (∀ w : V, MeasurePreserving (originalIIDMaskedMacroInputSceneReroot w)
              (ρ.condKernel c) (ρ.condKernel c)) ∧
            (∀ H G : LegalNonnegativeInputTest X,
              (∫ z, legalInputMeasureLaplacePair H G z ∂(ρ.condKernel c).map Prod.snd) =
                Real.exp (-(θ c * ((∫ x, 1 - Real.exp (-H.1 x) ∂volume.prod (α c)) +
                  ∫ y, 1 - Real.exp (-G.1 y) ∂volume.prod (β c))))) ∧
            IndepFun Prod.fst Prod.snd ((ρ.condKernel c).map Prod.snd) ∧
            (∀ᵐ z ∂ρ.condKernel c,
              z.1.1 = z.1.2 ∧
              IsFullOriginalBipartiteMatching (0 : X) (0 : X) z.1.1 z.2.1 z.2.2 ∧
              IsFullOriginalBipartiteMatching (0 : X) (0 : X) z.1.2 z.2.1 z.2.2) := by
  intro C S q V X T Scene Macro R e φ K scale mask ref θ α β η cost hcost hmask hφ huM
  let _actualMatchingMetric : MetricSpace M := F.metricSpace
  let _actualMatchingProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _actualMatchingPolish : PolishSpace M := inferInstance
  have hq : 0 < q := original_seed_transverse_finrank_pos S hdim
  have hqdim : 0 < Fintype.card (Fin q) := by simpa using hq
  have hdimker : q = finrank ℝ E - 1 := by
    have hh : q + 1 = finrank ℝ E := by
      simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using
        S.normalization.toLinearEquiv.finrank_eq
    omega
  have hnormMean (n : ℕ) : scale n ^ 2 = finslerMeanScale E n := by
    rw [show scale n = ((n : ℝ) + 1) ^ (1 / (q : ℝ)) from
      physicalSceneCanonicalHaarScale_eq_rpow q n]
    unfold finslerMeanScale
    rw [Nat.cast_add,Nat.cast_one,← Real.rpow_natCast (((n : ℝ) + 1) ^ (1 / (q : ℝ))) 2,
      ← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ) + 1),hdimker]
    congr 1
    ring
  have hscale2 : Tendsto (fun n ↦ scale n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_physicalSceneCanonicalHaarScale q hq)
  obtain ⟨Ln,hLn,Γ,hΓ,hInput⟩ :=
    D.original_masked_macro_conditional_input hF hcomplete hu ha hinj hdim i cost hcost (fun _ ↦ 1)
  refine ⟨Γ,hΓ,?_⟩
  intro m hm L hw
  have hLnEq (n : ℕ) : Ln n = originalIIDMaskedBipartiteMacroLaw (0 : X) μ ν hqdim
      (cost n) (hcost n) 1 n mask hmask (fun x ↦ scale n • φ x)
      (hφ.const_smul (scale n)) u huM := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [hLn n]
    simp only [originalIIDMaskedBipartiteMacroLaw, Fintype.card_fin,
      physicalSceneCanonicalHaarDomain]
    rfl
  have hwLn : Tendsto (fun n ↦ Ln (m n)) atTop (𝓝 L) := by
    simpa only [hLnEq] using hw
  have hInputL := hInput m hm L hwLn
  let ρ : Measure (V × Scene) := (L.map
    (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable.aemeasurable :
    Measure (V × Scene))
  let σ : Measure (V × T) := (L.map
    (measurable_originalIIDMaskedMacroTaggedInputProjection (0 : X)).aemeasurable :
    Measure (V × T))
  have hσ : σ = ρ.map (Prod.map id (Prod.snd : Scene → T)) :=
    originalMaskedMacro_taggedInput_eq_fullScene_input_projection (0 : X) L
  have hproj := ae_condKernel_map_readout_eq_of_joint_projection ρ
    (Prod.snd : Scene → T) measurable_snd
  dsimp only at hproj
  simp only [← hσ] at hproj
  have hρfst : ρ.fst = (η : Measure V) := hproj.1.symm.trans hInputL.1
  have hfull := D.ae_originalIID_supported_masked_macro_input_marginals
    (hcore := hcore) (hrecovery := hrecovery) (hF := hF) (hcomplete := hcomplete)
    (hu := hu) (ha := ha) (hinj := hinj) (hκ := hκ) (horder := horder)
    (hbalance := hbalance) (hA := hA) (hB := hB) (hμ := hμ) (hν := hν)
    (hreg := hreg) (hμreg := hμreg) (hface := hface) (hgap := hgap) (hdist := hdist)
    (spatialScale := scale) (hsp := physicalSceneCanonicalHaarScale_pos q) (hscale := hscale2)
    (j := C.seedIndex) (base := (0 : X)) γ originalGap bins U retentionError splitError
    Ksupport hK hμK hνK f g ε probeError hdata t hnormMean hq m hm L
  have hFullL := hfull (by
    convert hw using 1
    rfl)
  have hCountL := ae_isLegalCountingMeasure_of_originalIIDMaskedBipartiteMacroLaw_tendsto
    (0 : X) μ ν hqdim cost hcost (fun _ ↦ 1) (fun _ ↦ mask) (fun _ ↦ hmask)
    (fun n x ↦ scale n • φ x) (fun n ↦ hφ.const_smul (scale n)) u huM m L hw
  have hData := ae_conditional_originalMaskedMacro_integer_full_marginals (0 : X) L hCountL hFullL
  have hCounts := ae_conditional_originalMaskedMacro_input_counting (0 : X) L
  have hStationary := joint_and_ae_conditional_originalIIDMaskedMacroInputSceneReroot_of_tendsto
    (0 : X) μ ν hqdim cost hcost (fun _ ↦ 1) mask hmask
    (fun n x ↦ scale n • φ x) (fun n ↦ hφ.const_smul (scale n)) u huM m hm.tendsto_atTop hw
  have hShared := ae_conditional_originalIIDMaskedMacroInputScene_plan_pair_eq_of_tendsto
    (0 : X) μ ν hqdim cost hcost (fun _ ↦ 1) mask hmask
    (fun n x ↦ scale n • φ x) (fun n ↦ hφ.const_smul (scale n)) u huM m hw
  have hRestrict (p : V → Prop) (hp : ∀ᵐ c ∂ρ.fst, p c) :
      ∀ᵐ c ∂(η : Measure V).restrict K, p c := by
    apply ae_restrict_of_ae
    simpa only [← hρfst] using hp
  have hSharedK := hRestrict _ hShared
  have hDataK := hRestrict _ hData
  have hCountsK := hRestrict _ hCounts
  have hStationaryK := hRestrict _ hStationary.2
  have hprojK := hRestrict _ hproj.2
  refine ⟨hρfst,hStationary.1,?_⟩
  filter_upwards [hInputL.2.2,hDataK,hCountsK,hStationaryK,hprojK,hSharedK] with c hc hd hcount hstat hp hshared
  have hProfile : ∀ H G : LegalNonnegativeInputTest X,
      (∫ z, legalInputMeasureLaplacePair H G z ∂(ρ.condKernel c).map Prod.snd) =
        Real.exp (-(θ c * ((∫ x, 1 - Real.exp (-H.1 x)
          ∂volume.prod (condDistrib u a μ (ref c))) +
          ∫ y, 1 - Real.exp (-G.1 y) ∂volume.prod (condDistrib u a ν (ref c))))) := by
    rw [hp]
    exact hc.2.1
  have hθ : 0 ≤ θ c := mul_nonneg (NNReal.coe_nonneg _)
    (populationAtlasTheta_nonneg P a κ (μ.map a) C.seedIndex (ref c))
  have hCountMeas : MeasurableSet {z : T |
      IsLegalCountingMeasure (0 : X) z.1 ∧ IsLegalCountingMeasure (0 : X) z.2} :=
    ((isClosed_isLegalCountingMeasure (0 : X)).measurableSet.preimage measurable_fst).inter
      ((isClosed_isLegalCountingMeasure (0 : X)).measurableSet.preimage measurable_snd)
  have hRead : Measurable (Prod.snd : Scene → T) := measurable_snd
  have hInputCount : ∀ᵐ z ∂(ρ.condKernel c).map Prod.snd,
      IsLegalCountingMeasure (0 : X) z.1 ∧ IsLegalCountingMeasure (0 : X) z.2 :=
    (ae_map_iff hRead.aemeasurable hCountMeas).mpr hcount
  let _actualInputProbability : IsProbabilityMeasure ((ρ.condKernel c).map Prod.snd) :=
    Measure.isProbabilityMeasure_map hRead.aemeasurable
  have hSimple := ae_simple_pair_of_compact_poisson_profile q hq (θ c) hθ
    (condDistrib u a μ (ref c)) (condDistrib u a ν (ref c))
    ((ρ.condKernel c).map Prod.snd) hProfile hInputCount
  have hSimpleMeas : MeasurableSet {z : T |
      IsLegalSimpleCountingMeasure (0 : X) z.1 ∧ IsLegalSimpleCountingMeasure (0 : X) z.2} :=
    ((measurableSet_isLegalSimpleCountingMeasure (0 : X)).preimage measurable_fst).inter
      ((measurableSet_isLegalSimpleCountingMeasure (0 : X)).preimage measurable_snd)
  have hFullMatch : ∀ᵐ z ∂ρ.condKernel c,
      IsFullOriginalBipartiteMatching (0 : X) (0 : X) z.1.1 z.2.1 z.2.2 := by
    filter_upwards [hd, (ae_map_iff hRead.aemeasurable hSimpleMeas).mp hSimple] with z hz hs
    exact isFullOriginalBipartiteMatching_of_counting_simple_marginals
      (0 : X) (0 : X) z.1.1 z.2.1 z.2.2 hz.1 hs.1 hs.2 hz.2.1 hz.2.2
  have hFullPair : ∀ᵐ z ∂ρ.condKernel c,
      z.1.1 = z.1.2 ∧
      IsFullOriginalBipartiteMatching (0 : X) (0 : X) z.1.1 z.2.1 z.2.2 ∧
      IsFullOriginalBipartiteMatching (0 : X) (0 : X) z.1.2 z.2.1 z.2.2 := by
    filter_upwards [hshared,hFullMatch] with z he hm
    change z.1.1 = z.1.2 at he
    exact ⟨he,hm,he ▸ hm⟩
  refine ⟨hp,hc.1,hstat,hProfile,?_,hFullPair⟩
  rw [hp]
  exact hc.2.2

end SupportedActual

end OTSelector.Reconstruction
