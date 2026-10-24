import OTSelector.Reconstruction.FinslerPhysicalSceneRootedParameterizedCompactClipping

/-!
# Genuine joint compact kernels for the original macro-clock cutoff probe

The unchanged macro parameter and both physical clocks are retained. Compact
macro/source-clock projections of the original probe, the source spatial test
and the target cutoff supply an explicit compact support envelope.
-/
open Set Function MeasureTheory TopologicalSpace
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι]
local notation "V" => (ι → ℝ)
local notation "Point" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Point × Point)

/-- A compact product envelope keeping the actual macro parameter, source
spatial coordinate, source clock and target point. -/
def physicalSceneMacroClockCompactEnvelope (η : C_c(V, ℝ))
    (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ)) : Set (V × Edge) :=
  (Prod.fst '' tsupport g) ×ˢ
    ((tsupport η ×ˢ ((fun z : V × (ℝ × ℝ) ↦ z.2.1) '' tsupport g)) ×ˢ tsupport χ)

theorem isCompact_physicalSceneMacroClockCompactEnvelope (η : C_c(V, ℝ))
    (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ)) :
    IsCompact (physicalSceneMacroClockCompactEnvelope η g χ) :=
  (g.hasCompactSupport.image continuous_fst).prod
    ((η.hasCompactSupport.prod (g.hasCompactSupport.image continuous_snd.fst)).prod
      χ.hasCompactSupport)

/-- The literal original macro-clock probe, source spatial test and target
cutoff form one jointly compact test on macro parameter times physical edge. -/
def physicalSceneMacroClockCompactKernel (η : C_c(V, ℝ))
    (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ)) : C_c(V × Edge, ℝ) where
  toFun p := η p.2.1.1 * g (p.1, (p.2.1.2, p.2.2.2)) * χ p.2.2
  continuous_toFun :=
    ((η.continuous.comp continuous_snd.fst.fst).mul
      (g.continuous.comp (continuous_fst.prodMk
        (continuous_snd.fst.snd.prodMk continuous_snd.snd.snd)))).mul
      (χ.continuous.comp continuous_snd.snd)
  hasCompactSupport' := by
    apply (isCompact_physicalSceneMacroClockCompactEnvelope η g χ).of_isClosed_subset
      isClosed_closure
    apply closure_minimal _ (isCompact_physicalSceneMacroClockCompactEnvelope η g χ).isClosed
    intro p hp
    have hmul : η p.2.1.1 * g (p.1, (p.2.1.2, p.2.2.2)) * χ p.2.2 ≠ 0 := hp
    have hη := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hmul).1).1
    have hg := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hmul).1).2
    have hχ := (mul_ne_zero_iff.mp hmul).2
    have hgs : (p.1, (p.2.1.2, p.2.2.2)) ∈ tsupport g := subset_closure hg
    exact ⟨⟨_, hgs, rfl⟩, ⟨⟨subset_closure hη, ⟨_, hgs, rfl⟩⟩, subset_closure hχ⟩⟩

@[simp] theorem physicalSceneMacroClockCompactKernel_apply (η : C_c(V, ℝ))
    (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ)) (p : V × Edge) :
    physicalSceneMacroClockCompactKernel η g χ p =
      η p.2.1.1 * g (p.1, (p.2.1.2, p.2.2.2)) * χ p.2.2 := rfl

/-- The actual topological support is contained in the explicit compact envelope. -/
theorem tsupport_physicalSceneMacroClockCompactKernel_subset (η : C_c(V, ℝ))
    (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ)) :
    tsupport (physicalSceneMacroClockCompactKernel η g χ) ⊆
      physicalSceneMacroClockCompactEnvelope η g χ := by
  apply closure_minimal _ (isCompact_physicalSceneMacroClockCompactEnvelope η g χ).isClosed
  intro p hp
  have hmul : η p.2.1.1 * g (p.1, (p.2.1.2, p.2.2.2)) * χ p.2.2 ≠ 0 := hp
  have hη := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hmul).1).1
  have hg := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hmul).1).2
  have hχ := (mul_ne_zero_iff.mp hmul).2
  have hgs : (p.1, (p.2.1.2, p.2.2.2)) ∈ tsupport g := subset_closure hg
  exact ⟨⟨_, hgs, rfl⟩, ⟨⟨subset_closure hη, ⟨_, hgs, rfl⟩⟩, subset_closure hχ⟩⟩

/-- Projecting away the macro parameter keeps the same source spatial support. -/
theorem parameterizedCompactEdgeSupport_macroClockCompactKernel_subset (η : C_c(V, ℝ))
    (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ)) :
    parameterizedCompactEdgeSupport (physicalSceneMacroClockCompactKernel η g χ) ⊆
      {e : Edge | e.1.1 ∈ tsupport η} := by
  rintro e ⟨p, hp, rfl⟩
  exact (tsupport_physicalSceneMacroClockCompactKernel_subset η g χ hp).2.1.1

/-- The joint compact kernel has the literal three-factor supremum bound. -/
theorem norm_physicalSceneMacroClockCompactKernel_le (η : C_c(V, ℝ))
    (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ)) :
    ‖(physicalSceneMacroClockCompactKernel η g χ).toBoundedContinuousFunction‖ ≤
      ‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖ *
        ‖χ.toBoundedContinuousFunction‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro p
  change ‖η p.2.1.1 * g (p.1, (p.2.1.2, p.2.2.2)) * χ p.2.2‖ ≤ _
  rw [norm_mul, norm_mul]
  have hη := η.toBoundedContinuousFunction.norm_coe_le_norm p.2.1.1
  have hg := g.toBoundedContinuousFunction.norm_coe_le_norm (p.1, (p.2.1.2, p.2.2.2))
  have hχ := χ.toBoundedContinuousFunction.norm_coe_le_norm p.2.2
  exact mul_le_mul (mul_le_mul hη hg (norm_nonneg _) (norm_nonneg _)) hχ
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Parameterized compact integration is exactly the original cutoff-probe integral. -/
theorem parameterizedCompactReadout_macroClockCompactKernel_eq (η : C_c(V, ℝ))
    (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ))
    (w : V) (π : LocalFiniteMeasure Edge) :
    parameterizedCompactReadout (physicalSceneMacroClockCompactKernel η g χ) (w, π) =
      ∫ e, η e.1.1 * g (w, (e.1.2, e.2.2)) * χ e.2 ∂(π : Measure Edge) := rfl

variable (base : (ι → ℝ) × ℝ)
local instance macroClockKernelStandardBorel : StandardBorelSpace Point := inferInstance
local instance macroClockKernelConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance macroClockKernelConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance macroClockKernelConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance macroClockKernelPlanPolish : PolishSpace (LocalFiniteMeasure Edge) :=
  LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene Point Point
local notation "MacroScene" => V × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The selected full original plan reads exactly the actual macro-clock
cutoff probe, preserving the actual macroscopic parameter and both clocks. -/
theorem physicalSceneFullParameterizedCompactReadout_macroClockCompactKernel_eq
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ))
    (plus : Bool) (s : MacroScene) :
    physicalSceneFullParameterizedCompactReadout base
      (physicalSceneMacroClockCompactKernel η g χ) plus s =
      ∫ e, η e.1.1 * g (s.1, (e.1.2, e.2.2)) * χ e.2
        ∂((if plus then s.2.1.1 else s.2.1.2) : Measure Edge) := by
  cases plus <;> rfl

/-- The actual retained plan has the same literal cutoff-probe readout. -/
theorem physicalSceneRetainedParameterizedCompactReadout_macroClockCompactKernel_eq
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ))
    (plus : Bool) (s : JointScene) :
    physicalSceneRetainedParameterizedCompactReadout base
      (physicalSceneMacroClockCompactKernel η g χ) plus s =
      ∫ e, η e.1.1 * g (s.1.1, (e.1.2, e.2.2)) * χ e.2
        ∂((if plus then s.2.1.1 else s.2.1.2) : Measure Edge) := by
  cases plus <;> rfl

end OTSelector.Reconstruction
