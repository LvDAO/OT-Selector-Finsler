import OTSelector.Reconstruction.OriginalIIDColoredConditionalCandidate
import OTSelector.Reconstruction.OriginalIIDWholeCoreSceneKernel
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Measurable unit-density colored kernel of the same actual matching

The normalization scale is the explicit positive root of the original intensity.
The zero-intensity branch is one fixed empty probability law. Only the limiting
kernel is modified there; no finite original sampling law is altered.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000

/-- Joint measurability of an actual homeomorphic pushforward follows from its
point map and the original s-finite diffuse-measure kernel. -/
theorem measurable_localFiniteMapHomeomorph_param
    {A X : Type*} [MeasurableSpace A] [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (e : A → X ≃ₜ X) (he : Measurable (fun p : A × X ↦ e p.1 p.2)) :
    Measurable (fun p : A × LocalFiniteMeasure X ↦ localFiniteMapHomeomorph (e p.1) p.2) := by
  apply LocalFiniteMeasure.measurable_of_testIntegral
  intro F
  let κ : Kernel (A × LocalFiniteMeasure X) X :=
    localFiniteMeasureKernel.comap Prod.snd measurable_snd
  have hf : Measurable (fun p : (A × LocalFiniteMeasure X) × X ↦ F (e p.1.1 p.2)) :=
    F.continuous.measurable.comp (he.comp (measurable_fst.fst.prodMk measurable_snd))
  have hi := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  convert hi.measurable using 1
  funext p
  exact integral_map (e p.1).continuous.measurable.aemeasurable
    F.continuous.aestronglyMeasurable

local instance iidUnitColoredKernelColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance iidUnitColoredKernelInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance iidUnitColoredKernelColoredPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance iidUnitColoredKernelPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Variable nonzero spatial dilation of the entire original colored scene is
jointly measurable, including both actual plans and the immutable inputs. -/
theorem measurable_legalMarkedInputSceneDilation_param (q : ℕ) :
    Measurable (fun p : {d : ℝ // d ≠ 0} × LegalMarkedOptimalInputScene q ↦
      legalMarkedInputSceneDilation q p.1.1 p.1.2 p.2) := by
  have hedge : Measurable (fun p : {d : ℝ // d ≠ 0} × LegalMarkedPhysicalEdge q ↦
      legalMarkedEdgeDilation q p.1.1 p.1.2 p.2) := by
    change Measurable (fun p : {d : ℝ // d ≠ 0} × LegalMarkedPhysicalEdge q ↦
      ((p.1.1 • p.2.1.1,p.2.1.2),(p.1.1 • p.2.2.1,p.2.2.2)))
    fun_prop
  have hinput : Measurable (fun p : {d : ℝ // d ≠ 0} × LegalColoredInputPoint q ↦
      legalColoredInputDilation q p.1.1 p.1.2 p.2) := by
    change Measurable (fun p : {d : ℝ // d ≠ 0} × LegalColoredInputPoint q ↦
      ((p.1.1 • p.2.1.1,p.2.1.2),p.2.2))
    fun_prop
  have hE := measurable_localFiniteMapHomeomorph_param
    (fun d : {d : ℝ // d ≠ 0} ↦ legalMarkedEdgeDilation q d.1 d.2) hedge
  have hI := measurable_localFiniteMapHomeomorph_param
    (fun d : {d : ℝ // d ≠ 0} ↦ legalColoredInputDilation q d.1 d.2) hinput
  exact ((hE.comp (measurable_fst.prodMk measurable_snd.fst.fst)).prodMk
    (hE.comp (measurable_fst.prodMk measurable_snd.fst.snd))).prodMk
      (hI.comp (measurable_fst.prodMk measurable_snd.snd))

/-- The normalization uses the explicit positive q-th root; the harmless unit
value off the positive-intensity branch only defines a total point map. -/
def originalIIDUnitDilation (q : ℕ) (θ : ℝ) : ℝ :=
  if 0 < θ then θ ^ (q : ℝ)⁻¹ else 1

theorem originalIIDUnitDilation_pos (q : ℕ) (θ : ℝ) : 0 < originalIIDUnitDilation q θ := by
  unfold originalIIDUnitDilation
  split_ifs with h
  · exact Real.rpow_pos_of_pos h _
  · exact zero_lt_one

theorem measurable_originalIIDUnitDilation (q : ℕ) : Measurable (originalIIDUnitDilation q) := by
  unfold originalIIDUnitDilation
  exact ((Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ (q : ℝ)⁻¹)).measurable).piecewise
    (measurableSet_lt measurable_const measurable_id) measurable_const

theorem originalIIDUnitDilation_pow (q : ℕ) (hq : 0 < q) {θ : ℝ} (hθ : 0 < θ) :
    originalIIDUnitDilation q θ ^ q = θ := by
  simp only [originalIIDUnitDilation,hθ,↓reduceIte]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← Real.rpow_natCast,← Real.rpow_mul hθ.le,inv_mul_cancel₀ hq0,Real.rpow_one]

/-- The unit-density readout uses one explicit scale at each root and the
fixed empty colored scene at every nonpositive root intensity. -/
def originalIIDUnitColoredReadout {C : Type*} (q : ℕ) (θ : C → ℝ)
    (p : C × OriginalIIDMaskedMacroInputScene (Fin q)) : LegalMarkedOptimalInputScene q :=
  if 0 < θ p.1 then
    legalMarkedInputSceneDilation q (originalIIDUnitDilation q (θ p.1))
      (originalIIDUnitDilation_pos q (θ p.1)).ne' (originalColoredScene q p.2)
  else originalColoredScene q (originalIIDEmptyInputScene q)

theorem measurable_originalIIDUnitColoredReadout {C : Type*} [MeasurableSpace C]
    (q : ℕ) (θ : C → ℝ) (hθ : Measurable θ) :
    Measurable (originalIIDUnitColoredReadout q θ) := by
  have hd : Measurable (fun c ↦ originalIIDUnitDilation q (θ c)) :=
    (measurable_originalIIDUnitDilation q).comp hθ
  have hsub : Measurable (fun c ↦ (⟨originalIIDUnitDilation q (θ c),
      (originalIIDUnitDilation_pos q (θ c)).ne'⟩ : {d : ℝ // d ≠ 0})) :=
    hd.subtype_mk
  have hfull := (measurable_legalMarkedInputSceneDilation_param q).comp
    ((hsub.comp measurable_fst).prodMk
      ((continuous_originalColoredScene q).measurable.comp measurable_snd))
  exact hfull.piecewise (measurableSet_lt measurable_const (hθ.comp measurable_fst)) measurable_const

/-- The normalized kernel is a measurable pushforward of the same root and
its same actual conditional scene; the macroscopic root distribution is retained. -/
def originalIIDUnitColoredSceneKernel {C : Type*} [MeasurableSpace C]
    (q : ℕ) (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) :
    Kernel C (LegalMarkedOptimalInputScene q) :=
  ((Kernel.deterministic (id : C → C) measurable_id) ×ₖ Λ).mapOfMeasurable
    (originalIIDUnitColoredReadout q θ) (measurable_originalIIDUnitColoredReadout q θ hθ)

instance originalIIDUnitColoredSceneKernelMarkov {C : Type*} [MeasurableSpace C]
    (q : ℕ) (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ] :
    IsMarkovKernel (originalIIDUnitColoredSceneKernel q θ hθ Λ) :=
by
  unfold originalIIDUnitColoredSceneKernel
  rw [Kernel.mapOfMeasurable_eq_map]
  exact Kernel.IsMarkovKernel.map _ (measurable_originalIIDUnitColoredReadout q θ hθ)

/-- Pointwise, the measurable kernel is exactly the original conditional law
pushed by its own deterministic root readout. -/
theorem originalIIDUnitColoredSceneKernel_apply {C : Type*} [MeasurableSpace C]
    (q : ℕ) (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ] (c : C) :
    originalIIDUnitColoredSceneKernel q θ hθ Λ c =
      (Λ c).map (fun s ↦ originalIIDUnitColoredReadout q θ (c,s)) := by
  rw [originalIIDUnitColoredSceneKernel,Kernel.mapOfMeasurable_eq_map,
    Kernel.map_apply _ (measurable_originalIIDUnitColoredReadout q θ hθ),Kernel.prod_apply]
  simp only [Kernel.deterministic_apply,id_eq]
  rw [Measure.dirac_prod,Measure.map_map (measurable_originalIIDUnitColoredReadout q θ hθ)
    measurable_prodMk_left]
  rfl

/-- At a positive original root intensity the kernel is the literal same
coloring-then-dilation probability law, with no measurable choice of scale. -/
theorem originalIIDUnitColoredSceneKernel_eq_positive {C : Type*} [MeasurableSpace C]
    (q : ℕ) (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ]
    (c : C) (hc : 0 < θ c) :
    originalIIDUnitColoredSceneKernel q θ hθ Λ c =
      (originalUnitColoredLaw q ⟨Λ c,inferInstance⟩ (originalIIDUnitDilation q (θ c))
        (originalIIDUnitDilation_pos q (θ c)).ne' : Measure (LegalMarkedOptimalInputScene q)) := by
  rw [originalIIDUnitColoredSceneKernel_apply]
  change (Λ c).map (fun s ↦ originalIIDUnitColoredReadout q θ (c,s)) =
    ((Λ c).map (originalColoredScene q)).map _
  rw [Measure.map_map (continuous_legalMarkedInputSceneDilation q _ _).measurable
    (continuous_originalColoredScene q).measurable]
  congr 1
  funext s
  simp only [originalIIDUnitColoredReadout,hc,↓reduceIte,Function.comp_def]

/-- At zero or negative intensity the limit kernel is one fixed probability
law. Unit-PPP or weighted matching assertions are not made on that branch. -/
theorem originalIIDUnitColoredSceneKernel_eq_nonpositive {C : Type*} [MeasurableSpace C]
    (q : ℕ) (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ]
    (c : C) (hc : θ c ≤ 0) :
    originalIIDUnitColoredSceneKernel q θ hθ Λ c =
      Measure.dirac (originalColoredScene q (originalIIDEmptyInputScene q)) := by
  rw [originalIIDUnitColoredSceneKernel_apply]
  have heq : (fun s ↦ originalIIDUnitColoredReadout q θ (c,s)) =
      fun _ ↦ originalColoredScene q (originalIIDEmptyInputScene q) := by
    funext s
    simp only [originalIIDUnitColoredReadout,not_lt.mpr hc,↓reduceIte]
  rw [heq,Measure.map_const,measure_univ,one_smul]

/-- Root-dependent physical normalization does not renormalize the original
macroscopic root measure, including its original mass on the retained core. -/
theorem originalIIDUnitColoredSceneKernel_joint_fst {C : Type*} [MeasurableSpace C]
    (q : ℕ) (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ]
    (η : Measure C) [SFinite η] :
    (η ⊗ₘ originalIIDUnitColoredSceneKernel q θ hθ Λ).fst = η :=
  Measure.fst_compProd _ _

/-- The proved unit-density matching properties, on one fixed probability law. -/
def OriginalIIDUnitColoredProperties (q : ℕ) (gap : ℝ) (α β : Measure ℝ)
    (law : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) : Prop :=
  (∀ v, MeasurePreserving (legalMarkedInputSceneReroot q v)
    (law : Measure (LegalMarkedOptimalInputScene q)) law) ∧
    (∀ᵐ s ∂(law : Measure (LegalMarkedOptimalInputScene q)),
      s.1.1 = s.1.2 ∧ IsFullOriginalInputMatching q s ∧
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        gap / 2 ≤ e.2.2 - e.1.2 ∧ e.1.2 < e.2.2) ∧
    (∀ S : ℝ, 0 < S → ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
      (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
        x.1 ∉ haarRootCube (Fin q) S → F (x,c) = 0) →
      (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(law : Measure _)) =
        ∫ b, legalInputBlockLaplace (fun x ↦ F (x,0)) (fun x ↦ F (x,1)) b
          ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) ∧
    IsProbabilityMeasure (legalMarkedJointPalm q law) ∧
    (legalMarkedJointPalm q law).map (fun m ↦ m.1.1) = α ∧
    (legalMarkedJointPalm q law).map (fun m ↦ m.1.2) = β

/-- One original full-measure profile set suffices for all normalized-law
properties; no root-dependent choice of law or uncountable intersection is used. -/
theorem ae_originalIIDUnitColoredSceneKernel_properties
    {C : Type*} [MeasurableSpace C] (η : Measure C)
    (q : ℕ) (hq : 0 < q) (gap : ℝ) (hgap : 0 < gap)
    (θ : C → ℝ) (hθ : Measurable θ)
    (α β : C → Measure ℝ) [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (input : C → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ]
    (h : ∀ᵐ c ∂η, OriginalIIDConditionalMatchingProfile gap (θ c) (α c) (β c) (input c) (Λ c)) :
    ∀ᵐ c ∂η, 0 < θ c → OriginalIIDUnitColoredProperties q gap (α c) (β c)
      ⟨originalIIDUnitColoredSceneKernel q θ hθ Λ c,inferInstance⟩ := by
  filter_upwards [h] with c hc hpos
  have hlaw : (⟨originalIIDUnitColoredSceneKernel q θ hθ Λ c,inferInstance⟩ :
      ProbabilityMeasure (LegalMarkedOptimalInputScene q)) =
      originalUnitColoredLaw q ⟨Λ c,hc.1⟩ (originalIIDUnitDilation q (θ c))
        (originalIIDUnitDilation_pos q (θ c)).ne' :=
    ProbabilityMeasure.toMeasure_injective
      (originalIIDUnitColoredSceneKernel_eq_positive q θ hθ Λ c hpos)
  rw [hlaw]
  exact originalUnitColoredLaw_properties q gap (θ c) hgap hpos (α c) (β c)
    (input c) (Λ c) hc _ (originalIIDUnitDilation_pos q (θ c))
      (originalIIDUnitDilation_pow q hq hpos)

/-- Both plan copies in the normalized kernel come from the same actual root's
pair law with the explicit theta-root spatial dilation. -/
theorem originalIIDUnitColoredSceneKernel_pairLaw {C : Type*} [MeasurableSpace C]
    (q : ℕ) (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ]
    (c : C) (hc : 0 < θ c) :
    (originalIIDUnitColoredSceneKernel q θ hθ Λ c).map Prod.fst =
      ((Λ c).map Prod.fst).map (originalPairSceneDilation q (originalIIDUnitDilation q (θ c))
        (originalIIDUnitDilation_pos q (θ c)).ne') := by
  rw [originalIIDUnitColoredSceneKernel_eq_positive q θ hθ Λ c hc]
  exact originalUnitColoredLaw_pairLaw q _ _ _

/-- The measurable normalized kernel's Palm has exactly the Jacobian times its
same raw root Palm, with both clocks fixed and the full displacement scaled. -/
theorem originalIIDUnitColoredSceneKernel_palm_dilation {C : Type*} [MeasurableSpace C]
    (q : ℕ) (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ]
    (c : C) (hc : 0 < θ c)
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v)
      ((Λ c).map Prod.fst) ((Λ c).map Prod.fst))
    (hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)} ∂(Λ c).map Prod.fst) < ∞) :
    cubePalm (Fin q) (physicalScenePairCampbell
      ((originalIIDUnitColoredSceneKernel q θ hθ Λ c).map Prod.fst)) =
      ENNReal.ofReal |(originalIIDUnitDilation q (θ c) ^ q)⁻¹| •
        (cubePalm (Fin q) (physicalScenePairCampbell ((Λ c).map Prod.fst))).map
          (legalPairMarkDilation q (originalIIDUnitDilation q (θ c))) := by
  rw [originalIIDUnitColoredSceneKernel_pairLaw q θ hθ Λ c hc]
  exact original_raw_palm_dilation q _ hstat hunit _ _

section UnitColoredKernelSupportedActual
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

local instance iidUnitColoredKernelSupportedMatchingCorePointStandardBorel (q : ℕ) : StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidUnitColoredKernelSupportedMatchingCoreConfigTopology (q : ℕ) :
    TopologicalSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueTopology _
local instance iidUnitColoredKernelSupportedMatchingCoreConfigBorel (q : ℕ) :
    BorelSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueBorelSpace
local instance iidUnitColoredKernelSupportedMatchingCoreConfigPolish (q : ℕ) :
    PolishSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vaguePolishSpace
local instance iidUnitColoredKernelSupportedMatchingCoreInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidUnitColoredKernelSupportedMatchingCorePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidUnitColoredKernelSupportedMatchingCoreInputNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := ⟨⟨0,inferInstance⟩⟩
local instance iidUnitColoredKernelSupportedMatchingCorePlanNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩

local instance iidUnitColoredKernelSupportedMatchingCoreMacroPairPolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance iidUnitColoredKernelSupportedMatchingCoreSceneBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidUnitColoredKernelSupportedMatchingCoreMacroBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance iidUnitColoredKernelSupportedMatchingCoreMacroPairBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance

local instance iidUnitColoredKernelSupportedMatchingCoreScenePolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidUnitColoredKernelSupportedMatchingCoreSceneStandardBorel (q : ℕ) :
    StandardBorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidUnitColoredKernelSupportedMatchingCoreTaggedSceneBorel (q : ℕ) :
    BorelSpace ((Fin q → ℝ) × OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance






include hF hcomplete hu ha hinj in
omit [∀ j, SigmaFinite (κ j)] [IsProbabilityMeasure μ] in
/-- The exact original Haar-coordinate intensity has a globally measurable
coordinate expression, independent of any root representative selection. -/
theorem measurable_originalIIDCoordinateIntensity (j : ℕ) :
    let S := (P j).seed
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    Measurable (fun c : Fin (finrank ℝ S.covector.ker) → ℝ ↦
      (originalSeedCoordinateHaarFactor S (κ j) : ℝ) *
        (populationSeedPieceHaarDensity P a κ (μ.map a) j (e.symm c)).toReal) := by
  intro S e
  let _iidUnitIntensityMetric : MetricSpace M := F.metricSpace
  let _iidUnitIntensityProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _iidUnitIntensityPolish : PolishSpace M := inferInstance
  let _iidUnitIntensityRootBorel : BorelSpace (ℚ → M) := inferInstance
  exact (((measurable_populationSeedPieceHaarDensity P a κ (μ.map a)
    hF hcomplete hu ha hinj j).comp e.symm.continuous.measurable).ennreal_toReal).const_mul _

include hcore hrecovery hκ horder hbalance hA hB hμ hν hreg hμreg hface hgap hdist

/-- The actual whole-core scene kernel has a measurable unit-density colored
pushforward with explicit original-intensity scale. No finite sampling law or
root mass is changed, and no measurable readout or desired-law oracle is assumed. -/
theorem PopulationLocalPressureCore.original_supported_whole_core_unit_colored_kernel
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
            (volume : Measure V).restrict (originalMacroFrameOwner q K j) ⊗ₘ originalIIDFrameSceneKernel Q j) ∧
          ∃ (Ξ : Kernel V (LegalMarkedOptimalInputScene q)) (hΞ : IsMarkovKernel Ξ),
            letI := hΞ
            (∀ c ∈ K, 0 < θ c → Ξ c =
              ((Λ c).map (originalColoredScene q)).map
                (legalMarkedInputSceneDilation q (originalIIDUnitDilation q (θ c))
                  (originalIIDUnitDilation_pos q (θ c)).ne')) ∧
            (∀ c ∈ K, θ c ≤ 0 → Ξ c =
              Measure.dirac (originalColoredScene q (originalIIDEmptyInputScene q))) ∧
            (∀ c, c ∉ K → Ξ c =
              Measure.dirac (originalColoredScene q (originalIIDEmptyInputScene q))) ∧
            (∀ᵐ c ∂(volume : Measure V).restrict K, 0 < θ c →
              OriginalIIDUnitColoredProperties q gap (α c) (β c) ⟨Ξ c,inferInstance⟩) ∧
            ((volume : Measure V).restrict K ⊗ₘ Ξ).fst = (volume : Measure V).restrict K := by
  intro C S q V X T Scene Macro R e φ K scale mask ref θ α β cost hcost hmask hφ huM
  let _iidUnitKernelMetric : MetricSpace M := F.metricSpace
  let _iidUnitKernelProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _iidUnitKernelPolish : PolishSpace M := inferInstance
  let _iidUnitKernelRootBorel : BorelSpace (ℚ → M) := inferInstance
  have hRset : MeasurableSet (R '' C.roots) :=
    D.haar.measurable_cell_label_image hcomplete i C.roots_compact.measurableSet Subset.rfl
  have hKcore : MeasurableSet K :=
    e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hRset
  obtain ⟨Γ,hΓ,m,hm,Q,hweak,Λ,hΛ,hOwner,hOutside,hProfile,hRoot,hSum⟩ :=
    D.original_supported_whole_core_scene_kernel
      (hcore := hcore) (hrecovery := hrecovery) (hF := hF) (hcomplete := hcomplete)
      (hu := hu) (ha := ha) (hinj := hinj) (hκ := hκ) (horder := horder)
      (hbalance := hbalance) (hA := hA) (hB := hB) (hμ := hμ) (hν := hν)
      (hreg := hreg) (hμreg := hμreg) (hface := hface) (hgap := hgap) (hdist := hdist)
      γ originalGap bins U retentionError splitError Ksupport hK hμK hνK f g ε probeError hdata t hdim i
  let θcoord : V → ℝ := fun c ↦ (originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) *
    (populationSeedPieceHaarDensity P a κ (μ.map a) C.seedIndex (e.symm c)).toReal
  have hθcoord : Measurable θcoord :=
    measurable_originalIIDCoordinateIntensity hF hcomplete hu ha hinj hκ C.seedIndex
  have hrecover (z) (hz : z ∈ C.roots) : ref (e (R z)) = z := by
    dsimp only [ref]
    rw [e.symm_apply_apply]
    exact (D.haar.intensity i).root_identity z ((D.haar.intensity_roots i).symm ▸ hz)
  have hcoordinate : ∀ c ∈ K, θcoord c = θ c := by
    intro c hc
    obtain ⟨w,⟨z,hz,hRz⟩,hew⟩ := hc
    have hec : e (R z) = c :=
      (congrArg e (show R z = w from hRz)).trans (show e w = c from hew)
    have hcoord : e (R (ref c)) = c := by rw [← hec,hrecover z hz]
    have hRref : R (ref c) = e.symm c := by
      apply e.injective
      simpa only [e.apply_symm_apply] using hcoord
    change (originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) *
      (populationSeedPieceHaarDensity P a κ (μ.map a) C.seedIndex (e.symm c)).toReal =
        (originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) *
          (populationSeedPieceHaarDensity P a κ (μ.map a) C.seedIndex (R (ref c))).toReal
    rw [hRref]
  let θunit : V → ℝ := K.indicator θcoord
  have hθunit : Measurable θunit := hθcoord.indicator hKcore
  have heq : ∀ c ∈ K, θunit c = θ c := by
    intro c hc
    exact (Set.indicator_of_mem hc θcoord).trans (hcoordinate c hc)
  let Ξ := originalIIDUnitColoredSceneKernel q θunit hθunit Λ
  have hΞ : IsMarkovKernel Ξ := inferInstance
  have hposq : 0 < q := original_seed_transverse_finrank_pos S hdim
  have hProfileUnit : ∀ᵐ c ∂(volume : Measure V).restrict K,
      OriginalIIDConditionalMatchingProfile gap (θunit c) (α c) (β c) (Γ c) (Λ c) := by
    filter_upwards [hProfile,ae_restrict_mem hKcore] with c hc hmem
    change OriginalIIDConditionalMatchingProfile gap (θ c) (α c) (β c) (Γ c) (Λ c) at hc
    simpa only [heq c hmem] using hc
  have hProps := ae_originalIIDUnitColoredSceneKernel_properties ((volume : Measure V).restrict K)
    q hposq gap hgap θunit hθunit α β Γ Λ hProfileUnit
  refine ⟨Γ,hΓ,m,hm,Q,hweak,Λ,hΛ,hOwner,hOutside,hProfile,hRoot,hSum,Ξ,hΞ,?_,?_,?_,?_,?_⟩
  · intro c hc hp
    have hp' : 0 < θunit c := by simpa only [heq c hc] using hp
    have hread := originalIIDUnitColoredSceneKernel_eq_positive q θunit hθunit Λ c hp'
    change Ξ c = ((Λ c).map (originalColoredScene q)).map
      (legalMarkedInputSceneDilation q (originalIIDUnitDilation q (θunit c))
        (originalIIDUnitDilation_pos q (θunit c)).ne') at hread
    exact hread.trans (congrArg (fun x : ℝ ↦ ((Λ c).map (originalColoredScene q)).map
      (legalMarkedInputSceneDilation q (originalIIDUnitDilation q x)
        (originalIIDUnitDilation_pos q x).ne')) (heq c hc))
  · intro c hc hz
    exact originalIIDUnitColoredSceneKernel_eq_nonpositive q θunit hθunit Λ c
      (by simpa only [heq c hc] using hz)
  · intro c hc
    exact originalIIDUnitColoredSceneKernel_eq_nonpositive q θunit hθunit Λ c
      (by simp only [θunit,Set.indicator_of_notMem hc,le_refl])
  · filter_upwards [hProps,ae_restrict_mem hKcore] with c hc hmem hp
    exact hc (by simpa only [heq c hmem] using hp)
  · exact originalIIDUnitColoredSceneKernel_joint_fst q θunit hθunit Λ _

end UnitColoredKernelSupportedActual
end OTSelector.Reconstruction
