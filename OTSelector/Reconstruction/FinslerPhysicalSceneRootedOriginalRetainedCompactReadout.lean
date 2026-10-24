import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalSourceReferenceLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutMacroscopicMarginals
import OTSelector.Probability.CavityProbeReadoutPortmanteau

/-!
# Actual retained compact readouts pass both original weak stages in expectation

A fixed original auxiliary core supplies its own deterministic finite source
reference, uniformly over sample scales, actual roots and feasible environments.
Compact edge tests therefore have a genuine uniform bound. Bounded continuous
clipping passes their expectations through the separate sample and tilt limits.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-- A genuine AE bound on a continuous observable passes its expectation to the
weak limit by clipping, without any caller-supplied uniform-integrability premise. -/
theorem ae_bound_and_tendsto_integral_of_weak_uniform_bound
    {S : Type*} [MeasurableSpace S] [TopologicalSpace S]
    [OpensMeasurableSpace S] [HasOuterApproxClosed S]
    (Qn : ℕ → ProbabilityMeasure S) (Q : ProbabilityMeasure S)
    (hweak : Tendsto Qn atTop (𝓝 Q)) (f : S → ℝ) (hf : Continuous f)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n, ∀ᵐ s ∂(Qn n : Measure S), |f s| ≤ K) :
    (∀ᵐ s ∂(Q : Measure S), |f s| ≤ K) ∧
      Tendsto (fun n ↦ ∫ s, f s ∂(Qn n : Measure S)) atTop
        (𝓝 (∫ s, f s ∂(Q : Measure S))) := by
  have hQbound : ∀ᵐ s ∂(Q : Measure S), |f s| ≤ K :=
    ae_closed_set_of_physicalScene_weak_tendsto Q Qn hweak {s | |f s| ≤ K}
      (isClosed_le hf.abs continuous_const) hbound
  let gfun : S → ℝ := fun s ↦ max (-K) (min K (f s))
  have hgcont : Continuous gfun := continuous_const.max (continuous_const.min hf)
  have hgK : ∀ s, |gfun s| ≤ K := by
    intro s
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let g : BoundedContinuousFunction S ℝ := BoundedContinuousFunction.mkOfBound
    ⟨gfun, hgcont⟩ (2 * K) (fun s t ↦ by
      change dist (gfun s) (gfun t) ≤ 2 * K
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hgK s, hgK t]))
  have hclamp (s : S) (hs : |f s| ≤ K) : g s = f s := by
    change max (-K) (min K (f s)) = f s
    rw [min_eq_right (abs_le.mp hs).2, max_eq_right (abs_le.mp hs).1]
  have hleft (n : ℕ) : ∫ s, g s ∂(Qn n : Measure S) =
      ∫ s, f s ∂(Qn n : Measure S) :=
    integral_congr_ae ((hbound n).mono fun s hs ↦ hclamp s hs)
  have hright : ∫ s, g s ∂(Q : Measure S) = ∫ s, f s ∂(Q : Measure S) :=
    integral_congr_ae (hQbound.mono fun s hs ↦ hclamp s hs)
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) g
  rw [hright] at ht
  exact ⟨hQbound, ht.congr' (Eventually.of_forall fun n ↦ hleft n)⟩

section CompactReadout
variable {ι : Type*} [Fintype ι]
local notation "Endpoint" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Endpoint × Endpoint)

/-- A finite actual source reference bounds every compact edge-test readout
whose source support lies in its source window, with all target columns retained. -/
theorem abs_testIntegral_le_source_window_reference
    (π : LocalFiniteMeasure Edge) (U : Set Endpoint) (ref : Measure Endpoint)
    [IsFiniteMeasure ref] (error : ℝ≥0∞) (herrortop : error ≠ ⊤)
    (hdom : sourceOpenDominationDefectOn (π : Measure Edge) U ref error)
    (χ : C_c(Edge, ℝ)) (hχU : tsupport χ ⊆ U ×ˢ univ) :
    |LocalFiniteMeasure.testIntegral π χ| ≤
      ‖χ.toBoundedContinuousFunction‖ * (ref univ + error).toReal := by
  have hmass : (π : Measure Edge) (U ×ˢ univ) ≤ ref univ + error := by
    simpa only [univ_inter] using hdom univ isOpen_univ
  have hfinite : ref univ + error ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top ref univ, herrortop⟩
  have hzero : ∀ e : Edge, e ∉ U ×ˢ univ → χ e = 0 := by
    intro e he
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ he (hχU h))
  change |∫ e, χ e ∂(π : Measure Edge)| ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    _ ≤ ‖χ.toBoundedContinuousFunction‖ * (π : Measure Edge).real (U ×ˢ univ) := by
      simpa only [Real.norm_eq_abs] using norm_setIntegral_le_of_norm_le_const_ae
        (μ := (π : Measure Edge)) (s := U ×ˢ univ) (f := fun e ↦ χ e)
        (lt_of_le_of_lt hmass (lt_top_iff_ne_top.mpr hfinite))
        (Eventually.of_forall fun e ↦ χ.toBoundedContinuousFunction.norm_coe_le_norm e)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono hfinite hmass) (norm_nonneg _)
end CompactReadout

local instance retainedCompactReadoutStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance retainedCompactReadoutConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance retainedCompactReadoutConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance retainedCompactReadoutConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance retainedCompactReadoutPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

section RetainedReadout
variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)
local notation "Endpoint" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Endpoint × Endpoint)
local notation "PairScene" => CavityLocalScene Endpoint Endpoint
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The selected actual retained plan's compact test, with true selecting plus. -/
def physicalSceneRetainedCompactReadout (χ : C_c(Edge, ℝ)) (plus : Bool)
    (s : JointScene) : ℝ :=
  if plus then LocalFiniteMeasure.testIntegral s.2.1.1 χ
  else LocalFiniteMeasure.testIntegral s.2.1.2 χ

theorem continuous_physicalSceneRetainedCompactReadout (χ : C_c(Edge, ℝ)) (plus : Bool) :
    Continuous (physicalSceneRetainedCompactReadout base χ plus) := by
  cases plus
  · exact (LocalFiniteMeasure.continuous_testIntegral χ).comp continuous_snd.fst.snd
  · exact (LocalFiniteMeasure.continuous_testIntegral χ).comp continuous_snd.fst.fst
end RetainedReadout

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)



variable (j : ℕ)
set_option quotPrecheck false
local notation "V" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Edge" => (Point × Point)
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene Point Point
local notation "MacroScene" => V × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)
/-- Original globally feasible families produce their own retained compact-test bound and
expectation convergence through both weak stages, on the SAME actual masked laws. -/
theorem exists_original_retained_compact_readout_convergence_of_iterated
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, (κ j).IsAddHaarMeasure]
    (U : Set V) (hU : IsOpen U) (hUfinite : volume U ≠ ⊤)
    (χ : C_c(Edge, ℝ)) (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U})
    (error : ℝ≥0∞) (herror : error ≠ 0) (herrortop : error ≠ ⊤)
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (Penv : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (Penv n)]
    (ap am : ∀ (_ℓ n : ℕ), Ωn n → M → Fin (m n + 1) → ℝ)
    (hpm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ ap ℓ n z.1 z.2 k))
    (hmm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ am ℓ n z.1 z.2 k))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → M)
    (hY : ∀ n k, Measurable (fun w ↦ Y n w k))
    (weights : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (hfp : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation η₀ (weights n w) (ap ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation η₀ (weights n w) (am ℓ n w))
    (A B : Set M) (hA : MeasurableSet A) (hB : MeasurableSet B) (nearRadius : ℝ)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hnormalization : ∀ n, scale n ^ finrank ℝ (P j).seed.covector.ker = (m n : ℝ) + 1)
    (rootDomain : ℕ → Set V)
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((m n : ℝ) + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
    let Egood := D.retainedNearCarrierEvent A B nearRadius
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
      actualAllocationRootedMaskedMacroscopicSceneLaw base (Penv n) η₀
        (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n)
        H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
        Egood (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
        (coord n) (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n))
        u (by let _inst : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)
        (scale n) (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (R : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) → ∀ ψ : ℕ → ℕ,
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R) →
      (∀ ℓ n plus, ∀ᵐ s ∂(laws ℓ n : Measure JointScene),
        |physicalSceneRetainedCompactReadout base χ plus s| ≤ K) ∧
      (∀ ℓ plus,
        (∀ᵐ s ∂(Q ℓ : Measure JointScene),
          |physicalSceneRetainedCompactReadout base χ plus s| ≤ K) ∧
        Tendsto (fun n ↦ ∫ s, physicalSceneRetainedCompactReadout base χ plus s
          ∂(laws ℓ (φ ℓ n) : Measure JointScene)) atTop
          (𝓝 (∫ s, physicalSceneRetainedCompactReadout base χ plus s
            ∂(Q ℓ : Measure JointScene)))) ∧
      ∀ plus,
        (∀ᵐ s ∂(R : Measure JointScene),
          |physicalSceneRetainedCompactReadout base χ plus s| ≤ K) ∧
        Tendsto (fun ℓ ↦ ∫ s, physicalSceneRetainedCompactReadout base χ plus s
          ∂(Q (ψ ℓ) : Measure JointScene)) atTop
          (𝓝 (∫ s, physicalSceneRetainedCompactReadout base χ plus s
            ∂(R : Measure JointScene))) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨reference, hfinite, _hregular, _hac, href⟩ :=
    D.exists_original_retained_source_window_reference_of_accuracy j hF hcomplete hu ha hinj
      U hU.measurableSet hUfinite error herror
  let K := ‖χ.toBoundedContinuousFunction‖ * (reference univ + error).toReal
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  refine ⟨K, hK, ?_⟩
  dsimp only
  intro Q R φ _hφ ψ hinner houter
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  let Egood := D.retainedNearCarrierEvent A B nearRadius
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
  have hH : MeasurableSet H := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  have hE : MeasurableSet Egood :=
    D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n)
  let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
    actualAllocationRootedMaskedMacroscopicSceneLaw base (Penv n) η₀
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n) H hH Egood hE
      (coord n) (hcoord n) u hu.continuous.measurable (scale n)
      (rootDomain n) (hrootDomain n)
  let Γp := fun ℓ n ↦ physicalSceneGlobalAllocationFamily η₀ (ap ℓ n) (Y n)
  let Γm := fun ℓ n ↦ physicalSceneGlobalAllocationFamily η₀ (am ℓ n) (Y n)
  have hsp (ℓ n : ℕ) : ∀ᵐ w ∂Penv n, (Γp ℓ n w).fst = η₀ := by
    filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq (Penv n) η₀
      (ap ℓ n) (Y n) (weights n) (hfp ℓ n), hfp ℓ n] with w he hw
    dsimp only [Γp, Γm]
    rw [he, physicalSceneAllocationPlan_fst hw (Y n w)]
  have hsm (ℓ n : ℕ) : ∀ᵐ w ∂Penv n, (Γm ℓ n w).fst = η₀ := by
    filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq (Penv n) η₀
      (am ℓ n) (Y n) (weights n) (hfm ℓ n), hfm ℓ n] with w he hw
    dsimp only [Γp, Γm]
    rw [he, physicalSceneAllocationPlan_fst hw (Y n w)]
  have hphysical (n : ℕ) (Γ : Measure (M × M)) (hfst : Γ.fst = η₀) (root : V) :
      sourceOpenDominationDefectOn
        (physicalSceneRootedPlan ((Γ.restrict Egood).restrict (H ×ˢ univ))
          (coord n) u ((m n : ℝ) + 1) root) (U ×ˢ univ) reference error := by
    intro O hO
    have hb := href (scale n) (hscale n) root Γ hfst A B nearRadius O hO.measurableSet
    rw [hnormalization n] at hb
    have heq : ((Γ.restrict Egood).restrict (H ×ˢ univ)) = Γ.restrict (Egood ∩ (H ×ˢ univ)) := by
      rw [Measure.restrict_restrict (hH.prod MeasurableSet.univ), inter_comm]
    rw [← heq, Measure.fst_apply (hO.measurableSet.inter (hU.measurableSet.prod MeasurableSet.univ))] at hb
    have htest : (Prod.fst : Edge → Point) ⁻¹' (O ∩ (U ×ˢ univ)) =
        (O ∩ (U ×ˢ univ)) ×ˢ univ := by
      ext e
      simp
    simpa only [htest, coord] using hb
  have hfiniteLaw (ℓ n : ℕ) : ∀ᵐ s ∂(laws ℓ n : Measure JointScene),
      sourceOpenDominationDefectOn (s.2.1.1 : Measure Edge) (U ×ˢ univ) reference error ∧
      sourceOpenDominationDefectOn (s.2.1.2 : Measure Edge) (U ×ˢ univ) reference error := by
    exact ae_physicalSceneRootedMaskedMacroscopicSceneLaw_sourceReference base (Penv n)
      (Γp ℓ n) (Γm ℓ n)
      (measurable_physicalSceneGlobalAllocationFamily η₀ (ap ℓ n) (hpm ℓ n) (Y n) (hY n))
      (measurable_physicalSceneGlobalAllocationFamily η₀ (am ℓ n) (hmm ℓ n) (Y n) (hY n))
      H hH Egood hE (coord n) (hcoord n) u hu.continuous.measurable (scale n)
      (Y n) (hY n) (rootDomain n) (hrootDomain n) (U ×ˢ univ) (hU.prod isOpen_univ)
      reference error (by
        filter_upwards [hsp ℓ n, hsm ℓ n] with w hwp hwm root
        exact ⟨hphysical n (Γp ℓ n w) hwp root, hphysical n (Γm ℓ n w) hwm root⟩)
  have hsupport : tsupport χ ⊆ (U ×ˢ univ) ×ˢ univ :=
    fun _ he ↦ ⟨⟨hχU he, mem_univ _⟩, mem_univ _⟩
  have hbound (ℓ n : ℕ) (plus : Bool) : ∀ᵐ s ∂(laws ℓ n : Measure JointScene),
      |physicalSceneRetainedCompactReadout base χ plus s| ≤ K := by
    filter_upwards [hfiniteLaw ℓ n] with s hs
    cases plus
    · exact abs_testIntegral_le_source_window_reference s.2.1.2 (U ×ˢ univ) reference
        error herrortop hs.2 χ hsupport
    · exact abs_testIntegral_le_source_window_reference s.2.1.1 (U ×ˢ univ) reference
        error herrortop hs.1 χ hsupport
  have hinnerReadout (ℓ : ℕ) (plus : Bool) :=
    ae_bound_and_tendsto_integral_of_weak_uniform_bound (fun n ↦ laws ℓ (φ ℓ n))
      (Q ℓ) (hinner ℓ) (physicalSceneRetainedCompactReadout base χ plus)
      (continuous_physicalSceneRetainedCompactReadout base χ plus) K hK
      (fun n ↦ hbound ℓ (φ ℓ n) plus)
  exact ⟨hbound, hinnerReadout, fun plus ↦
    ae_bound_and_tendsto_integral_of_weak_uniform_bound (fun ℓ ↦ Q (ψ ℓ)) R houter
      (physicalSceneRetainedCompactReadout base χ plus)
      (continuous_physicalSceneRetainedCompactReadout base χ plus) K hK
      (fun ℓ ↦ (hinnerReadout (ψ ℓ) plus).1)⟩

end PopulationLocalPressureCore
end OTSelector.Reconstruction
