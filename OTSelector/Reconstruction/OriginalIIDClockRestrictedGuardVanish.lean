import OTSelector.Reconstruction.OriginalIIDActualTaggedEnergyLiminf
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Original clock-restricted Taylor guards: exact endpoint/core/spatial
decomposition and unchanged Haar normalization on measurable macro cores. -/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- Normalizing a root domain contained in a measured macro core preserves at
most that core's original Lebesgue measure. The true scale Jacobian cancels N. -/
theorem map_cavityRoot_normalized_le_core {q : ℕ}
    (scale N : ℝ) (hs : 0 < scale) (hN : 0 < N) (hnorm : scale ^ q = N)
    {roots K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (hroots : roots ⊆ (fun z ↦ scale⁻¹ • z) ⁻¹' K) :
    (cavityRootMeasure volume roots N).map (fun z ↦ scale⁻¹ • z) ≤
      (volume : Measure (Fin q → ℝ)).restrict K := by
  have hm : Measurable (fun z : Fin q → ℝ ↦ scale⁻¹ • z) := by fun_prop
  have hmap : (volume : Measure (Fin q → ℝ)).map (fun z ↦ scale⁻¹ • z) =
      ENNReal.ofReal N • (volume : Measure (Fin q → ℝ)) := by
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hs.ne')]
    simp only [Module.finrank_fin_fun, inv_pow, inv_inv, hnorm, abs_of_pos hN]
  calc
    _ ≤ (cavityRootMeasure volume ((fun z ↦ scale⁻¹ • z) ⁻¹' K) N).map
        (fun z ↦ scale⁻¹ • z) := by
      apply Measure.map_mono _ hm
      exact smul_le_smul_left _ ((volume : Measure (Fin q → ℝ)).restrict_mono_set hroots)
    _ = _ := by
      rw [cavityRootMeasure, Measure.map_smul, ← Measure.restrict_map hm hK,
        hmap, Measure.restrict_smul, smul_smul,
        ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hN).ne' ENNReal.ofReal_ne_top,
        one_smul]

/-- Every nonnegative normalized-root observation is dominated on any
measurable subcore by its unchanged original macro-core integral. -/
theorem lintegral_cavityRoot_normalized_le_core {q : ℕ}
    (scale N : ℝ) (hs : 0 < scale) (hN : 0 < N) (hnorm : scale ^ q = N)
    {roots K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (hroots : roots ⊆ (fun z ↦ scale⁻¹ • z) ⁻¹' K)
    (f : (Fin q → ℝ) → ℝ≥0∞) :
    (∫⁻ root, f (scale⁻¹ • root) ∂cavityRootMeasure volume roots N) ≤
      ∫⁻ c in K, f c ∂volume := by
  rw [← (measurableEmbedding_const_smul₀ (inv_ne_zero hs.ne')).lintegral_map]
  exact lintegral_mono' (map_cavityRoot_normalized_le_core
    scale N hs hN hnorm hK hroots) le_rfl

/-- A bounded source and an escaped rooted target give a genuine long edge.
The complete transverse displacement is retained. -/
theorem rooted_spatial_bad_subset_longEdge
    {ι M : Type*} [Fintype ι] (coord : M → (ι → ℝ)) (root : ι → ℝ)
    (U : Set (ι → ℝ)) (W R : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) (hRW : W ≤ R) :
    {p : M × M | coord p.1-root ∈ U} ∩
        {p | ¬(‖coord p.1-root‖ ≤ R ∧ ‖coord p.2-root‖ ≤ R)} ⊆
      {p | coord p.1-root ∈ U} ∩
        {p | ENNReal.ofReal ((R-W)^2) ≤ ENNReal.ofReal (‖coord p.2-coord p.1‖^2)} := by
  intro p hp
  have hx : ‖coord p.1-root‖ ≤ W := hW _ hp.1
  have hy : R < ‖coord p.2-root‖ := lt_of_not_ge (fun h ↦ hp.2 ⟨hx.trans hRW,h⟩)
  have htriangle : ‖coord p.2-root‖ ≤ ‖coord p.2-coord p.1‖ + ‖coord p.1-root‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (coord p.2-coord p.1) (coord p.1-root)
  refine ⟨hp.1, ENNReal.ofReal_le_ofReal ?_⟩
  have hdiff : R-W ≤ ‖coord p.2-coord p.1‖ := by linarith
  exact sq_le_sq₀ (sub_nonneg.mpr hRW) (norm_nonneg _) |>.mpr hdiff

/-- The bounded endpoint-core mass is jointly measurable in the original
sample and the original macro root. -/
theorem measurable_kernel_endpoint_core_escape
    {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M] {q : ℕ}
    (κ : Kernel Ω (M × M)) [IsSFiniteKernel κ]
    (endpoint : M × M → M) (hend : Measurable endpoint)
    {H : Set M} (hH : MeasurableSet H)
    (φ : M → Fin q → ℝ) (hφ : Measurable φ)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (R scale : ℝ) :
    Measurable (fun p : Ω × (Fin q → ℝ) ↦
      κ p.1 (endpoint ⁻¹' (H ∩ φ ⁻¹' rootCoreEscapeSet K R scale p.2))) := by
  let T : Set ((Ω × (Fin q → ℝ)) × (M × M)) :=
    {p | endpoint p.2 ∈ H ∧ φ (endpoint p.2) ∉ K ∧
      ‖scale • (φ (endpoint p.2)-p.1.2)‖ ≤ R}
  have hp : Measurable (fun p : (Ω × (Fin q → ℝ)) × (M × M) ↦ endpoint p.2) :=
    hend.comp measurable_snd
  have hT : MeasurableSet T :=
    (hH.preimage hp).inter ((hK.compl.preimage (hφ.comp hp)).inter
      (measurableSet_Iic.preimage
        ((((hφ.comp hp).sub measurable_fst.snd).const_smul scale).norm)))
  have hm := Kernel.measurable_kernel_prodMk_left
    (κ := κ.comap Prod.fst measurable_fst) hT
  convert hm using 1
  funext p
  congr 1
  ext e
  simp only [rootCoreEscapeSet, T, mem_preimage, mem_inter_iff, mem_compl_iff,
    Metric.mem_closedBall, dist_zero_right, Set.mem_ofPred_eq]

/-- The actual endpoint escape averaged in sample/root order is bounded by
the same actual finite macro-core escape in macro/sample order. This bridges
the original Haar root law to the proved exterior-collar limit. -/
theorem lintegral_originalIID_core_escape_rootAverage_le_macro
    {M : Type*} [MeasurableSpace M] {q n : ℕ}
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost)) (selectionScale : ℝ)
    {H : Set M} (hH : MeasurableSet H)
    (φ : M → Fin q → ℝ) (hφ : Measurable φ)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (R scale : ℝ)
    (hs : 0 < scale) (hnorm : scale ^ q = ((n+1 : ℕ) : ℝ))
    (roots : Set (Fin q → ℝ))
    (hroots : roots ⊆ (fun z ↦ scale⁻¹ • z) ⁻¹' K) (color : Fin 2) :
    (∫⁻ ξ, ∫⁻ root,
      originalIIDMaskedCoreEscapeMass cost selectionScale H φ K R scale color
        (scale⁻¹ • root) ξ
      ∂cavityRootMeasure volume roots ((n+1 : ℕ) : ℝ)
      ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤
      ∫⁻ c in K, ∫⁻ ξ,
        originalIIDMaskedCoreEscapeMass cost selectionScale H φ K R scale color c ξ
      ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n+1) ↦ ν)) ∂volume := by
  let Ω := (Fin (n+1) → M) × (Fin (n+1) → M)
  let κ : Kernel Ω (M × M) :=
    ⟨originalIIDOptimalPhysicalPlan cost selectionScale,
      measurable_originalIIDOptimalPhysicalPlan cost hcost selectionScale⟩
  letI : IsMarkovKernel κ := ⟨fun ξ ↦ by
    change IsProbabilityMeasure (originalIIDOptimalPhysicalPlan cost selectionScale ξ)
    infer_instance⟩
  let κH := κ.restrict (hH.prod MeasurableSet.univ)
  have hm : Measurable (fun p : Ω × (Fin q → ℝ) ↦
      originalIIDMaskedCoreEscapeMass cost selectionScale H φ K R scale color p.2 p.1) := by
    have hend : Measurable (if color = 0 then (Prod.fst : M × M → M) else Prod.snd) := by
      split_ifs <;> fun_prop
    exact (measurable_kernel_endpoint_core_escape κH _ hend hH φ hφ hK R scale).const_mul _
  calc
    _ ≤ ∫⁻ ξ, ∫⁻ c in K,
        originalIIDMaskedCoreEscapeMass cost selectionScale H φ K R scale color c ξ
      ∂volume ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n+1) ↦ ν)) := by
      apply lintegral_mono
      intro ξ
      exact lintegral_cavityRoot_normalized_le_core scale ((n+1 : ℕ) : ℝ) hs
        (by positivity) hnorm hK hroots _
    _ = _ := lintegral_lintegral_swap hm.aemeasurable

/-- Every actual fixed physical event in a moving source window is jointly
measurable in its sample and root. -/
theorem measurable_kernel_rooted_event_mass
    {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    {ι : Type*} [Fintype ι] (κ : Kernel Ω (M × M)) [IsSFiniteKernel κ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U)
    {B : Set (M × M)} (hB : MeasurableSet B) (N : ℝ) :
    Measurable (fun p : Ω × (ι → ℝ) ↦ ENNReal.ofReal N *
      κ p.1 ({e | coord e.1-p.2 ∈ U} ∩ B)) := by
  let T : Set ((Ω × (ι → ℝ)) × (M × M)) :=
    {p | coord p.2.1-p.1.2 ∈ U ∧ p.2 ∈ B}
  have hT : MeasurableSet T :=
    (hU.preimage (((hcoord.comp measurable_snd.fst).sub measurable_fst.snd))).inter
      (hB.preimage measurable_snd)
  exact (Kernel.measurable_kernel_prodMk_left
    (κ := κ.comap Prod.fst measurable_fst) hT).const_mul _

/-- Full long-edge mass is precisely the unchanged original finite event mass. -/
theorem physicalSceneRootedPlan_longEdgeWindow_eq_mass
    {M ι : Type*} [MeasurableSpace M] [Fintype ι]
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (root : ι → ℝ)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) (threshold : ℝ≥0∞) :
    physicalSceneRootedPlan Γ coord u N root (physicalSceneLongEdgeWindow U threshold) =
      ENNReal.ofReal N * Γ ({p | coord p.1-root ∈ U} ∩
        {p | threshold ≤ ENNReal.ofReal (‖coord p.2-coord p.1‖^2)}) := by
  unfold physicalSceneRootedPlan
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_physicalSceneRootedObservation coord hcoord u hu root)
      (measurableSet_physicalSceneLongEdgeWindow hU threshold)]
  congr 2
  ext p
  simp only [mem_preimage, physicalSceneLongEdgeWindow, physicalSceneRootedObservation,
    mem_inter_iff, Set.mem_ofPred_eq, sub_sub_sub_cancel_right]

/-- The source-window target-seed defect is exactly the same real crossing
readout before either root or sample is integrated. -/
theorem rootedPhysicalSeedTargetEscapeMass_source_eq_mass
    {M ι : Type*} [MeasurableSpace M] [Fintype ι]
    (Γ : Measure (M × M)) {H : Set M} (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (N : ℝ) (root : ι → ℝ) {U : Set (ι → ℝ)} (hU : MeasurableSet U) :
    rootedPhysicalSeedTargetEscapeMass Γ H coord N U 0 root =
      ENNReal.ofReal N * (Γ.restrict (H ×ˢ univ))
        ({p | coord p.1-root ∈ U} ∩ (univ ×ˢ Hᶜ)) := by
  have hW : MeasurableSet {p : M × M | coord p.1-root ∈ U} :=
    hU.preimage ((hcoord.comp measurable_fst).sub measurable_const)
  rw [rootedPhysicalSeedTargetEscapeMass]
  simp only [ite_true]
  have hInd : (fun e : M × M ↦ U.indicator (fun _ ↦ (1 : ℝ≥0∞)) (coord e.1-root)) =
      {p : M × M | coord p.1-root ∈ U}.indicator (fun _ ↦ 1) := by
    funext e
    by_cases he : coord e.1-root ∈ U <;> simp [he]
  rw [cavityRootWindowReadout, hInd, lintegral_indicator_fun_one hW,
    Measure.restrict_apply hW,
    Measure.restrict_apply (hW.inter (MeasurableSet.univ.prod hH.compl))]
  congr 2
  ext p
  simp only [mem_inter_iff, mem_prod, mem_univ, and_true, true_and]
  tauto

private theorem lintegral_lintegral_add_four
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    (μ : Measure Ω) (ν : Measure V) [SFinite ν]
    (f₀ f₁ f₂ f₃ : Ω × V → ℝ≥0∞)
    (h₀ : Measurable f₀) (h₁ : Measurable f₁) (h₂ : Measurable f₂) :
    (∫⁻ ξ, ∫⁻ root, f₀ (ξ,root)+f₁ (ξ,root)+f₂ (ξ,root)+f₃ (ξ,root) ∂ν ∂μ) =
      (∫⁻ ξ, ∫⁻ root, f₀ (ξ,root) ∂ν ∂μ) +
      (∫⁻ ξ, ∫⁻ root, f₁ (ξ,root) ∂ν ∂μ) +
      (∫⁻ ξ, ∫⁻ root, f₂ (ξ,root) ∂ν ∂μ) +
      (∫⁻ ξ, ∫⁻ root, f₃ (ξ,root) ∂ν ∂μ) := by
  have hi (ξ : Ω) :
      (∫⁻ root, f₀ (ξ,root)+f₁ (ξ,root)+f₂ (ξ,root)+f₃ (ξ,root) ∂ν) =
        (∫⁻ root, f₀ (ξ,root) ∂ν) + (∫⁻ root, f₁ (ξ,root) ∂ν) +
        (∫⁻ root, f₂ (ξ,root) ∂ν) + (∫⁻ root, f₃ (ξ,root) ∂ν) := by
    have h0 : Measurable (fun root ↦ f₀ (ξ,root)) :=
      h₀.comp (measurable_const.prodMk measurable_id)
    have h01 : Measurable (fun root ↦ f₀ (ξ,root)+f₁ (ξ,root)) :=
      h0.add (h₁.comp (measurable_const.prodMk measurable_id))
    have h012 : Measurable (fun root ↦ f₀ (ξ,root)+f₁ (ξ,root)+f₂ (ξ,root)) :=
      h01.add (h₂.comp (measurable_const.prodMk measurable_id))
    rw [lintegral_add_left h012,lintegral_add_left h01,lintegral_add_left h0]
  simp_rw [hi]
  have H0 : Measurable (fun ξ ↦ ∫⁻ root, f₀ (ξ,root) ∂ν) := h₀.lintegral_prod_right'
  have H01 : Measurable (fun ξ ↦ (∫⁻ root, f₀ (ξ,root) ∂ν) +
      ∫⁻ root, f₁ (ξ,root) ∂ν) := H0.add h₁.lintegral_prod_right'
  have H012 : Measurable (fun ξ ↦ (∫⁻ root, f₀ (ξ,root) ∂ν) +
      (∫⁻ root, f₁ (ξ,root) ∂ν) + ∫⁻ root, f₂ (ξ,root) ∂ν) :=
    H01.add h₂.lintegral_prod_right'
  rw [lintegral_add_left H012,lintegral_add_left H01,lintegral_add_left H0]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
namespace PopulationLocalPressureCore

/-- The genuine clock-restricted guard is covered by the two bounded core
escapes, true target-seed crossing and spatial escape, on the SAME original
source-restricted plan. Endpoint regularity is inherited almost everywhere. -/
theorem original_clock_guard_le_core_crossing_spatial
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) (R scale : ℝ)
    {U : Set (D.coreSpatialCoordinateSpace i)} (hU : MeasurableSet U)
    (z : ℚ → M) (c : D.coreSpatialCoordinateSpace i)
    (hz : z ∈ (D.haar.continuous.coefficient i).roots)
    (hc : c = D.coreMacroLabel i z) (Γ : Measure (M × M))
    (hreg : ∀ᵐ p ∂Γ, p.1 ∈ F.potentialRegularDomain u ∧
      p.2 ∈ F.potentialRegularDomain u) :
    let C := D.haar.continuous.coefficient i
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) C.seedIndex
    let φ := fun x ↦ D.coreMacroLabel i (a x)
    let K := D.coreMacroLabel i '' C.roots
    let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale
    let ΓH := Γ.restrict (H ×ˢ univ)
    let Γclock := ΓH.restrict {p | (u p.1,u p.2) ∈ C.window.region}
    D.originalTaylorGuardMass i R scale U z (scale • c) Γclock ≤
      ΓH (Prod.fst ⁻¹' (H ∩ φ ⁻¹' rootCoreEscapeSet K R scale c)) +
      ΓH (Prod.snd ⁻¹' (H ∩ φ ⁻¹' rootCoreEscapeSet K R scale c)) +
      ΓH ({p | coord p.1-scale • c ∈ U} ∩ (univ ×ˢ Hᶜ)) +
      ΓH ({p | coord p.1-scale • c ∈ U} ∩
        {p | ¬(‖coord p.1-scale • c‖ ≤ R ∧ ‖coord p.2-scale • c‖ ≤ R)}) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  intro C H φ K coord ΓH Γclock
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex
  have hcoord : Measurable coord :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj C.seedIndex scale
  have hcoordφ (x : M) : coord x = scale • φ x := rfl
  let W := {p : M × M | coord p.1-scale • c ∈ U}
  let T := {p : M × M | (u p.1,u p.2) ∈ C.window.region}
  let G := W \ D.originalRootedTaylorWindow i R scale U z (scale • c)
  have hG : MeasurableSet G :=
    (hU.preimage ((hcoord.comp measurable_fst).sub measurable_const)).diff
      (D.measurableSet_originalRootedTaylorWindow hF hcomplete hu ha hinj i R scale hU z _)
  have hmask := D.original_core_escape_mask_eq_coordinate hF hcomplete hu ha hinj i
  dsimp only at hmask
  rw [Set.image_image] at hmask
  change H \ a ⁻¹' C.roots = H ∩ φ ⁻¹' Kᶜ at hmask
  rw [originalTaylorGuardMass]
  change Γclock G ≤ _
  change (ΓH.restrict T) G ≤ _
  rw [Measure.restrict_apply hG]
  have hcover : ∀ᵐ p ∂ΓH, p ∈ G ∩ T → p ∈
      (Prod.fst ⁻¹' (H ∩ φ ⁻¹' rootCoreEscapeSet K R scale c)) ∪
      (Prod.snd ⁻¹' (H ∩ φ ⁻¹' rootCoreEscapeSet K R scale c)) ∪
      (W ∩ (univ ×ˢ Hᶜ)) ∪
      (W ∩ {p | ¬(‖coord p.1-scale • c‖ ≤ R ∧ ‖coord p.2-scale • c‖ ≤ R)}) := by
    filter_upwards [ae_restrict_mem (hH.prod MeasurableSet.univ), ae_restrict_of_ae hreg]
      with p hpH hpreg
    intro hp
    have hpW : p ∈ W := hp.1.1
    by_cases hsp : ‖coord p.1-scale • c‖ ≤ R ∧ ‖coord p.2-scale • c‖ ≤ R
    · by_cases hyH : p.2 ∈ H
      · have hbad : ¬(a p.1 ∈ C.roots ∧ a p.2 ∈ C.roots) := by
          intro hcore
          exact hp.1.2 ⟨hz,by rw [hc]; rfl,hcore.1,hcore.2,hpreg.1,hpreg.2,hp.2,
            hsp.1,hsp.2,hpW⟩
        by_cases hax : a p.1 ∈ C.roots
        · have hay : a p.2 ∉ C.roots := fun hy ↦ hbad ⟨hax,hy⟩
          have hesc : p.2 ∈ H ∩ φ ⁻¹' Kᶜ := by rw [← hmask]; exact ⟨hyH,hay⟩
          apply Or.inl ∘ Or.inl ∘ Or.inr
          refine ⟨hyH,hesc.2,?_⟩
          simpa only [hcoordφ, mem_preimage, Metric.mem_closedBall, dist_zero_right, smul_sub]
            using hsp.2
        · have hesc : p.1 ∈ H ∩ φ ⁻¹' Kᶜ := by
            rw [← hmask]
            exact ⟨hpH.1,hax⟩
          apply Or.inl ∘ Or.inl ∘ Or.inl
          refine ⟨hpH.1,hesc.2,?_⟩
          simpa only [hcoordφ, mem_preimage, Metric.mem_closedBall, dist_zero_right, smul_sub]
            using hsp.1
      · exact Or.inl (Or.inr ⟨hpW,mem_univ _,hyH⟩)
    · exact Or.inr ⟨hpW,hsp⟩
  exact (measure_mono_ae hcover).trans ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))

/-- The genuine expected clock-restricted Taylor remainder in an original
root domain. Its reference is the original inverse seed map. -/
def originalIIDClockGuardExpectation
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (n : ℕ)
    (cost : M → M → ℝ) (selectionScale R scale : ℝ)
    (roots U : Set (D.coreSpatialCoordinateSpace i)) : ℝ≥0∞ :=
  let C := D.haar.continuous.coefficient i
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
    (lambda := lambda) C.seedIndex
  let Γclock := fun ξ ↦
    ((originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale ξ).restrict (H ×ˢ univ)).restrict
      {p | (u p.1,u p.2) ∈ C.window.region}
  ∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n+1 : ℕ) : ℝ) *
    D.originalTaylorGuardMass i R scale U
      (D.originalRootedTaylorReference i (scale⁻¹ • root)) root (Γclock ξ)
    ∂cavityRootMeasure volume roots ((n+1 : ℕ) : ℝ)
    ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))

/-- A finite actual guard is bounded by the two genuine macro-core escape
integrals, the original seed-crossing mass, and the complete source long tail.
The bound is uniform over all measured root subdomains of the same macro core. -/
theorem originalIID_clock_guard_expectation_le_components
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (i : Fin D.haar.continuous.count) (n : ℕ)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (selectionScale R W scale : ℝ) (hs : 0 < scale)
    (hnorm : scale ^ finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker =
      ((n+1 : ℕ) : ℝ))
    {U : Set (D.coreSpatialCoordinateSpace i)} (hU : MeasurableSet U)
    (hW : ∀ x ∈ U, ‖x‖ ≤ W) (hRW : W ≤ R)
    {roots fullRoots : Set (D.coreSpatialCoordinateSpace i)}
    (hroots : MeasurableSet roots) (hsub : roots ⊆ fullRoots)
    (hcore : roots ⊆ (fun root ↦ scale⁻¹ • root) ⁻¹'
      (D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots)) :
    let C := D.haar.continuous.coefficient i
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) C.seedIndex
    let φ := fun x ↦ D.coreMacroLabel i (a x)
    let K := D.coreMacroLabel i '' C.roots
    let N := ((n+1 : ℕ) : ℝ)
    let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale
    let ΓH := fun ξ ↦ (Γ ξ).restrict (H ×ˢ univ)
    let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale
    D.originalIIDClockGuardExpectation i n cost selectionScale R scale roots U ≤
      (∫⁻ c in K, ∫⁻ ξ,
        originalIIDMaskedCoreEscapeMass cost selectionScale H φ K R scale 0 c ξ ∂law ∂volume) +
      (∫⁻ c in K, ∫⁻ ξ,
        originalIIDMaskedCoreEscapeMass cost selectionScale H φ K R scale 1 c ξ ∂law ∂volume) +
      volume U * (∫⁻ ξ, Γ ξ (physicalSceneCoreCrossing H) ∂law) +
      (∫⁻ ξ, ∫⁻ root,
        physicalSceneRootedPlan (ΓH ξ) coord u N root
          (physicalSceneLongEdgeWindow U (ENNReal.ofReal ((R-W)^2)))
        ∂cavityRootMeasure volume fullRoots N ∂law) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  intro C H φ K N law Γ ΓH coord
  let Ω := (Fin (n+1) → M) × (Fin (n+1) → M)
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex
  have hφ : Measurable φ := by
    have hp := measurable_physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      hF hcomplete hu ha hinj C.seedIndex 1
    change Measurable (fun x : M ↦ (1 : ℝ) • φ x) at hp
    simpa only [one_smul] using hp
  have hcoord : Measurable coord :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj C.seedIndex scale
  have hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots := by
    simpa only [D.haar.intensity_roots i] using (D.haar.intensity i).continuous_label
  have hK : IsCompact K := C.roots_compact.image_of_continuousOn
    ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL.continuous.comp_continuousOn hlabel)
  have hUf : volume U ≠ ⊤ := ne_top_of_le_ne_top
    (isCompact_closedBall (0 : D.coreSpatialCoordinateSpace i) W).measure_ne_top
    (measure_mono (fun x hx ↦ by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hW x hx))
  let κ₀ : Kernel Ω (M × M) := ⟨Γ, measurable_originalIIDOptimalPhysicalPlan cost hcost selectionScale⟩
  letI : IsMarkovKernel κ₀ := ⟨fun ξ ↦ by
    change IsProbabilityMeasure (Γ ξ)
    infer_instance⟩
  let κH := κ₀.restrict (hH.prod MeasurableSet.univ)
  let rootLaw := cavityRootMeasure volume roots N
  letI : SFinite rootLaw := by
    dsimp only [rootLaw,cavityRootMeasure]
    infer_instance
  let f₀ : Ω × D.coreSpatialCoordinateSpace i → ℝ≥0∞ := fun p ↦
    originalIIDMaskedCoreEscapeMass cost selectionScale H φ K R scale 0 (scale⁻¹ • p.2) p.1
  let f₁ : Ω × D.coreSpatialCoordinateSpace i → ℝ≥0∞ := fun p ↦
    originalIIDMaskedCoreEscapeMass cost selectionScale H φ K R scale 1 (scale⁻¹ • p.2) p.1
  let f₂ : Ω × D.coreSpatialCoordinateSpace i → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal N * ΓH p.1 ({e | coord e.1-p.2 ∈ U} ∩ (univ ×ˢ Hᶜ))
  let f₃ : Ω × D.coreSpatialCoordinateSpace i → ℝ≥0∞ := fun p ↦
    physicalSceneRootedPlan (ΓH p.1) coord u N p.2
      (physicalSceneLongEdgeWindow U (ENNReal.ofReal ((R-W)^2)))
  have hnormmap : Measurable (fun p : Ω × D.coreSpatialCoordinateSpace i ↦
      (p.1,scale⁻¹ • p.2)) := measurable_fst.prodMk (measurable_snd.const_smul scale⁻¹)
  have hf₀ : Measurable f₀ := by
    change Measurable (fun p : Ω × D.coreSpatialCoordinateSpace i ↦
      ((n+1 : ℕ) : ℝ≥0∞) * κH p.1
        (Prod.fst ⁻¹' (H ∩ φ ⁻¹' rootCoreEscapeSet K R scale (scale⁻¹ • p.2))))
    have h := (measurable_kernel_endpoint_core_escape κH Prod.fst measurable_fst
      hH φ hφ hK.measurableSet R scale).const_mul ((n+1 : ℕ) : ℝ≥0∞)
    exact h.comp hnormmap
  have hf₁ : Measurable f₁ := by
    change Measurable (fun p : Ω × D.coreSpatialCoordinateSpace i ↦
      ((n+1 : ℕ) : ℝ≥0∞) * κH p.1
        (Prod.snd ⁻¹' (H ∩ φ ⁻¹' rootCoreEscapeSet K R scale (scale⁻¹ • p.2))))
    have h := (measurable_kernel_endpoint_core_escape κH Prod.snd measurable_snd
      hH φ hφ hK.measurableSet R scale).const_mul ((n+1 : ℕ) : ℝ≥0∞)
    exact h.comp hnormmap
  have hf₂ : Measurable f₂ :=
    measurable_kernel_rooted_event_mass κH coord hcoord hU
      (MeasurableSet.univ.prod hH.compl) N
  have hreg := ae_originalIIDOptimalPhysicalPlan_carried (n := n+1)
    μ ν cost hcost selectionScale hμreg hνreg
  have hfirst :
      D.originalIIDClockGuardExpectation i n cost selectionScale R scale roots U ≤
        ∫⁻ ξ, ∫⁻ root, f₀ (ξ,root)+f₁ (ξ,root)+f₂ (ξ,root)+f₃ (ξ,root)
          ∂rootLaw ∂law := by
    apply lintegral_mono_ae
    filter_upwards [hreg] with ξ hξ
    apply lintegral_mono_ae
    have hmem : ∀ᵐ root ∂rootLaw, scale⁻¹ • root ∈ K :=
      Measure.ae_smul_measure ((ae_restrict_mem hroots).mono hcore) _
    filter_upwards [hmem] with root hr
    obtain ⟨z,hz,hzroot⟩ := hr
    have href : D.originalRootedTaylorReference i (scale⁻¹ • root) = z := by
      rw [← hzroot]
      exact D.originalRootedTaylorReference_coreMacroLabel hF hcomplete hu ha hinj i hz
    have hroot : scale • (scale⁻¹ • root) = root := by
      rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
    have hb := D.original_clock_guard_le_core_crossing_spatial
      hF hcomplete hu ha hinj i R scale hU z (scale⁻¹ • root) hz hzroot.symm (Γ ξ) hξ
    rw [hroot] at hb
    have hspace := measure_mono (μ := ΓH ξ)
      (rooted_spatial_bad_subset_longEdge coord root U W R hW hRW)
    change ENNReal.ofReal N * D.originalTaylorGuardMass i R scale U
      (D.originalRootedTaylorReference i (scale⁻¹ • root)) root _ ≤ _
    rw [href]
    apply (mul_le_mul_of_nonneg_left hb bot_le).trans
    rw [mul_add,mul_add,mul_add]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    apply add_le_add
    · simp only [f₀,f₁,f₂,originalIIDMaskedCoreEscapeMass,N,ENNReal.ofReal_natCast,
        ite_true,h10,ite_false]
      exact le_rfl
    · dsimp only [f₃]
      rw [physicalSceneRootedPlan_longEdgeWindow_eq_mass _ coord hcoord u
        hu.continuous.measurable N root hU]
      exact mul_le_mul_of_nonneg_left hspace bot_le
  apply hfirst.trans
  rw [lintegral_lintegral_add_four law rootLaw f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂]
  apply add_le_add
  · apply add_le_add
    · exact add_le_add
        (lintegral_originalIID_core_escape_rootAverage_le_macro
          μ ν cost hcost selectionScale hH φ hφ hK.measurableSet R scale hs hnorm roots hcore 0)
        (lintegral_originalIID_core_escape_rootAverage_le_macro
          μ ν cost hcost selectionScale hH φ hφ hK.measurableSet R scale hs hnorm roots hcore 1)
    · have hb (ξ : Ω) := lintegral_rootedPhysicalSeedTargetEscapeMass_le
        (Γ ξ) H coord hcoord N (by dsimp [N]; positivity) roots U hU 0
      have heq (ξ : Ω) (root) : rootedPhysicalSeedTargetEscapeMass (Γ ξ) H coord N U 0 root =
          f₂ (ξ,root) :=
        rootedPhysicalSeedTargetEscapeMass_source_eq_mass (Γ ξ) hH coord hcoord N root hU
      simp_rw [heq] at hb
      calc
        _ ≤ ∫⁻ ξ, volume U * Γ ξ (physicalSceneCoreCrossing H) ∂law :=
          lintegral_mono hb
        _ = _ := lintegral_const_mul' _ _ hUf
  · apply lintegral_mono
    intro ξ
    exact lintegral_mono' (smul_le_smul_left _
      ((volume : Measure (D.coreSpatialCoordinateSpace i)).restrict_mono_set hsub)) le_rfl

/-- The same original clock-restricted Taylor guard has arbitrarily small
expected mass after one spatial cutoff and an eventual sample bound. Every
measurable root subdomain of the fixed measured core uses the same bound.
The true energy hypothesis concerns only the original finite optimizer. -/
theorem exists_eventually_originalIID_clock_guard_small
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
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
    (i : Fin D.haar.continuous.count)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (selectionScale spatialScale : ℕ → ℝ)
    (hsp : ∀ n, 0 < spatialScale n) (hlarge : Tendsto spatialScale atTop atTop)
    (hnorm : ∀ n, spatialScale n ^
      finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker =
        ((n+1 : ℕ) : ℝ))
    (fullRoots : ℕ → Set (D.coreSpatialCoordinateSpace i))
    (hRoot : ∀ n, volume (fullRoots n) = ENNReal.ofReal ((n+1 : ℕ) : ℝ))
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((spatialScale n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (selectionScale n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    {U : Set (D.coreSpatialCoordinateSpace i)} (hU : MeasurableSet U)
    (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) :
    ∀ η : ℝ≥0∞, 0 < η → ∃ R : ℝ, 0 ≤ R ∧ W ≤ R ∧
      ∀ᶠ n in atTop, ∀ roots : Set (D.coreSpatialCoordinateSpace i), MeasurableSet roots →
        roots ⊆ fullRoots n →
        roots ⊆ (fun root ↦ (spatialScale n)⁻¹ • root) ⁻¹'
          (D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots) →
        D.originalIIDClockGuardExpectation i n (cost n) (selectionScale n) R
          (spatialScale n) roots U ≤ η := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
    (lambda := μ.map a) C.seedIndex
  let φ := fun x ↦ D.coreMacroLabel i (a x)
  let K := D.coreMacroLabel i '' C.roots
  let N := fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)
  let law := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n+1) ↦ ν))
  let Γ := fun n ↦ originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (selectionScale n)
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition
    (P := P) (a := a) C.seedIndex (spatialScale n)
  let escape := fun (R : ℝ) (color : Fin 2) n ↦ ∫⁻ c in K, ∫⁻ ξ,
    originalIIDMaskedCoreEscapeMass (cost n) (selectionScale n) H φ K R
      (spatialScale n) color c ξ ∂law n ∂volume
  let cross := fun n ↦ ∫⁻ ξ, Γ n ξ (physicalSceneCoreCrossing H) ∂law n
  let tail := fun threshold n ↦ ∫⁻ ξ, ∫⁻ root,
    physicalSceneRootedPlan ((Γ n ξ).restrict (H ×ˢ univ)) (coord n) u (N n) root
      (physicalSceneLongEdgeWindow U threshold)
    ∂cavityRootMeasure volume (fullRoots n) (N n) ∂law n
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex
  have hφ : Measurable φ := by
    have hp := measurable_physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      hF hcomplete hu ha hinj C.seedIndex 1
    change Measurable (fun x : M ↦ (1 : ℝ) • φ x) at hp
    simpa only [one_smul] using hp
  have hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots := by
    simpa only [D.haar.intensity_roots i] using (D.haar.intensity i).continuous_label
  have hK : IsCompact K := C.roots_compact.image_of_continuousOn
    ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL.continuous.comp_continuousOn hlabel)
  have hUf : volume U ≠ ⊤ := ne_top_of_le_ne_top
    (isCompact_closedBall (0 : D.coreSpatialCoordinateSpace i) W).measure_ne_top
    (measure_mono (fun x hx ↦ by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hW x hx))
  have hN (n : ℕ) : 0 < N n := by dsimp [N]; positivity
  have hscale : Tendsto (fun n ↦ (spatialScale n)^2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp hlarge
  have he (R : ℝ) (color : Fin 2) : Tendsto (escape R color) atTop (𝓝 0) :=
    tendsto_lintegral_originalIIDMaskedCoreEscapeMass μ ν hH φ hφ hK R
      spatialScale hsp hlarge hnorm cost selectionScale color
  have hcross : Tendsto cross atTop (𝓝 0) :=
    tendsto_originalIID_fixed_seed_crossing_mass_zero hpopulation hrecovery
      hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg hface
      hgap hdist C.seedIndex cost hcost selectionScale spatialScale hsp hscale
      budget hbudget henergy
  have hcrossU := ENNReal.Tendsto.const_mul hcross (a := volume U) (Or.inr hUf)
  simp only [mul_zero] at hcrossU
  have htail := exists_originalIID_fixed_seed_uniform_both_tail_tightness
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist C.seedIndex
    (I := Unit) (fun _ n ↦ cost n) (fun _ n ↦ hcost n) (fun _ n ↦ selectionScale n)
    spatialScale hsp hscale N hN fullRoots hRoot budget hbudget
    (henergy.mono fun n hn _ ↦ hn) U hU hUf
  intro η hη
  let ε := η / 4
  have hε : 0 < ε := ENNReal.div_pos hη.ne' (by norm_num)
  obtain ⟨threshold,htpos,htfinite,htsmall⟩ := htail ε hε
  let R := max W 0 + Real.sqrt threshold.toReal + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRW : W ≤ R := by
    have := Real.sqrt_nonneg threshold.toReal
    dsimp [R]
    linarith [le_max_left W 0]
  have hthreshold : threshold ≤ ENNReal.ofReal ((R-W)^2) := by
    rw [ENNReal.le_ofReal_iff_toReal_le htfinite (sq_nonneg _)]
    have hsqrt := Real.sqrt_nonneg threshold.toReal
    have hsq := Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ threshold.toReal)
    have hdiff : Real.sqrt threshold.toReal ≤ R-W := by
      dsimp [R]
      linarith [le_max_left W 0]
    nlinarith
  refine ⟨R,hR,hRW,?_⟩
  filter_upwards [(he R 0).eventually_le_const hε,
    (he R 1).eventually_le_const hε,hcrossU.eventually_le_const hε,htsmall]
    with n hn₀ hn₁ hn₂ hn₃
  intro roots hroots hsub hcore
  have hfinite := D.originalIID_clock_guard_expectation_le_components
    hF hcomplete hu ha hinj hμreg hreg i n (cost n) (hcost n) (selectionScale n)
    R W (spatialScale n) (hsp n) (hnorm n) hU hW hRW hroots hsub hcore
  have htailmono : tail (ENNReal.ofReal ((R-W)^2)) n ≤ tail threshold n := by
    apply lintegral_mono
    intro ξ
    apply lintegral_mono
    intro root
    exact measure_mono (fun e he ↦ ⟨he.1,hthreshold.trans he.2⟩)
  have htailbound : tail (ENNReal.ofReal ((R-W)^2)) n ≤ ε :=
    htailmono.trans ((hn₃ ()).1)
  calc
    _ ≤ escape R 0 n + escape R 1 n + volume U * cross n +
        tail (ENNReal.ofReal ((R-W)^2)) n := hfinite
    _ ≤ ε+ε+ε+ε := add_le_add (add_le_add (add_le_add hn₀ hn₁) hn₂) htailbound
    _ = η := by
      change η/4+η/4+η/4+η/4 = η
      rw [show η/4+η/4+η/4+η/4 = 4*(η/4) by ring]
      exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
