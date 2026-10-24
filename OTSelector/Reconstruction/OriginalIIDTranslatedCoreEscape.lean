import OTSelector.Reconstruction.OriginalIIDClockRestrictedGuardVanish
import OTSelector.Reconstruction.OriginalIIDTranslatedWindowBudget
import OTSelector.Reconstruction.OriginalIIDRawPalmRootLabelLaw

/-!
# Translated bounded source windows escape the old root core with vanishing mass

The unchanged original iid optimizer, original source mask and actual finite
root normalization are retained. Root translation and the true Haar Jacobian
reduce every selected root subdomain to the same old compact macro core. The
existing exterior-collar estimate then gives a vanishing mass without energy
or boundary-null assumptions.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000

/-- A bounded source window outside the old physical root core is dominated
by its own actual coordinate-core escape. The same source mask and raw plan
are retained on both sides. -/
theorem originalIID_translated_source_core_escape_mass_le
    {M : Type*} [MeasurableSpace M] {q n : ℕ}
    (cost : M → M → ℝ) (selectionScale : ℝ)
    {H B : Set M} (hH : MeasurableSet H) (hB : MeasurableSet B)
    (φ : M → Fin q → ℝ) (hφ : Measurable φ)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (hmask : H \ B = H ∩ φ ⁻¹' Kᶜ)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (W s : ℝ) (hs : 0 < s) (hW : ∀ x ∈ U, ‖x‖ ≤ W)
    (z : Fin q → ℝ) (ξ : (Fin (n+1) → M) × (Fin (n+1) → M)) :
    ENNReal.ofReal ((n+1 : ℕ) : ℝ) *
      ((originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale ξ).restrict (H ×ˢ univ))
        {p | s • φ p.1-z ∈ U ∧ p.1 ∉ B} ≤
      originalIIDMaskedCoreEscapeMass cost selectionScale H φ K W s 0 (s⁻¹ • z) ξ := by
  have hE : MeasurableSet {p : M × M | s • φ p.1-z ∈ U ∧ p.1 ∉ B} :=
    (hU.preimage (((hφ.comp measurable_fst).const_smul s).sub_const z)).inter
      (hB.compl.preimage measurable_fst)
  have hA : MeasurableSet ((Prod.fst : M × M → M) ⁻¹'
      (H ∩ φ ⁻¹' rootCoreEscapeSet K W s (s⁻¹ • z))) :=
    (hH.inter ((measurableSet_rootCoreEscapeSet hK W s (s⁻¹ • z)).preimage hφ)).preimage
      measurable_fst
  simp only [originalIIDMaskedCoreEscapeMass, Fin.isValue, ↓reduceIte,
    ENNReal.ofReal_natCast]
  apply mul_le_mul_of_nonneg_left _ bot_le
  rw [Measure.restrict_apply hE, Measure.restrict_apply hA]
  apply measure_mono
  rintro p ⟨⟨hpW,hpB⟩,hpH⟩
  have hescape : p.1 ∈ H ∩ φ ⁻¹' Kᶜ := by
    rw [← hmask]
    exact ⟨hpH.1,hpB⟩
  refine ⟨⟨hpH.1,hescape.2,?_⟩,hpH⟩
  change s • (φ p.1-s⁻¹ • z) ∈ Metric.closedBall 0 W
  rw [Metric.mem_closedBall,dist_zero_right,smul_sub,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  exact hW _ hpW

/-- Every translated root domain whose actual macro tags lie in K pays at
most the same original macro-core escape. This is uniform over all selected
subcores and over the frame center, with the original N exactly canceled. -/
theorem lintegral_originalIID_translated_source_core_escape_le_macro
    {M : Type*} [MeasurableSpace M] {q n : ℕ}
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost)) (selectionScale : ℝ)
    {H B : Set M} (hH : MeasurableSet H) (hB : MeasurableSet B)
    (φ : M → Fin q → ℝ) (hφ : Measurable φ)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (hmask : H \ B = H ∩ φ ⁻¹' Kᶜ)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (W s : ℝ) (hs : 0 < s) (hnorm : s ^ q = ((n+1 : ℕ) : ℝ))
    (hW : ∀ x ∈ U, ‖x‖ ≤ W) (center : Fin q → ℝ)
    (roots : Set (Fin q → ℝ))
    (hroots : roots ⊆ (fun root ↦ center+physicalSceneMacroscopicRoot s root) ⁻¹' K) :
    let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n+1 : ℕ) : ℝ) *
      ((originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale ξ).restrict (H ×ˢ univ))
        {p | s • φ p.1-(root+s • center) ∈ U ∧ p.1 ∉ B}
      ∂cavityRootMeasure volume roots ((n+1 : ℕ) : ℝ) ∂law) ≤
      ∫⁻ c in K, ∫⁻ ξ, originalIIDMaskedCoreEscapeMass cost selectionScale H φ K W s 0 c ξ
        ∂law ∂volume := by
  intro law
  let shifted := (fun root ↦ s • center+root) '' roots
  have hshifted : shifted ⊆ (fun root ↦ s⁻¹ • root) ⁻¹' K := by
    rintro root ⟨r,hr,rfl⟩
    have htag : s⁻¹ • (s • center+r) = center+physicalSceneMacroscopicRoot s r := by
      rw [smul_add,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]
      congr 1
      ext k
      simp [physicalSceneMacroscopicRoot, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    change s⁻¹ • (s • center+r) ∈ K
    rw [htag]
    exact hroots hr
  calc
    _ ≤ ∫⁻ ξ, ∫⁻ root,
        originalIIDMaskedCoreEscapeMass cost selectionScale H φ K W s 0
          (s⁻¹ • (s • center+root)) ξ
        ∂cavityRootMeasure volume roots ((n+1 : ℕ) : ℝ) ∂law := by
      apply lintegral_mono
      intro ξ
      apply lintegral_mono
      intro root
      simpa only [add_comm] using originalIID_translated_source_core_escape_mass_le
        cost selectionScale hH hB φ hφ hK hmask hU W s hs hW (s • center+root) ξ
    _ = ∫⁻ ξ, ∫⁻ root,
        originalIIDMaskedCoreEscapeMass cost selectionScale H φ K W s 0 (s⁻¹ • root) ξ
        ∂cavityRootMeasure volume shifted ((n+1 : ℕ) : ℝ) ∂law := by
      apply lintegral_congr
      intro ξ
      exact lintegral_cavityRootMeasure_add_const roots ((n+1 : ℕ) : ℝ) (s • center)
        (fun root ↦ originalIIDMaskedCoreEscapeMass cost selectionScale H φ K W s 0
          (s⁻¹ • root) ξ)
    _ ≤ _ := lintegral_originalIID_core_escape_rootAverage_le_macro μ ν cost hcost selectionScale
      hH φ hφ hK W s hs hnorm shifted hshifted 0

/-- Actual translated bounded-source mass outside the old physical core
vanishes for any changing selected root subdomains and frame centers, all
contained in the same fixed compact original macro core. -/
theorem tendsto_lintegral_originalIID_translated_source_core_escape
    {M : Type*} [MeasurableSpace M] {q : ℕ}
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H B : Set M} (hH : MeasurableSet H) (hB : MeasurableSet B)
    (φ : M → Fin q → ℝ) (hφ : Measurable φ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K)
    (hmask : H \ B = H ∩ φ ⁻¹' Kᶜ)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    (hnorm : ∀ n, s n ^ q = ((n+1 : ℕ) : ℝ))
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (selectionScale : ℕ → ℝ) (center : ℕ → Fin q → ℝ)
    (roots : ℕ → Set (Fin q → ℝ))
    (hroots : ∀ n, roots n ⊆
      (fun root ↦ center n+physicalSceneMacroscopicRoot (s n) root) ⁻¹' K) :
    Tendsto (fun n ↦ ∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n+1 : ℕ) : ℝ) *
      ((originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (selectionScale n) ξ).restrict (H ×ˢ univ))
        {p | s n • φ p.1-(root+s n • center n) ∈ U ∧ p.1 ∉ B}
      ∂cavityRootMeasure volume (roots n) ((n+1 : ℕ) : ℝ)
      ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n+1) ↦ ν))) atTop (𝓝 0) := by
  have hmacro := tendsto_lintegral_originalIIDMaskedCoreEscapeMass μ ν hH φ hφ hK W
    s hs hlarge hnorm cost selectionScale 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmacro
    (fun _ ↦ bot_le) (fun n ↦
      lintegral_originalIID_translated_source_core_escape_le_macro μ ν (cost n) (hcost n)
        (selectionScale n) hH hB φ hφ hK.measurableSet hmask hU W (s n) (hs n)
        (hnorm n) hW (center n) (roots n) (hroots n))

section ActualOriginalCore
open Manifold OTSelector.Geometry
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

omit [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure] in
/-- For the actual old Haar core, physical root escape within the full
original seed is exactly escape from its same original coordinate image.
The original full-seed inverse proves this identity before any auxiliary core. -/
theorem PopulationHaarPressureCore.original_seed_core_escape_mask_eq_coordinate
    (D : PopulationHaarPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) C.seedIndex
    H \ a ⁻¹' C.roots = H ∩ (fun x ↦ e (R (a x))) ⁻¹' (e '' (R '' C.roots))ᶜ := by
  intro C S R e H
  ext x
  constructor
  · rintro ⟨hxH,hxroots⟩
    refine ⟨hxH,?_⟩
    rintro ⟨w,⟨z,hz,hRz⟩,hew⟩
    have hec : e (R z) = e (R (a x)) := (congrArg e hRz).trans hew
    have hlabel : physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex z =
        physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex (a x) := hec
    have hzroot := physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj
      C.seedIndex (C.roots_subset_piece hz)
    have hxroot := physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj
      C.seedIndex hxH
    have hzx : z = a x := hzroot.symm.trans
      ((congrArg (physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex) hlabel).trans hxroot)
    apply hxroots
    change a x ∈ C.roots
    rwa [← hzx]
  · rintro ⟨hxH,hxK⟩
    refine ⟨hxH,?_⟩
    intro hxroots
    exact hxK ⟨R (a x),⟨a x,hxroots,rfl⟩,rfl⟩

omit [∀ j, (κ j).IsAddHaarMeasure] in
/-- For ONE old actual Haar core and arbitrary selected macro subdomains,
bounded shifted source windows lose vanishing mass outside its old roots.
The window U, the original seed mask, all iid samples and the optimizer stay
literal; no kinetic or scalar-clock support input is required. -/
theorem PopulationHaarPressureCore.original_iid_translated_source_core_escape_tendsto
    (D : PopulationHaarPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := Module.finrank ℝ S.covector.ker
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let K := e '' (R '' C.roots)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) C.seedIndex
    ∀ (U : Set (Fin q → ℝ)), MeasurableSet U →
      ∀ W : ℝ, (∀ x ∈ U, ‖x‖ ≤ W) →
      ∀ (s : ℕ → ℝ), (∀ n, 0 < s n) → Tendsto s atTop atTop →
        (∀ n, s n ^ q = ((n+1 : ℕ) : ℝ)) →
      ∀ (cost : ℕ → M → M → ℝ), (∀ n, Measurable (Function.uncurry (cost n))) →
      ∀ (selectionScale : ℕ → ℝ) (center : ℕ → Fin q → ℝ)
        (domains : ℕ → Set (Fin q → ℝ)) (A : Set (Fin q → ℝ)), A ⊆ K →
      Tendsto (fun n ↦ ∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n+1 : ℕ) : ℝ) *
        ((originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (selectionScale n) ξ).restrict
          (H ×ˢ univ))
          {p | s n • e (R (a p.1))-(root+s n • center n) ∈ U ∧ a p.1 ∉ C.roots}
        ∂cavityRootMeasure volume
          (domains n ∩ (fun root ↦ center n+physicalSceneMacroscopicRoot (s n) root) ⁻¹' A)
          ((n+1 : ℕ) : ℝ)
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) atTop (𝓝 0) := by
  intro C S q R e K H U hU W hW s hs hlarge hnorm cost hcost selectionScale center domains A hAK
  let _coreEscapeMetric : MetricSpace M := F.metricSpace
  let _coreEscapeProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _coreEscapePolish : PolishSpace M := inferInstance
  let _coreEscapeBorel : BorelSpace (ℚ → M) := inferInstance
  have hlabel : ContinuousOn R C.roots := by
    simpa only [D.intensity_roots i] using (D.intensity i).continuous_label
  have hK : IsCompact K := (C.roots_compact.image_of_continuousOn hlabel).image e.continuous
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex
  have hB : MeasurableSet (a ⁻¹' C.roots) := C.roots_compact.measurableSet.preimage ha
  have hφ : Measurable (fun x ↦ e (R (a x))) := e.continuous.measurable.comp
    ((measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj).comp ha)
  exact tendsto_lintegral_originalIID_translated_source_core_escape μ ν hH hB _ hφ hK
    (D.original_seed_core_escape_mask_eq_coordinate hF hcomplete hu ha hinj i)
    hU W hW s hs hlarge hnorm cost hcost selectionScale center
    (fun n ↦ domains n ∩ (fun root ↦ center n+physicalSceneMacroscopicRoot (s n) root) ⁻¹' A)
    (fun n ↦ inter_subset_right.trans (preimage_mono hAK))

end ActualOriginalCore
end OTSelector.Reconstruction
