import OTSelector.Reconstruction.OriginalIIDFullSeedInputConvergence
import OTSelector.MeasureTheory.ProbabilityMeasureWeakLimitKernel

/-!
# Measurable weak-limit kernels of the actual original full-seed inputs

The finite input laws use the same original iid arrays at every coordinate root.
Only the limiting probability kernel receives an arbitrary value off the common
full-measure retained-root set.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction BigOperators ENNReal

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess

set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false

/-- A weakly continuous probability field is measurable for the actual Giry
sigma algebra, using Portmanteau's one-sided weak-Borel coercion. -/
theorem original_measurable_probabilityMeasure_of_continuous
    {S C : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [PseudoMetrizableSpace S] [SeparableSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [OpensMeasurableSpace C]
    {P : C → ProbabilityMeasure S} (hP : Continuous P) : Measurable P := by
  have hcoerce := measurable_probabilityMeasure_toMeasure_weakBorel_general (S := S)
  let : MeasurableSpace (ProbabilityMeasure S) := borel (ProbabilityMeasure S)
  have : BorelSpace (ProbabilityMeasure S) := ⟨rfl⟩
  exact (hcoerce.comp hP.measurable).subtype_mk

section FiniteRootMeasurability

variable {C Ω X : Type*} [MeasurableSpace C] [MeasurableSpace Ω]
  [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X] [SecondCountableTopology X]

omit [ProperSpace X] [SecondCountableTopology X] in
/-- Original deterministic endpoint masks remain jointly measurable when the
observation coordinates depend measurably on the macroscopic root. -/
theorem measurable_original_parameterizedMaskedTuple
    (N : ℕ) (base : X) {A : Set Ω} (hA : MeasurableSet A)
    {obs : C × Ω → X} (hobs : Measurable obs) :
    Measurable (fun p : C × (Fin N → Ω) ↦
      LocalConfiguration.ofMaskedTuple base A (fun x ↦ obs (p.1, x)) p.2) := by
  apply LocalConfiguration.measurable_iff_countingMeasure_comp.mpr
  simp_rw [LocalConfiguration.countingMeasure_ofMaskedTuple]
  apply Finset.measurable_sum
  intro j _
  have hsample : Measurable (fun p : C × (Fin N → Ω) ↦ p.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact ((Measure.measurable_dirac.comp (hobs.comp (measurable_fst.prodMk hsample))).ite
    (hA.preimage hsample) measurable_const)

/-- The locally finite encoding is exactly the pushforward of the unchanged
full original iid arrays by their retained endpoint observations. -/
theorem originalIidMaskedLocalInputPairMeasure_eq_map
    (μ ν : Measure Ω) (N : ℕ) (base : X) {AS AT : Set Ω}
    (hAS : MeasurableSet AS) (hAT : MeasurableSet AT)
    {obsS obsT : Ω → X} (hobsS : Measurable obsS) (hobsT : Measurable obsT) :
    originalIidMaskedLocalInputPairMeasure μ ν N base AS AT obsS obsT =
      ((Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν))).map
        (fun z : (Fin N → Ω) × (Fin N → Ω) ↦
          (LocalConfiguration.toLocalFiniteMeasure
              (LocalConfiguration.ofMaskedTuple base AS obsS z.1),
            LocalConfiguration.toLocalFiniteMeasure
              (LocalConfiguration.ofMaskedTuple base AT obsT z.2))) := by
  have hleft : Measurable (fun z : (Fin N → Ω) × (Fin N → Ω) ↦
      LocalConfiguration.ofMaskedTuple base AS obsS z.1) :=
    (LocalConfiguration.measurable_ofMaskedTuple base hAS hobsS N).comp measurable_fst
  have hright : Measurable (fun z : (Fin N → Ω) × (Fin N → Ω) ↦
      LocalConfiguration.ofMaskedTuple base AT obsT z.2) :=
    (LocalConfiguration.measurable_ofMaskedTuple base hAT hobsT N).comp measurable_snd
  have ht : Measurable (fun cfg : LocalConfiguration base × LocalConfiguration base ↦
      (LocalConfiguration.toLocalFiniteMeasure cfg.1,
        LocalConfiguration.toLocalFiniteMeasure cfg.2)) :=
    ((measurable_originalConfigurationLocalFinite base).comp measurable_fst).prodMk
      ((measurable_originalConfigurationLocalFinite base).comp measurable_snd)
  unfold originalIidMaskedLocalInputPairMeasure originalIidMaskedConfigurationPairLaw
  exact Measure.map_map ht (hleft.prodMk hright)

omit [MeasurableSpace C] [MeasurableSpace Ω] [StandardBorelSpace X] in
/-- With a fixed original sample, continuously moving its observed coordinates
moves the same retained counting measure continuously in the compact-test topology. -/
theorem continuous_original_parameterizedMaskedTupleLocal
    [TopologicalSpace C] (N : ℕ) (base : X) (A : Set Ω)
    (obs : C × Ω → X) (hobs : ∀ x, Continuous (fun c ↦ obs (c, x)))
    (sample : Fin N → Ω) :
    Continuous (fun c ↦ LocalConfiguration.toLocalFiniteMeasure
      (LocalConfiguration.ofMaskedTuple base A (fun x ↦ obs (c, x)) sample)) := by
  classical
  apply LocalFiniteMeasure.isEmbedding_testIntegral.continuous_iff.mpr
  apply continuous_pi
  intro F
  change Continuous (fun c ↦ LocalFiniteMeasure.testIntegral
    (LocalConfiguration.toLocalFiniteMeasure
      (LocalConfiguration.ofMaskedTuple base A (fun x ↦ obs (c, x)) sample)) F)
  simp_rw [LocalConfiguration.testIntegral_toLocalFiniteMeasure,
    LocalConfiguration.testIntegral_ofMaskedTuple]
  apply continuous_finsetSum
  intro j _
  by_cases hj : sample j ∈ A
  · simp only [Set.indicator_of_mem hj]
    exact F.continuous.comp (hobs (sample j))
  · simp only [Set.indicator_of_notMem hj]
    exact continuous_const

set_option backward.isDefEq.respectTransparency true in
/-- Continuous root translations give weakly continuous laws of the SAME finite
original iid observations, even though their dependence on the sample is only measurable. -/
theorem continuous_original_parameterizedIidMaskedLocalInputPairLaw
    [TopologicalSpace C] [FirstCountableTopology C]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ) (base : X) {AS AT : Set Ω}
    (hAS : MeasurableSet AS) (hAT : MeasurableSet AT)
    {obsS obsT : C × Ω → X} (hobsS : Measurable obsS) (hobsT : Measurable obsT)
    (hcontS : ∀ x, Continuous (fun c ↦ obsS (c, x)))
    (hcontT : ∀ x, Continuous (fun c ↦ obsT (c, x))) :
    Continuous (fun c : C ↦ originalIidMaskedLocalInputPairLaw μ ν N base hAS hAT
      (obsS := fun x ↦ obsS (c, x)) (obsT := fun x ↦ obsT (c, x))
      (hobsS.comp (measurable_const.prodMk measurable_id))
      (hobsT.comp (measurable_const.prodMk measurable_id))) := by
  let Q := (Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν))
  let _Qprob : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
  let f := fun c (z : (Fin N → Ω) × (Fin N → Ω)) ↦
    (LocalConfiguration.toLocalFiniteMeasure
        (LocalConfiguration.ofMaskedTuple base AS (fun x ↦ obsS (c, x)) z.1),
      LocalConfiguration.toLocalFiniteMeasure
        (LocalConfiguration.ofMaskedTuple base AT (fun x ↦ obsT (c, x)) z.2))
  have hf (c : C) : Measurable (f c) := by
    have hS := LocalConfiguration.measurable_ofMaskedTuple base hAS
      (obs := fun x ↦ obsS (c, x))
      (hobsS.comp ((measurable_const (a := c)).prodMk measurable_id)) N
    have hT := LocalConfiguration.measurable_ofMaskedTuple base hAT
      (obs := fun x ↦ obsT (c, x))
      (hobsT.comp ((measurable_const (a := c)).prodMk measurable_id)) N
    exact ((measurable_originalConfigurationLocalFinite base).comp
      (hS.comp measurable_fst)).prodMk
        ((measurable_originalConfigurationLocalFinite base).comp (hT.comp measurable_snd))
  have hfc (z : (Fin N → Ω) × (Fin N → Ω)) : Continuous (fun c ↦ f c z) :=
    (continuous_original_parameterizedMaskedTupleLocal N base AS obsS hcontS z.1).prodMk
      (continuous_original_parameterizedMaskedTupleLocal N base AT obsT hcontT z.2)
  apply continuous_iff_continuousAt.mpr
  intro c
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have hread (d : C) :
      (∫ z, F z ∂(originalIidMaskedLocalInputPairLaw μ ν N base hAS hAT
        (obsS := fun x ↦ obsS (d, x)) (obsT := fun x ↦ obsT (d, x))
        (hobsS.comp (measurable_const.prodMk measurable_id))
        (hobsT.comp (measurable_const.prodMk measurable_id)) :
        Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))) =
      ∫ z, F (f d z) ∂Q := by
    change (∫ z, F z ∂originalIidMaskedLocalInputPairMeasure μ ν N base AS AT _ _) = _
    rw [originalIidMaskedLocalInputPairMeasure_eq_map μ ν N base hAS hAT
      (obsS := fun x ↦ obsS (d, x)) (obsT := fun x ↦ obsT (d, x))
      (hobsS.comp ((measurable_const (a := d)).prodMk measurable_id))
      (hobsT.comp ((measurable_const (a := d)).prodMk measurable_id))]
    exact integral_map (hf d).aemeasurable F.continuous.aestronglyMeasurable
  simp_rw [hread]
  exact tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖F‖)
    (.of_forall (fun d ↦ (F.continuous.measurable.comp (hf d)).aestronglyMeasurable))
    (.of_forall (fun d ↦ .of_forall (fun z ↦ F.norm_coe_le_norm (f d z))))
    (integrable_const _) (.of_forall (fun z ↦ (F.continuous.comp (hfc z)).tendsto c))

end FiniteRootMeasurability
section ActualCore

open Metric Module Manifold OTSelector.Geometry
open scoped ContDiff ENNReal NNReal

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

set_option maxHeartbeats 1800000 in
/-- The actual full-seed iid input limits form a measurable Markov kernel on the
original compact coordinate core. All finite-root laws retain their exact original
sampling, while one common full-measure root set carries whole-sequence weak
convergence, the original Poisson profile, and independence of the two colors. -/
theorem PopulationLocalPressureCore.original_full_seed_input_limit_kernel
    [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    (hnormalization : ∀ n,
      s n ^ finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker =
        ((n + 1 : ℕ) : ℝ)) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let V := Fin q → ℝ
    let X := V × ℝ
    let T := LocalFiniteMeasure X × LocalFiniteMeasure X
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let mask := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
    let obs := fun n c x ↦ (s n • (e (R (a x)) - c), u x)
    let θ := fun c ↦ originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c)
    let μS := fun c ↦ (volume : Measure V).prod (condDistrib u a η₀ (ref c))
    let μT := fun c ↦ (volume : Measure V).prod (condDistrib u a η₁ (ref c))
    ∃ PN : ℕ → V → ProbabilityMeasure T,
      (∀ n, Measurable (PN n)) ∧
      (∀ c n, (PN n c : Measure T) =
        originalIidMaskedLocalInputPairMeasure η₀ η₁ (n + 1) (0 : X)
          mask mask (obs n c) (obs n c)) ∧
      ∃ Q : V → ProbabilityMeasure T, Measurable Q ∧
        ∃ Γ : Kernel V T, IsMarkovKernel Γ ∧
          (∀ c, Γ c = (Q c : Measure T)) ∧
          ∀ᵐ c ∂(volume : Measure V).restrict K,
            Tendsto (fun n ↦ PN n c) atTop (𝓝 (Q c)) ∧
            (∀ H G : LegalNonnegativeInputTest X,
              (∫ z, legalInputMeasureLaplacePair H G z ∂Γ c) =
                Real.exp (-(θ c * ((∫ x, 1 - Real.exp (-H.1 x) ∂μS c) +
                  ∫ y, 1 - Real.exp (-G.1 y) ∂μT c)))) ∧
            IndepFun Prod.fst Prod.snd (Γ c) := by
  dsimp only
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let q := finrank ℝ S.covector.ker
  let V := Fin q → ℝ
  let X := V × ℝ
  let T := LocalFiniteMeasure X × LocalFiniteMeasure X
  let _inputPolish : PolishSpace (LocalFiniteMeasure X) := LocalFiniteMeasure.instPolishSpace
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let K := e '' (R '' C.roots)
  let ref := fun c ↦ a (S.curve (e.symm c) 0)
  let mask := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
  have hmask : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj C.seedIndex
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  let obs := fun n (p : V × M) ↦ (s n • (e (R (a p.2)) - p.1), u p.2)
  have hobs n : Measurable (obs n) := by
    exact ((((e.continuous.measurable.comp (hR.comp ha)).comp measurable_snd).sub
      measurable_fst).const_smul (s n)).prodMk (hu.continuous.measurable.comp measurable_snd)
  have hcont n (x : M) : Continuous (fun c ↦ obs n (c, x)) := by
    change Continuous (fun c : V ↦ (s n • (e (R (a x)) - c), u x))
    exact (((continuous_const : Continuous (fun _ : V ↦ e (R (a x)))).sub
      continuous_id).const_smul (s n)).prodMk continuous_const
  let PN : ℕ → V → ProbabilityMeasure T := fun n c ↦
    originalIidMaskedLocalInputPairLaw η₀ η₁ (n + 1) (0 : X) hmask hmask
      (obsS := fun x ↦ obs n (c, x)) (obsT := fun x ↦ obs n (c, x))
      ((hobs n).comp ((measurable_const (a := c)).prodMk measurable_id))
      ((hobs n).comp ((measurable_const (a := c)).prodMk measurable_id))
  have hPNcont (n : ℕ) : Continuous (PN n) :=
    continuous_original_parameterizedIidMaskedLocalInputPairLaw η₀ η₁ (n + 1) (0 : X)
      hmask hmask (hobs n) (hobs n) (hcont n) (hcont n)
  have hPNmeas (n : ℕ) : Measurable (PN n) :=
    original_measurable_probabilityMeasure_of_continuous (hPNcont n)
  let θ := fun c ↦ originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c)
  let μS := fun c ↦ (volume : Measure V).prod (condDistrib u a η₀ (ref c))
  let μT := fun c ↦ (volume : Measure V).prod (condDistrib u a η₁ (ref c))
  let profile := fun c (Q : ProbabilityMeasure T) ↦
    (∀ H G : LegalNonnegativeInputTest X,
      (∫ z, legalInputMeasureLaplacePair H G z ∂(Q : Measure T)) =
        Real.exp (-(θ c * ((∫ x, 1 - Real.exp (-H.1 x) ∂μS c) +
          ∫ y, 1 - Real.exp (-G.1 y) ∂μT c)))) ∧
      IndepFun Prod.fst Prod.snd (Q : Measure T)
  have hlim : ∀ᵐ c ∂(volume : Measure V).restrict K,
      ∃ Q : ProbabilityMeasure T, Tendsto (fun n ↦ PN n c) atTop (𝓝 Q) ∧ profile c Q := by
    filter_upwards [D.original_ae_full_seed_input_tendsto
      hF hcomplete hu ha hinj i s hs hlarge hnormalization] with c hc
    obtain ⟨PN0, Q, hPN0, hconv, hLaplace, hindep⟩ := hc
    have heq : PN0 = (fun n ↦ PN n c) :=
      funext (fun n ↦ Subtype.ext (hPN0 n))
    rw [heq] at hconv
    exact ⟨Q, hconv, hLaplace, hindep⟩
  obtain ⟨Q, hQ, Γ, hΓ, hΓQ, hΓlim⟩ :=
    exists_markovKernel_ae_weak_limit_with_profile_of_continuous
      ((volume : Measure V).restrict K) PN hPNcont profile hlim
  refine ⟨PN, hPNmeas, ?_, Q, hQ, Γ, hΓ, hΓQ, ?_⟩
  · intro c n
    rfl
  · filter_upwards [hΓlim] with c hc
    refine ⟨hc.1, ?_, ?_⟩
    · intro H G
      rw [hΓQ c]
      exact hc.2.1 H G
    · rw [hΓQ c]
      exact hc.2.2

end ActualCore

end OTSelector.Reconstruction
