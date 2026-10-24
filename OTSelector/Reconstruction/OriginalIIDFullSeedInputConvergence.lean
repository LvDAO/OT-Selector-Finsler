import OTSelector.Reconstruction.OriginalIIDLocalInputIdentification
import OTSelector.Reconstruction.OriginalIIDFullSeedLocalCountMoments

/-!
# Full weak convergence of the actual original full-seed iid input laws

Uniform compact count moments supply tightness of the original pair laws.
The already proved unique weak subsequential profile then determines a full
weak limit of that same sequence.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction BigOperators ENNReal

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false

/-- A finite scaled one-point mass limit bounds every original iid first moment,
including the finite initial prefix of the sequence. -/
theorem original_iid_mass_bound_of_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsFiniteMeasure η]
    (A : ℕ → Set Ω) {L : ℝ}
    (hlim : Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ) * η.real (A n)) atTop (𝓝 L)) :
    ∃ b : ℝ≥0∞, b ≠ (⊤ : ℝ≥0∞) ∧ ∀ n, ((n + 1 : ℕ) : ℝ≥0∞) * η (A n) ≤ b := by
  obtain ⟨b, hb⟩ := hlim.bddAbove_range
  refine ⟨ENNReal.ofReal b, ENNReal.ofReal_ne_top, fun n ↦ ?_⟩
  have hfin : ((n + 1 : ℕ) : ℝ≥0∞) * η (A n) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def] using
    hb (mem_range_self n)

section ActualMoments

variable {Ω X : Type*} [MeasurableSpace Ω]
  [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X] [SecondCountableTopology X]

/-- Measurable observations of the locally finite pair law are evaluated on the
same two original iid arrays, including the original deterministic masks. -/
theorem lintegral_originalIidMaskedLocalInputPairMeasure
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ) (base : X) {AS AT : Set Ω}
    (hAS : MeasurableSet AS) (hAT : MeasurableSet AT)
    {obsS obsT : Ω → X} (hobsS : Measurable obsS) (hobsT : Measurable obsT)
    (f : LocalFiniteMeasure X × LocalFiniteMeasure X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂originalIidMaskedLocalInputPairMeasure μ ν N base AS AT obsS obsT) =
      ∫⁻ z : (Fin N → Ω) × (Fin N → Ω),
        f (LocalConfiguration.toLocalFiniteMeasure
            (LocalConfiguration.ofMaskedTuple base AS obsS z.1),
          LocalConfiguration.toLocalFiniteMeasure
            (LocalConfiguration.ofMaskedTuple base AT obsT z.2))
        ∂(Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν)) := by
  have hm : Measurable (fun c : LocalConfiguration base × LocalConfiguration base ↦
      (LocalConfiguration.toLocalFiniteMeasure c.1,
        LocalConfiguration.toLocalFiniteMeasure c.2)) :=
    ((measurable_originalConfigurationLocalFinite base).comp measurable_fst).prodMk
      ((measurable_originalConfigurationLocalFinite base).comp measurable_snd)
  have hcfg : Measurable (fun z : (Fin N → Ω) × (Fin N → Ω) ↦
      (LocalConfiguration.ofMaskedTuple base AS obsS z.1,
        LocalConfiguration.ofMaskedTuple base AT obsT z.2)) :=
    ((LocalConfiguration.measurable_ofMaskedTuple base hAS hobsS N).comp measurable_fst).prodMk
      ((LocalConfiguration.measurable_ofMaskedTuple base hAT hobsT N).comp measurable_snd)
  change (∫⁻ z, f z ∂(originalIidMaskedConfigurationPairLaw μ ν N N base base AS AT
    obsS obsT).map _) = _
  rw [lintegral_map hf hm, originalIidMaskedConfigurationPairLaw]
  exact lintegral_map (hf.comp hm) hcfg

omit [MeasurableSpace Ω] [ProperSpace X] [BorelSpace X]
  [StandardBorelSpace X] [SecondCountableTopology X] in
/-- A compact observation window can be bounded by any original endpoint event
which contains its retained observations; every repeated label remains counted. -/
theorem original_maskedTuple_count_le_indicatorCount
    (N : ℕ) (base : X) (mask A : Set Ω) (obs : Ω → X)
    (sample : Fin N → Ω) {U : Set X} (hU : MeasurableSet U)
    (hdom : ∀ x ∈ mask, obs x ∈ U → x ∈ A) :
    LocalConfiguration.countingMeasure
      (LocalConfiguration.ofMaskedTuple base mask obs sample) U ≤
      ∑ j : Fin N, A.indicator (1 : Ω → ℝ≥0∞) (sample j) := by
  classical
  rw [LocalConfiguration.countingMeasure_ofMaskedTuple, Measure.finsetSum_apply]
  apply Finset.sum_le_sum
  intro j _
  by_cases hmask : sample j ∈ mask
  · simp only [hmask, ite_true]
    rw [Measure.dirac_apply' _ hU]
    by_cases hu : obs (sample j) ∈ U
    · simp [hu, hdom _ hmask hu]
    · simp [hu]
  · simp [hmask]

set_option maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency true in
/-- An open source window's expected mass is bounded by the actual original
source iid endpoint count in a containing event. -/
theorem lintegral_originalIidMaskedLocalInputPairMeasure_fst_mass_le
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ) (base : X) {AS AT A : Set Ω}
    (hAS : MeasurableSet AS) (hAT : MeasurableSet AT) (hA : MeasurableSet A)
    {obsS obsT : Ω → X} (hobsS : Measurable obsS) (hobsT : Measurable obsT)
    {U : Set X} (hU : IsOpen U) (hdom : ∀ x ∈ AS, obsS x ∈ U → x ∈ A) :
    (∫⁻ z : LocalFiniteMeasure X × LocalFiniteMeasure X, (z.1 : Measure X) U
      ∂originalIidMaskedLocalInputPairMeasure μ ν N base AS AT obsS obsT) ≤
      ∫⁻ sample : Fin N → Ω, ∑ j : Fin N,
        A.indicator (1 : Ω → ℝ≥0∞) (sample j) ∂Measure.pi (fun _ : Fin N ↦ μ) := by
  have hf : Measurable (fun z : LocalFiniteMeasure X × LocalFiniteMeasure X ↦
      (z.1 : Measure X) U) :=
    (LocalFiniteMeasure.measurable_measure_open hU).comp measurable_fst
  rw [lintegral_originalIidMaskedLocalInputPairMeasure μ ν N base hAS hAT hobsS hobsT _ hf]
  change (∫⁻ z : (Fin N → Ω) × (Fin N → Ω),
    LocalConfiguration.countingMeasure
      (LocalConfiguration.ofMaskedTuple base AS obsS z.1) U
      ∂(Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν))) ≤ _
  have hc : Measurable (fun sample : Fin N → Ω ↦
      ∑ j : Fin N, A.indicator (1 : Ω → ℝ≥0∞) (sample j)) :=
    Finset.measurable_sum _ (fun j _ ↦
      (measurable_const.indicator hA).comp (measurable_pi_apply j))
  calc
    _ ≤ ∫⁻ z : (Fin N → Ω) × (Fin N → Ω),
        (∑ j : Fin N, A.indicator (1 : Ω → ℝ≥0∞) (z.1 j))
        ∂(Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν)) := by
      exact lintegral_mono (fun z : (Fin N → Ω) × (Fin N → Ω) ↦
        original_maskedTuple_count_le_indicatorCount N base AS A obsS z.1 hU.measurableSet hdom)
    _ = _ := by
      rw [← lintegral_map hc measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

set_option maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency true in
/-- The target window bound uses the unchanged original target iid sample,
with its own deterministic endpoint mask. -/
theorem lintegral_originalIidMaskedLocalInputPairMeasure_snd_mass_le
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ) (base : X) {AS AT A : Set Ω}
    (hAS : MeasurableSet AS) (hAT : MeasurableSet AT) (hA : MeasurableSet A)
    {obsS obsT : Ω → X} (hobsS : Measurable obsS) (hobsT : Measurable obsT)
    {U : Set X} (hU : IsOpen U) (hdom : ∀ x ∈ AT, obsT x ∈ U → x ∈ A) :
    (∫⁻ z : LocalFiniteMeasure X × LocalFiniteMeasure X, (z.2 : Measure X) U
      ∂originalIidMaskedLocalInputPairMeasure μ ν N base AS AT obsS obsT) ≤
      ∫⁻ sample : Fin N → Ω, ∑ j : Fin N,
        A.indicator (1 : Ω → ℝ≥0∞) (sample j) ∂Measure.pi (fun _ : Fin N ↦ ν) := by
  have hf : Measurable (fun z : LocalFiniteMeasure X × LocalFiniteMeasure X ↦
      (z.2 : Measure X) U) :=
    (LocalFiniteMeasure.measurable_measure_open hU).comp measurable_snd
  rw [lintegral_originalIidMaskedLocalInputPairMeasure μ ν N base hAS hAT hobsS hobsT _ hf]
  change (∫⁻ z : (Fin N → Ω) × (Fin N → Ω),
    LocalConfiguration.countingMeasure
      (LocalConfiguration.ofMaskedTuple base AT obsT z.2) U
      ∂(Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν))) ≤ _
  have hc : Measurable (fun sample : Fin N → Ω ↦
      ∑ j : Fin N, A.indicator (1 : Ω → ℝ≥0∞) (sample j)) :=
    Finset.measurable_sum _ (fun j _ ↦
      (measurable_const.indicator hA).comp (measurable_pi_apply j))
  calc
    _ ≤ ∫⁻ z : (Fin N → Ω) × (Fin N → Ω),
        (∑ j : Fin N, A.indicator (1 : Ω → ℝ≥0∞) (z.2 j))
        ∂(Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν)) := by
      exact lintegral_mono (fun z : (Fin N → Ω) × (Fin N → Ω) ↦
        original_maskedTuple_count_le_indicatorCount N base AT A obsT z.2 hU.measurableSet hdom)
    _ = _ := by
      rw [← lintegral_map hc measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

end ActualMoments

/-- Joint local first moments give tightness without changing the pair law or
assuming independence of its two coordinates. -/
theorem original_input_pair_tight_of_localMass_bounds
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (P : ℕ → ProbabilityMeasure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (hcover : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ U n)
    (bS bT : ℕ → ℝ≥0∞) (hbS : ∀ n, bS n ≠ ∞) (hbT : ∀ n, bT n ≠ ∞)
    (hS : ∀ i n, ∫⁻ z, (z.1 : Measure X) (U n)
      ∂(P i : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)) ≤ bS n)
    (hT : ∀ i n, ∫⁻ z, (z.2 : Measure X) (U n)
      ∂(P i : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)) ≤ bT n) :
    IsTightMeasureSet (range fun i ↦
      (P i : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))) := by
  apply IsTightMeasureSet.prodMk
  · apply LocalFiniteMeasure.isTightMeasureSet_of_lintegral_localMass_le U hU hcover _ bS hbS
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩ n
    rw [Measure.fst, lintegral_map (LocalFiniteMeasure.measurable_measure_open (hU n))
      measurable_fst]
    exact hS i n
  · apply LocalFiniteMeasure.isTightMeasureSet_of_lintegral_localMass_le U hU hcover _ bT hbT
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩ n
    rw [Measure.snd, lintegral_map (LocalFiniteMeasure.measurable_measure_open (hU n))
      measurable_snd]
    exact hT i n

/-- Tightness and uniqueness across genuine weak subsequences imply convergence
of the whole original sequence; Prokhorov also supplies the limit's existence. -/
theorem original_input_exists_tendsto_of_tight_unique_subseq
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [T2Space S] [PseudoMetrizableSpace S] [SeparableSpace S]
    (P : ℕ → ProbabilityMeasure S)
    (htight : IsTightMeasureSet (range fun n ↦ (P n : Measure S)))
    (hunique : ∀ (φ ψ : ℕ → ℕ), StrictMono φ → StrictMono ψ →
      ∀ Q Q' : ProbabilityMeasure S,
        Tendsto (P ∘ φ) atTop (𝓝 Q) → Tendsto (P ∘ ψ) atTop (𝓝 Q') → Q = Q') :
    ∃ Q : ProbabilityMeasure S, Tendsto P atTop (𝓝 Q) := by
  obtain ⟨Q, φ, hφ, hQ⟩ := exists_tendsto_subseq_probabilityMeasure_of_isTight P htight
  refine ⟨Q, ?_⟩
  by_contra hnot
  obtain ⟨A, hA, hbad⟩ := not_tendsto_iff_exists_frequently_notMem.mp hnot
  obtain ⟨ψ, hψ, hψbad⟩ := extraction_of_frequently_atTop hbad
  have hsubtight : IsTightMeasureSet (range fun n ↦ (P (ψ n) : Measure S)) :=
    htight.subset (by rintro _ ⟨n, rfl⟩; exact ⟨ψ n, rfl⟩)
  obtain ⟨Q', ξ, hξ, hQ'⟩ :=
    exists_tendsto_subseq_probabilityMeasure_of_isTight (P ∘ ψ) hsubtight
  have heq : Q = Q' := hunique φ (ψ ∘ ξ) hφ (hψ.comp hξ) Q Q' hQ hQ'
  subst Q'
  obtain ⟨n, hn⟩ := (hQ'.eventually_mem hA).exists
  exact hψbad (ξ n) hn

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

set_option maxHeartbeats 2200000 in
/-- The unchanged original full-seed iid input pair laws converge weakly at one
common full-measure set of retained coordinate roots. Their limit has the actual
Poisson compact Laplace profile and independent original source and target clocks.
Both compact containment and the limit's existence follow from the proved
original count moments; no tightness or desired-law assumption is supplied. -/
theorem PopulationLocalPressureCore.original_ae_full_seed_input_tendsto
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
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let mask := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
    ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      let obs := fun n x ↦ (s n • (e (R (a x)) - c), u x)
      let θ := originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c)
      let μS := (volume : Measure (Fin q → ℝ)).prod (condDistrib u a η₀ (ref c))
      let μT := (volume : Measure (Fin q → ℝ)).prod (condDistrib u a η₁ (ref c))
      ∃ PN : ℕ → ProbabilityMeasure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) ×
          LocalFiniteMeasure ((Fin q → ℝ) × ℝ)),
        ∃ Q : ProbabilityMeasure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) ×
          LocalFiniteMeasure ((Fin q → ℝ) × ℝ)),
        (∀ n, (PN n : Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) ×
            LocalFiniteMeasure ((Fin q → ℝ) × ℝ))) =
          originalIidMaskedLocalInputPairMeasure η₀ η₁ (n + 1) (0 : ((Fin q → ℝ) × ℝ))
            mask mask (obs n) (obs n)) ∧
        Tendsto PN atTop (𝓝 Q) ∧
        (∀ H G : LegalNonnegativeInputTest ((Fin q → ℝ) × ℝ),
          (∫ z, legalInputMeasureLaplacePair H G z
            ∂(Q : Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) ×
              LocalFiniteMeasure ((Fin q → ℝ) × ℝ)))) =
            Real.exp (-(θ * ((∫ x, 1 - Real.exp (-H.1 x) ∂μS) +
              ∫ y, 1 - Real.exp (-G.1 y) ∂μT)))) ∧
        IndepFun Prod.fst Prod.snd (Q : Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) ×
          LocalFiniteMeasure ((Fin q → ℝ) × ℝ))) := by
  dsimp only
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let q := finrank ℝ S.covector.ker
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let mask := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
  let X := (Fin q → ℝ) × ℝ
  let _inputPolish : PolishSpace (LocalFiniteMeasure X) := LocalFiniteMeasure.instPolishSpace
  have hmask : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj C.seedIndex
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  filter_upwards [D.original_ae_full_seed_input_weak_subseq_identification
    hF hcomplete hu ha hinj i s hs hlarge hnormalization,
    D.original_ae_full_seed_spatial_mass_tendsto
      hF hcomplete hu ha hinj i s hs hlarge hnormalization] with c hc hmass
  obtain ⟨PN, hPN, hprofile, hunique⟩ := hc
  let obs := fun n x ↦ (s n • (e (R (a x)) - c), u x)
  have hobs n : Measurable (obs n) := by
    change Measurable (fun x ↦ (s n • (e (R (a x)) - c), u x))
    exact (((e.continuous.measurable.comp (hR.comp ha)).sub_const c).const_smul (s n)).prodMk
      hu.continuous.measurable
  let Ex := CompactExhaustion.choice X
  have hspatial (m : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ Ex m, ‖p.1‖ < B := by
    obtain ⟨B, hB, hbound⟩ :=
      ((Ex.isCompact m).image continuous_fst).isBounded.exists_pos_norm_lt
    exact ⟨B, hB, fun p hp ↦ hbound _ ⟨p, hp, rfl⟩⟩
  choose B hB hspatial using hspatial
  let A := fun n m ↦ mask ∩ {x | (obs n x).1 ∈ closedBall 0 (B m)}
  have hA n m : MeasurableSet (A n m) :=
    hmask.inter (isClosed_closedBall.measurableSet.preimage (hobs n).fst)
  have hdom n m : ∀ x ∈ mask, obs n x ∈ interior (Ex m) → x ∈ A n m := by
    intro x hx hxu
    exact ⟨hx, mem_closedBall_zero_iff.mpr (hspatial m _ (interior_subset hxu)).le⟩
  have hbS (m : ℕ) : ∃ b : ℝ≥0∞, b ≠ (⊤ : ℝ≥0∞) ∧
      ∀ n, ((n + 1 : ℕ) : ℝ≥0∞) * η₀ (A n m) ≤ b := by
    apply original_iid_mass_bound_of_tendsto η₀ (fun n ↦ A n m)
    simpa only [A, obs, ite_true] using hmass (B m) (hB m) (0 : Fin 2)
  have hbT (m : ℕ) : ∃ b : ℝ≥0∞, b ≠ (⊤ : ℝ≥0∞) ∧
      ∀ n, ((n + 1 : ℕ) : ℝ≥0∞) * η₁ (A n m) ≤ b := by
    apply original_iid_mass_bound_of_tendsto η₁ (fun n ↦ A n m)
    simpa only [A, obs, one_ne_zero, ite_false] using hmass (B m) (hB m) (1 : Fin 2)
  choose bS hbS hcountS using hbS
  choose bT hbT hcountT using hbT
  have hcover : ∀ K : Set X, IsCompact K → ∃ m, K ⊆ interior (Ex m) := by
    intro K hK
    obtain ⟨m, hm⟩ := Ex.exists_superset_of_isCompact hK
    exact ⟨m + 1, hm.trans (Ex.subset_interior_succ m)⟩
  have hS n m : (∫⁻ z : LocalFiniteMeasure X × LocalFiniteMeasure X,
      (z.1 : Measure X) (interior (Ex m)) ∂(PN n : Measure _)) ≤ bS m := by
    rw [hPN n]
    exact (lintegral_originalIidMaskedLocalInputPairMeasure_fst_mass_le η₀ η₁
      (n + 1) (0 : X) hmask hmask (hA n m) (hobs n) (hobs n)
      isOpen_interior (hdom n m)).trans
        ((lintegral_iid_indicatorCount_eq η₀ (hA n m) (n + 1)).trans_le (hcountS m n))
  have hT n m : (∫⁻ z : LocalFiniteMeasure X × LocalFiniteMeasure X,
      (z.2 : Measure X) (interior (Ex m)) ∂(PN n : Measure _)) ≤ bT m := by
    rw [hPN n]
    exact (lintegral_originalIidMaskedLocalInputPairMeasure_snd_mass_le η₀ η₁
      (n + 1) (0 : X) hmask hmask (hA n m) (hobs n) (hobs n)
      isOpen_interior (hdom n m)).trans
        ((lintegral_iid_indicatorCount_eq η₁ (hA n m) (n + 1)).trans_le (hcountT m n))
  have htight := original_input_pair_tight_of_localMass_bounds PN
    (fun m ↦ interior (Ex m)) (fun _ ↦ isOpen_interior) hcover bS bT hbS hbT hS hT
  obtain ⟨Q, hfull⟩ := original_input_exists_tendsto_of_tight_unique_subseq PN htight hunique
  have hlimit := hprofile id strictMono_id Q (by simpa only [comp_id] using hfull)
  exact ⟨PN, Q, hPN, hfull, hlimit.1, hlimit.2⟩

end ActualCore


end OTSelector.Reconstruction
