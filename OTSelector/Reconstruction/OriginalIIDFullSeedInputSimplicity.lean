import OTSelector.Reconstruction.OriginalIIDFullSeedInputKernel
import OTSelector.Reconstruction.OriginalIIDRootedCountingLimit
import OTSelector.PointProcess.CutoffLaplaceLaw
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputFiniteSimplicity
import OTSelector.Reconstruction.OriginalIIDFinitePoissonReference

/-!
# Simplicity of the actual full-seed iid input weak limit

All finite laws remain the original iid masked input laws. Their closed integer
carrier survives the genuine weak limit. The actual compact Poisson Laplace
profile identifies simple finite Poisson restrictions, with its original
nonnegative intensity retained, on a countable compact exhaustion.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false

section Counting
variable {Ω X : Type*} [MeasurableSpace Ω]
  [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X] [SecondCountableTopology X]
local instance originalInputSimplicityLawPolish : PolishSpace (LocalFiniteMeasure X) :=
  LocalFiniteMeasure.instPolishSpace

/-- Both finite input coordinates are the literal original masked integer
configurations, including any repeated observations. -/
theorem ae_counting_originalIidMaskedLocalInputPairMeasure
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ) (base : X) {AS AT : Set Ω}
    (hAS : MeasurableSet AS) (hAT : MeasurableSet AT)
    {obsS obsT : Ω → X} (hobsS : Measurable obsS) (hobsT : Measurable obsT) :
    ∀ᵐ z ∂originalIidMaskedLocalInputPairMeasure μ ν N base AS AT obsS obsT,
      IsLegalCountingMeasure base z.1 ∧ IsLegalCountingMeasure base z.2 := by
  have hS : Measurable (fun z : (Fin N → Ω) × (Fin N → Ω) ↦
      LocalConfiguration.toLocalFiniteMeasure (LocalConfiguration.ofMaskedTuple base AS obsS z.1)) :=
    (measurable_originalConfigurationLocalFinite base).comp
      ((LocalConfiguration.measurable_ofMaskedTuple base hAS hobsS N).comp measurable_fst)
  have hT : Measurable (fun z : (Fin N → Ω) × (Fin N → Ω) ↦
      LocalConfiguration.toLocalFiniteMeasure (LocalConfiguration.ofMaskedTuple base AT obsT z.2)) :=
    (measurable_originalConfigurationLocalFinite base).comp
      ((LocalConfiguration.measurable_ofMaskedTuple base hAT hobsT N).comp measurable_snd)
  have hE : MeasurableSet {z : LocalFiniteMeasure X × LocalFiniteMeasure X |
      IsLegalCountingMeasure base z.1 ∧ IsLegalCountingMeasure base z.2} :=
    ((isClosed_isLegalCountingMeasure base).preimage continuous_fst).measurableSet.inter
      ((isClosed_isLegalCountingMeasure base).preimage continuous_snd).measurableSet
  rw [originalIidMaskedLocalInputPairMeasure_eq_map μ ν N base hAS hAT hobsS hobsT]
  apply (ae_map_iff (hS.prodMk hT).aemeasurable hE).mpr
  exact .of_forall fun z ↦ ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- A genuine weak limit of those same original finite laws retains both
integer point measures; no counting assertion about the desired law is assumed. -/
theorem ae_counting_of_originalIidMaskedLocalInputPairMeasure_tendsto
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ → ℕ) (base : X) {AS AT : Set Ω}
    (hAS : MeasurableSet AS) (hAT : MeasurableSet AT)
    {obsS obsT : ℕ → Ω → X} (hobsS : ∀ n, Measurable (obsS n))
    (hobsT : ∀ n, Measurable (obsT n))
    (PN : ℕ → ProbabilityMeasure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (Q : ProbabilityMeasure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (hPN : ∀ n, (PN n : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)) =
      originalIidMaskedLocalInputPairMeasure μ ν (N n) base AS AT (obsS n) (obsT n))
    (hweak : Tendsto PN atTop (𝓝 Q)) :
    ∀ᵐ z ∂(Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)),
      IsLegalCountingMeasure base z.1 ∧ IsLegalCountingMeasure base z.2 := by
  have hn (n : ℕ) : ∀ᵐ z ∂(PN n : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)),
      IsLegalCountingMeasure base z.1 ∧ IsLegalCountingMeasure base z.2 := by
    rw [hPN n]
    exact ae_counting_originalIidMaskedLocalInputPairMeasure μ ν (N n) base
      hAS hAT (hobsS n) (hobsT n)
  exact (ae_isLegalCountingMeasure_of_continuous_readout_tendsto base Prod.fst
    continuous_fst PN Q hweak (fun n ↦ (hn n).mono (fun _ h ↦ h.1))).and
      (ae_isLegalCountingMeasure_of_continuous_readout_tendsto base Prod.snd
        continuous_snd PN Q hweak (fun n ↦ (hn n).mono (fun _ h ↦ h.2)))
end Counting

section Restrictions
variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

/-- Generic lifting of a compact restriction law to the original vague
carrier, whose finite-version fallback is pointwise unused on that compact. -/
theorem map_legalInputRestrictionLocal_eq_of_cutoff_laplace
    (P P' : Measure (LocalFiniteMeasure X)) [IsFiniteMeasure P] [IsFiniteMeasure P']
    (η : C(X, ℝ)) (hη : ∀ x, 0 ≤ η x) {U : Set X} (hU : IsCompact U)
    (hηU : EqOn η 1 U)
    (h : ∀ F : LegalNonnegativeInputTest X,
      (∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η, fun x ↦ mul_nonneg (F.2 x) (hη x)⟩ μ ∂P) =
      ∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η, fun x ↦ mul_nonneg (F.2 x) (hη x)⟩ μ ∂P') :
    P.map (legalInputRestrictionLocal U) = P'.map (legalInputRestrictionLocal U) := by
  have hraw := map_legalInput_restrict_eq_of_cutoff_laplace P P' η hη hU.measurableSet hηU h
  let lift := finitePlanLocalVersion (id : Measure X → Measure X)
  have hlift : Measurable lift := measurable_finitePlanLocalVersion id measurable_id
  have hrestrict : Measurable (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X).restrict U) :=
    measurable_localFiniteMeasure_coe.comp (measurable_legalInputRestrictionLocal hU.measurableSet)
  have hmap := congrArg (fun R : Measure (Measure X) ↦ R.map lift) hraw
  rw [Measure.map_map hlift hrestrict, Measure.map_map hlift hrestrict] at hmap
  simpa only [Function.comp_def, lift, finitePlanLocalVersion_restrict_compact_eq hU] using hmap

/-- Simplicity on a countable compact exhaustion gives unit atoms of the same
whole integer measure, without an uncountable intersection of exceptional sets. -/
theorem ae_simple_counting_of_compact_restrictions
    [StandardBorelSpace X] (base : X) (P : Measure (LocalFiniteMeasure X))
    (hc : ∀ᵐ μ ∂P, IsLegalCountingMeasure base μ)
    (hlocal : ∀ U : Set X, IsCompact U →
      ∀ᵐ μ ∂P, IsLegalSimpleCountingMeasure base (legalInputRestrictionLocal U μ)) :
    ∀ᵐ μ ∂P, IsLegalSimpleCountingMeasure base μ := by
  let K := CompactExhaustion.choice X
  filter_upwards [ae_all_iff.mpr (fun n ↦ hlocal (K n) (K.isCompact n)), hc] with μ hm hcount
  apply (isLegalSimpleCountingMeasure_iff base μ).mpr
  refine ⟨hcount, fun x ↦ ?_⟩
  obtain ⟨n, hxn⟩ := K.exists_mem x
  have hunit := ((isLegalSimpleCountingMeasure_iff base _).mp (hm n)).2 x
  change ((μ : Measure X).restrict (K n)) {x} ≤ 1 at hunit
  simpa only [Measure.restrict_apply (measurableSet_singleton x),
    singleton_inter_of_mem hxn] using hunit
end Restrictions
section SpatialSupport
/-- Every actual compact spatial/clock test vanishes outside one finite
spatial cube, without a bounded-clock assumption on the mark distribution. -/
theorem exists_originalInput_spatial_cube_support (q : ℕ)
    (F : C_c((Fin q → ℝ) × ℝ, ℝ)) :
    ∃ S > 0, ∀ x : (Fin q → ℝ) × ℝ,
      x.1 ∉ haarRootCube (Fin q) S → F x = 0 := by
  obtain ⟨S,hS,hbound⟩ := (F.hasCompactSupport.image continuous_fst).isBounded.exists_pos_norm_lt
  refine ⟨S,hS,?_⟩
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hsupp
  apply hx
  have hn : ‖x.1‖ < S := hbound _ ⟨x, hsupp, rfl⟩
  have hi (i : Fin q) : |x.1 i| ≤ S := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x.1 i).trans hn.le
  exact ⟨fun i ↦ (abs_le.mp (hi i)).1, fun i ↦ (abs_le.mp (hi i)).2⟩
end SpatialSupport

section MarginalProfile
variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

/-- Setting the unused test to zero extracts both actual marginal Laplace
profiles from the original joint two-color profile, with its same intensity. -/
theorem originalInput_marginal_laplace_of_pair_profile
    (P : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)) [IsFiniteMeasure P]
    (θ : ℝ) (μS μT : Measure X)
    (h : ∀ H G : LegalNonnegativeInputTest X,
      (∫ z, legalInputMeasureLaplacePair H G z ∂P) =
        Real.exp (-(θ * ((∫ x, 1 - Real.exp (-H.1 x) ∂μS) +
          ∫ y, 1 - Real.exp (-G.1 y) ∂μT)))) :
    (∀ H : LegalNonnegativeInputTest X,
      (∫ μ, legalInputMeasureLaplace H μ ∂P.map Prod.fst) =
        Real.exp (-(θ * ∫ x, 1 - Real.exp (-H.1 x) ∂μS))) ∧
    (∀ G : LegalNonnegativeInputTest X,
      (∫ μ, legalInputMeasureLaplace G μ ∂P.map Prod.snd) =
        Real.exp (-(θ * ∫ y, 1 - Real.exp (-G.1 y) ∂μT))) := by
  constructor
  · intro H
    rw [integral_map measurable_fst.aemeasurable
      (legalInputMeasureLaplace H).continuous.aestronglyMeasurable]
    simpa [legalInputMeasureLaplacePair] using h H ⟨0, fun _ ↦ le_rfl⟩
  · intro G
    rw [integral_map measurable_snd.aemeasurable
      (legalInputMeasureLaplace G).continuous.aestronglyMeasurable]
    simpa [legalInputMeasureLaplacePair] using h ⟨0, fun _ ↦ le_rfl⟩ G
end MarginalProfile

/-- A genuine compact Poisson profile with arbitrary nonnegative intensity
makes the same integer input simple. Clock laws can have atoms. -/
theorem ae_simple_counting_of_compact_poisson_profile
    (q : ℕ) (hq : 0 < q) (θ : ℝ) (hθ : 0 ≤ θ)
    (α : Measure ℝ) [IsProbabilityMeasure α]
    (P : Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ))) [IsProbabilityMeasure P]
    (hLaplace : ∀ F : LegalNonnegativeInputTest ((Fin q → ℝ) × ℝ),
      (∫ μ, legalInputMeasureLaplace F μ ∂P) =
        Real.exp (-(θ * ∫ x, 1 - Real.exp (-F.1 x) ∂volume.prod α)))
    (hc : ∀ᵐ μ ∂P, IsLegalCountingMeasure (0 : (Fin q → ℝ) × ℝ) μ) :
    ∀ᵐ μ ∂P, IsLegalSimpleCountingMeasure (0 : (Fin q → ℝ) × ℝ) μ := by
  let X := (Fin q → ℝ) × ℝ
  apply ae_simple_counting_of_compact_restrictions (0 : X) P hc
  intro U hU
  obtain ⟨η,hηU,hη⟩ := LocalFiniteMeasure.exists_compact_cutoff hU
  obtain ⟨S,hS,hηzero⟩ := exists_originalInput_spatial_cube_support q η
  let P' := originalFinitePoissonInputLaw q hS θ α
  have _hPprob : IsProbabilityMeasure P' :=
    isProbabilityMeasure_originalFinitePoissonInputLaw q hS θ α
  have hlocalLaw : P.map (legalInputRestrictionLocal U) =
      P'.map (legalInputRestrictionLocal U) := by
    apply map_legalInputRestrictionLocal_eq_of_cutoff_laplace P P' η.toContinuousMap
      (fun x ↦ (hη x).1) hU hηU
    intro F
    let G : LegalNonnegativeInputTest X :=
      ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η.toContinuousMap,
        fun x ↦ mul_nonneg (F.2 x) (hη x).1⟩
    have hGzero (x : X) (hx : x.1 ∉ haarRootCube (Fin q) S) : G.1 x = 0 := by
      change F.1 x * η x = 0
      rw [hηzero x hx, mul_zero]
    exact (hLaplace G).trans
      (integral_originalFinitePoissonInputLaw_laplace_eq q hS θ hθ α G hGzero).symm
  have hsimp := measurableSet_isLegalSimpleCountingMeasure (0 : X)
  have hrestrict := measurable_legalInputRestrictionLocal hU.measurableSet
  apply (ae_map_iff hrestrict.aemeasurable hsimp).mp
  rw [hlocalLaw]
  apply (ae_map_iff hrestrict.aemeasurable hsimp).mpr
  exact (ae_simple_originalFinitePoissonInputLaw q hq hS θ α).mono fun μ hm ↦
    isLegalSimpleCountingMeasure_restrict (0 : X) μ hm U

/-- The original two-color Poisson profile has simple integer inputs in both
coordinates at its genuine intensity, without a diffuse-clock assumption. -/
theorem ae_simple_pair_of_compact_poisson_profile
    (q : ℕ) (hq : 0 < q) (θ : ℝ) (hθ : 0 ≤ θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (P : Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) ×
      LocalFiniteMeasure ((Fin q → ℝ) × ℝ))) [IsProbabilityMeasure P]
    (hLaplace : ∀ H G : LegalNonnegativeInputTest ((Fin q → ℝ) × ℝ),
      (∫ z, legalInputMeasureLaplacePair H G z ∂P) =
        Real.exp (-(θ * ((∫ x, 1 - Real.exp (-H.1 x) ∂(volume.prod α)) +
          ∫ y, 1 - Real.exp (-G.1 y) ∂(volume.prod β)))))
    (hc : ∀ᵐ z ∂P,
      IsLegalCountingMeasure (0 : (Fin q → ℝ) × ℝ) z.1 ∧
        IsLegalCountingMeasure (0 : (Fin q → ℝ) × ℝ) z.2) :
    ∀ᵐ z ∂P,
      IsLegalSimpleCountingMeasure (0 : (Fin q → ℝ) × ℝ) z.1 ∧
        IsLegalSimpleCountingMeasure (0 : (Fin q → ℝ) × ℝ) z.2 := by
  let X := (Fin q → ℝ) × ℝ
  have hprof := originalInput_marginal_laplace_of_pair_profile P θ
    (volume.prod α) (volume.prod β) hLaplace
  have hcountmeas := (isClosed_isLegalCountingMeasure (0 : X)).measurableSet
  have hSCount : ∀ᵐ μ ∂P.map Prod.fst, IsLegalCountingMeasure (0 : X) μ :=
    (ae_map_iff measurable_fst.aemeasurable hcountmeas).mpr (hc.mono fun _ h ↦ h.1)
  have hTCount : ∀ᵐ μ ∂P.map Prod.snd, IsLegalCountingMeasure (0 : X) μ :=
    (ae_map_iff measurable_snd.aemeasurable hcountmeas).mpr (hc.mono fun _ h ↦ h.2)
  have _hSProb : IsProbabilityMeasure (P.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have _hTProb : IsProbabilityMeasure (P.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hS := ae_simple_counting_of_compact_poisson_profile q hq θ hθ α
    (P.map Prod.fst) hprof.1 hSCount
  have hT := ae_simple_counting_of_compact_poisson_profile q hq θ hθ β
    (P.map Prod.snd) hprof.2 hTCount
  have hsimplemeas := measurableSet_isLegalSimpleCountingMeasure (0 : X)
  exact ((ae_map_iff measurable_fst.aemeasurable hsimplemeas).mp hS).and
    ((ae_map_iff measurable_snd.aemeasurable hsimplemeas).mp hT)

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


/-- The unchanged actual full-seed input laws have one measurable limit kernel
whose same full-measure root set carries the genuine intensity, whole Poisson
Laplace profile, independence, and simple integer inputs in both colors.
Simplicity and integer counting are derived from its original finite laws. -/
theorem PopulationLocalPressureCore.original_full_seed_input_limit_kernel_simple
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
            IndepFun Prod.fst Prod.snd (Γ c) ∧
            (∀ᵐ z ∂Γ c, IsLegalSimpleCountingMeasure (0 : X) z.1 ∧
              IsLegalSimpleCountingMeasure (0 : X) z.2) := by
  dsimp only
  let _actualInputSimplicityMetric : MetricSpace M := F.metricSpace
  let _actualInputSimplicityProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _actualInputSimplicityPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let q := finrank ℝ S.covector.ker
  let V := Fin q → ℝ
  let X := V × ℝ
  let T := LocalFiniteMeasure X × LocalFiniteMeasure X
  let _actualInputSimplicityLfmPolish : PolishSpace (LocalFiniteMeasure X) :=
    LocalFiniteMeasure.instPolishSpace
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let ref := fun c : V ↦ a (S.curve (e.symm c) 0)
  let mask := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
  have hmask : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj C.seedIndex
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have hobs (n : ℕ) (c : V) : Measurable
      (fun x : M ↦ (s n • (e (R (a x)) - c), u x)) :=
    (((e.continuous.measurable.comp (hR.comp ha)).sub measurable_const).const_smul (s n)).prodMk
      hu.continuous.measurable
  have hq : 0 < q := Nat.pos_of_ne_zero (fun hzero ↦ by
    have hn := hnormalization 1
    change s 1 ^ q = ((1 + 1 : ℕ) : ℝ) at hn
    norm_num [hzero] at hn)
  obtain ⟨PN,hPN,hraw,Q,hQ,Γ,hΓ,hΓQ,hAE⟩ :=
    D.original_full_seed_input_limit_kernel hF hcomplete hu ha hinj i s hs hlarge hnormalization
  refine ⟨PN,hPN,hraw,Q,hQ,Γ,hΓ,hΓQ,?_⟩
  filter_upwards [hAE] with c hc
  have hcount := ae_counting_of_originalIidMaskedLocalInputPairMeasure_tendsto
    η₀ η₁ (fun n ↦ n + 1) (0 : X) hmask hmask
    (fun n ↦ hobs n c) (fun n ↦ hobs n c) (fun n ↦ PN n c) (Q c)
    (hraw c) hc.1
  have hΓcount : ∀ᵐ z ∂Γ c,
      IsLegalCountingMeasure (0 : X) z.1 ∧ IsLegalCountingMeasure (0 : X) z.2 := by
    rw [hΓQ c]
    exact hcount
  have _hΓprob : IsProbabilityMeasure (Γ c) := by rw [hΓQ c]; infer_instance
  let θ := originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c)
  have hθ : 0 ≤ θ := by
    exact mul_nonneg (NNReal.coe_nonneg _)
      (populationAtlasTheta_nonneg P a κ lambda C.seedIndex (ref c))
  have hsimple := ae_simple_pair_of_compact_poisson_profile q hq θ hθ
    (condDistrib u a η₀ (ref c)) (condDistrib u a η₁ (ref c)) (Γ c) hc.2.1 hΓcount
  exact ⟨hc.1, hc.2.1, hc.2.2, hsimple⟩

end ActualCore

end OTSelector.Reconstruction
