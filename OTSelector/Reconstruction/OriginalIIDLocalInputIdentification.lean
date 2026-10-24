import OTSelector.Reconstruction.OriginalIIDFullSeedLocalLaplace
import OTSelector.Probability.OriginalIIDConfigurationLaplace
import OTSelector.PointProcess.PairLaplaceDetermination
import OTSelector.PointProcess.LocalConfiguration.Polish
import OTSelector.MeasureTheory.LocalFiniteMeasureProbability

/-!
# Weak subsequential identification of the actual full-seed iid input laws

The original full fixed-seed observations are measurably encoded as locally
finite measure pairs. Their proved compact Laplace limits identify every
extracted weak limit, including the original intensity, both conditional clocks,
independence of the colors, and uniqueness across weak subsequences.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false

section LawIdentification

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]

local instance : PolishSpace (LocalFiniteMeasure X) := LocalFiniteMeasure.instPolishSpace


/-- A genuine weak subsequence retains the already proved compact Laplace
limit, because these observations are bounded and continuous. -/
theorem original_input_weak_subseq_laplace
    (P : ℕ → ProbabilityMeasure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (Q : ProbabilityMeasure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hweak : Tendsto (P ∘ φ) atTop (𝓝 Q))
    (F G : LegalNonnegativeInputTest X) {L : ℝ}
    (hLaplace : Tendsto (fun n ↦ ∫ z, legalInputMeasureLaplacePair F G z
      ∂(P n : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))) atTop (𝓝 L)) :
    (∫ z, legalInputMeasureLaplacePair F G z
      ∂(Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))) = L := by
  have hobs := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak
    (legalInputMeasureLaplacePair F G)
  exact tendsto_nhds_unique hobs (hLaplace.comp hφ.tendsto_atTop)


/-- The analytic compact Laplace profile identifies every weak subsequential
pair law, independently of the chosen extracted subsequence. -/
theorem original_input_weak_subseq_unique
    (P : ℕ → ProbabilityMeasure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (Q Q' : ProbabilityMeasure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (φ ψ : ℕ → ℕ) (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hweak : Tendsto (P ∘ φ) atTop (𝓝 Q))
    (hweak' : Tendsto (P ∘ ψ) atTop (𝓝 Q'))
    (L : LegalNonnegativeInputTest X → LegalNonnegativeInputTest X → ℝ)
    (hLaplace : ∀ F G, Tendsto (fun n ↦ ∫ z, legalInputMeasureLaplacePair F G z
      ∂(P n : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))) atTop (𝓝 (L F G))) :
    Q = Q' := by
  have : IsProbabilityMeasure (Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)) := Q.property
  have : IsProbabilityMeasure (Q' : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)) := Q'.property
  apply Subtype.ext
  apply measure_eq_of_legalInput_compact_laplace_pair
    (Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (Q' : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))
  intro F G
  exact (original_input_weak_subseq_laplace P Q φ hφ hweak F G (hLaplace F G)).trans
    (original_input_weak_subseq_laplace P Q' ψ hψ hweak' F G (hLaplace F G)).symm


/-- A factorized compact Laplace profile proves independence of the actual
two input colors in the extracted limit; independence is not a hypothesis. -/
theorem original_input_indep_of_factorized_laplace
    (Q : ProbabilityMeasure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (LS LT : LegalNonnegativeInputTest X → ℝ)
    (hS0 : LS ⟨0, fun _ ↦ le_rfl⟩ = 1) (hT0 : LT ⟨0, fun _ ↦ le_rfl⟩ = 1)
    (hLaplace : ∀ F G,
      (∫ z, legalInputMeasureLaplacePair F G z
        ∂(Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))) = LS F * LT G) :
    IndepFun Prod.fst Prod.snd (Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)) := by
  have : IsProbabilityMeasure (Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)) := Q.property
  apply indepFun_of_legalInput_compact_laplace_factorization (X := X)
    (Ω := LocalFiniteMeasure X × LocalFiniteMeasure X)
    (Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (Prod.fst : (LocalFiniteMeasure X × LocalFiniteMeasure X) → LocalFiniteMeasure X)
    (Prod.snd : (LocalFiniteMeasure X × LocalFiniteMeasure X) → LocalFiniteMeasure X)
    measurable_fst measurable_snd
  intro F G
  have hS := hLaplace F ⟨0, fun _ ↦ le_rfl⟩
  have hT := hLaplace ⟨0, fun _ ↦ le_rfl⟩ G
  simp only [legalInputMeasureLaplacePair, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    legalInputMeasureLaplace_zero, mul_one, one_mul, hS0, hT0] at hS hT
  rw [hS, hT]
  exact hLaplace F G

/-- The two original Poisson exponents factor, so the extracted source and
target inputs are independent. The original intensity and clock measures are
retained in the profile, not replaced by a newly chosen input coupling. -/
theorem original_input_indep_of_poisson_laplace
    (Q : ProbabilityMeasure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    (μS μT : Measure X) (θ : ℝ)
    (hLaplace : ∀ F G : LegalNonnegativeInputTest X,
      (∫ z, legalInputMeasureLaplacePair F G z
        ∂(Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))) =
        Real.exp (-(θ * ((∫ x, 1 - Real.exp (-F.1 x) ∂μS) +
          ∫ y, 1 - Real.exp (-G.1 y) ∂μT)))) :
    IndepFun Prod.fst Prod.snd (Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X)) := by
  let LS := fun F : LegalNonnegativeInputTest X ↦
    Real.exp (-(θ * ∫ x, 1 - Real.exp (-F.1 x) ∂μS))
  let LT := fun G : LegalNonnegativeInputTest X ↦
    Real.exp (-(θ * ∫ y, 1 - Real.exp (-G.1 y) ∂μT))
  apply original_input_indep_of_factorized_laplace Q LS LT (by simp [LS]) (by simp [LT])
  intro F G
  rw [hLaplace]
  dsimp only [LS, LT]
  rw [← Real.exp_add]
  congr 1
  ring

end LawIdentification

section ActualObservation

variable {Ω X : Type*} [MeasurableSpace Ω]
  [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X] [SecondCountableTopology X]

theorem measurable_originalConfigurationLocalFinite (base : X) :
    Measurable (LocalConfiguration.toLocalFiniteMeasure : LocalConfiguration base → LocalFiniteMeasure X) := by
  apply LocalFiniteMeasure.measurable_of_testIntegral
  intro f
  simpa only [LocalConfiguration.testIntegral_toLocalFiniteMeasure] using
    LocalConfiguration.measurable_testIntegral (base := base) f

/-- The literal original two-color observation on the locally finite carrier. -/
def originalIidMaskedLocalInputPairMeasure
    (μ ν : Measure Ω) (N : ℕ) (base : X) (AS AT : Set Ω) (obsS obsT : Ω → X) :
    Measure (LocalFiniteMeasure X × LocalFiniteMeasure X) :=
  (originalIidMaskedConfigurationPairLaw μ ν N N base base AS AT obsS obsT).map
    (fun cfg : LocalConfiguration base × LocalConfiguration base ↦
      (LocalConfiguration.toLocalFiniteMeasure cfg.1, LocalConfiguration.toLocalFiniteMeasure cfg.2))

set_option backward.isDefEq.respectTransparency true in
/-- The actual masked original configuration pair law on the proved locally
finite compact-test carrier. This is a pushforward of the same original iid
arrays, not a new coupling or a limiting-law assumption. -/
def originalIidMaskedLocalInputPairLaw
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ) (base : X) {AS AT : Set Ω}
    (hAS : MeasurableSet AS) (hAT : MeasurableSet AT)
    {obsS obsT : Ω → X} (hobsS : Measurable obsS) (hobsT : Measurable obsT) :
    ProbabilityMeasure (LocalFiniteMeasure X × LocalFiniteMeasure X) := by
  let P := originalIidMaskedConfigurationPairLaw μ ν N N base base AS AT obsS obsT
  have hP : IsProbabilityMeasure P :=
    isProbabilityMeasure_originalIidMaskedConfigurationPairLaw μ ν N N base base hAS hAT
      (obsS := obsS) (obsT := obsT) hobsS hobsT
  have hm : Measurable (fun c : LocalConfiguration base × LocalConfiguration base ↦
      (LocalConfiguration.toLocalFiniteMeasure c.1, LocalConfiguration.toLocalFiniteMeasure c.2)) :=
    ((measurable_originalConfigurationLocalFinite base).comp measurable_fst).prodMk
      ((measurable_originalConfigurationLocalFinite base).comp measurable_snd)
  let PP : ProbabilityMeasure (LocalConfiguration base × LocalConfiguration base) := ⟨P, hP⟩
  exact PP.map hm.aemeasurable

/-- Compact Laplace readings on the locally finite carrier are exactly the
actual original configuration readings; no observation interface is assumed. -/
theorem integral_originalIidMaskedLocalInputPairLaw_laplace
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ) (base : X) {AS AT : Set Ω}
    (hAS : MeasurableSet AS) (hAT : MeasurableSet AT)
    {obsS obsT : Ω → X} (hobsS : Measurable obsS) (hobsT : Measurable obsT)
    (F G : LegalNonnegativeInputTest X) :
    (∫ z, legalInputMeasureLaplacePair F G z
      ∂(originalIidMaskedLocalInputPairLaw μ ν N base hAS hAT hobsS hobsT :
        Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))) =
      ∫ cfg, Real.exp (-(LocalConfiguration.testIntegral cfg.1 F.1 +
        LocalConfiguration.testIntegral cfg.2 G.1))
        ∂originalIidMaskedConfigurationPairLaw μ ν N N base base AS AT obsS obsT := by
  have hm : Measurable (fun c : LocalConfiguration base × LocalConfiguration base ↦
      (LocalConfiguration.toLocalFiniteMeasure c.1, LocalConfiguration.toLocalFiniteMeasure c.2)) :=
    ((measurable_originalConfigurationLocalFinite base).comp measurable_fst).prodMk
      ((measurable_originalConfigurationLocalFinite base).comp measurable_snd)
  change (∫ z, legalInputMeasureLaplacePair F G z
    ∂(originalIidMaskedConfigurationPairLaw μ ν N N base base AS AT obsS obsT).map
      (fun c ↦ (LocalConfiguration.toLocalFiniteMeasure c.1,
        LocalConfiguration.toLocalFiniteMeasure c.2))) = _
  rw [integral_map hm.aemeasurable (legalInputMeasureLaplacePair F G).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun cfg ↦ by
    change Real.exp (-LocalFiniteMeasure.testIntegral (LocalConfiguration.toLocalFiniteMeasure cfg.1) F.1) *
      Real.exp (-LocalFiniteMeasure.testIntegral (LocalConfiguration.toLocalFiniteMeasure cfg.2) G.1) = _
    rw [LocalConfiguration.testIntegral_toLocalFiniteMeasure,
      LocalConfiguration.testIntegral_toLocalFiniteMeasure, ← Real.exp_add, ← neg_add]

end ActualObservation

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
/-- Every genuine weak subsequential original FULL fixed-seed input law has the actual local
Poisson Laplace profile with the SAME intensity and original conditional clocks.
Its two original colors are independent. The sequence is the measurable
pushforward of the same original iid arrays; no local-Laplace callback or
desired-law assumption is imposed. -/
theorem PopulationLocalPressureCore.original_ae_full_seed_input_weak_subseq_identification
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
      ∃ PN : ℕ → ProbabilityMeasure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) × LocalFiniteMeasure ((Fin q → ℝ) × ℝ)),
        (∀ n, (PN n : Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) × LocalFiniteMeasure ((Fin q → ℝ) × ℝ))) =
          originalIidMaskedLocalInputPairMeasure η₀ η₁ (n + 1) (0 : ((Fin q → ℝ) × ℝ))
            mask mask (obs n) (obs n)) ∧
        (∀ (φ : ℕ → ℕ), StrictMono φ → ∀ Q : ProbabilityMeasure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) × LocalFiniteMeasure ((Fin q → ℝ) × ℝ)),
          Tendsto (PN ∘ φ) atTop (𝓝 Q) →
          (∀ H G : LegalNonnegativeInputTest ((Fin q → ℝ) × ℝ),
            (∫ z, legalInputMeasureLaplacePair H G z
              ∂(Q : Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) × LocalFiniteMeasure ((Fin q → ℝ) × ℝ)))) =
              Real.exp (-(θ * ((∫ x, 1 - Real.exp (-H.1 x) ∂μS) +
                ∫ y, 1 - Real.exp (-G.1 y) ∂μT)))) ∧
          IndepFun Prod.fst Prod.snd (Q : Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) × LocalFiniteMeasure ((Fin q → ℝ) × ℝ)))) ∧
        (∀ (φ ψ : ℕ → ℕ), StrictMono φ → StrictMono ψ →
          ∀ Q Q' : ProbabilityMeasure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ) × LocalFiniteMeasure ((Fin q → ℝ) × ℝ)),
            Tendsto (PN ∘ φ) atTop (𝓝 Q) → Tendsto (PN ∘ ψ) atTop (𝓝 Q') → Q = Q') := by
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
  let ref := fun c ↦ a (S.curve (e.symm c) 0)
  let mask := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
  let X := (Fin q → ℝ) × ℝ
  have hmask : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj C.seedIndex
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  filter_upwards [D.original_ae_twoColor_full_seed_iid_laplace_tendsto hF hcomplete hu ha hinj i
    s hs hlarge hnormalization] with c hc
  let obs := fun n x ↦ (s n • (e (R (a x)) - c), u x)
  have hobs n : Measurable (obs n) := by
    change Measurable (fun x ↦ (s n • (e (R (a x)) - c), u x))
    exact (((e.continuous.measurable.comp (hR.comp ha)).sub_const c).const_smul (s n)).prodMk
      hu.continuous.measurable
  let PN := fun n ↦ originalIidMaskedLocalInputPairLaw η₀ η₁ (n + 1) (0 : X)
    hmask hmask (hobs n) (hobs n)
  let θ := originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c)
  let μS := (volume : Measure (Fin q → ℝ)).prod (condDistrib u a η₀ (ref c))
  let μT := (volume : Measure (Fin q → ℝ)).prod (condDistrib u a η₁ (ref c))
  let L := fun H G : LegalNonnegativeInputTest X ↦
    Real.exp (-(θ * ((∫ x, 1 - Real.exp (-H.1 x) ∂μS) +
      ∫ y, 1 - Real.exp (-G.1 y) ∂μT)))
  have hLaplace (H G : LegalNonnegativeInputTest X) :
      Tendsto (fun n ↦ ∫ z, legalInputMeasureLaplacePair H G z
        ∂(PN n : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))) atTop (𝓝 (L H G)) := by
    have hsupport (F : LegalNonnegativeInputTest X) :
        ∃ B : ℝ, 0 < B ∧ ∀ p, p.1 ∉ closedBall 0 B → F.1 p = 0 := by
      obtain ⟨B, hB, hbound⟩ :=
        (F.1.hasCompactSupport.image continuous_fst).isBounded.exists_pos_norm_lt
      refine ⟨B, hB, ?_⟩
      intro p hp
      by_contra hF
      apply hp
      exact mem_closedBall_zero_iff.mpr (hbound p.1 ⟨p, subset_tsupport F.1 hF, rfl⟩).le
    have hraw := hc H.1 G.1 H.1.continuous.measurable G.1.continuous.measurable
      H.2 G.2 (hsupport H) (hsupport G)
    apply hraw.congr'
    exact .of_forall fun n ↦ ((integral_originalIidMaskedLocalInputPairLaw_laplace η₀ η₁
      (n + 1) (0 : X) hmask hmask (hobs n) (hobs n) H G).trans
        (integral_originalIidMaskedConfigurationPairLaw_laplace_eq_sum η₀ η₁
          (n + 1) (n + 1) (0 : X) (0 : X) hmask hmask (hobs n) (hobs n) H.1 G.1)).symm
  refine ⟨PN, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro φ hφ Q hweak
    have hprofile : ∀ H G : LegalNonnegativeInputTest X,
        (∫ z, legalInputMeasureLaplacePair H G z
          ∂(Q : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))) = L H G :=
      fun H G ↦ original_input_weak_subseq_laplace PN Q φ hφ hweak H G (hLaplace H G)
    exact ⟨hprofile, original_input_indep_of_poisson_laplace Q μS μT θ hprofile⟩
  · intro φ ψ hφ hψ Q Q' hweak hweak'
    exact original_input_weak_subseq_unique PN Q Q' φ ψ hφ hψ hweak hweak' L hLaplace

end ActualCore

end OTSelector.Reconstruction
