import OTSelector.Probability.CavitySemidiscreteConfigurationSupport
import OTSelector.Probability.CavitySemidiscreteCountableScene

/-!
# Both original limiting plans use the same countable target cloud

Actual finite-environment target marginals supply support over the original
integer cloud. Closedness retains that property for both correlated plans in
one weak limit, without assuming equality of projected limiting marginals.
-/

open Function Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability
open PointProcess PointProcess.LocalConfiguration

variable {ι A B : Type*} [Fintype ι]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [MetricSpace B] [ProperSpace B] [MeasurableSpace B]
  [BorelSpace B] [SecondCountableTopology B]
  (base : (ι → ℝ) × B)

local instance cavitySemidiscreteCountablePlanLimitLocalInst1 : StandardBorelSpace ((ι → ℝ) × B) := inferInstance
local instance cavitySemidiscreteCountablePlanLimitLocalInst2 : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance cavitySemidiscreteCountablePlanLimitLocalInst3 : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance cavitySemidiscreteCountablePlanLimitLocalInst4 : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance cavitySemidiscreteCountablePlanLimitLocalInst5 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace
local instance cavitySemidiscreteCountablePlanLimitLocalInst6 : PolishSpace (LocalFiniteMeasure ((ι → ℝ) × B)) :=
  LocalFiniteMeasure.instPolishSpace

/-- Both actual plans use the same original integer target cloud almost surely. -/
theorem ae_cavityRootedCountableSceneLaw_plans_supported
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j)) (N : ℝ)
    (hfeas : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aplus (ω, s)) ∧
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aminus (ω, s))) :
    ∀ᵐ s ∂(cavityRootedCountableSceneLaw base P μ ρ p hp aplus aminus
      hplusm hminusm Y hY N : Measure (CavityCountableTargetScene (A := A) base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.1 ∧
        SupportedOverConfiguration Prod.snd s.2 s.1.2.1 := by
  apply (ae_map_iff
    (measurable_cavityRootedCountableScene base μ p hp aplus aminus
      hplusm hminusm Y hY N).aemeasurable
    (((isClosed_supportedOverConfiguration Prod.snd continuous_snd).preimage
      (continuous_snd.prodMk continuous_fst.fst)).inter
      ((isClosed_supportedOverConfiguration Prod.snd continuous_snd).preimage
        (continuous_snd.prodMk continuous_fst.snd.fst))).measurableSet).mpr
  have hf : ∀ᵐ v ∂P.prod ρ,
      IsSemidiscreteAllocation μ (p v.1) (fun s ↦ aplus (v.1, s)) ∧
      IsSemidiscreteAllocation μ (p v.1) (fun s ↦ aminus (v.1, s)) := by
    apply ae_of_ae_map (μ := P.prod ρ)
      (p := fun ω ↦ IsSemidiscreteAllocation μ (p ω) (fun s ↦ aplus (ω, s)) ∧
        IsSemidiscreteAllocation μ (p ω) (fun s ↦ aminus (ω, s)))
      measurable_fst.aemeasurable
    simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hfeas
  filter_upwards [hf] with v hv
  have hh := cavityRootedLocalScene_targetMarginals μ p aplus aminus Y N v.1 hv.1 hv.2 v.2
  have ht := supportedOnConfiguration_semidiscreteTargetCloud (base := base)
    (p v.1) (fun j ↦ cavitySpatialTranslate v.2 (Y v.1 j)) N
  exact ⟨supportedOverConfiguration_of_map_le Prod.snd continuous_snd _ _ _ hh.1.le ht,
    supportedOverConfiguration_of_map_le Prod.snd continuous_snd _ _ _ hh.2.le ht⟩

/-- Both plans in an actual common weak scene remain over its own countable cloud. -/
theorem ae_actualRootedCountableScene_plans_supported
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (ρ : ℕ → Measure (ι → ℝ)) [∀ n, IsProbabilityMeasure (ρ n)]
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ) (hp : ∀ n, Measurable (p n))
    (Y : ∀ n, Ω n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (aplus aminus : ∀ n, Ω n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
    (N : ℕ → ℝ) (Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base))
    (hweak : Tendsto (fun n ↦ cavityRootedCountableSceneLaw base (P n) (μ n) (ρ n)
      (p n) (hp n) (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n) (N n))
      atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.1 ∧
        SupportedOverConfiguration Prod.snd s.2 s.1.2.1 := by
  have hs n := ae_cavityRootedCountableSceneLaw_plans_supported base (P n) (μ n) (ρ n)
    (p n) (hp n) (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n) (N n) (hfeas n)
  exact (ae_supportedOverConfiguration_of_weak_tendsto Q _ hweak Prod.snd continuous_snd
    Prod.snd (fun s ↦ s.1.1) continuous_snd continuous_fst.fst
    (fun n ↦ (hs n).mono fun _ h ↦ h.1)).and
    (ae_supportedOverConfiguration_of_weak_tendsto Q _ hweak Prod.snd continuous_snd
      Prod.snd (fun s ↦ s.1.2.1) continuous_snd continuous_fst.snd.fst
      (fun n ↦ (hs n).mono fun _ h ↦ h.2))

end OTSelector.Probability
