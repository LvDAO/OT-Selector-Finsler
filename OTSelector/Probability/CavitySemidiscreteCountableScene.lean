import OTSelector.Probability.CavitySemidiscreteSceneSubsequence
import OTSelector.Probability.OriginalTargetConfigurationTightness

/-!
# One original scene retains both plans, weighted targets and integer atoms

The actual unweighted labels are added to the existing correlated scene before
taking a weak subsequence. Original local counting bounds supply their tightness,
and the closed support relation proves that the limiting weighted target has a
countable carrier. Projecting the extended scene recovers the previous law exactly.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace
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

local instance cavitySemidiscreteCountableSceneLocalInst1 : StandardBorelSpace ((ι → ℝ) × B) := inferInstance
local instance cavitySemidiscreteCountableSceneLocalInst2 : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance cavitySemidiscreteCountableSceneLocalInst3 : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance cavitySemidiscreteCountableSceneLocalInst4 : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance cavitySemidiscreteCountableSceneLocalInst5 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace
local instance cavitySemidiscreteCountableSceneLocalInst6 : PolishSpace (LocalFiniteMeasure ((ι → ℝ) × B)) :=
  LocalFiniteMeasure.instPolishSpace

/-- The existing actual target scene, together with its original integer cloud. -/
abbrev CavityCountableTargetScene :=
  (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B)) ×
   LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B)) ×
   LocalFiniteMeasure ((ι → ℝ) × B)) × LocalConfiguration base

def cavityRootedCountableScene {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure ((ι → ℝ) × A))
    (p : Ω → Fin (m + 1) → ℝ)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ)
    (v : Ω × (ι → ℝ)) : CavityCountableTargetScene (A := A) base :=
  (((cavityRootedLocalScene μ aplus aminus Y N v).1,
    (cavityRootedLocalScene μ aplus aminus Y N v).2,
    cavityRootedLocalTargetCloud p Y N v), cavityRootedTargetConfiguration base Y v)

theorem measurable_cavityRootedCountableScene
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j)) (N : ℝ) :
    Measurable (cavityRootedCountableScene base μ p aplus aminus Y N) := by
  have hm := measurable_cavityRootedLocalScene μ aplus aminus hplusm hminusm Y hY N
  have ht := measurable_cavityRootedLocalTargetCloud p hp Y hY N
  exact (hm.fst.prodMk (hm.snd.prodMk ht)).prodMk
    (measurable_cavityRootedTargetConfiguration base Y hY)

/-- The joint law uses the same original environment and the same root. -/
def cavityRootedCountableSceneLaw
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j)) (N : ℝ) :
    ProbabilityMeasure (CavityCountableTargetScene (A := A) base) :=
  ⟨(P.prod ρ).map (cavityRootedCountableScene base μ p aplus aminus Y N),
    Measure.isProbabilityMeasure_map
      (measurable_cavityRootedCountableScene base μ p hp aplus aminus
        hplusm hminusm Y hY N).aemeasurable⟩

/-- Forgetting the integer coordinate recovers the existing actual scene law. -/
theorem map_cavityRootedCountableSceneLaw_targetScene
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j)) (N : ℝ) :
    ProbabilityMeasure.map
      (cavityRootedCountableSceneLaw base P μ ρ p hp aplus aminus hplusm hminusm Y hY N)
      (f := Prod.fst) measurable_fst.aemeasurable =
      cavityRootedSceneTargetLaw P μ ρ p hp aplus aminus hplusm hminusm Y hY N := by
  apply Subtype.ext
  change ((P.prod ρ).map (cavityRootedCountableScene base μ p aplus aminus Y N)).map
    Prod.fst = _
  rw [Measure.map_map measurable_fst
    (measurable_cavityRootedCountableScene base μ p hp aplus aminus hplusm hminusm Y hY N)]
  rfl

/-- Every original finite law retains its exact weighted/label support relation. -/
theorem ae_cavityRootedCountableSceneLaw_supported
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j)) (N : ℝ) :
    ∀ᵐ s ∂(cavityRootedCountableSceneLaw base P μ ρ p hp aplus aminus
      hplusm hminusm Y hY N : Measure (CavityCountableTargetScene (A := A) base)),
      SupportedOnConfiguration s.2 s.1.2.2 := by
  apply (ae_map_iff
    (measurable_cavityRootedCountableScene base μ p hp aplus aminus
      hplusm hminusm Y hY N).aemeasurable
    (isClosed_supportedOnConfiguration.preimage
      (continuous_snd.prodMk continuous_fst.snd.snd)).measurableSet).mpr
  exact Eventually.of_forall (fun v ↦
    supportedOnConfiguration_semidiscreteTargetCloud (p v.1)
      (fun j ↦ cavitySpatialTranslate v.2 (Y v.1 j)) N)

/-- Original iid target laws produce one actual weak scene with a countably
supported weighted target. The integer cloud is kept in the same joint law. -/
theorem exists_tendsto_subseq_cavityRootedCountableSceneLaw
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : ℕ → Measure ((ι → ℝ) × B)) [∀ n, IsProbabilityMeasure (ν n)]
    (ρ : ℕ → Measure (ι → ℝ)) [∀ n, IsProbabilityMeasure (ρ n)]
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ω n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (henv : ∀ n, MeasurePreserving (fun ω ↦ (p n ω, Y n ω)) (P n)
      ((dirichletOne (m n)).prod (Measure.pi (fun _ : Fin (m n + 1) ↦ ν n))))
    (aplus aminus : ∀ n, Ω n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
    (D : ℕ → Set (ι → ℝ))
    (hν : ∀ n, (ν n).map Prod.fst =
      (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ • volume.restrict (D n)) :
    ∃ Q, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ cavityRootedCountableSceneLaw base (P (φ n)) (μ (φ n)) (ρ (φ n))
        (p (φ n)) (henv (φ n)).measurable.fst (aplus (φ n)) (aminus (φ n))
        (hplusm (φ n)) (hminusm (φ n)) (Y (φ n)) (hY (φ n)) ((m (φ n) : ℝ) + 1))
        atTop (𝓝 Q) ∧
      ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
        SupportedOnConfiguration s.2 s.1.2.2 := by
  let laws (n : ℕ) := cavityRootedCountableSceneLaw base (P n) (μ n) (ρ n)
    (p n) (henv n).measurable.fst (aplus n) (aminus n)
    (hplusm n) (hminusm n) (Y n) (hY n) ((m n : ℝ) + 1)
  have hYlaw (n : ℕ) (j : Fin (m n + 1)) :
      MeasurePreserving (fun ω ↦ Y n ω j) (P n) (ν n) :=
    (measurePreserving_eval (fun _ : Fin (m n + 1) ↦ ν n) j).comp
      (measurePreserving_snd.comp (henv n))
  have htight : IsTightMeasureSet (range fun n ↦ (laws n : Measure
      (CavityCountableTargetScene (A := A) base))) := by
    apply isTightMeasureSet_original_joint_of_marginals
      (fun n ↦ (P n).prod (ρ n)) _ _
    · intro n
      have hm := measurable_cavityRootedLocalScene (μ n) (aplus n) (aminus n)
        (hplusm n) (hminusm n) (Y n) (hY n) ((m n : ℝ) + 1)
      exact hm.fst.prodMk (hm.snd.prodMk
        (measurable_cavityRootedLocalTargetCloud (p n) (henv n).measurable.fst
          (Y n) (hY n) ((m n : ℝ) + 1)))
    · intro n
      exact measurable_cavityRootedTargetConfiguration base (Y n) (hY n)
    · exact isTightMeasureSet_cavityRootedLocalSceneWithTarget m P μ ν ρ p Y hY henv
        aplus aminus hplusm hminusm hfeas D hν
    · exact isTightMeasureSet_cavityRootedTargetConfiguration base m P ρ ν Y hYlaw D hν
  obtain ⟨Q, φ, hφ, hlim⟩ :=
    exists_tendsto_subseq_probabilityMeasure_of_isTight laws htight
  refine ⟨Q, φ, hφ, hlim, ?_⟩
  apply ae_supportedOnConfiguration_of_weak_tendsto Q (laws ∘ φ) hlim
    Prod.snd (fun s ↦ s.1.2.2) continuous_snd continuous_fst.snd.snd
  intro n
  exact ae_cavityRootedCountableSceneLaw_supported base (P (φ n)) (μ (φ n)) (ρ (φ n))
    (p (φ n)) (henv (φ n)).measurable.fst (aplus (φ n)) (aminus (φ n))
    (hplusm (φ n)) (hminusm (φ n)) (Y (φ n)) (hY (φ n)) ((m (φ n) : ℝ) + 1)

end OTSelector.Probability
