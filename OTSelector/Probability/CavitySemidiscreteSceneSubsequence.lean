import OTSelector.Probability.CavitySemidiscreteSceneTightness

/-!
# A common weak subsequence of original plans and their target cloud

The actual original environment law supplies compactness. Both plans and the
same target cloud are retained together in the extracted probability law.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [T2Space B] [LocallyCompactSpace B] [PseudoMetrizableSpace B]
  [SigmaCompactSpace B] [SecondCountableTopology B]

local instance : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace

local instance : PolishSpace (LocalFiniteMeasure ((ι → ℝ) × B)) :=
  LocalFiniteMeasure.instPolishSpace

/-- The true joint law of both original plans and their common weighted cloud. -/
def cavityRootedSceneTargetLaw {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j)) (N : ℝ) :
    ProbabilityMeasure
      (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B)) ×
       LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B)) ×
       LocalFiniteMeasure ((ι → ℝ) × B)) := by
  let scene := cavityRootedLocalScene μ aplus aminus Y N
  have hm := measurable_cavityRootedLocalScene μ aplus aminus hplusm hminusm Y hY N
  have ht := measurable_cavityRootedLocalTargetCloud p hp Y hY N
  exact ⟨(P.prod ρ).map (fun v ↦ ((scene v).1, (scene v).2,
      cavityRootedLocalTargetCloud p Y N v)),
    Measure.isProbabilityMeasure_map (hm.fst.prodMk (hm.snd.prodMk ht)).aemeasurable⟩

/-- Original target laws and almost-sure allocation feasibility yield an actual
joint-law subsequence; no tightness, plan-moment or limiting-law oracle is used. -/
theorem exists_tendsto_subseq_cavityRootedSceneTargetLaw
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
      Tendsto (fun n ↦ cavityRootedSceneTargetLaw (P (φ n)) (μ (φ n)) (ρ (φ n))
        (p (φ n)) (henv (φ n)).measurable.fst (aplus (φ n)) (aminus (φ n))
        (hplusm (φ n)) (hminusm (φ n)) (Y (φ n)) (hY (φ n)) ((m (φ n) : ℝ) + 1))
        atTop (𝓝 Q) := by
  apply exists_tendsto_subseq_probabilityMeasure_of_isTight
    (fun n ↦ cavityRootedSceneTargetLaw (P n) (μ n) (ρ n) (p n) (henv n).measurable.fst
      (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n) ((m n : ℝ) + 1))
  exact isTightMeasureSet_cavityRootedLocalSceneWithTarget m P μ ν ρ p Y hY henv
    aplus aminus hplusm hminusm hfeas D hν

/-- Forgetting the target coordinate gives exactly the existing actual two-plan
scene law, with its original uniform root and no replacement coupling. -/
theorem map_cavityRootedSceneTargetLaw_pair
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N) :
    letI := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
    ProbabilityMeasure.map
      (cavityRootedSceneTargetLaw P μ (cavityRootMeasure volume D N) p hp
        aplus aminus hplusm hminusm Y hY N)
      (f := fun v ↦ (v.1, v.2.1)) (measurable_fst.prodMk measurable_snd.fst).aemeasurable =
      cavityRootedLocalSceneLaw P μ aplus aminus hplusm hminusm Y hY N hN D hD := by
  apply Subtype.ext
  change ((P.prod (cavityRootMeasure volume D N)).map (fun v ↦
      ((cavityRootedLocalScene μ aplus aminus Y N v).1,
       (cavityRootedLocalScene μ aplus aminus Y N v).2,
       cavityRootedLocalTargetCloud p Y N v))).map (fun v ↦ (v.1, v.2.1)) = _
  have hm := measurable_cavityRootedLocalScene μ aplus aminus hplusm hminusm Y hY N
  have ht := measurable_cavityRootedLocalTargetCloud p hp Y hY N
  rw [Measure.map_map (measurable_fst.prodMk measurable_snd.fst)
    (hm.fst.prodMk (hm.snd.prodMk ht))]
  rfl

end OTSelector.Probability
