import OTSelector.Probability.CavitySemidiscreteActualScene
import OTSelector.Probability.DirichletMarkedCloudMoments

/-!
# Tightness of the actual common rooted scene

The original Dirichlet-weighted target cloud supplies all local moments. Exact
finite target marginals then give tightness of both original allocation plans
together with that same cloud, even if feasibility only holds almost surely.
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

/-- The actual target cloud shares the original environment and spatial root
with both original plans. -/
def cavityRootedLocalTargetCloud {Ω : Type*} {m : ℕ}
    (p : Ω → Fin (m + 1) → ℝ) (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (N : ℝ) (v : Ω × (ι → ℝ)) : LocalFiniteMeasure ((ι → ℝ) × B) :=
  semidiscreteLocalTargetCloud (p v.1)
    (fun j ↦ cavitySpatialTranslate v.2 (Y v.1 j)) N

theorem measurable_cavityRootedLocalTargetCloud {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j)) (N : ℝ) :
    Measurable (cavityRootedLocalTargetCloud p Y N) := by
  apply measurable_semidiscreteLocalTargetCloud
  · intro j
    exact ((measurable_pi_apply j).comp hp).comp measurable_fst
  · intro j
    exact measurable_cavitySpatialTranslate.comp
      (measurable_snd.prodMk ((hY j).comp measurable_fst))
  · exact measurable_const

omit [T2Space A] [LocallyCompactSpace A] [T2Space B] [LocallyCompactSpace B] in
/-- At every original feasible environment, both actual scene plans have exactly
the original target cloud as their second marginal. -/
theorem cavityRootedLocalScene_targetMarginals
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsFiniteMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (ω : Ω)
    (hplus : IsSemidiscreteAllocation μ (p ω) (fun s ↦ aplus (ω, s)))
    (hminus : IsSemidiscreteAllocation μ (p ω) (fun s ↦ aminus (ω, s))) (z : ι → ℝ) :
    (((cavityRootedLocalScene μ aplus aminus Y N (ω, z)).1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).snd =
        (cavityRootedLocalTargetCloud p Y N (ω, z) : Measure ((ι → ℝ) × B))) ∧
      (((cavityRootedLocalScene μ aplus aminus Y N (ω, z)).2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).snd =
        (cavityRootedLocalTargetCloud p Y N (ω, z) : Measure ((ι → ℝ) × B))) := by
  have := hplus.isFiniteMeasure_cavitySpatialRootedPlan (Y ω) N z
  have := hminus.isFiniteMeasure_cavitySpatialRootedPlan (Y ω) N z
  simp only [cavityRootedLocalScene, coe_finitePlanLocalVersion,
    ite_eq_left (measure_lt_top (cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z) univ),
    ite_eq_left (measure_lt_top (cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z) univ)]
  exact ⟨hplus.snd_cavitySpatialRootedPlan _ _ _, hminus.snd_cavitySpatialRootedPlan _ _ _⟩

/-- The actual common law is tight using only original feasibility and the
original Dirichlet/target environment law with normalized Haar spatial marginal. -/
theorem isTightMeasureSet_cavityRootedLocalSceneWithTarget
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
    IsTightMeasureSet (range (fun n ↦ ((P n).prod (ρ n)).map (fun v ↦
      ((cavityRootedLocalScene (μ n) (aplus n) (aminus n) (Y n) ((m n : ℝ) + 1) v).1,
       (cavityRootedLocalScene (μ n) (aplus n) (aminus n) (Y n) ((m n : ℝ) + 1) v).2,
       cavityRootedLocalTargetCloud (p n) (Y n) ((m n : ℝ) + 1) v)))) := by
  let K := CompactExhaustion.choice ((ι → ℝ) × B)
  let C : ℕ → ℝ := fun k ↦ 2 * volume.real (Prod.fst '' K k) +
    (volume.real (Prod.fst '' K k)) ^ 2
  have hscene (n : ℕ) : MeasurePreserving
      (fun v : Ω n × (ι → ℝ) ↦ (v.2, (p n v.1, Y n v.1)))
      ((P n).prod (ρ n))
      ((ρ n).prod ((dirichletOne (m n)).prod (Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)))) :=
    ((MeasurePreserving.id (ρ n)).prod (henv n)).comp Measure.measurePreserving_swap
  have hsq (n k : ℕ) := integral_original_markedTargetCloud_sq_le (m n)
    ((P n).prod (ρ n)) (ρ n) (ν n) Prod.snd (fun v ↦ p n v.1)
    (fun j v ↦ Y n v.1 j) (hscene n) (D n) (hν n) (K k) (K.isCompact k)
  have hdom (n : ℕ) : ∀ᵐ v ∂(P n).prod (ρ n),
      (((cavityRootedLocalScene (μ n) (aplus n) (aminus n) (Y n) ((m n : ℝ) + 1) v).1 :
        Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).snd ≤ (cavityRootedLocalTargetCloud (p n) (Y n) ((m n : ℝ) + 1) v : Measure ((ι → ℝ) × B))) ∧
      (((cavityRootedLocalScene (μ n) (aplus n) (aminus n) (Y n) ((m n : ℝ) + 1) v).2 :
        Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).snd ≤ (cavityRootedLocalTargetCloud (p n) (Y n) ((m n : ℝ) + 1) v : Measure ((ι → ℝ) × B))) := by
    have hf : ∀ᵐ v ∂(P n).prod (ρ n),
        IsSemidiscreteAllocation (μ n) (p n v.1) (fun s ↦ aplus n (v.1, s)) ∧
        IsSemidiscreteAllocation (μ n) (p n v.1) (fun s ↦ aminus n (v.1, s)) := by
      apply ae_of_ae_map (μ := (P n).prod (ρ n))
        (p := fun ω : Ω n ↦
          IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
          IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
        measurable_fst.aemeasurable
      simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hfeas n
    filter_upwards [hf] with v hv
    have hh := cavityRootedLocalScene_targetMarginals (μ n) (p n) (aplus n) (aminus n)
      (Y n) ((m n : ℝ) + 1) v.1 hv.1 hv.2 v.2
    exact ⟨hh.1.le, hh.2.le⟩
  exact LocalFiniteMeasure.isTightMeasureSet_original_twoPlans_target
    (fun n ↦ (P n).prod (ρ n)) _ _ _
    (fun n ↦ (measurable_cavityRootedLocalScene (μ n) (aplus n) (aminus n)
      (hplusm n) (hminusm n) (Y n) (hY n) _).fst)
    (fun n ↦ (measurable_cavityRootedLocalScene (μ n) (aplus n) (aminus n)
      (hplusm n) (hminusm n) (Y n) (hY n) _).snd)
    (fun n ↦ measurable_cavityRootedLocalTargetCloud (p n) (henv n).measurable.fst (Y n) (hY n) _)
    (fun n ↦ (hdom n).mono fun _ h ↦ h.1) (fun n ↦ (hdom n).mono fun _ h ↦ h.2)
    K C (fun n k ↦ (hsq n k).1) (fun n k ↦ (hsq n k).2)

end OTSelector.Probability
