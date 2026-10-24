import OTSelector.MeasureTheory.WeakSourceDomination
import OTSelector.Reconstruction.FinslerQuadraticCostDifferenceSourceLaw

/-!
# Actual frozen-reference scene limits have the original diffuse source law

The normalized Haar cell and unchanged conditional mark law give pointwise
source domination before taking a limit. Closedness retains this pathwise bound,
and hence absolute continuity, for both plans in the same weak scene.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
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

local instance cavitySemidiscreteFrozenSourceLimitLocalInst1 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Original frozen source identities imply domination of both actual limiting
source marginals by Haar times the same original conditional mark law. -/
theorem ae_actualRootedScene_frozen_source_le
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (κ : Measure A) [IsProbabilityMeasure κ]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (D₀ : ℕ → Set (ι → ℝ)) (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (hμ : ∀ n, μ n = (ENNReal.ofReal (N n))⁻¹ • (volume.restrict (D₀ n)).prod κ)
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ω n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (aplus aminus : ∀ n, Ω n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal (N n))
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B)))
    (hweak : Tendsto (fun n ↦ cavityRootedLocalSceneLaw (P n) (μ n)
      (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n)
      (N n) (hN n) (D n) (hD n)) atTop (𝓝 Q)) :
    ∀ᵐ π ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B))),
      (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst ≤ volume.prod κ ∧
      (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst ≤ volume.prod κ := by
  have hdom n : ∀ᵐ π ∂(cavityRootedLocalSceneLaw (P n) (μ n)
      (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n)
      (N n) (hN n) (D n) (hD n) :
      Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B))),
      (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst ≤ volume.prod κ ∧
      (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst ≤ volume.prod κ := by
    have : IsProbabilityMeasure (cavityRootMeasure volume (D n) (N n)) :=
      isProbabilityMeasure_cavityRootMeasure volume (D n) (N n) (hN n) (hD n)
    apply (ae_map_iff
      (measurable_cavityRootedLocalScene (μ n) (aplus n) (aminus n)
        (hplusm n) (hminusm n) (Y n) (hY n) (N n)).aemeasurable
      (((isClosed_map_le_fixed (volume.prod κ) Prod.fst continuous_fst).preimage
        continuous_fst).inter ((isClosed_map_le_fixed (volume.prod κ) Prod.fst
          continuous_fst).preimage continuous_snd)).measurableSet).mpr
    have hf : ∀ᵐ v ∂(P n).prod (cavityRootMeasure volume (D n) (N n)),
        IsSemidiscreteAllocation (μ n) (p n v.1) (fun s ↦ aplus n (v.1, s)) ∧
        IsSemidiscreteAllocation (μ n) (p n v.1) (fun s ↦ aminus n (v.1, s)) := by
      apply ae_of_ae_map (μ := (P n).prod (cavityRootMeasure volume (D n) (N n)))
        (p := fun ω ↦ IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
          IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
        measurable_fst.aemeasurable
      simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hfeas n
    filter_upwards [hf] with v hv
    change ((cavityRootedLocalScene (μ n) (aplus n) (aminus n) (Y n) (N n) v).1 :
      Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst ≤ volume.prod κ ∧
      ((cavityRootedLocalScene (μ n) (aplus n) (aminus n) (Y n) (N n) v).2 :
      Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst ≤ volume.prod κ
    have hle (a : ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
        (ha : IsSemidiscreteAllocation (μ n) (p n v.1) a) :
        (cavitySpatialRootedPlan (μ n) a (Y n v.1) (N n) v.2).fst ≤ volume.prod κ := by
      rw [ha.fst_cavitySpatialRootedPlan, hμ n]
      exact frozen_source_rooted_le κ (D₀ n) (hN n) v.2
    have hp := hv.1.isFiniteMeasure_cavitySpatialRootedPlan (Y n v.1) (N n) v.2
    have hm := hv.2.isFiniteMeasure_cavitySpatialRootedPlan (Y n v.1) (N n) v.2
    simp only [cavityRootedLocalScene, coe_finitePlanLocalVersion,
      ite_eq_left (measure_lt_top
        (cavitySpatialRootedPlan (μ n) (fun s ↦ aplus n (v.1, s)) (Y n v.1) (N n) v.2) univ),
      ite_eq_left (measure_lt_top
        (cavitySpatialRootedPlan (μ n) (fun s ↦ aminus n (v.1, s)) (Y n v.1) (N n) v.2) univ)]
    exact ⟨hle _ hv.1, hle _ hv.2⟩
  exact (ae_map_le_fixed_of_weak_tendsto Q _ hweak (volume.prod κ) Prod.fst
    continuous_fst Prod.fst continuous_fst (fun n ↦ (hdom n).mono fun _ h ↦ h.1)).and
    (ae_map_le_fixed_of_weak_tendsto Q _ hweak (volume.prod κ) Prod.fst
      continuous_fst Prod.snd continuous_snd (fun n ↦ (hdom n).mono fun _ h ↦ h.2))

end OTSelector.Probability
