import OTSelector.Probability.CavitySemidiscreteSourceMarginalLimit
import OTSelector.Probability.CavitySemidiscreteExpectedMarginalError

/-!
# Expected displacement energy preserves common source marginals

Actual displacement energy controls the target escape of compact source tests.
Haar root averaging and weak convergence then preserve equality of the full
source marginals, even though the source projection is not proper.
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
  [SigmaCompactSpace B] [SecondCountableTopology B] [CompactSpace B]

local instance cavitySemidiscreteEnergyMarginalLimitLocalInst1 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Actual expected displacement energy prevents source-marginal mass from escaping
in the noncompact target direction. Both original limiting plans have exactly the
same full source marginal. -/
theorem ae_actualRootedScene_equal_source_marginals_of_energy
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
    (D : ℕ → Set (ι → ℝ)) (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (hD : ∀ n, volume (D n) = ENNReal.ofReal (N n))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ n, (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (‖(Y n ω e.2).1 - e.1.1‖ ^ 2)
      ∂semidiscreteAllocationMeasure (μ n) (fun s ↦ aplus n (ω, s)) ∂P n) ≤ C)
    (henergyminus : ∀ n, (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (‖(Y n ω e.2).1 - e.1.1‖ ^ 2)
      ∂semidiscreteAllocationMeasure (μ n) (fun s ↦ aminus n (ω, s)) ∂P n) ≤ C)
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B)))
    (hweak : Tendsto (fun n ↦ cavityRootedLocalSceneLaw (P n) (μ n)
      (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n)
      (N n) (hN n) (D n) (hD n)) atTop (𝓝 Q)) :
    ∀ᵐ π ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B))),
      (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst =
        (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst := by
  let KX := CompactExhaustion.choice ((ι → ℝ) × A)
  let f := LocalFiniteMeasure.separatingTest KX
  have hex (i : ℕ ⊕ (ℕ × ℕ)) : ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ tsupport (f i), ‖x.1‖ ≤ r := by
    obtain ⟨r, hr, hs⟩ := ((f i).hasCompactSupport.image continuous_fst).isBounded.subset_closedBall_lt 0 0
    refine ⟨r, hr, fun x hx ↦ ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hs (mem_image_of_mem _ hx)
  choose radius _hrad hnorm using hex
  let U := fun i ↦ Metric.closedBall (0 : ι → ℝ) (radius i)
  have hUm (i) : MeasurableSet (U i) := (isCompact_closedBall _ _).measurableSet
  have hUf (i) : volume (U i) ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
  let err : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞ := fun i R ↦ ENNReal.ofReal ‖(f i).toBoundedContinuousFunction‖ *
    (volume (U i) * C / ENNReal.ofReal (((R : ℝ) + 1) ^ 2) +
      volume (U i) * C / ENNReal.ofReal (((R : ℝ) + 1) ^ 2))
  have hden : Tendsto (fun R : ℕ ↦ ENNReal.ofReal (((R : ℝ) + 1) ^ 2)) atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_atTop.comp ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  have herr (i) : Tendsto (err i) atTop (𝓝 0) := by
    have hd : Tendsto (fun R : ℕ ↦ volume (U i) * C /
        ENNReal.ofReal (((R : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
      simpa only [ENNReal.div_top] using ENNReal.Tendsto.const_div hden
        (Or.inr (ENNReal.mul_ne_top (hUf i) hC))
    simpa only [err, add_zero, mul_zero] using
      ENNReal.Tendsto.const_mul (hd.add hd) (Or.inr ENNReal.ofReal_ne_top)
  have hlocal := ae_actualRootedScene_locallyFinite_source_marginals m P μ p Y hY
    aplus aminus hplusm hminusm hfeas D N hN hD Q hweak
  apply ae_common_source_marginal_of_weak_cutoff_errors Q _ hweak KX
    (fun i ↦ cavitySpatialTargetExhaustion (B := B) (radius i)) hlocal err herr
  intro i R n
  apply cavityRootedLocalSceneLaw_product_test_error_le (P n) (μ n) (p n)
    (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n) (hfeas n)
    (N n) (hN n) (D n) (hD n) (f i) (U i) (hUm i) (hUf i) (radius i)
    _ (hnorm i) C (henergyplus n) (henergyminus n) R
  intro x hx
  simpa only [U, Metric.mem_closedBall, dist_zero_right] using hnorm i x hx

end OTSelector.Probability
