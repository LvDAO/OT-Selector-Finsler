import OTSelector.Probability.CavitySemidiscreteActualScene
import OTSelector.Probability.CavitySemidiscreteSpatialBasis

/-!
# Monotonicity of actual rooted opposite-tilt weak limits

For every finite environment the actual optimizer comparison controls all bounded
rectangle witnesses. A countable spatial basis and the actual vague scene law
then exclude every strict two-cycle violation in each weak limit.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped BigOperators ENNReal Classical

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

/-- Every weak limit of the actual common rooted scene has a two-cycle monotone
average support. No witness-limit or support-monotonicity premise is imposed. -/
theorem ae_actualRootedScene_average_support_twoCycle
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (k : A → B → (ι → ℝ) → ℝ)
    (g a₀ aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (htzero : Tendsto t atTop (𝓝 0)) (G : ℝ)
    (hopt : ∀ n, ∀ᵐ ω ∂P n,
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j)) (fun s ↦ a₀ n (ω, s)) ∧
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j) + t n * g n (ω, s) j)
        (fun s ↦ aplus n (ω, s)) ∧
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j) + (-t n) * g n (ω, s) j)
        (fun s ↦ aminus n (ω, s)) ∧
      (∀ j, Integrable (fun s ↦ cavitySpatialDifferenceCost k s (Y n ω j)) (μ n)) ∧
      (∀ j, Integrable (fun s ↦ g n (ω, s) j) (μ n)) ∧
      (∀ᵐ s ∂μ n, ∀ j, |g n (ω, s) j| ≤ G))
    (D : ℕ → Set (ι → ℝ)) (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (hD : ∀ n, volume (D n) = ENNReal.ofReal (N n))
    (hc : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B)))
    (hweak : Tendsto (fun n ↦ cavityRootedLocalSceneLaw (P n) (μ n)
      (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n)
      (N n) (hN n) (D n) (hD n)) atTop (𝓝 Q)) :
    ∀ᵐ π ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B))),
      OTSelector.Reconstruction.IsTwoCycleMonotone (cavitySpatialDifferenceCost k)
        (LocalFiniteMeasure.cavityAverage π : Measure _).support := by
  let BX := cavitySpatialBasis (ι := ι) (A := A)
  let BY := countableBasis ((ι → ℝ) × B)
  have hBX : IsTopologicalBasis BX := isTopologicalBasis_cavitySpatialBasis
  have hBY : IsTopologicalBasis BY := isBasis_countableBasis _
  apply ae_cavityAverage_support_twoCycle_of_weak_witness Q _ hweak
    (cavitySpatialDifferenceCost k) hc hBX hBY countable_cavitySpatialBasis
    (countable_countableBasis _)
  intro i hi
  have hleft : (i.1.1.1.val ×ˢ i.1.1.2.val).Nonempty :=
    (nonempty_of_mem_cavitySpatialBasis i.1.1.1.property).prod
      (nonempty_of_mem_countableBasis i.1.1.2.property)
  have hright : (i.1.2.1.val ×ˢ i.1.2.2.val).Nonempty :=
    (nonempty_of_mem_cavitySpatialBasis i.1.2.1.property).prod
      (nonempty_of_mem_countableBasis i.1.2.2.property)
  obtain ⟨K, hK, offset, hbox⟩ :=
    exists_phaseCell_of_cavitySpatialBasis i.1.1.1.property i.1.2.1.property
  have hA₀ := (hBX.isOpen i.1.1.1.property).measurableSet
  have hA₁ := (hBX.isOpen i.1.2.1.property).measurableSet
  have hB₀ := (hBY.isOpen i.1.1.2.property).measurableSet
  have hB₁ := (hBY.isOpen i.1.2.2.property).measurableSet
  have hε : (0 : ℝ) < i.2 := by exact_mod_cast hi.1
  have hwmeas : Measurable (fun π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) ↦
      cavityBasisCycleWitness (LocalFiniteMeasure.cavityAverage π : Measure _) i) :=
    (lowerSemicontinuous_cavityBasisCycleWitness hBX hBY
      (fun π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) ↦
        (LocalFiniteMeasure.cavityAverage π : Measure _))
      (fun _ hU ↦ lowerSemicontinuous_cavityAverage_open hU) i).measurable
  have hmean := tendsto_actual_rooted_cycle_rectangle_expectation_zero m P μ p Y hY k
    g a₀ aplus aminus hplusm hminusm t ht htzero G hopt
    i.1.1.1.val i.1.2.1.val i.1.1.2.val i.1.2.2.val hA₀ hA₁ hB₀ hB₁
    (hi.disjoint hleft hright).1 K hK offset hbox i.2 hε
    (fun s hs s' hs' y hy y' hy' ↦ hi.2 s hs y hy s' hs' y' hy') D N hN
  apply hmean.congr'
  apply Filter.Eventually.of_forall
  intro n
  change (∫⁻ v : Ωn n × (ι → ℝ), _ ∂_) =
    ∫⁻ π, cavityBasisCycleWitness (LocalFiniteMeasure.cavityAverage π : Measure _) i
      ∂((P n).prod (cavityRootMeasure volume (D n) (N n))).map
        (cavityRootedLocalScene (μ n) (aplus n) (aminus n) (Y n) (N n))
  rw [lintegral_map hwmeas
    (measurable_cavityRootedLocalScene (μ n) (aplus n) (aminus n)
      (hplusm n) (hminusm n) (Y n) (hY n) (N n))]
  have := isProbabilityMeasure_cavityRootMeasure volume (D n) (N n) (hN n) (hD n)
  have he := (measurePreserving_fst (μ := P n)
    (ν := cavityRootMeasure volume (D n) (N n))).quasiMeasurePreserving.ae (hopt n)
  apply lintegral_congr_ae
  filter_upwards [he] with v hv
  rw [cavityRootedLocalScene_average (μ n) (aplus n) (aminus n)
    (hplusm n) (hminusm n) (Y n) (N n) v.1 (p n v.1) hv.2.1.1 hv.2.2.1.1 v.2]
  rfl

end OTSelector.Probability
