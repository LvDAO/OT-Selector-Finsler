import OTSelector.Limit.SupportedPressureConcentration
import OTSelector.Probability.RowMeanConvergence

/-!
# Original whole-face selection from mean pressures

For independent iid colors and effective dimension `q > 4`, concentration is
derived from bounded original distances on the compact support. It is enough
to prove convergence of the central expectation and the one-sided lower tilted
expectations. These remaining mean-pressure and differentiability premises are
analytic inputs; they are not asserted here to follow from Finsler geometry.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction

namespace OTSelector.Pressure
open Probability

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The original ambient whole-face selector requires only mean pressure estimates once `q > 4`.
The centered sampling estimates are proved internally from the original iid laws. -/
theorem existsUnique_supported_empirical_selector_of_iid_mean_pressure
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ x ∂(ν : Measure M), x ∈ K)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun ω i ↦ X n i ω) (fun ω i ↦ Y n i ω) (P n))
    (φ : M → ℝ) (hφ : LipschitzWith 1 φ) (q : ℝ) (hq : 4 < q)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((K × K) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0)
    (hzero : ∀ f, Tendsto (fun n ↦ ∫ ω,
      supportedDistancePressure μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i ω) (fun i ↦ Y n i ω) φ (((n + 1 : ℕ) : ℝ) ^ (2 / q)) f 0 ∂P n)
        atTop (𝓝 (pressure f 0)))
    (hlower : ∀ f t, |t| < radius f → Tendsto (fun n ↦ max (pressure f t - ∫ ω,
      supportedDistancePressure μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i ω) (fun i ↦ Y n i ω) φ (((n + 1 : ℕ) : ℝ) ^ (2 / q)) f t ∂P n) 0)
        atTop (𝓝 0)) :
    ∃! π : ProbabilityMeasure (M × M),
      (∀ f : (K × K) →ᵇ ℝ, ∫ z, f z ∂((π : Measure (M × M)).comap
        (Prod.map ((↑) : K → M) ((↑) : K → M))) = derivative f) ∧
      (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
        {ω | ∃ γ ∈ empiricalOptimalFace (fun i ↦ X n i ω) (fun i ↦ Y n i ω), γ ∉ U})
        atTop (𝓝 0)) ∧
      IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  let F (f : (K × K) →ᵇ ℝ) (t : ℝ) (z : Σ n, Ω n) : ℝ :=
    supportedDistancePressure μ ν K hK.measurableSet hμ hν
      (fun i ↦ X z.1 i z.2) (fun i ↦ Y z.1 i z.2) φ
      (((z.1 + 1 : ℕ) : ℝ) ^ (2 / q)) f t
  have hcenter (f : (K × K) →ᵇ ℝ) (t ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n ↦ (P n).real {ω |
        ε ≤ |F f t ⟨n, ω⟩ - ∫ ω', F f t ⟨n, ω'⟩ ∂P n|}) atTop (𝓝 0) :=
    tendsto_centered_supportedDistancePressure P μ ν K hK hμ hν X Y hX hY hXi hYi
      hXlaw hYlaw hXY φ hφ.continuous q hq f t hε
  apply existsUnique_supported_empirical_selector_of_iid_pressure P X Y μ ν K hK hμ hν
    hX hY hXi hYi hXlaw hYlaw φ hφ q (lt_trans (by norm_num) hq)
    pressure radius derivative hradius hderiv
  · intro f
    exact (tendsto_rowProbabilityFilter_real_iff P (F f 0) (pressure f 0)).mp
      (tendsto_row_of_centered_of_mean P (F f 0) (pressure f 0) (hcenter f 0) (hzero f))
  · intro f t ht
    have h := (tendsto_rowProbabilityFilter_real_iff P
      (fun z ↦ max (pressure f t - F f t z) 0) 0).mp
      (tendsto_row_posPart_of_centered_of_meanLower P (F f t) (pressure f t)
        (hcenter f t) (hlower f t ht))
    simpa only [sub_zero, abs_of_nonneg (le_max_right (_ : ℝ) 0)] using h

end OTSelector.Pressure
