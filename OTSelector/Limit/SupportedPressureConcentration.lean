import OTSelector.Limit.EmpiricalPressureConcentration
import OTSelector.Limit.SupportedEmpiricalSelector

/-!
# Centered pressure concentration for compactly supported ambient samples

The original ambient cost and sample law agree almost everywhere with the
compact carrier construction. Both expectations and centered outer event
probabilities agree. Thus `q > 4` gives concentration on the original space,
without imposing compactness on the ambient manifold.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction

namespace OTSelector.Pressure
open Probability Reconstruction

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The centered original ambient pressure converges in probability for `q > 4`. -/
theorem tendsto_centered_supportedDistancePressure
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ x ∂(ν : Measure M), x ∈ K)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun ω i ↦ X n i ω) (fun ω i ↦ Y n i ω) (P n))
    (φ : M → ℝ) (hφ : Continuous φ) (q : ℝ) (hq : 4 < q)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real {ω |
      ε ≤ |supportedDistancePressure μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i ω) (fun i ↦ Y n i ω) φ (((n + 1 : ℕ) : ℝ) ^ (2 / q)) f t -
        ∫ ω', supportedDistancePressure μ ν K hK.measurableSet hμ hν
          (fun i ↦ X n i ω') (fun i ↦ Y n i ω')
          φ (((n + 1 : ℕ) : ℝ) ^ (2 / q)) f t ∂P n|}) atTop (𝓝 0) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let XK := fun n i ↦ supportedVersion μ K hK.measurableSet hμ (X n i)
  let YK := fun n i ↦ supportedVersion ν K hK.measurableSet hν (Y n i)
  have h := tendsto_centered_empiricalDistancePressure P
    (probabilityOnSubset μ K hK.measurableSet hμ)
    (probabilityOnSubset ν K hK.measurableSet hν) XK YK
    (fun n i ↦ measurable_supportedVersion μ K hK.measurableSet hμ (hX n i))
    (fun n i ↦ measurable_supportedVersion ν K hK.measurableSet hν (hY n i))
    (fun n ↦ iIndepFun_supportedVersion μ K hK.measurableSet hμ (hXi n))
    (fun n ↦ iIndepFun_supportedVersion ν K hK.measurableSet hν (hYi n))
    (fun n i ↦ map_supportedVersion μ K hK.measurableSet hμ (hX n i) (hXlaw n i))
    (fun n i ↦ map_supportedVersion ν K hK.measurableSet hν (hY n i) (hYlaw n i))
    (fun n ↦ indepFun_supportedVersion_family μ ν K hK.measurableSet hμ hν (hXY n))
    (fun x : K ↦ φ x) (hφ.comp continuous_subtype_val) q hq f t hε
  convert h using 1
  funext n
  have heq := supportedDistancePressure_eq_ae μ ν K hK.measurableSet hμ hν
    (X n) (Y n) (hX n) (hY n) (hXlaw n) (hYlaw n) φ
    (((n + 1 : ℕ) : ℝ) ^ (2 / q)) f t
  have hmean := integral_congr_ae heq
  exact outer_probability_congr_ae
    (heq.sub (Eventually.of_forall fun _ ↦ hmean)) {v : ℝ | ε ≤ |v|}

end OTSelector.Pressure
