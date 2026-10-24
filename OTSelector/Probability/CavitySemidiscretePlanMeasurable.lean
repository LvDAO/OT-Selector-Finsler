import OTSelector.Probability.CavitySemidiscretePlanBlocks
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Jointly measurable original semidiscrete plan measures

The actual finite allocation coefficients, target cloud, and spatial rooting maps
produce a measurable measure-valued map on their common environment. This supplies
an actual scene law for the diffuse-plan limit argument.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {V S X Y : Type*}
  [MeasurableSpace V] [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y]

/-- A jointly measurable density and parameter-dependent observation give measurable
pushforward measures on the original source law. -/
theorem measurable_parameterized_map_withDensity
    (μ : Measure S) [SFinite μ] (ρ : V × S → ℝ≥0∞) (hρ : Measurable ρ)
    (f : V × S → X) (hf : Measurable f) :
    Measurable (fun v ↦ (μ.withDensity (fun s ↦ ρ (v, s))).map (fun s ↦ f (v, s))) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  have hfv (v : V) : Measurable (fun s ↦ f (v, s)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hm := (hρ.indicator (hU.preimage hf)).lintegral_prod_right' (ν := μ)
  have heq (v : V) :
      ((μ.withDensity (fun s ↦ ρ (v, s))).map (fun s ↦ f (v, s))) U =
      ∫⁻ s, ((fun s ↦ f (v, s)) ⁻¹' U).indicator (fun s ↦ ρ (v, s)) s ∂μ := by
    rw [Measure.map_apply (hfv v) hU, withDensity_apply _ (hU.preimage (hfv v)),
      lintegral_indicator (hU.preimage (hfv v))]
  simp_rw [heq]
  exact hm

/-- The actual original allocation plan, with a parameter-dependent source observation
and finite physical target cloud. The parameter can include the independent spatial root. -/
def parameterizedSemidiscretePlan
    (μ : Measure S) (a : V × S → Fin (m + 1) → ℝ)
    (f : V × S → X) (y : V → Fin (m + 1) → Y) (v : V) : Measure (X × Y) :=
  (semidiscreteAllocationMeasure μ (fun s ↦ a (v, s))).map
    (Prod.map (fun s ↦ f (v, s)) (y v))

/-- The original environment and root jointly determine a measurable actual plan. -/
theorem measurable_parameterizedSemidiscretePlan
    (μ : Measure S) [SFinite μ] (a : V × S → Fin (m + 1) → ℝ)
    (ha : ∀ j, Measurable (fun z ↦ a z j))
    (f : V × S → X) (hf : Measurable f)
    (y : V → Fin (m + 1) → Y) (hy : ∀ j, Measurable (fun v ↦ y v j)) :
    Measurable (parameterizedSemidiscretePlan μ a f y) := by
  have hfv (v : V) : Measurable (fun s ↦ f (v, s)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have heq (v : V) : parameterizedSemidiscretePlan μ a f y v =
      ∑ j, (μ.withDensity (fun s ↦ ENNReal.ofReal (a (v, s) j))).map
        (fun s ↦ (f (v, s), y v j)) := by
    unfold parameterizedSemidiscretePlan semidiscreteAllocationMeasure
    rw [Measure.map_finset_sum' ((hfv v).prodMap (measurable_of_finite (y v))).aemeasurable]
    apply Finset.sum_congr rfl
    intro j _
    rw [Measure.map_map ((hfv v).prodMap (measurable_of_finite (y v)))
      (show Measurable (fun s : S ↦ (s, j)) from measurable_id.prodMk measurable_const)]
    rfl
  have hm := Finset.measurable_sum Finset.univ (fun j _ ↦
    measurable_parameterized_map_withDensity μ _ (ha j).ennreal_ofReal
      (fun z : V × S ↦ (f z, y z.1 j)) (hf.prodMk ((hy j).comp measurable_fst)))
  change Measurable (fun v ↦ parameterizedSemidiscretePlan μ a f y v)
  simpa only [heq] using hm

/-- Random nonnegative total-mass scaling preserves measurability of the same plan. -/
theorem measurable_scaled_parameterizedSemidiscretePlan
    (μ : Measure S) [SFinite μ] (a : V × S → Fin (m + 1) → ℝ)
    (ha : ∀ j, Measurable (fun z ↦ a z j))
    (f : V × S → X) (hf : Measurable f)
    (y : V → Fin (m + 1) → Y) (hy : ∀ j, Measurable (fun v ↦ y v j))
    (N : V → ℝ≥0∞) (hN : Measurable N) :
    Measurable (fun v ↦ N v • parameterizedSemidiscretePlan μ a f y v) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [Measure.smul_apply, smul_eq_mul]
  exact hN.mul ((Measure.measurable_coe hU).comp
    (measurable_parameterizedSemidiscretePlan μ a ha f hf y hy))

end OTSelector.Probability
