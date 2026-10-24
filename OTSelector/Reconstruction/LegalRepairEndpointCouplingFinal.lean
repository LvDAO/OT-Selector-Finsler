import OTSelector.Transport.Neumann.EndpointCoupling
import OTSelector.Reconstruction.LipschitzPreservingSmoothApproximation

/-!
# The unconditional endpoint transport coupling

This file instantiates the capture theorem
`capturesLipschitzDual_of_compact_support` inside the endpoint coupling theorem
`exists_endpointCoupling_edist_le_of_neumannFlux`.

The only remaining side condition of the capture theorem is that the reference
measure is carried by the compact carrier. That condition is derived here from
the actual residual support together with the positive lower density bound: a
residual density bounded below by a positive constant cannot live only on the
complement of the carrier without forcing the reference measure of that
complement to vanish.

The resulting end-to-end theorem constructs, from the residual gradient bound
alone, a genuine coupling of the two residual measures whose extended-distance
cost is bounded by the explicit constant
`C * sqrt (card ι * (μ univ).toReal)`. No capture, flux, energy or coupling is
assumed.
-/
open Set Metric MeasureTheory MeasureTheory.Measure TopologicalSpace Filter Function
open scoped Distributions RealInnerProductSpace BoundedContinuousFunction Convolution ContDiff ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive lower density bound together with the actual residual support
forces the reference measure to be carried by the same compact set. -/
theorem ae_mem_of_residualDensityMeasure_ae_mem
    {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ] {f : (ι → ℝ) → ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (hfl : ∀ᵐ x ∂μ, ρ ≤ f x)
    {K₀ : Set (ι → ℝ)} (hK₀ : MeasurableSet K₀)
    (hν : ∀ᵐ x ∂(residualDensityMeasure μ f), x ∈ K₀) :
    ∀ᵐ x ∂μ, x ∈ K₀ := by
  have hνzero : residualDensityMeasure μ f (K₀ᶜ) = 0 := by
    have h := (ae_iff.mp hν)
    rw [show K₀ᶜ = {x | ¬ x ∈ K₀} from rfl]
    exact h
  have hineq : ENNReal.ofReal ρ * μ K₀ᶜ ≤ residualDensityMeasure μ f (K₀ᶜ) := by
    rw [residualDensityMeasure, withDensity_apply (fun x => ENNReal.ofReal (f x)) hK₀.compl]
    calc ENNReal.ofReal ρ * μ K₀ᶜ
        = ∫⁻ _x in K₀ᶜ, ENNReal.ofReal ρ ∂μ := by
          rw [lintegral_const, restrict_apply_univ]
      _ ≤ ∫⁻ x in K₀ᶜ, ENNReal.ofReal (f x) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae hfl] with x hx
          exact ENNReal.ofReal_le_ofReal hx
  rw [hνzero] at hineq
  have hmul : ENNReal.ofReal ρ * μ K₀ᶜ = 0 := le_antisymm hineq (by simp)
  have hρne : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.mpr hρ).ne'
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h hρne
  · rw [ae_iff]
    rwa [show K₀ᶜ = {x | ¬ x ∈ K₀} from rfl] at h

/-- A residual density measure inherits every almost-sure support restriction
from the reference measure. -/
theorem ae_mem_of_ae_mem_reference
    (μ : Measure (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    {K₀ : Set (ι → ℝ)} (hμ : ∀ᵐ x ∂μ, x ∈ K₀) :
    ∀ᵐ x ∂(residualDensityMeasure μ f), x ∈ K₀ :=
  (Measure.AbsolutelyContinuous.ae_le
    (MeasureTheory.withDensity_absolutelyContinuous μ (fun x => ENNReal.ofReal (f x)))) hμ

/-- **The unconditional endpoint transport coupling.** For two original residual
probability densities on a finite reference measure, the actual weak flux
constructed from the residual gradient estimate with constant `C` pairs with
every original smooth test with bounded energy. The actual residual support and
the positive lower density bound then supply the compact carrier of the capture
theorem, and the two residual measures admit a genuine coupling with
extended-distance cost at most `C * sqrt (card ι * (μ univ).toReal)`. -/
theorem exists_endpointCoupling_edist_le_of_neumannFlux_final
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (f g : (ι → ℝ) → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hfl : ∀ᵐ x ∂μ, ρ ≤ f x) (hgl : ∀ᵐ x ∂μ, ρ ≤ g x)
    (hprobS : IsProbabilityMeasure (residualDensityMeasure μ f))
    (hprobT : IsProbabilityMeasure (residualDensityMeasure μ g))
    {K₀ : Set (ι → ℝ)} (hK₀ : IsCompact K₀)
    (hνsuppS : ∀ᵐ x ∂(residualDensityMeasure μ f), x ∈ K₀)
    (hK₀K : K₀ ⊆ interior (K : Set (ι → ℝ)))
    (hbound : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ x, φ x * f x ∂μ) - ∫ x, φ x * g x ∂μ‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μ φ‖) :
    ∃ π : Measure ((ι → ℝ) × (ι → ℝ)),
      Vlasov.IsCoupling π (residualDensityMeasure μ f) (residualDensityMeasure μ g) ∧
      (∫⁻ z, edist z.1 z.2 ∂π) ≤
        ENNReal.ofReal (C * Real.sqrt ((Fintype.card ι : ℝ) * (μ univ).toReal)) := by
  have hμsupp : ∀ᵐ x ∂μ, x ∈ K₀ :=
    ae_mem_of_residualDensityMeasure_ae_mem hρ hfl hK₀.measurableSet hνsuppS
  have hνsuppT : ∀ᵐ x ∂(residualDensityMeasure μ g), x ∈ K₀ :=
    ae_mem_of_ae_mem_reference μ g hμsupp
  exact exists_endpointCoupling_edist_le_of_neumannFlux K μ f g hf hg hρ hC hfl hgl
    hprobS hprobT hK₀ hνsuppS hνsuppT hbound
    (capturesLipschitzDual_of_compact_support K μ f g hprobS hprobT hK₀ hμsupp hK₀K)

end OTSelector.Reconstruction
