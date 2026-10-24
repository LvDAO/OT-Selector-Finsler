import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Transport.PositiveDensityInterpolationAction

## Lemma skeleton

* **Conditions:** Two nonnegative densities share a strictly positive lower bound, the flux is square-integrable, and the time law is a probability carried by [0,1].

* **Objects:** Linear density interpolation and its genuine space-time quadratic action.

* **Proof detail:** The convex combination retains the common density lower bound. Divide the squared flux norm by that density, dominate by its L2 energy divided by the lower bound, and integrate the product estimate.

## Mathematical sources

- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=116): Section 7.1, pp. 112–113, equations (7.2)–(7.5).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=147): Section 5B, Theorem 5.32 (Fubini), pp. 132–133.

Source relation (corollary): Only the positive-density action estimate is formalized; no continuity equation or Benamou–Brenier optimizer is postulated by this module.
-/

/-!
# The actual positive-density interpolation action

The same fixed flux is used at every interpolation time. A common lower density
bound controls its literal space-time action by its original L² energy. No
transport coupling or continuity-equation solution is postulated here.
-/
open Set MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]

/-- Linear interpolation of the two actual residual densities. -/
def residualDensityInterpolation (f g : X → ℝ) (τ : ℝ) (x : X) : ℝ :=
  (1 - τ) * f x + τ * g x

/-- The actual quadratic action density of the unchanged flux along the linear
residual-density interpolation. -/
def residualInterpolationAction (j : X → V) (f g : X → ℝ) (z : ℝ × X) : ℝ :=
  ‖j z.2‖ ^ 2 / residualDensityInterpolation f g z.1 z.2

omit [MeasurableSpace X] in
theorem residualDensityInterpolation_lower {f g : X → ℝ} {ρ τ : ℝ} {x : X}
    (hτ : τ ∈ Icc (0 : ℝ) 1) (hf : ρ ≤ f x) (hg : ρ ≤ g x) :
    ρ ≤ residualDensityInterpolation f g τ x := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hτ.2) (sub_nonneg.mpr hf)
  have h₂ := mul_nonneg hτ.1 (sub_nonneg.mpr hg)
  dsimp only [residualDensityInterpolation]
  nlinarith

omit [MeasurableSpace X] in
theorem residualInterpolationAction_le {j : X → V} {f g : X → ℝ}
    {ρ τ : ℝ} {x : X} (hρ : 0 < ρ) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hf : ρ ≤ f x) (hg : ρ ≤ g x) :
    0 ≤ residualInterpolationAction j f g (τ, x) ∧
      residualInterpolationAction j f g (τ, x) ≤ ρ⁻¹ * ‖j x‖ ^ 2 := by
  have hl := residualDensityInterpolation_lower hτ hf hg
  have hp : 0 < residualDensityInterpolation f g τ x := hρ.trans_le hl
  refine ⟨div_nonneg (sq_nonneg _) hp.le, ?_⟩
  dsimp only [residualInterpolationAction]
  calc
    _ ≤ ‖j x‖ ^ 2 / ρ := div_le_div_of_nonneg_left (sq_nonneg _) hρ hl
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- The actual space-time action is integrable and obeys the exact inverse
lower-density times energy estimate. The interpolation-time law may be any
probability supported on the unit interval. -/
theorem residualInterpolationAction_integrable_and_integral_le
    (μ : Measure X) [SFinite μ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (j : X → V) (hj : MemLp j 2 μ) (f g : X → ℝ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hτ : ∀ᵐ τ ∂ν, τ ∈ Icc (0 : ℝ) 1)
    (hfl : ∀ᵐ x ∂μ, ρ ≤ f x) (hgl : ∀ᵐ x ∂μ, ρ ≤ g x) :
    Integrable (residualInterpolationAction j f g) (ν.prod μ) ∧
      (∫ z, residualInterpolationAction j f g z ∂ν.prod μ) ≤
        ρ⁻¹ * ∫ x, ‖j x‖ ^ 2 ∂μ := by
  have hjprod := hj.comp_snd ν
  have henergy : Integrable (fun z : ℝ × X ↦ ‖j z.2‖ ^ 2) (ν.prod μ) :=
    (memLp_two_iff_integrable_sq_norm hjprod.aestronglyMeasurable).mp hjprod
  have hbound : ∀ᵐ z ∂ν.prod μ,
      0 ≤ residualInterpolationAction j f g z ∧
        residualInterpolationAction j f g z ≤ ρ⁻¹ * ‖j z.2‖ ^ 2 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae hτ,
      (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae hfl,
      (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae hgl] with z hz hz₀ hz₁
    exact residualInterpolationAction_le hρ hz hz₀ hz₁
  have hmeas : AEStronglyMeasurable (residualInterpolationAction j f g) (ν.prod μ) := by
    have hd : AEMeasurable
        (fun z : ℝ × X ↦ residualDensityInterpolation f g z.1 z.2) (ν.prod μ) :=
      ((aemeasurable_const.sub measurable_fst.aemeasurable).mul hf.comp_snd).add
        (measurable_fst.aemeasurable.mul hg.comp_snd)
    exact ((hjprod.aestronglyMeasurable.norm.aemeasurable.pow_const 2).div hd).aestronglyMeasurable
  have hI : Integrable (residualInterpolationAction j f g) (ν.prod μ) :=
    (henergy.const_mul ρ⁻¹).mono' hmeas (hbound.mono fun z hz ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
      exact hz.2)
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ z : ℝ × X, ρ⁻¹ * ‖j z.2‖ ^ 2 ∂ν.prod μ :=
      integral_mono_ae hI (henergy.const_mul ρ⁻¹) (hbound.mono fun _ hz ↦ hz.2)
    _ = ρ⁻¹ * ∫ x, ‖j x‖ ^ 2 ∂μ := by
      rw [integral_const_mul]
      erw [integral_fun_snd (μ := ν) (ν := μ) (fun x ↦ ‖j x‖ ^ 2)]
      simp

end OTSelector.Reconstruction
