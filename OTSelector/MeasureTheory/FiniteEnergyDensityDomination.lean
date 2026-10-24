import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
## Lemma skeleton

* **Conditions:** A sigma-finite reference/root law, finite positive energy measure and almost-everywhere measurable nonnegative real p whose density measure is dominated by energy.
* **Objects:** Order of finite-measure RN derivatives, integrable energy density, almost-everywhere p domination and the total mean budget.
* **Proof detail:** Take RN derivatives of the measure order, use the derivative of p times the root law, and integrate against the finite absolutely continuous part of energy.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27

**Relationship to the sources:** RN/Lebesgue decomposition corollary allowing a singular energy part. Energy absolute continuity or uniform integrability is not assumed.
-/

/-! Finite energy measures control nonnegative pressure densities even when
energy concentrates into a singular part. No absolute continuity of energy,
uniform integrability or convergence of finite-sample densities is assumed. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {Z : Type*} [MeasurableSpace Z]

/-- Order of finite measures gives order of their absolutely continuous
Radon-Nikodym densities; singular parts are retained in the measures. -/
theorem ae_rnDeriv_le_of_finite_measure_le
    (μ ν rootLaw : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite rootLaw] (hle : μ ≤ ν) :
    μ.rnDeriv rootLaw ≤ᵐ[rootLaw] ν.rnDeriv rootLaw := by
  have heq : ν - μ + μ = ν := Measure.sub_add_cancel_of_le hle
  have hadd := Measure.rnDeriv_add (ν - μ) μ rootLaw
  rw [heq] at hadd
  filter_upwards [hadd] with z hz
  rw [hz]
  exact le_add_left le_rfl

/-- A true nonnegative pressure measure dominated by finite original energy
has a canonical integrable majorant: the absolutely continuous part of that
energy. Singular limiting energy needs no further regularity or removal. -/
theorem integrable_pressure_of_finite_energy_measure
    (rootLaw energy : Measure Z) [SigmaFinite rootLaw] [IsFiniteMeasure energy]
    (p : Z → ℝ) (hp : AEStronglyMeasurable p rootLaw) (hpnonneg : 0 ≤ᵐ[rootLaw] p)
    (hlocal : rootLaw.withDensity (fun z ↦ ENNReal.ofReal (p z)) ≤ energy) :
    Integrable (fun z ↦ (energy.rnDeriv rootLaw z).toReal) rootLaw ∧
      (p ≤ᵐ[rootLaw] fun z ↦ (energy.rnDeriv rootLaw z).toReal) ∧
      Integrable p rootLaw ∧ (∫ z, p z ∂rootLaw) ≤ energy.real univ := by
  let pressure := rootLaw.withDensity (fun z ↦ ENNReal.ofReal (p z))
  let _ : IsFiniteMeasure pressure := isFiniteMeasure_of_le energy hlocal
  have hmono := ae_rnDeriv_le_of_finite_measure_le pressure energy rootLaw hlocal
  have hpressure := Measure.rnDeriv_withDensity₀ rootLaw hp.aemeasurable.ennreal_ofReal
  have hmajorant : Integrable (fun z ↦ (energy.rnDeriv rootLaw z).toReal) rootLaw := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (ν := rootLaw) (measure_ne_top energy univ))
  have hle : p ≤ᵐ[rootLaw] fun z ↦ (energy.rnDeriv rootLaw z).toReal := by
    filter_upwards [hmono, hpressure, hpnonneg, Measure.rnDeriv_lt_top energy rootLaw]
      with z hz hzp hzn hzf
    rw [hzp] at hz
    simpa only [ENNReal.toReal_ofReal hzn] using
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hzf.ne).mpr hz
  have hpI : Integrable p rootLaw := hmajorant.mono' hp (by
    filter_upwards [hle, hpnonneg] with z hz hzn
    simpa only [Real.norm_eq_abs, abs_of_nonneg hzn] using hz)
  refine ⟨hmajorant, hle, hpI, ?_⟩
  exact (integral_mono_ae hpI hmajorant hle).trans
    (by simpa only [setIntegral_univ] using
      (Measure.setIntegral_toReal_rnDeriv_le (ν := rootLaw) (measure_ne_top energy univ)))

end OTSelector.Reconstruction
