import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
## Lemma skeleton

* **Conditions:** A probability law, measurable nonnegative kinetic term, bounded measurable probe, and a finite upper bound for a shifted nonnegative lower integral.
* **Objects:** Kinetic and probe integrability and the unshifted signed mean inequality.
* **Proof detail:** First obtain integrability from the finite nonnegative shifted energy and the bounded probe; then use linearity and cancel the deterministic shift.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp).
  https://measure.axler.net/MIRA.pdf#page=211

**Relationship to the sources:** Derived bounded-perturbation and constant-shift argument; the integrability conclusions are proved rather than supplied.
-/

/-! Recover signed means and kinetic integrability from nonnegative shifted energy. -/
open MeasureTheory Filter
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- A finite bound on the true shifted energy controls the unshifted signed
value and makes both original kinetic and bounded probe readouts integrable. -/
theorem integrable_signed_energy_of_shifted_lintegral_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (kin probe : X → ℝ) (hk : Measurable kin) (hkn : ∀ x, 0 ≤ kin x)
    (hg : Measurable probe) {G : ℝ} (hgb : ∀ x, |probe x| ≤ G)
    (t p : ℝ) (hlow : 0 ≤ p + |t| * G)
    (hbound : (∫⁻ x, ENNReal.ofReal (kin x + t * probe x + |t| * G) ∂μ) ≤
      ENNReal.ofReal (p + |t| * G)) :
    Integrable kin μ ∧ Integrable probe μ ∧
      (∫ x, kin x ∂μ) + t * (∫ x, probe x ∂μ) ≤ p := by
  let shift (x : X) := kin x + t * probe x + |t| * G
  have hm : Measurable shift :=
    (hk.add (measurable_const.mul hg)).add measurable_const
  have hn (x : X) : 0 ≤ shift x := by
    have hb : |t * probe x| ≤ |t| * G := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hgb x) (abs_nonneg t)
    dsimp only [shift]
    linarith [(abs_le.mp hb).1, hkn x]
  have hsI : Integrable shift μ := ⟨hm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (.of_forall hn)).mpr
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  have hmean : (∫ x, shift x ∂μ) ≤ p + |t| * G := by
    rw [← ofReal_integral_eq_lintegral_ofReal hsI (.of_forall hn)] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff hlow).mp hbound
  have hgI : Integrable probe μ := Integrable.of_bound hg.aestronglyMeasurable G
    (.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hgb x)
  have hkI : Integrable kin μ :=
    ((hsI.sub (integrable_const (|t| * G))).sub (hgI.const_mul t)).congr
      (.of_forall fun x ↦ by
        change (kin x + t * probe x + |t| * G - |t| * G) - t * probe x = kin x
        ring)
  refine ⟨hkI, hgI, ?_⟩
  change (∫ x, kin x + t * probe x + |t| * G ∂μ) ≤ p + |t| * G at hmean
  have hcostI : Integrable (fun x ↦ kin x + t * probe x) μ := hkI.add (hgI.const_mul t)
  rw [integral_add hcostI (integrable_const _),
    integral_add hkI (hgI.const_mul t), integral_const_mul, integral_const] at hmean
  simpa only [probReal_univ, one_smul, add_le_add_iff_right] using hmean

end OTSelector.Probability
