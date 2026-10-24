import OTSelector.Probability.DirichletRootedTargetMass
import Mathlib.MeasureTheory.Group.Measure

/-!
# Local target mass bounds in translated original coordinate windows

Translation invariance bounds the mass of a window cut by the original finite
domain. The rooted Dirichlet second-moment estimate therefore has the exact
bound 2|B|+|B|², with no containment condition on the translated window.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableSub₂ E]
  [MeasurableAdd₂ E]

/-- Cutting a translated window by the original domain only reduces its mass.
The normalization is the original domain mass N. -/
theorem normalized_restrict_translated_mass_le (m ν : Measure E)
    [m.IsAddRightInvariant] (D : Set E) {N : ℝ} (hN : 0 < N)
    (hν : ν = (ENNReal.ofReal N)⁻¹ • m.restrict D)
    {B : Set E} (hB : MeasurableSet B) (hBfinite : m B ≠ ∞) (u : E) :
    N * ν.real {y | y - u ∈ B} ≤ m.real B := by
  have hA : MeasurableSet {y | y - u ∈ B} :=
    (measurable_id.sub measurable_const) hB
  have htranslate : m {y | y - u ∈ B} = m B := by
    calc
      _ = m ((fun y ↦ y + -u) ⁻¹' B) := by
        congr 1
        ext y
        simp only [mem_ofPred_eq, mem_preimage, sub_eq_add_neg]
      _ = m B := measure_preimage_add_right m (-u) B
  rw [hν, measureReal_ennreal_smul_apply, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hN.le, measureReal_restrict_apply hA,
    ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  calc
    _ ≤ m.real {y | y - u ∈ B} :=
      measureReal_mono inter_subset_left (htranslate.trans_ne hBfinite)
    _ = m.real B := congrArg ENNReal.toReal htranslate

/-- The actual random target cloud satisfies the paper's local second-moment
bound after averaging any independent root, including the original uniform root. -/
theorem integral_translated_dirichletTargetMass_sq_le (n : ℕ)
    (m ν ρ : Measure E) [m.IsAddRightInvariant]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] (D : Set E)
    (hν : ν = (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ • m.restrict D)
    {B : Set E} (hB : MeasurableSet B) (hBfinite : m B ≠ ∞) :
    (∫ z, (dirichletRootedTargetMass n {q : E × E | q.2 - q.1 ∈ B} z) ^ 2
      ∂ρ.prod ((dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))) ≤
      2 * m.real B + (m.real B) ^ 2 := by
  apply integral_dirichletRootedTargetMass_sq_le n ρ ν
    ((measurable_snd.sub measurable_fst) hB) measureReal_nonneg
  exact Filter.Eventually.of_forall fun u ↦
    normalized_restrict_translated_mass_le m ν D (by positivity) hν hB hBfinite u

end OTSelector.Probability
