import OTSelector.Probability.DirichletOriginalTargetScene
import OTSelector.Probability.SecondMomentMassTails
import OTSelector.Probability.DirichletTranslatedWindow

/-!
# Uniform local-mass tails for original rooted target clouds

The exact moment calculation and original scene law give quantitative mass and
probability tails on the original sample space. The constants depend only on
window mass, so the estimates are uniform over sample size and imply uniform
integrability of the local target masses.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {Ω R S : Type*} [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace S]

/-- Both quantitative tail estimates hold for the original root, original
Dirichlet weights and original iid target observations. -/
theorem original_dirichletRootedTargetMass_tail_bounds
    (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Measure R) [IsProbabilityMeasure ρ] (ν : Measure S) [IsProbabilityMeasure ν]
    (U : Ω → R) (p : Ω → Fin (n + 1) → ℝ) (Y : Fin (n + 1) → Ω → S)
    (hscene : MeasurePreserving
      (fun sample ↦ (U sample, (p sample, fun j ↦ Y j sample))) P
      (ρ.prod ((dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))))
    {H : Set (R × S)} (hH : MeasurableSet H) {V : ℝ} (hV : 0 ≤ V)
    (hmass : ∀ᵐ r ∂ρ, ((n : ℝ) + 1) * ν.real {y | (r, y) ∈ H} ≤ V) :
    let f := fun sample ↦ dirichletRootedTargetMass n H
      (U sample, (p sample, fun j ↦ Y j sample))
    ∀ L > 0,
      (∫ sample in {sample | L ≤ f sample}, f sample ∂P) ≤ (2 * V + V ^ 2) / L ∧
      P.real {sample | L ≤ f sample} ≤ (2 * V + V ^ 2) / L ^ 2 := by
  dsimp only
  intro L hL
  have hm := (measurable_dirichletRootedTargetMass n hH).comp hscene.measurable
  have hi : Integrable (fun sample ↦ dirichletRootedTargetMass n H
      (U sample, (p sample, fun j ↦ Y j sample))) P := by
    have h := hscene.integrable_comp_of_integrable
      (integrable_dirichletRootedTargetMass_pow n ρ ν hH 1)
    simpa only [pow_one, Function.comp_def] using h
  have hpos : ∀ᵐ sample ∂P, 0 ≤ dirichletRootedTargetMass n H
      (U sample, (p sample, fun j ↦ Y j sample)) := by
    apply ae_of_ae_map
      (p := fun z : R × ((Fin (n + 1) → ℝ) × (Fin (n + 1) → S)) ↦
        0 ≤ dirichletRootedTargetMass n H z)
      (μ := P) hscene.measurable.aemeasurable
    rw [hscene.map_eq]
    exact (ae_dirichletRootedTargetMass_bounds n ρ ν H).mono (fun _ h ↦ h.1)
  obtain ⟨hsq, hsecond⟩ := integral_original_dirichletRootedTargetMass_sq_le
    n P ρ ν U p Y hscene hH hV hmass
  exact ⟨setIntegral_mass_tail_le_of_second_moment hm hi hsq hpos hsecond hL,
    probability_mass_tail_le_of_second_moment hsq hsecond hL⟩

end OTSelector.Probability
