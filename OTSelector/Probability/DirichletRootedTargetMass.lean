import OTSelector.Probability.DirichletWeightedTargetMass

/-!
# Independent roots and actual local target masses

A measurable source-target window may depend on an independent root. The exact
Dirichlet second moment gives the same uniform bound after averaging that root.
This is the local mass estimate needed for the original rooted target scenes.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {R S : Type*} [MeasurableSpace R] [MeasurableSpace S]

/-- Actual weighted target mass in a window determined by the root. -/
def dirichletRootedTargetMass (n : ℕ) (H : Set (R × S))
    (z : R × ((Fin (n + 1) → ℝ) × (Fin (n + 1) → S))) : ℝ :=
  ((n : ℝ) + 1) * ∑ j, z.2.1 j * H.indicator (fun _ ↦ (1 : ℝ)) (z.1, z.2.2 j)

theorem measurable_dirichletRootedTargetMass (n : ℕ) {H : Set (R × S)}
    (hH : MeasurableSet H) : Measurable (dirichletRootedTargetMass n H) := by
  have hm : Measurable (H.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hH
  unfold dirichletRootedTargetMass
  fun_prop

omit [MeasurableSpace R] [MeasurableSpace S] in
/-- Fixing the root gives precisely the original local target mass. -/
theorem dirichletRootedTargetMass_eq (n : ℕ) (H : Set (R × S)) (r : R)
    (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → S)) :
    dirichletRootedTargetMass n H (r, z) =
      dirichletWeightedTargetMass n {y | (r, y) ∈ H} z := rfl

/-- The original rooted local mass is nonnegative and at most the cloud's
total mass almost surely, for every root-dependent window. -/
theorem ae_dirichletRootedTargetMass_bounds (n : ℕ)
    (ρ : Measure R) [IsProbabilityMeasure ρ] (ν : Measure S) [IsProbabilityMeasure ν]
    (H : Set (R × S)) :
    ∀ᵐ z ∂ρ.prod ((dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν))),
      0 ≤ dirichletRootedTargetMass n H z ∧
        dirichletRootedTargetMass n H z ≤ (n : ℝ) + 1 := by
  have hs₀ : ∀ᵐ z ∂(dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)),
      z.1 ∈ stdSimplex ℝ (Fin (n + 1)) := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    simpa only [Measure.map_fst_prod, measure_univ, one_smul] using
      ae_mem_stdSimplex_dirichletOne n
  have hs : ∀ᵐ z ∂ρ.prod ((dirichletOne n).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))),
      z.2.1 ∈ stdSimplex ℝ (Fin (n + 1)) := by
    apply ae_of_ae_map (p := fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → S) ↦
      z.1 ∈ stdSimplex ℝ (Fin (n + 1))) measurable_snd.aemeasurable
    simpa only [Measure.map_snd_prod, measure_univ, one_smul] using hs₀
  filter_upwards [hs] with z hz
  exact dirichletWeightedTargetMass_bounds n {y | (z.1, y) ∈ H} hz z.2.2

/-- Actual rooted local masses have integrable polynomial moments. -/
theorem integrable_dirichletRootedTargetMass_pow (n : ℕ)
    (ρ : Measure R) [IsProbabilityMeasure ρ] (ν : Measure S) [IsProbabilityMeasure ν]
    {H : Set (R × S)} (hH : MeasurableSet H) (k : ℕ) :
    Integrable (fun z ↦ (dirichletRootedTargetMass n H z) ^ k)
      (ρ.prod ((dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))) := by
  have hm := measurable_dirichletRootedTargetMass n hH
  have hmk : Measurable (fun z ↦ (dirichletRootedTargetMass n H z) ^ k) := by fun_prop
  apply Integrable.of_bound hmk.aestronglyMeasurable (((n : ℝ) + 1) ^ k)
  filter_upwards [ae_dirichletRootedTargetMass_bounds n ρ ν H] with z hb
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hb.1]
  exact pow_le_pow_left₀ hb.1 hb.2 k

/-- An independent random root preserves the sample-size independent second
moment bound whenever each root window has unweighted mean mass at most V. -/
theorem integral_dirichletRootedTargetMass_sq_le (n : ℕ)
    (ρ : Measure R) [IsProbabilityMeasure ρ] (ν : Measure S) [IsProbabilityMeasure ν]
    {H : Set (R × S)} (hH : MeasurableSet H) {V : ℝ} (hV : 0 ≤ V)
    (hmass : ∀ᵐ r ∂ρ, ((n : ℝ) + 1) * ν.real {y | (r, y) ∈ H} ≤ V) :
    (∫ z, (dirichletRootedTargetMass n H z) ^ 2
      ∂ρ.prod ((dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))) ≤
      2 * V + V ^ 2 := by
  have hi := integrable_dirichletRootedTargetMass_pow n ρ ν hH 2
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ : R, (2 * V + V ^ 2) ∂ρ := by
      apply integral_mono_ae hi.integral_prod_left (integrable_const _)
      filter_upwards [hmass] with r hr
      simp_rw [dirichletRootedTargetMass_eq]
      exact integral_dirichletWeightedTargetMass_sq_le n ν
        ((measurable_const.prodMk measurable_id) hH) hV hr
    _ = 2 * V + V ^ 2 := by simp

end OTSelector.Probability
