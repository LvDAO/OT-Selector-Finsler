import OTSelector.Probability.SemidiscreteTargetCloud
import OTSelector.MeasureTheory.LocalFiniteMeasureMarginalTightness
import OTSelector.Probability.DirichletTranslatedWindow

/-!
# Original Dirichlet moments for the actual target measure

The finite atomic cloud has exactly the previously estimated rooted local mass.
This identifies its actual vague-law moment bounds on the original probability
space, with unchanged root, weights and observations.
-/

open MeasureTheory ProbabilityTheory Set Function Filter TopologicalSpace
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {Y : Type*} [MeasurableSpace Y]

/-- Actual finite target measure evaluation is the original weighted indicator
sum, with its exact total-mass scale. -/
theorem semidiscreteTargetCloud_real (p : Fin (m + 1) → ℝ)
    (hp : ∀ j, 0 ≤ p j) (y : Fin (m + 1) → Y) {N : ℝ} (hN : 0 ≤ N)
    {A : Set Y} (hA : MeasurableSet A) :
    (semidiscreteTargetCloud p y N).real A =
      N * ∑ j, p j * A.indicator (fun _ ↦ (1 : ℝ)) (y j) := by
  classical
  rw [semidiscreteTargetCloud_eq_sum, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal hN]
  congr 1
  simp only [measureReal_def, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun j _ ↦
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hp j), Measure.dirac_apply' _ hA]
  by_cases hj : y j ∈ A <;> simp [hj]

/-- The actual observed target cloud has precisely the old rooted-mass scalar
readout; the observation may depend on the original root. -/
theorem semidiscreteTargetCloud_real_eq_rootedMass
    {R S : Type*} [MeasurableSpace R] [MeasurableSpace S]
    (T : R × S → Y)
    (r : R) (p : Fin (m + 1) → ℝ) (hp : ∀ j, 0 ≤ p j)
    (y : Fin (m + 1) → S) {A : Set Y} (hA : MeasurableSet A) :
    (semidiscreteTargetCloud p (fun j ↦ T (r, y j)) ((m : ℝ) + 1)).real A =
      dirichletRootedTargetMass m (T ⁻¹' A) (r, (p, y)) := by
  rw [semidiscreteTargetCloud_real p hp _ (by positivity) hA]
  unfold dirichletRootedTargetMass
  congr 1

/-- Uniform original target-count bounds give local second moments of the actual
random measure, on the original probability space. -/
theorem integral_original_semidiscreteTargetCloud_sq_le
    {Ω R S : Type*} [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Measure R) [IsProbabilityMeasure ρ] (ν : Measure S) [IsProbabilityMeasure ν]
    (U : Ω → R) (p : Ω → Fin (m + 1) → ℝ) (y : Fin (m + 1) → Ω → S)
    (hscene : MeasurePreserving
      (fun ω ↦ (U ω, (p ω, fun j ↦ y j ω))) P
      (ρ.prod ((dirichletOne m).prod (Measure.pi (fun _ : Fin (m + 1) ↦ ν)))))
    (T : R × S → Y) (hT : Measurable T)
    {A : Set Y} (hA : MeasurableSet A) {V : ℝ} (hV : 0 ≤ V)
    (hmass : ∀ᵐ r ∂ρ, ((m : ℝ) + 1) * ν.real {s | T (r, s) ∈ A} ≤ V) :
    Integrable (fun ω ↦ ((semidiscreteTargetCloud (p ω)
      (fun j ↦ T (U ω, y j ω)) ((m : ℝ) + 1)).real A) ^ 2) P ∧
    (∫ ω, ((semidiscreteTargetCloud (p ω)
      (fun j ↦ T (U ω, y j ω)) ((m : ℝ) + 1)).real A) ^ 2 ∂P) ≤ 2 * V + V ^ 2 := by
  have hs : ∀ᵐ ω ∂P, p ω ∈ stdSimplex ℝ (Fin (m + 1)) := by
    have hmap : MeasurePreserving (fun z : R × ((Fin (m + 1) → ℝ) ×
        (Fin (m + 1) → S)) ↦ z.2.1)
        (ρ.prod ((dirichletOne m).prod (Measure.pi (fun _ : Fin (m + 1) ↦ ν))))
        (dirichletOne m) :=
      measurePreserving_fst.comp measurePreserving_snd
    have hh := hmap.comp hscene
    apply ae_of_ae_map (p := fun q : Fin (m + 1) → ℝ ↦ q ∈ stdSimplex ℝ (Fin (m + 1)))
      hh.measurable.aemeasurable
    rw [hh.map_eq]
    exact ae_mem_stdSimplex_dirichletOne m
  have heq : (fun ω ↦ ((semidiscreteTargetCloud (p ω)
      (fun j ↦ T (U ω, y j ω)) ((m : ℝ) + 1)).real A) ^ 2) =ᵐ[P]
      fun ω ↦ (dirichletRootedTargetMass m (T ⁻¹' A)
        (U ω, (p ω, fun j ↦ y j ω))) ^ 2 := by
    filter_upwards [hs] with ω hω
    rw [semidiscreteTargetCloud_real_eq_rootedMass T _ _ hω.1 _ hA]
  obtain ⟨hi, hb⟩ := integral_original_dirichletRootedTargetMass_sq_le m P ρ ν U p y
    hscene (hT hA) hV hmass
  exact ⟨hi.congr heq.symm, (integral_congr_ae heq).trans_le hb⟩

end OTSelector.Probability
