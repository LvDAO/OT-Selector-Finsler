import OTSelector.Probability.DirichletRootedTargetMass

/-!
# Rooted target moments on the original probability space

The original iid target array, Dirichlet weight vector and independent root
give exactly the joint law used in the local-mass calculation. The moment bound
therefore holds for the original random variables, without replacing their
probability space or choosing a new coupling.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {Ω R S : Type*} [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace S]

/-- The actual independent root, weights and iid targets have the required
product scene law on their original probability space. -/
theorem measurePreserving_original_dirichletTargetScene
    (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Measure R) [IsProbabilityMeasure ρ] (ν : Measure S) [IsProbabilityMeasure ν]
    (U : Ω → R) (p : Ω → Fin (n + 1) → ℝ) (Y : Fin (n + 1) → Ω → S)
    (hU : Measurable U) (hp : Measurable p) (hY : ∀ j, Measurable (Y j))
    (hUlaw : P.map U = ρ) (hplaw : P.map p = dirichletOne n)
    (hYlaw : ∀ j, P.map (Y j) = ν) (hYi : iIndepFun Y P)
    (hpY : IndepFun p (fun sample j ↦ Y j sample) P)
    (hUscene : IndepFun U (fun sample ↦ (p sample, fun j ↦ Y j sample)) P) :
    MeasurePreserving (fun sample ↦ (U sample, (p sample, fun j ↦ Y j sample))) P
      (ρ.prod ((dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))) := by
  have hmY : Measurable (fun sample j ↦ Y j sample) := measurable_pi_lambda _ hY
  have hlY : P.map (fun sample j ↦ Y j sample) = Measure.pi (fun _ : Fin (n + 1) ↦ ν) := by
    rw [hYi.map_fun_eq_pi_map (fun j ↦ (hY j).aemeasurable)]
    simp_rw [hYlaw]
  have hpair := hpY.map_prod_eq_prod_map_map hp.aemeasurable hmY.aemeasurable
  rw [hplaw, hlY] at hpair
  have hscene := hUscene.map_prod_eq_prod_map_map hU.aemeasurable
    (hp.prodMk hmY).aemeasurable
  rw [hUlaw, hpair] at hscene
  exact ⟨hU.prodMk (hp.prodMk hmY), hscene⟩

/-- Transfer of the rooted mass bound to an original scene with its actual law. -/
theorem integral_original_dirichletRootedTargetMass_sq_le
    (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Measure R) [IsProbabilityMeasure ρ] (ν : Measure S) [IsProbabilityMeasure ν]
    (U : Ω → R) (p : Ω → Fin (n + 1) → ℝ) (Y : Fin (n + 1) → Ω → S)
    (hscene : MeasurePreserving
      (fun sample ↦ (U sample, (p sample, fun j ↦ Y j sample))) P
      (ρ.prod ((dirichletOne n).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))))
    {H : Set (R × S)} (hH : MeasurableSet H) {V : ℝ} (hV : 0 ≤ V)
    (hmass : ∀ᵐ r ∂ρ, ((n : ℝ) + 1) * ν.real {y | (r, y) ∈ H} ≤ V) :
    Integrable (fun sample ↦
      (dirichletRootedTargetMass n H (U sample, (p sample, fun j ↦ Y j sample))) ^ 2) P ∧
    (∫ sample, (dirichletRootedTargetMass n H
      (U sample, (p sample, fun j ↦ Y j sample))) ^ 2 ∂P) ≤ 2 * V + V ^ 2 := by
  have hi := integrable_dirichletRootedTargetMass_pow n ρ ν hH 2
  have hm := measurable_dirichletRootedTargetMass n hH
  have hmk : Measurable (fun z ↦ (dirichletRootedTargetMass n H z) ^ 2) := by fun_prop
  refine ⟨hscene.integrable_comp_of_integrable hi, ?_⟩
  have hb := integral_dirichletRootedTargetMass_sq_le n ρ ν hH hV hmass
  rw [← hscene.map_eq, integral_map hscene.measurable.aemeasurable hmk.aestronglyMeasurable] at hb
  exact hb

end OTSelector.Probability
