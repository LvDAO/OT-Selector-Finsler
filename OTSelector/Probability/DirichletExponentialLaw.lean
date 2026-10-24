import OTSelector.Probability.DirichletExponentialScale
import Mathlib.Probability.Independence.Basic

/-!
# Normalized independent exponentials

Dividing genuine independent mean-one exponentials by their sum gives the
reference Dirichlet law. The total has the gamma law and is independent of
the normalized vector. The last theorem transfers this joint law to any
original probability space carrying the independent exponential variables.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- The total of a finite mass vector. -/
def totalMass (n : ℕ) (x : Fin (n + 1) → ℝ) : ℝ := ∑ i, x i

/-- Normalize a mass vector by its total, using the usual totalized inverse. -/
noncomputable def normalizedMass (n : ℕ) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  (totalMass n x)⁻¹ • x

/-- The total and normalized vector together. -/
noncomputable def totalNormalizedMass (n : ℕ) (x : Fin (n + 1) → ℝ) :
    ℝ × (Fin (n + 1) → ℝ) := (totalMass n x, normalizedMass n x)

theorem measurable_totalMass (n : ℕ) : Measurable (totalMass n) := by
  unfold totalMass
  fun_prop

theorem measurable_normalizedMass (n : ℕ) : Measurable (normalizedMass n) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_totalMass n).inv.mul (measurable_pi_apply i)

theorem measurable_totalNormalizedMass (n : ℕ) : Measurable (totalNormalizedMass n) :=
  (measurable_totalMass n).prodMk (measurable_normalizedMass n)

theorem totalNormalizedMass_scaleSimplex (n : ℕ) {s : ℝ}
    {p : Fin (n + 1) → ℝ} (hs : s ≠ 0) (hp : ∑ i, p i = 1) :
    totalNormalizedMass n (scaleSimplex n (s, p)) = (s, p) := by
  have hsum : totalMass n (scaleSimplex n (s, p)) = s := by
    simp only [totalMass, scaleSimplex, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      hp, mul_one]
  apply Prod.ext
  · exact hsum
  · change (totalMass n (scaleSimplex n (s, p)))⁻¹ • (s • p) = p
    rw [hsum, inv_smul_smul₀ hs]

/-- The genuine exponential product, expressed by its total and normalized
weights, is exactly a product of gamma and Dirichlet laws. -/
theorem map_totalNormalizedMass_pi_exp (n : ℕ) :
    (Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1)).map (totalNormalizedMass n) =
      (gammaMeasure ((n : ℝ) + 1) 1).prod (dirichletOne n) := by
  let := isProbabilityMeasure_gammaMeasure
    (by positivity : (0 : ℝ) < (n : ℝ) + 1) (by norm_num : (0 : ℝ) < 1)
  have hpos : ∀ᵐ z ∂(gammaMeasure ((n : ℝ) + 1) 1).prod (dirichletOne n), 0 < z.1 :=
    (measurePreserving_fst.quasiMeasurePreserving).ae (ae_pos_gammaMeasure _ _)
  have hsum : ∀ᵐ z ∂(gammaMeasure ((n : ℝ) + 1) 1).prod (dirichletOne n),
      ∑ i, z.2 i = 1 :=
    (measurePreserving_snd.quasiMeasurePreserving).ae
      ((ae_mem_stdSimplex_dirichletOne n).mono fun _ hp ↦ hp.2)
  rw [← map_gamma_dirichlet_scale_eq_pi_exp n,
    Measure.map_map (measurable_totalNormalizedMass n) (measurable_scaleSimplex n)]
  have heq : totalNormalizedMass n ∘ scaleSimplex n =ᵐ[
      (gammaMeasure ((n : ℝ) + 1) 1).prod (dirichletOne n)] id := by
    filter_upwards [hpos, hsum] with z hz hp
    exact totalNormalizedMass_scaleSimplex n hz.ne' hp
  rw [Measure.map_congr heq, Measure.map_id]

/-- Normalized independent exponentials have the already constructed uniform
Dirichlet law. -/
theorem map_normalizedMass_pi_exp (n : ℕ) :
    (Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1)).map (normalizedMass n) =
      dirichletOne n := by
  let := isProbabilityMeasure_gammaMeasure
    (by positivity : (0 : ℝ) < (n : ℝ) + 1) (by norm_num : (0 : ℝ) < 1)
  change (Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1)).map
    (Prod.snd ∘ totalNormalizedMass n) = _
  rw [← Measure.map_map measurable_snd (measurable_totalNormalizedMass n),
    map_totalNormalizedMass_pi_exp, Measure.map_snd_prod, measure_univ, one_smul]

/-- The total of independent exponentials has the corresponding gamma law. -/
theorem map_totalMass_pi_exp (n : ℕ) :
    (Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1)).map (totalMass n) =
      gammaMeasure ((n : ℝ) + 1) 1 := by
  change (Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1)).map
    (Prod.fst ∘ totalNormalizedMass n) = _
  rw [← Measure.map_map measurable_fst (measurable_totalNormalizedMass n),
    map_totalNormalizedMass_pi_exp, Measure.map_fst_prod, measure_univ, one_smul]

/-- The random total is independent of the normalized weights. -/
theorem indepFun_totalMass_normalizedMass_pi_exp (n : ℕ) :
    IndepFun (totalMass n) (normalizedMass n)
      (Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1)) := by
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_totalMass n).aemeasurable (measurable_normalizedMass n).aemeasurable).mpr
  rw [map_totalMass_pi_exp, map_normalizedMass_pi_exp]
  exact map_totalNormalizedMass_pi_exp n

/-- The same joint law holds on the original probability space; independence and
individual exponential laws suffice, with no distribution identity as input. -/
theorem map_totalNormalizedMass_iid_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (X : Fin (n + 1) → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = expMeasure 1) :
    μ.map (fun ω ↦ totalNormalizedMass n (fun i ↦ X i ω)) =
      (gammaMeasure ((n : ℝ) + 1) 1).prod (dirichletOne n) := by
  have hvec : Measurable (fun ω i ↦ X i ω) := measurable_pi_lambda _ hX
  change μ.map (totalNormalizedMass n ∘ (fun ω i ↦ X i ω)) = _
  rw [← Measure.map_map (measurable_totalNormalizedMass n) hvec,
    hi.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable)]
  simp_rw [hlaw]
  exact map_totalNormalizedMass_pi_exp n

end OTSelector.Probability
