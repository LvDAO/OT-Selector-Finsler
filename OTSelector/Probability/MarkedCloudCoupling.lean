import OTSelector.Probability.MarkedPoissonCube
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Coupling marked clouds at two intensities

For `rho <= rho + delta`, a Poisson count of rate `rho + delta` is coupled to a
Poisson count of rate `rho` by adding an independent Poisson `delta` variable.
Using one common iid marked position sequence for both counts gives a coupling
of the two marked cloud laws in which the smaller cloud is a prefix of the
larger cloud.  This is the coupling used to prove continuity of the pressure in
the intensity.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {A : Type*} [MeasurableSpace A]

/-- The count coupling: a `Poisson rho` count and the sum with an independent
`Poisson delta` count. -/
noncomputable def countCouple (ρ δ : ℝ≥0) : Measure (ℕ × ℕ) :=
  ((poissonMeasure ρ).prod (poissonMeasure δ)).map (fun p : ℕ × ℕ => (p.1, p.1 + p.2))

/-- The first coordinate of the count coupling has the `rho` law. -/
theorem countCouple_map_fst (ρ δ : ℝ≥0) :
    (countCouple ρ δ).map Prod.fst = poissonMeasure ρ := by
  unfold countCouple
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have h : (Prod.fst ∘ fun p : ℕ × ℕ => (p.1, p.1 + p.2)) = Prod.fst := rfl
  rw [h, Measure.map_fst_prod, measure_univ, one_smul]

/-- The second coordinate of the count coupling has the `rho + delta` law. -/
theorem countCouple_map_snd (ρ δ : ℝ≥0) :
    (countCouple ρ δ).map Prod.snd = poissonMeasure (ρ + δ) := by
  unfold countCouple
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have h : (Prod.snd ∘ fun p : ℕ × ℕ => (p.1, p.1 + p.2)) = fun p => p.1 + p.2 := rfl
  rw [h]
  -- The sum of two independent Poisson variables, via the convolution law.
  have hlaw : ((poissonMeasure ρ).prod (poissonMeasure δ)).map (fun p : ℕ × ℕ => p.1 + p.2)
      = poissonMeasure (ρ + δ) := by
    rw [← poissonMeasure_conv_poissonMeasure]
    rfl
  exact hlaw

/-- The marked cloud coupling: one common iid marked sequence and the coupled
counts. -/
noncomputable def cloudCouple (q : ℕ) (A : Type*) [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (ρ δ : ℝ≥0) :
    Measure ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) :=
  (countCouple ρ δ).prod (markedSeqLaw (q := q) A α)

/-- Extract the smaller cloud from the coupling. -/
def coupledSmall {q : ℕ} (z : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) :
    MarkedCloudSpace q A := (z.1.1, z.2)

/-- Extract the larger cloud from the coupling. -/
def coupledLarge {q : ℕ} (z : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) :
    MarkedCloudSpace q A := (z.1.2, z.2)

/-- Measurability of the smaller cloud extraction. -/
theorem measurable_coupledSmall (q : ℕ) :
    Measurable (coupledSmall (q := q) :
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) → MarkedCloudSpace q A) := by
  unfold coupledSmall
  fun_prop

/-- Measurability of the larger cloud extraction. -/
theorem measurable_coupledLarge (q : ℕ) :
    Measurable (coupledLarge (q := q) :
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) → MarkedCloudSpace q A) := by
  unfold coupledLarge
  fun_prop

/-- The smaller marginal is the `rho` cloud. -/
theorem cloudCouple_map_small (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (ρ δ : ℝ≥0) :
    (cloudCouple (q := q) A α ρ δ).map (coupledSmall (q := q)) =
      markedPoissonLaw (q := q) A α ρ := by
  unfold cloudCouple coupledSmall markedPoissonLaw
  rw [show (fun z : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A) => (z.1.1, z.2)) =
      Prod.map Prod.fst id from rfl]
  rw [← Measure.map_prod_map]
  · rw [countCouple_map_fst, Measure.map_id]
  · exact measurable_fst
  · exact measurable_id

/-- The larger marginal is the `rho + delta` cloud. -/
theorem cloudCouple_map_large (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (ρ δ : ℝ≥0) :
    (cloudCouple (q := q) A α ρ δ).map (coupledLarge (q := q)) =
      markedPoissonLaw (q := q) A α (ρ + δ) := by
  unfold cloudCouple coupledLarge markedPoissonLaw
  rw [show (fun z : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A) => (z.1.2, z.2)) =
      Prod.map Prod.snd id from rfl]
  rw [← Measure.map_prod_map]
  · rw [countCouple_map_snd, Measure.map_id]
  · exact measurable_snd
  · exact measurable_id

/-- The two-cloud coupling of intensity `rho` to intensity `rho + delta`. -/
noncomputable def twoCloudCouple (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    Measure (((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B))) :=
  (cloudCouple (q := q) A α ρ δ).prod (cloudCouple (q := q) B β ρ δ)

/-- The `rho` two-cloud marginal of the coupling. -/
theorem twoCloudCouple_map_small (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    (twoCloudCouple (q := q) A B α β ρ δ).map
        (fun z => (coupledSmall (q := q) z.1, coupledSmall (q := q) z.2)) =
      twoMarkedCloudLaw (q := q) A B α β ρ := by
  haveI hcount : IsProbabilityMeasure (countCouple ρ δ) := by
    unfold countCouple
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI hcloudA : IsProbabilityMeasure (cloudCouple (q := q) A α ρ δ) := by
    unfold cloudCouple
    infer_instance
  haveI hcloud : IsProbabilityMeasure (cloudCouple (q := q) B β ρ δ) := by
    unfold cloudCouple
    infer_instance
  unfold twoCloudCouple twoMarkedCloudLaw
  rw [show (fun z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
        ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      (coupledSmall (q := q) z.1, coupledSmall (q := q) z.2)) =
      Prod.map (coupledSmall (q := q)) (coupledSmall (q := q)) from rfl]
  rw [← Measure.map_prod_map]
  · rw [cloudCouple_map_small, cloudCouple_map_small]
  · exact measurable_coupledSmall q
  · exact measurable_coupledSmall q

/-- The `rho + delta` two-cloud marginal of the coupling. -/
theorem twoCloudCouple_map_large (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    (twoCloudCouple (q := q) A B α β ρ δ).map
        (fun z => (coupledLarge (q := q) z.1, coupledLarge (q := q) z.2)) =
      twoMarkedCloudLaw (q := q) A B α β (ρ + δ) := by
  haveI hcount : IsProbabilityMeasure (countCouple ρ δ) := by
    unfold countCouple
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI hcloudA : IsProbabilityMeasure (cloudCouple (q := q) A α ρ δ) := by
    unfold cloudCouple
    infer_instance
  haveI hcloud : IsProbabilityMeasure (cloudCouple (q := q) B β ρ δ) := by
    unfold cloudCouple
    infer_instance
  unfold twoCloudCouple twoMarkedCloudLaw
  rw [show (fun z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
        ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      (coupledLarge (q := q) z.1, coupledLarge (q := q) z.2)) =
      Prod.map (coupledLarge (q := q)) (coupledLarge (q := q)) from rfl]
  rw [← Measure.map_prod_map]
  · rw [cloudCouple_map_large, cloudCouple_map_large]
  · exact measurable_coupledLarge q
  · exact measurable_coupledLarge q

end OTSelector.Probability
