import OTSelector.Finite.MaxCardValueRegularity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Regularity of the expected maximum-cardinality pressure

The tilted maximum-cardinality value of a random cloud is concave and Lipschitz
in the tilt, uniformly in the realization.  Integrating over the cloud law
preserves both properties.  These lemmas are stated for clouds of random size,
so they apply directly to Poisson inputs.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

open OTSelector

/-- The tilted maximum-cardinality value of a random cloud. -/
def tiltedCloudValue {Ω : Type*} (cost probe : (ω : Ω) → ℕ → ℕ → ℝ)
    (t : ℝ) (ω : Ω) (Np Nm : ℕ) : ℝ :=
  PartialMatching.maxCardValue (fun i : Fin Np ↦ fun j : Fin Nm ↦
    cost ω (i : ℕ) (j : ℕ) + t * probe ω (i : ℕ) (j : ℕ))

/-- Concavity in the tilt passes through the expectation. -/
theorem concaveOn_integral_tiltedCloudValue
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cost probe : (ω : Ω) → ℕ → ℕ → ℝ) (Np Nm : Ω → ℕ)
    (V : ℝ → Ω → ℝ)
    (hV : ∀ t, V t = fun ω ↦ tiltedCloudValue cost probe t ω (Np ω) (Nm ω))
    (hInt : ∀ t, Integrable (V t) P) :
    ConcaveOn ℝ Set.univ (fun t ↦ ∫ ω, V t ω ∂P) := by
  refine ⟨convex_univ, ?_⟩
  intro t _ u _ a b ha hb hab
  have hcomb : Integrable (fun ω ↦ a * V t ω + b * V u ω) P :=
    ((hInt t).const_mul a).add ((hInt u).const_mul b)
  have hpt : ∀ ω, a * V t ω + b * V u ω ≤ V (a * t + b * u) ω := by
    intro ω
    have hconc := (PartialMatching.concaveOn_maxCardValue_perturbed
      (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦
        cost ω (i : ℕ) (j : ℕ))
      (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦
        probe ω (i : ℕ) (j : ℕ))).2 (mem_univ t) (mem_univ u) ha hb hab
    have hVt : V t ω = PartialMatching.maxCardValue
        (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦
          cost ω (i : ℕ) (j : ℕ) + t * probe ω (i : ℕ) (j : ℕ)) := by
      rw [hV t]; rfl
    have hVu : V u ω = PartialMatching.maxCardValue
        (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦
          cost ω (i : ℕ) (j : ℕ) + u * probe ω (i : ℕ) (j : ℕ)) := by
      rw [hV u]; rfl
    have hVm : V (a * t + b * u) ω = PartialMatching.maxCardValue
        (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦
          cost ω (i : ℕ) (j : ℕ) + (a * t + b * u) * probe ω (i : ℕ) (j : ℕ)) := by
      rw [hV (a * t + b * u)]; rfl
    rw [hVt, hVu, hVm]
    simpa only [smul_eq_mul] using hconc
  have hle := integral_mono hcomb (hInt (a * t + b * u)) hpt
  have hsplit : ∫ ω, (a * V t ω + b * V u ω) ∂P =
      a * (∫ ω, V t ω ∂P) + b * (∫ ω, V u ω ∂P) := by
    rw [integral_add ((hInt t).const_mul a) ((hInt u).const_mul b),
      integral_const_mul, integral_const_mul]
  rw [hsplit] at hle
  simpa only [smul_eq_mul] using hle

/-- The expected pressure is Lipschitz in the tilt with the uniform probe bound. -/
theorem abs_integral_tiltedCloudValue_sub_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cost probe : (ω : Ω) → ℕ → ℕ → ℝ) (Np Nm : Ω → ℕ)
    (V : ℝ → Ω → ℝ)
    (hV : ∀ t, V t = fun ω ↦ tiltedCloudValue cost probe t ω (Np ω) (Nm ω))
    {G : ℝ} (hG : 0 ≤ G) (hprobe : ∀ ω i j, |probe ω i j| ≤ G)
    (hInt : ∀ t, Integrable (V t) P)
    (hcard : Integrable (fun ω ↦ ((min (Np ω) (Nm ω) : ℕ) : ℝ)) P) (t u : ℝ) :
    |(∫ ω, V t ω ∂P) - ∫ ω, V u ω ∂P| ≤
      (∫ ω, ((min (Np ω) (Nm ω) : ℕ) : ℝ) ∂P) * (G * |t - u|) := by
  have hdiff : Integrable (fun ω ↦ V t ω - V u ω) P := (hInt t).sub (hInt u)
  have hpt : ∀ ω, |V t ω - V u ω| ≤
      ((min (Np ω) (Nm ω) : ℕ) : ℝ) * (G * |t - u|) := by
    intro ω
    have h := PartialMatching.abs_maxCardValue_perturbed_sub_le
      (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦ cost ω (i : ℕ) (j : ℕ))
      (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦ probe ω (i : ℕ) (j : ℕ))
      (G := G) (fun i j ↦ hprobe ω (i : ℕ) (j : ℕ)) hG (t := t) (u := u)
    have hVt : V t ω = PartialMatching.maxCardValue
        (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦
          cost ω (i : ℕ) (j : ℕ) + t * probe ω (i : ℕ) (j : ℕ)) := by
      rw [hV t]; rfl
    have hVu : V u ω = PartialMatching.maxCardValue
        (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦
          cost ω (i : ℕ) (j : ℕ) + u * probe ω (i : ℕ) (j : ℕ)) := by
      rw [hV u]; rfl
    rw [hVt, hVu]
    calc |PartialMatching.maxCardValue (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦
          cost ω (i : ℕ) (j : ℕ) + t * probe ω (i : ℕ) (j : ℕ)) -
        PartialMatching.maxCardValue (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦
          cost ω (i : ℕ) (j : ℕ) + u * probe ω (i : ℕ) (j : ℕ))|
        ≤ |t - u| * ((min (Np ω) (Nm ω) : ℕ) : ℝ) * G := h
      _ = ((min (Np ω) (Nm ω) : ℕ) : ℝ) * (G * |t - u|) := by ring
  calc |(∫ ω, V t ω ∂P) - ∫ ω, V u ω ∂P|
      = |∫ ω, (V t ω - V u ω) ∂P| := by rw [integral_sub (hInt t) (hInt u)]
    _ ≤ ∫ ω, |V t ω - V u ω| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, ((min (Np ω) (Nm ω) : ℕ) : ℝ) * (G * |t - u|) ∂P :=
        integral_mono hdiff.abs (hcard.mul_const _) hpt
    _ = (∫ ω, ((min (Np ω) (Nm ω) : ℕ) : ℝ) ∂P) * (G * |t - u|) :=
        integral_mul_const _ _

/-- Uniform boundedness of the expected pressure by the expected maximum
cardinality times the largest edge cost. -/
theorem abs_integral_tiltedCloudValue_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cost probe : (ω : Ω) → ℕ → ℕ → ℝ) (Np Nm : Ω → ℕ)
    (V : ℝ → Ω → ℝ)
    (hV : ∀ t, V t = fun ω ↦ tiltedCloudValue cost probe t ω (Np ω) (Nm ω))
    {Bc G t : ℝ} (hBc0 : 0 ≤ Bc) (hG0 : 0 ≤ G)
    (hcost : ∀ ω i j, |cost ω i j| ≤ Bc) (hprobe : ∀ ω i j, |probe ω i j| ≤ G)
    (hInt : ∀ t, Integrable (V t) P)
    (hcard : Integrable (fun ω ↦ ((min (Np ω) (Nm ω) : ℕ) : ℝ)) P) :
    |∫ ω, V t ω ∂P| ≤
      (∫ ω, ((min (Np ω) (Nm ω) : ℕ) : ℝ) ∂P) * (Bc + |t| * G) := by
  have hpt : ∀ ω, |V t ω| ≤ ((min (Np ω) (Nm ω) : ℕ) : ℝ) * (Bc + |t| * G) := by
    intro ω
    have h := PartialMatching.abs_maxCardValue_perturbed_le
      (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦ cost ω (i : ℕ) (j : ℕ))
      (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦ probe ω (i : ℕ) (j : ℕ))
      (Bc := Bc) (G := G) (fun i j ↦ hcost ω (i : ℕ) (j : ℕ)) hBc0
      (fun i j ↦ hprobe ω (i : ℕ) (j : ℕ)) hG0 (t := t)
    have hVt : V t ω = PartialMatching.maxCardValue
        (fun i : Fin (Np ω) ↦ fun j : Fin (Nm ω) ↦
          cost ω (i : ℕ) (j : ℕ) + t * probe ω (i : ℕ) (j : ℕ)) := by
      rw [hV t]; rfl
    rw [hVt]
    exact h
  calc |∫ ω, V t ω ∂P| ≤ ∫ ω, |V t ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, ((min (Np ω) (Nm ω) : ℕ) : ℝ) * (Bc + |t| * G) ∂P :=
        integral_mono (hInt t).abs (hcard.mul_const _) hpt
    _ = (∫ ω, ((min (Np ω) (Nm ω) : ℕ) : ℝ) ∂P) * (Bc + |t| * G) :=
        integral_mul_const _ _

end OTSelector.Probability
