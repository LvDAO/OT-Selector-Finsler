import OTSelector.Probability.CavitySemidiscreteTiltConcavity
import OTSelector.Analysis.Convex.ConcaveSecantBounds

/-!
# Supergradients of the tilted semidiscrete value

At a fixed Dirichlet mass vector and a fixed cost environment, a tuple that is
optimal for the tilted cost `c + t g` gives the probe cost `q = cost_g(a)` as a
supergradient of the value function at `t`:

`V(s) ≤ V(t) + (s - t) q` for every real `s`.

The proof is the affine tilt identity plus feasibility of `a` at every other
tilt.  Applying the abstract secant bounds of `ConcaveSecantBounds` then yields
the paper's four bracketing inequalities, which are the finite-level input of
`hasDerivAt_of_concave_supergradient_sequence`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S : Type*} [MeasurableSpace S] {m : ℕ}

/-- **Tilted optima are supergradients.**  If `a` is optimal for the cost
`c + t g` at the mass vector `p`, then the probe cost of `a` is a supergradient
of the tilted value at `t`. -/
theorem semidiscreteValue_supergradient_of_tilted_optimal
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c g : S → Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    {p : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    {t : ℝ}
    (hopt : ∀ b, IsSemidiscreteAllocation μ p b →
      semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) a ≤
        semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) b) :
    ∀ s : ℝ,
      semidiscreteValue μ (fun x j ↦ c x j + s * g x j) p ≤
        semidiscreteValue μ (fun x j ↦ c x j + t * g x j) p +
          (s - t) * semidiscreteAllocationCost μ g a := by
  intro s
  have hct : ∀ j, Integrable (fun x ↦ c x j + t * g x j) μ :=
    fun j ↦ (hc j).add ((hg j).const_mul t)
  have hcs : ∀ j, Integrable (fun x ↦ c x j + s * g x j) μ :=
    fun j ↦ (hc j).add ((hg j).const_mul s)
  have hVt : semidiscreteValue μ (fun x j ↦ c x j + t * g x j) p =
      semidiscreteAllocationCost μ (fun x j ↦ c x j + t * g x j) a :=
    semidiscreteValue_eq_cost_of_optimal μ _ hct p a ha hopt
  have hle := semidiscreteValue_le_cost μ (fun x j ↦ c x j + s * g x j) hcs p a ha
  have haffs := semidiscreteAllocationCost_tilt_affine μ c g a ha hc hg s
  have hafft := semidiscreteAllocationCost_tilt_affine μ c g a ha hc hg t
  rw [hVt, hafft]
  rw [haffs] at hle
  linarith

/-- The four finite-level bracketing inequalities around a positive tilt `t`,
as consumed by `hasDerivAt_of_concave_supergradient_sequence`.  The right
supergradient `qpos` is bracketed by the interval slope over `[t, 2t]` and the
right secant slope at `t`; the left supergradient `qneg` by the left secant
slope at `t` and the interval slope over `[-2t, -t]`. -/
theorem semidiscrete_tilt_brackets
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c g : S → Fin (m + 1) → ℝ) (apos aneg : S → Fin (m + 1) → ℝ)
    {p : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p apos)
    (ha' : IsSemidiscreteAllocation μ p aneg)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    {t : ℝ} (ht : 0 < t)
    (hoptpos : ∀ b, IsSemidiscreteAllocation μ p b →
      semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) apos ≤
        semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) b)
    (hoptneg : ∀ b, IsSemidiscreteAllocation μ p b →
      semidiscreteAllocationCost μ (fun s j ↦ c s j + (-t) * g s j) aneg ≤
        semidiscreteAllocationCost μ (fun s j ↦ c s j + (-t) * g s j) b) :
    (semidiscreteValue μ (fun x j ↦ c x j + (2 * t) * g x j) p -
        semidiscreteValue μ (fun x j ↦ c x j + t * g x j) p) / t ≤
      semidiscreteAllocationCost μ g apos ∧
    semidiscreteAllocationCost μ g apos ≤
      (semidiscreteValue μ (fun x j ↦ c x j + t * g x j) p -
        semidiscreteValue μ (fun x j ↦ c x j) p) / t ∧
    (semidiscreteValue μ (fun x j ↦ c x j) p -
        semidiscreteValue μ (fun x j ↦ c x j + (-t) * g x j) p) / t ≤
      semidiscreteAllocationCost μ g aneg ∧
    semidiscreteAllocationCost μ g aneg ≤
      (semidiscreteValue μ (fun x j ↦ c x j + (-t) * g x j) p -
        semidiscreteValue μ (fun x j ↦ c x j + (-(2 * t)) * g x j) p) / t := by
  have hsupPos := semidiscreteValue_supergradient_of_tilted_optimal
    μ c g apos ha hc hg hoptpos
  have hsupNeg := semidiscreteValue_supergradient_of_tilted_optimal
    μ c g aneg ha' hc hg hoptneg
  have hsupPos' : ∀ s : ℝ,
      semidiscreteValue μ (fun x j ↦ c x j + s * g x j) p ≤
        semidiscreteValue μ (fun x j ↦ c x j + t * g x j) p +
          semidiscreteAllocationCost μ g apos * (s - t) :=
    fun s => by simpa only [mul_comm] using hsupPos s
  have hsupNeg' : ∀ s : ℝ,
      semidiscreteValue μ (fun x j ↦ c x j + s * g x j) p ≤
        semidiscreteValue μ (fun x j ↦ c x j + (-t) * g x j) p +
          semidiscreteAllocationCost μ g aneg * (s + t) :=
    fun s => by simpa only [mul_comm, sub_neg_eq_add] using hsupNeg s
  have hpos := intervalSlope_le_of_supergradient_pos (p := fun s ↦
      semidiscreteValue μ (fun x j ↦ c x j + s * g x j) p)
    (q := semidiscreteAllocationCost μ g apos) (t := t) ht hsupPos'
  have hneg := leftSlope_le_of_supergradient_neg (p := fun s ↦
      semidiscreteValue μ (fun x j ↦ c x j + s * g x j) p)
    (q := semidiscreteAllocationCost μ g aneg) (t := t) ht hsupNeg'
  refine ⟨hpos.1, ?_, ?_, ?_⟩
  · simpa only [zero_mul, add_zero] using hpos.2
  · simpa only [zero_mul, add_zero] using hneg.1
  · simpa only [sub_neg_eq_add] using hneg.2

end OTSelector.Probability
