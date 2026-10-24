import OTSelector.Finite.LegalMatchingValue
import OTSelector.Finite.MaxCardValueAssignment
import OTSelector.Geometry.Finsler.DistanceLocalizationSupportBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Completing a legal partial optimum in the original physical problem

The legal graph can leave vertices unmatched. Its actual maximum-cardinality
optimum is extended in the full physical graph, paying the original cost bound
only for the true missing cardinality. The added physical edges need not obey
the local clock graph. No distribution is assigned to the selected orphans.
-/

open Set Function Matrix MeasureTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction.PartialMatching

variable {m n : ℕ}

/-- Complete an actual legal optimum and compare to a physical cost. Only
legal edges require a model comparison; the true physical bound pays for the
remaining vertices. Signed tilted costs are allowed. -/
theorem maxCardValue_le_legalMaximumValue_add_missing
    (allowed : Finset (Fin m × Fin n)) (c d : Fin m → Fin n → ℝ)
    (α error B : ℝ) (hlegal : ∀ i j, (i, j) ∈ allowed → c i j ≤ α * d i j + error)
    (hB : ∀ i j, c i j ≤ B) :
    OTSelector.PartialMatching.maxCardValue c ≤
      α * legalMaximumValue allowed d + (legalMaximumCard allowed : ℝ) * error +
        ((min m n - legalMaximumCard allowed : ℕ) : ℝ) * B := by
  obtain ⟨σ, hσlegal, hσcard, hσcost⟩ := exists_cost_eq_legalMaximumValue allowed d
  have hc : σ.cost c ≤ α * σ.cost d + (σ.card : ℝ) * error := by
    calc
      σ.cost c ≤ ∑ e ∈ σ.edges, (α * d e.1 e.2 + error) :=
        Finset.sum_le_sum fun e he ↦ hlegal e.1 e.2 (hσlegal he)
      _ = α * σ.cost d + (σ.card : ℝ) * error := by
        simp only [OTSelector.PartialMatching.cost, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, OTSelector.PartialMatching.card]
  obtain ⟨τ, hτcard, hτcost⟩ :=
    OTSelector.PartialMatching.exists_maxCardinality_cost_le c σ hB
  calc
    OTSelector.PartialMatching.maxCardValue c ≤ τ.cost c :=
      OTSelector.PartialMatching.maxCardValue_le_of_card c hτcard
    _ ≤ σ.cost c + ((min m n - σ.card : ℕ) : ℝ) * B := hτcost
    _ ≤ α * σ.cost d + (σ.card : ℝ) * error +
        ((min m n - σ.card : ℕ) : ℝ) * B := add_le_add hc le_rfl
    _ = _ := by rw [hσcard, hσcost]

/-- The original full assignment is bounded by its legal maximum-cardinality
minimum plus the physical cost of exactly the missing vertices. -/
theorem assignmentValue_le_legalMaximumValue_add_missing
    (allowed : Finset (Fin n × Fin n)) (c g : Fin n → Fin n → ℝ) (t B : ℝ)
    (hB : ∀ i j, perturbedEdgeCost c g t i j ≤ B) :
    perturbedAssignmentValue c g t ≤
      legalMaximumValue allowed (perturbedEdgeCost c g t) +
        ((n - legalMaximumCard allowed : ℕ) : ℝ) * B := by
  have h := maxCardValue_le_legalMaximumValue_add_missing allowed
    (perturbedEdgeCost c g t) (perturbedEdgeCost c g t) 1 0 B
    (fun i j _ ↦ by simp) hB
  simpa only [OTSelector.PartialMatching.maxCardValue_eq_perturbedAssignmentValue,
    one_mul, mul_zero, add_zero, min_self] using h

/-- Normalize the physical completion error by the original sample size. -/
theorem normalized_assignmentValue_le_legalMaximumValue_add_missing
    (allowed : Finset (Fin n × Fin n)) (c g : Fin n → Fin n → ℝ) (t B : ℝ)
    (hB : ∀ i j, perturbedEdgeCost c g t i j ≤ B) :
    perturbedAssignmentValue c g t / (n : ℝ) ≤
      legalMaximumValue allowed (perturbedEdgeCost c g t) / (n : ℝ) +
        ((n - legalMaximumCard allowed : ℕ) : ℝ) * B / (n : ℝ) := by
  simpa only [add_div] using div_le_div_of_nonneg_right
    (assignmentValue_le_legalMaximumValue_add_missing allowed c g t B hB)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

end OTSelector.Reconstruction.PartialMatching

namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Measurable finite legal graphs and almost-sure physical edge bounds give
integrable legal minima at their actual maximum cardinalities. -/
theorem integrable_legalMaximumValue_of_ae_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {m n : ℕ}
    (allowed : Ω → Finset (Fin m × Fin n))
    (hallowed : ∀ S, MeasurableSet {ξ | allowed ξ = S})
    (c : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, |c ξ i j| ≤ B) :
    Integrable (fun ξ ↦ PartialMatching.legalMaximumValue (allowed ξ) (c ξ)) P := by
  apply Integrable.of_bound
    (PartialMatching.measurable_legalMaximumValue allowed hallowed c hc).aestronglyMeasurable
    ((min m n : ℕ) * B)
  filter_upwards [hbound] with ξ hξ
  simpa only [Real.norm_eq_abs] using
    PartialMatching.abs_legalMaximumValue_le_min (allowed ξ) (c ξ) hB hξ

/-- The same integrability producer covers the full original tilted assignment. -/
theorem integrable_assignmentValue_of_ae_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {n : ℕ}
    (c g : Ω → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, |perturbedEdgeCost (c ξ) (g ξ) t i j| ≤ B) :
    Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t) P := by
  have h := integrable_legalMaximumValue_of_ae_bound P
    (fun _ ↦ (Finset.univ : Finset (Fin n × Fin n)))
    (fun S ↦ by by_cases hS : (Finset.univ : Finset (Fin n × Fin n)) = S <;> simp [hS])
    (fun ξ ↦ perturbedEdgeCost (c ξ) (g ξ) t)
    (fun i j ↦ (hc i j).add ((hg i j).const_mul t)) hB hbound
  have heq : (fun ξ ↦ PartialMatching.legalMaximumValue Finset.univ
      (perturbedEdgeCost (c ξ) (g ξ) t)) =
      (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t) := by
    funext ξ
    rw [PartialMatching.legalMaximumValue_univ,
      OTSelector.PartialMatching.maxCardValue_eq_perturbedAssignmentValue]
  rw [heq] at h
  exact h

/-- The expected physical completion error uses the actual legal cardinality
deficit. In particular it does not require a law for adaptively unmatched points. -/
theorem integral_assignmentValue_le_legalMaximumValue_add_missing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (allowed : Ω → Finset (Fin n × Fin n))
    (c g : Ω → Matrix (Fin n) (Fin n) ℝ) (t B : ℝ)
    (hB : ∀ᵐ ξ ∂P, ∀ i j, perturbedEdgeCost (c ξ) (g ξ) t i j ≤ B)
    (hphysical : Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t) P)
    (hlegal : Integrable
      (fun ξ ↦ PartialMatching.legalMaximumValue (allowed ξ)
        (perturbedEdgeCost (c ξ) (g ξ) t)) P)
    (hmissing : Integrable
      (fun ξ ↦ ((n - PartialMatching.legalMaximumCard (allowed ξ) : ℕ) : ℝ)) P) :
    (∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t ∂P) / (n : ℝ) ≤
      (∫ ξ, PartialMatching.legalMaximumValue (allowed ξ)
        (perturbedEdgeCost (c ξ) (g ξ) t) ∂P) / (n : ℝ) +
      (∫ ξ, ((n - PartialMatching.legalMaximumCard (allowed ξ) : ℕ) : ℝ) ∂P) *
        B / (n : ℝ) := by
  have hpoint : ∀ᵐ ξ ∂P, perturbedAssignmentValue (c ξ) (g ξ) t ≤
      PartialMatching.legalMaximumValue (allowed ξ) (perturbedEdgeCost (c ξ) (g ξ) t) +
        ((n - PartialMatching.legalMaximumCard (allowed ξ) : ℕ) : ℝ) * B := by
    filter_upwards [hB] with ξ hξ
    exact PartialMatching.assignmentValue_le_legalMaximumValue_add_missing
      (allowed ξ) (c ξ) (g ξ) t B hξ
  have h := integral_mono_ae hphysical (hlegal.add (hmissing.mul_const B)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hlegal (hmissing.mul_const B), integral_mul_const] at h
  simpa only [add_div] using div_le_div_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

/-- An actual square-root count-discrepancy estimate controls the entire
expected physical repair cost with the original sample-size normalization. -/
theorem integral_assignmentValue_le_legalMaximumValue_add_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (allowed : Ω → Finset (Fin n × Fin n))
    (c g : Ω → Matrix (Fin n) (Fin n) ℝ) (t B C : ℝ) (hBnonneg : 0 ≤ B)
    (hB : ∀ᵐ ξ ∂P, ∀ i j, perturbedEdgeCost (c ξ) (g ξ) t i j ≤ B)
    (hphysical : Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t) P)
    (hlegal : Integrable
      (fun ξ ↦ PartialMatching.legalMaximumValue (allowed ξ)
        (perturbedEdgeCost (c ξ) (g ξ) t)) P)
    (hmissing : Integrable
      (fun ξ ↦ ((n - PartialMatching.legalMaximumCard (allowed ξ) : ℕ) : ℝ)) P)
    (hcount : (∫ ξ, ((n - PartialMatching.legalMaximumCard (allowed ξ) : ℕ) : ℝ) ∂P) ≤
      C * Real.sqrt (n : ℝ)) :
    (∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t ∂P) / (n : ℝ) ≤
      (∫ ξ, PartialMatching.legalMaximumValue (allowed ξ)
        (perturbedEdgeCost (c ξ) (g ξ) t) ∂P) / (n : ℝ) +
      C * B * Real.sqrt (n : ℝ) / (n : ℝ) := by
  apply (integral_assignmentValue_le_legalMaximumValue_add_missing
    P allowed c g t B hB hphysical hlegal hmissing).trans
  apply add_le_add le_rfl
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcount hBnonneg) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Compact original Finsler carriers supply the physical completion constant
uniformly in every graph, sample, tilt and bounded probe. -/
theorem exists_finsler_legal_assignment_repair_bound
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) {u : M → ℝ}
    (hu : let _instPhysicalRepairMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    ∃ D > 0, ∀ (n : ℕ) (X Y : Fin n → M),
      (∀ i, X i ∈ A) → (∀ j, Y j ∈ B) →
      ∀ (allowed : Finset (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℝ)
        (G : ℝ≥0), (∀ i j, |g i j| ≤ G) →
        ∀ scale t : ℝ, 0 ≤ scale →
          perturbedAssignmentValue
              (fun i j ↦ scale *
                ((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i))) g t /
              (n : ℝ) ≤
            PartialMatching.legalMaximumValue allowed (fun i j ↦ scale *
              ((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)) + t * g i j) /
              (n : ℝ) +
            ((n - PartialMatching.legalMaximumCard allowed : ℕ) : ℝ) *
              (scale * D + |t| * (G : ℝ)) / (n : ℝ) := by
  obtain ⟨D, hD, hbound⟩ := F.exists_uniform_compact_distance_slack_bound hA hB hu
  refine ⟨D, hD, ?_⟩
  intro n X Y hXA hYB allowed g G hg scale t hscale
  apply PartialMatching.normalized_assignmentValue_le_legalMaximumValue_add_missing
  intro i j
  have hc := mul_le_mul_of_nonneg_left (hbound (X i) (hXA i) (Y j) (hYB j)).2 hscale
  have hp : t * g i j ≤ |t| * (G : ℝ) :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg t))
  exact add_le_add hc hp

end OTSelector.Reconstruction
