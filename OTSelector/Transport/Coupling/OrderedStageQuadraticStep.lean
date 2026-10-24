import OTSelector.Transport.Coupling.FiniteStagePotential
import OTSelector.Transport.Coupling.OrderedStageChain
import OTSelector.Transport.Coupling.WeightedQuadraticGluing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingOrderedQuadraticStep.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingOrderedQuadraticStep`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseStageCouplingOrderedQuadraticStep

**Conditions:** An actual ordered stage-step witness has finite segment measures and integrable original quadratic costs; the explicit positive stage index and total length parameters are retained.

**Objects:** Joint/active/completed quadratic energy and the exact weighted prefix invariant.

**Proof detail:** Use RN component domination for integrability, transfer the continuing joint marginals, apply the unequal-weight two-segment bound, and rearrange with weight N/n so the next-step energy coefficient telescopes.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185), Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4); [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf), Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini); [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48; [OTSelector project, Original classwise stage Neumann construction](main.tex#eq:interleaved-path-stage-neumann), main.tex label eq:interleaved-path-stage-neumann, line 10809.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Actual quadratic integrability and energy bookkeeping for an ordered step. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 600000
variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- An ordered step's actual endpoint, fresh, and split plans carry finite
quadratic costs. The displayed equalities retain the exact two stage energies. -/
theorem FiniteOrderedStageStep.quadratic_energy
    {ν S T : ℕ → Measure E} {n : ℕ}
    {w : FiniteOrderedStagePrefix ν S T n} {π : Measure (E × E)}
    (v : FiniteOrderedStageStep ν S T n w π)
    (hactive : Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) w.active)
    (hcompleted : Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) w.completed)
    (hπ : Integrable (fun p ↦ dist p.1 p.2 ^ 2) π)
    {k : ℝ} (hk : 0 < k) :
    Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) v.nextActive ∧
    Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) v.exits ∧
    Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) v.toPrefix.completed ∧
    (∫ p, dist p.1.2 p.2.2 ^ 2 ∂v.toPrefix.completed) =
      (∫ p, dist p.1.2 p.2.2 ^ 2 ∂w.completed) +
        (∫ p, dist p.1.2 p.2 ^ 2 ∂v.exits) ∧
    (∫ p, dist p.1.2 p.2 ^ 2 ∂v.nextActive) +
        (∫ p, dist p.1.2 p.2 ^ 2 ∂v.exits) =
      (∫ p, dist p.1.1.2 p.2 ^ 2 ∂v.triple) +
        (∫ p, dist p.1 p.2 ^ 2 ∂v.birth) ∧
    (∫ p, dist p.1.1.2 p.2 ^ 2 ∂v.triple) ≤
      (k + 1) / k * (∫ p, dist p.1.2 p.2 ^ 2 ∂w.active) +
        (k + 1) * (∫ p, dist p.1 p.2 ^ 2 ∂v.continuing) ∧
    (∫ p, dist p.1 p.2 ^ 2 ∂v.continuing) +
        (∫ p, dist p.1 p.2 ^ 2 ∂v.birth) = ∫ p, dist p.1 p.2 ^ 2 ∂π := by
  have hcle : v.continuing ≤ π :=
    (Measure.le_add_right le_rfl : v.continuing ≤ v.continuing + v.birth).trans_eq v.source_decomp
  have hble : v.birth ≤ π :=
    (Measure.le_add_left le_rfl : v.birth ≤ v.continuing + v.birth).trans_eq v.source_decomp
  have hc := hπ.mono_measure hcle
  have hb := hπ.mono_measure hble
  obtain ⟨hθ, hweighted⟩ := finiteStageJoint_quadratic_weighted_le
    Prod.snd id id measurable_snd measurable_id measurable_id w.active v.continuing
    v.triple v.triple_first v.triple_second hactive hc hk
  let δ := v.triple.map (fun z ↦ (z.1.1, z.2))
  let fresh := v.birth.map (fun z ↦ ((n, z.1), z.2))
  let exit := v.exits.map (fun z ↦ (z.1, (n, z.2)))
  have hδmap : Measurable (fun z : ((ℕ × E) × E) × E ↦ (z.1.1, z.2)) := by fun_prop
  have hfreshmap : Measurable (fun z : E × E ↦ ((n, z.1), z.2)) := by fun_prop
  have hexitmap : Measurable (fun z : (ℕ × E) × E ↦ (z.1, (n, z.2))) := by fun_prop
  have hcost : Measurable (fun p : (ℕ × E) × E ↦ dist p.1.2 p.2 ^ 2) := by fun_prop
  have hcostC : Measurable (fun p : (ℕ × E) × (ℕ × E) ↦ dist p.1.2 p.2.2 ^ 2) := by fun_prop
  have hδ : Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) δ :=
    (integrable_map_measure hcost.aestronglyMeasurable hδmap.aemeasurable).mpr hθ
  have hfresh : Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) fresh :=
    (integrable_map_measure hcost.aestronglyMeasurable hfreshmap.aemeasurable).mpr hb
  have hincoming : Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) (v.nextActive + v.exits) := by
    rw [v.target_decomp]
    exact integrable_add_measure.mpr ⟨hδ, hfresh⟩
  obtain ⟨hnext, hexit⟩ := integrable_add_measure.mp hincoming
  have hexittag : Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) exit :=
    (integrable_map_measure hcostC.aestronglyMeasurable hexitmap.aemeasurable).mpr hexit
  have hnew : v.toPrefix.completed = w.completed + exit := rfl
  refine ⟨hnext, hexit, ?_, ?_, ?_, hweighted, ?_⟩
  · rw [hnew]
    exact integrable_add_measure.mpr ⟨hcompleted, hexittag⟩
  · rw [hnew, integral_add_measure hcompleted hexittag]
    congr 1
    exact integral_map hexitmap.aemeasurable hcostC.aestronglyMeasurable
  · rw [← integral_add_measure hnext hexit, v.target_decomp,
      integral_add_measure hδ hfresh]
    congr 1
    · exact integral_map hδmap.aemeasurable hcost.aestronglyMeasurable
    · exact integral_map hfreshmap.aemeasurable hcost.aestronglyMeasurable
  · rw [← integral_add_measure hc hb, v.source_decomp]

/-- The actual ordered step propagates the linear-length quadratic potential;
all split energies come from its genuine plans and exact marginal construction. -/
theorem FiniteOrderedStageStep.quadratic_prefix_le
    {ν S T : ℕ → Measure E} {n : ℕ}
    {w : FiniteOrderedStagePrefix ν S T n} {π : Measure (E × E)}
    (v : FiniteOrderedStageStep ν S T n w π) (N : ℕ)
    (hn : 0 < n) (hN : n + 1 ≤ N)
    (hactive : Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) w.active)
    (hcompleted : Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) w.completed)
    (hπ : Integrable (fun p ↦ dist p.1 p.2 ^ 2) π) :
    Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) v.toPrefix.active ∧
    Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) v.toPrefix.completed ∧
    (∫ p, dist p.1.2 p.2.2 ^ 2 ∂v.toPrefix.completed) +
        (N : ℝ) / (n + 1 : ℕ) * (∫ p, dist p.1.2 p.2 ^ 2 ∂v.toPrefix.active) ≤
      (∫ p, dist p.1.2 p.2.2 ^ 2 ∂w.completed) +
        (N : ℝ) / n * (∫ p, dist p.1.2 p.2 ^ 2 ∂w.active) +
        (N : ℝ) * (∫ p, dist p.1 p.2 ^ 2 ∂π) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (n : ℝ) + 1 ≤ N := by exact_mod_cast hN
  obtain ⟨hnext, hexit, hcomp, hcompE, hsplit, hweighted, hstage⟩ :=
    v.quadratic_energy hactive hcompleted hπ hnR
  refine ⟨hnext, hcomp, ?_⟩
  have h := finiteStage_quadratic_prefix_potential_le
    (G := ∫ p, dist p.1.2 p.2.2 ^ 2 ∂w.completed) hnR hNR
    (integral_nonneg fun _ ↦ sq_nonneg _)
    (integral_nonneg fun _ ↦ sq_nonneg _) hweighted hsplit
  rw [hstage] at h
  have hactive_eq : v.toPrefix.active = v.nextActive := rfl
  simpa only [hcompE, hactive_eq, Nat.cast_add, Nat.cast_one] using h

/-- At the first genuine stage, the empty active law eliminates the joint.
The exact split energy supplies the base of the linear-length bound. -/
theorem FiniteOrderedStageStep.quadratic_prefix_zero_le
    {ν S T : ℕ → Measure E}
    {w : FiniteOrderedStagePrefix ν S T 0} {π : Measure (E × E)}
    (v : FiniteOrderedStageStep ν S T 0 w π) (N : ℕ) (hN : 1 ≤ N)
    (hν₀ : ν 0 = 0)
    (hπ : Integrable (fun p ↦ dist p.1 p.2 ^ 2) π) :
    Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) v.toPrefix.active ∧
    Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) v.toPrefix.completed ∧
    (∫ p, dist p.1.2 p.2.2 ^ 2 ∂v.toPrefix.completed) +
        (N : ℝ) * (∫ p, dist p.1.2 p.2 ^ 2 ∂v.toPrefix.active) ≤
      (N : ℝ) * (∫ p, dist p.1 p.2 ^ 2 ∂π) := by
  have hA : w.active = 0 := by
    apply (Measure.map_eq_zero_iff measurable_snd.aemeasurable).mp
    exact w.active_target.trans hν₀
  have hG : w.completed = 0 := by
    apply (Measure.map_eq_zero_iff measurable_fst.aemeasurable).mp
    simpa only [Measure.fst, hA, Measure.map_zero, add_zero,
      finiteStageLabelledPrefix_zero] using w.source_balance
  have hθ : v.triple = 0 := by
    apply (Measure.map_eq_zero_iff measurable_fst.aemeasurable).mp
    exact v.triple_first.trans hA
  have hc : v.continuing = 0 := by
    rw [← v.triple_second, hθ, Measure.map_zero]
  have hactive : Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) w.active := by simp [hA]
  have hcompleted : Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) w.completed := by simp [hG]
  obtain ⟨hnext, hexit, hcomp, hcompE, hsplit, _, hstage⟩ :=
    v.quadratic_energy hactive hcompleted hπ (show (0 : ℝ) < 1 by norm_num)
  simp only [hθ, integral_zero_measure, zero_add] at hsplit
  simp only [hc, integral_zero_measure, zero_add] at hstage
  simp only [hG, integral_zero_measure, zero_add] at hcompE
  have hX : 0 ≤ ∫ p, dist p.1.2 p.2 ^ 2 ∂v.exits := integral_nonneg fun _ ↦ sq_nonneg _
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨hnext, hcomp, ?_⟩
  rw [hcompE]
  change (∫ p, dist p.1.2 p.2 ^ 2 ∂v.exits) +
    (N : ℝ) * (∫ p, dist p.1.2 p.2 ^ 2 ∂v.nextActive) ≤ _
  rw [← hstage, ← hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hNR hX]

end OTSelector.Reconstruction

end
end
