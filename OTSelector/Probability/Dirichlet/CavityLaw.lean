import OTSelector.Probability.Dirichlet.CavityExchangeability
import OTSelector.Probability.Dirichlet.CavitySuccess
import OTSelector.Probability.DirichletLawIdentification
import OTSelector.Probability.DirichletReference
import OTSelector.Transport.Semidiscrete.CavityCells

/-!
Conditions: A probability source law, measurable finite target costs and atomless pairwise cost-difference laws; the simpler conversion/measurability helpers require only a finite source measure.

Objects: Exact factorial mixed moments, a measurable actual cavity-mass vector in the simplex and equality of its pushforward law with the constructed Dirichlet(1,…,1) reference law.

Proof detail: Solve the successful-subset normalization for every natural mixed moment, convert finite ENNReal masses to real coordinates and show the cells partition the probability source. Compact-simplex polynomial moment determination identifies the law.

References: OTSelector project: main.tex label thm:iid-cavity-dirichlet, line 4290; Thomas P. Minka: Section 1, equations (1)–(3), p. 1; equations (19)–(20), p. 2.
Relation: The reference Dirichlet formulas are classical. Their identification with the actual cavity mass vector is the project theorem and follows from its own combinatorial normalization, not from a textbook assumption that cavity masses are Dirichlet.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityDirichletLaw.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityDirichletLaw`; the selected original proof blocks follow. -/
section

/-!
# The actual iid cavity cell mass law

The constructed successful-subset identity gives the factorial mixed moments of the
actual cavity cells. Their masses form a measurable simplex vector, so compact moment
determinacy identifies its law with the explicit standard Dirichlet probability.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Actual iid cavity masses have the explicit factorial mixed moments. -/
theorem lintegral_iid_cavityCellMass_nat_powers
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (r : Fin (m + 1) → ℕ) :
    (∫⁻ w, ∏ j, cavityCellMass μ (iidCapacityInputCost c (fun k w ↦ w k))
      (fun z j ↦ c j z.2) 0 j w ^ r j ∂Measure.pi (fun _ : Fin m ↦ μ)) =
      ENNReal.ofReal ((m.factorial : ℝ) * (∏ j, (r j).factorial : ℝ) /
        (m + ∑ j, r j).factorial) := by
  classical
  have hnorm := iid_cavity_mixed_moment_normalization μ c hc hatom r
  have hnat : ((m + ∑ j, r j).choose m * Nat.multinomial Finset.univ r) *
      (m.factorial * ∏ j, (r j).factorial) = (m + ∑ j, r j).factorial := by
    calc
      _ = (m + ∑ j, r j).choose m * m.factorial *
          ((∏ j, (r j).factorial) * Nat.multinomial Finset.univ r) := by ring
      _ = (m + ∑ j, r j).choose m * m.factorial * (∑ j, r j).factorial := by
        rw [Nat.multinomial_spec]
      _ = _ := by
        simpa only [Nat.add_sub_cancel_left] using
          Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m (∑ j, r j))
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ Nat.cast_nonneg ((r j).factorial))]
  simp only [ENNReal.ofReal_natCast]
  apply (ENNReal.eq_div_iff (by positivity) (by simp)).mpr
  have hcast :
      (((m + ∑ j, r j).choose m : ℝ≥0∞) * Nat.multinomial Finset.univ r) *
        ((m.factorial : ℝ≥0∞) * ∏ j, ((r j).factorial : ℝ≥0∞)) =
        (m + ∑ j, r j).factorial := by exact_mod_cast hnat
  rw [← hcast]
  calc
    _ = ((m.factorial : ℝ≥0∞) * ∏ j, ((r j).factorial : ℝ≥0∞)) *
        (((m + ∑ j, r j).choose m : ℝ≥0∞) * Nat.multinomial Finset.univ r *
          (∫⁻ w, ∏ j, cavityCellMass μ (iidCapacityInputCost c (fun k w ↦ w k))
            (fun z j ↦ c j z.2) 0 j w ^ r j ∂Measure.pi (fun _ : Fin m ↦ μ))) := by ring
    _ = _ := by rw [hnorm, mul_one]

/-- The real-valued vector of actual cell probabilities for the retained iid cloud. -/
def iidCavityMassVector (μ : Measure S) (c : Fin (m + 1) → S → ℝ)
    (w : Fin m → S) (j : Fin (m + 1)) : ℝ :=
  (cavityCellMass μ (iidCapacityInputCost c (fun k w ↦ w k))
    (fun z j ↦ c j z.2) 0 j w).toReal

/-- Real cavity probabilities recover the original finite cell measures exactly. -/
theorem ofReal_iidCavityMassVector (μ : Measure S) [IsFiniteMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (w : Fin m → S) (j : Fin (m + 1)) :
    ENNReal.ofReal (iidCavityMassVector μ c w j) =
      cavityCellMass μ (iidCapacityInputCost c (fun k w ↦ w k))
        (fun z j ↦ c j z.2) 0 j w :=
  ENNReal.ofReal_toReal (measure_ne_top μ _)

/-- The actual mass vector is measurable in the retained observations. -/
theorem measurable_iidCavityMassVector (μ : Measure S) [IsFiniteMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j)) :
    Measurable (iidCavityMassVector μ c) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_cavityCellMass μ _ _ (measurable_iidCavityRetained c hc)
    (fun l ↦ (hc l).comp measurable_snd) 0 j).ennreal_toReal

/-- Atomless score differences make the actual mass vector a simplex point at every
retained cloud, including configurations of measure zero. -/
theorem iidCavityMassVector_mem_stdSimplex (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (w : Fin m → S) : iidCavityMassVector μ c w ∈ stdSimplex ℝ (Fin (m + 1)) := by
  let retained := iidCapacityInputCost c (fun (k : Fin m) (w : Fin m → S) ↦ w k)
  let row : (Fin m → S) × S → Fin (m + 1) → ℝ := fun z j ↦ c j z.2
  have hrow (j : Fin (m + 1)) : Measurable (fun z ↦ row z j) :=
    (hc j).comp measurable_snd
  have hno : ∀ j l, j ≠ l →
      μ {s | cavityScore retained row 0 (w, s) j = cavityScore retained row 0 (w, s) l} = 0 := by
    intro j l hjl
    have := hatom j l hjl
    exact measure_cavityScore_eq_zero_of_atomless μ retained row hrow 0 j l w
  have hsum : ∑ j, cavityCellMass μ retained row 0 j w = 1 := by
    simpa only [measure_univ] using
      sum_cavityCellMass μ retained row (measurable_iidCavityRetained c hc) hrow 0 w hno
  refine ⟨fun j ↦ ENNReal.toReal_nonneg, ?_⟩
  change ∑ j, (cavityCellMass μ retained row 0 j w).toReal = 1
  have hfinite (j : Fin (m + 1)) : cavityCellMass μ retained row 0 j w ≠ ∞ :=
    measure_ne_top μ _
  rw [← ENNReal.toReal_sum (fun j _ ↦ hfinite j), hsum, ENNReal.toReal_one]

/-- The actual iid cavity probabilities have the standard Dirichlet law. No graph,
successful-subset, or distributional identity is assumed. -/
theorem map_iidCavityMassVector_eq_dirichletOne
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s))) :
    (Measure.pi (fun _ : Fin m ↦ μ)).map (iidCavityMassVector μ c) = dirichletOne m := by
  apply map_eq_dirichletOne_of_mixed_moments m _ _ (measurable_iidCavityMassVector μ c hc)
    (Eventually.of_forall (iidCavityMassVector_mem_stdSimplex μ c hc hatom))
  intro r
  simp_rw [ofReal_iidCavityMassVector]
  exact lintegral_iid_cavityCellMass_nat_powers μ c hc hatom r

end OTSelector.Probability

end
end
