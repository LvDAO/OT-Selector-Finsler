import OTSelector.MeasureTheory.Lp.FiniteBandEnergySum
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.RegularBirthBandTrafficLtwo.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.RegularBirthBandTrafficLtwo`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Lp.BandWidthEnergySum

## Lemma skeleton

* **Conditions:** Finite L2 birth bands with moments at most C s² times nonnegative local energies, a shared total-energy budget and cardinality times width bounded by H.
* **Objects:** Finite band-sum L2 bound sqrt(H C E s).
* **Proof detail:** Use Minkowski and finite Cauchy–Schwarz on square roots of local energies, then insert the shared sum budget and cardinality-width inequality.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=214): Section 7A, Theorem 7.14, p. 199 (Minkowski).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=211): Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp).

Source relation (composition): Derived bandwidth-sensitive estimate spending the original energy budget once.
-/

/-! Regular birth uses the original scalar s I frame and one physical compact
clock span. Its finite band estimate spends the same original momentum budget. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- Actual regular-birth mean-square bounds `C s² V_i` over a fixed compact
clock span have their physical sqrt(s) L2 gain, retaining joint band energies. -/
theorem regularBirth_finiteBand_traffic_memLp_two_of_momentum_budget
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    {E C s H : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (hNs : (bands.card : ℝ) * s ≤ H)
    (hV : (∑ i ∈ bands, v i) ≤ E)
    (hmean : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤ C * s ^ 2 * v i) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤
        ENNReal.ofReal (Real.sqrt H * Real.sqrt C * Real.sqrt E * Real.sqrt s) := by
  have h := finiteBand_traffic_memLp_two_of_quadratic_energy_budget P bands T hT
    (fun _ ↦ 0) v (fun _ ↦ le_rfl) hv (cE := 0) (cV := C * s ^ 2)
    (by norm_num) (by positivity) (E := 0) (by simp) hV
    (by intro i hi; simpa only [mul_zero, zero_add, mul_assoc] using hmean i hi)
  refine ⟨h.1, h.2.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  simp only [Real.sqrt_zero, zero_mul, zero_add]
  rw [Real.sqrt_mul hC, Real.sqrt_sq_eq_abs, abs_of_pos hs]
  have hsqrt : Real.sqrt (bands.card : ℝ) * s =
      Real.sqrt ((bands.card : ℝ) * s) * Real.sqrt s := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), mul_assoc, Real.mul_self_sqrt hs.le]
  calc
    _ = (Real.sqrt (bands.card : ℝ) * s) * (Real.sqrt C * Real.sqrt E) := by ring
    _ = (Real.sqrt ((bands.card : ℝ) * s) * Real.sqrt s) *
        (Real.sqrt C * Real.sqrt E) := by rw [hsqrt]
    _ ≤ (Real.sqrt H * Real.sqrt s) * (Real.sqrt C * Real.sqrt E) := by gcongr
    _ = _ := by ring

end OTSelector.Probability

end
end
