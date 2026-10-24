import OTSelector.MeasureTheory.ShiftedIntegralMassCancellation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalIIDFiniteSignedShiftCancellation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalIIDFiniteSignedShiftCancellation`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.FiniteSignedShiftCancellation

## Lemma skeleton

* **Conditions:** Finite heterogeneous candidate laws and integrable signed readouts with nonnegative shifted versions; physical signed means and total candidate masses converge as stated.
* **Objects:** Finite summed shift identity, signed lower bound retaining the actual summed mass defect, and its vanishing-defect conclusion.
* **Proof detail:** Sum the exact finite shift formulas, pass the physical real limit through ofReal, subtract the total candidate shift and let the actual summed mass defect tend to zero.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): Finite-family extension of signed shift cancellation; the shifted liminf inequality is an input and unequal domains are allowed.
-/

/-!
# Signed shift cancellation for finite heterogeneous candidate domains

Every candidate keeps its own original finite measure and signed integral.
The finite nonnegative shifted sum equals ofReal of the signed sum plus the
actual summed candidate mass. Comparing with the original physical ENNReal
liminf retains the two-domain mass defect explicitly. Refinement cancels that
defect only when the summed candidate masses really recover the physical mass.
-/

open Set Function Filter MeasureTheory Topology
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Summing genuinely nonnegative shifts over different finite candidate
spaces retains the sum of their ACTUAL masses, with no sigma-space replacement. -/
theorem sum_lintegral_ofReal_add_shift_eq
    {I : Type*} [Fintype I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (ρ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ρ i)]
    (f : ∀ i, X i → ℝ) (hf : ∀ i, Integrable (f i) (ρ i)) (s : ℝ)
    (hnonneg : ∀ i, ∀ᵐ x ∂ρ i, 0 ≤ f i x+s) :
    (∑ i, ∫⁻ x, ENNReal.ofReal (f i x+s) ∂ρ i) =
      ENNReal.ofReal ((∑ i, ∫ x, f i x ∂ρ i)+s*(∑ i, (ρ i).real univ)) := by
  classical
  have hpos (i : I) : 0 ≤ (∫ x, f i x ∂ρ i)+s*(ρ i).real univ := by
    rw [← integral_add_shift_eq (ρ i) (f i) (hf i) s]
    exact integral_nonneg_of_ae (hnonneg i)
  calc
    _ = ∑ i, ENNReal.ofReal ((∫ x, f i x ∂ρ i)+s*(ρ i).real univ) :=
      Finset.sum_congr rfl (fun i _ ↦ lintegral_ofReal_add_shift_eq (ρ i) (f i) (hf i) s (hnonneg i))
    _ = ENNReal.ofReal (∑ i, ((∫ x, f i x ∂ρ i)+s*(ρ i).real univ)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hpos i)).symm
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum]

/-- Actual physical signed integral convergence controls the genuine shifted
nonnegative ENNReal sequence. Only that ENNReal sequence is later given liminf. -/
theorem tendsto_shifted_lintegral_of_signed_integral_tendsto
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (μ : ∀ n, Measure (Y n)) [∀ n, IsFiniteMeasure (μ n)]
    (g : ∀ n, Y n → ℝ) (hg : ∀ n, Integrable (g n) (μ n))
    (s mphysical L : ℝ)
    (hgn : ∀ n, ∀ᵐ y ∂μ n, 0 ≤ g n y+s)
    (hμmass : ∀ n, (μ n).real univ = mphysical)
    (hphysical : Tendsto (fun n ↦ ∫ y, g n y ∂μ n) atTop (𝓝 L)) :
    0 ≤ L+s*mphysical ∧
      Tendsto (fun n ↦ ∫⁻ y, ENNReal.ofReal (g n y+s) ∂μ n)
        atTop (𝓝 (ENNReal.ofReal (L+s*mphysical))) := by
  have hreal : Tendsto (fun n ↦ (∫ y, g n y ∂μ n)+s*mphysical)
      atTop (𝓝 (L+s*mphysical)) := hphysical.add_const _
  have hphysicalShift (n : ℕ) : (∫ y, g n y+s ∂μ n) =
      (∫ y, g n y ∂μ n)+s*mphysical := by
    rw [integral_add_shift_eq (μ n) (g n) (hg n) s,hμmass n]
  refine ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hreal (fun n ↦ ?_), ?_⟩
  · rw [← hphysicalShift n]
    exact integral_nonneg_of_ae (hgn n)
  · have heq (n : ℕ) : (∫⁻ y, ENNReal.ofReal (g n y+s) ∂μ n) =
        ENNReal.ofReal ((∫ y, g n y ∂μ n)+s*mphysical) := by
      rw [lintegral_ofReal_add_shift_eq (μ n) (g n) (hg n) s (hgn n),hμmass n]
    simp_rw [heq]
    simpa only [Function.comp_def] using ENNReal.continuous_ofReal.tendsto _ |>.comp hreal

/-- A true finite shifted ENNReal lower sum yields the signed sum with its
exact defect `physical mass - sum of candidate masses`. No equal-domain mass
assumption is made, and all candidate spaces may be different. -/
theorem sum_integral_le_of_shifted_lintegral_sum_le_liminf
    {I : Type*} [Fintype I] {X : I → Type*} {Y : ℕ → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ n, MeasurableSpace (Y n)]
    (ρ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ρ i)]
    (μ : ∀ n, Measure (Y n)) [∀ n, IsFiniteMeasure (μ n)]
    (f : ∀ i, X i → ℝ) (hf : ∀ i, Integrable (f i) (ρ i))
    (g : ∀ n, Y n → ℝ) (hg : ∀ n, Integrable (g n) (μ n))
    (s : ℝ) (_hs : 0 ≤ s)
    (hfn : ∀ i, ∀ᵐ x ∂ρ i, 0 ≤ f i x+s)
    (hgn : ∀ n, ∀ᵐ y ∂μ n, 0 ≤ g n y+s)
    (mphysical L : ℝ) (hμmass : ∀ n, (μ n).real univ = mphysical)
    (hphysical : Tendsto (fun n ↦ ∫ y, g n y ∂μ n) atTop (𝓝 L))
    (hshift : (∑ i, ∫⁻ x, ENNReal.ofReal (f i x+s) ∂ρ i) ≤
      liminf (fun n ↦ ∫⁻ y, ENNReal.ofReal (g n y+s) ∂μ n) atTop) :
    (∑ i, ∫ x, f i x ∂ρ i) ≤ L+s*(mphysical-∑ i, (ρ i).real univ) := by
  obtain ⟨hnonneg,henn⟩ := tendsto_shifted_lintegral_of_signed_integral_tendsto
    μ g hg s mphysical L hgn hμmass hphysical
  rw [sum_lintegral_ofReal_add_shift_eq ρ f hf s hfn,henn.liminf_eq] at hshift
  have hbound := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hshift
  linarith

/-- Finite heterogeneous candidates may vary with the refinement index,
including their index set and their individual spaces. The actual finite
shifted ENNReal lower bounds, original mass recovery and a fixed signed target
then imply the final signed target bound, with the defect derived internally. -/
theorem le_of_finite_shifted_candidate_mass_convergence
    {I : ℕ → Type*} [∀ j, Fintype (I j)]
    {X : (j : ℕ) → I j → Type*} {Y : ℕ → Type*}
    [∀ j i, MeasurableSpace (X j i)] [∀ n, MeasurableSpace (Y n)]
    (ρ : ∀ j i, Measure (X j i)) [∀ j i, IsFiniteMeasure (ρ j i)]
    (μ : ∀ n, Measure (Y n)) [∀ n, IsFiniteMeasure (μ n)]
    (f : ∀ j i, X j i → ℝ) (hf : ∀ j i, Integrable (f j i) (ρ j i))
    (g : ∀ n, Y n → ℝ) (hg : ∀ n, Integrable (g n) (μ n))
    (s : ℝ) (hs : 0 ≤ s)
    (hfn : ∀ j i, ∀ᵐ x ∂ρ j i, 0 ≤ f j i x+s)
    (hgn : ∀ n, ∀ᵐ y ∂μ n, 0 ≤ g n y+s)
    (mphysical V L : ℝ) (hμmass : ∀ n, (μ n).real univ = mphysical)
    (hphysical : Tendsto (fun n ↦ ∫ y, g n y ∂μ n) atTop (𝓝 L))
    (hmass : Tendsto (fun j ↦ ∑ i, (ρ j i).real univ) atTop (𝓝 mphysical))
    (hlower : ∀ j, V ≤ ∑ i, ∫ x, f j i x ∂ρ j i)
    (hshift : ∀ j, (∑ i, ∫⁻ x, ENNReal.ofReal (f j i x+s) ∂ρ j i) ≤
      liminf (fun n ↦ ∫⁻ y, ENNReal.ofReal (g n y+s) ∂μ n) atTop) : V ≤ L := by
  apply le_of_signed_shift_mass_convergence (fun j ↦ ∑ i, ∫ x, f j i x ∂ρ j i)
    (fun j ↦ ∑ i, (ρ j i).real univ) V L s mphysical hmass hlower
  intro j
  exact sum_integral_le_of_shifted_lintegral_sum_le_liminf (ρ j) μ (f j) (hf j) g hg s hs
    (hfn j) hgn mphysical L hμmass hphysical (hshift j)

end OTSelector.Reconstruction

end
end
