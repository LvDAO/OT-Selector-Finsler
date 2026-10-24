import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Measure.Haar.Unique
import OTSelector.LinearAlgebra.Matrix.PositiveCongruenceRank
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.DoublePoleResidueGram.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.DoublePoleResidueGram`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.DoublePoleResidueGram

**Conditions:** The actual inverse field has a simple pole and its mobility a double pole, with continuous coefficients/remainders; the rank conclusion assumes a positive-definite endpoint weight.

**Objects:** The actual double-pole residue G and its weighted Gram expression R C(0) Rᵀ.

**Proof detail:** Multiply both actual pole identities by s² and pass to the endpoint limit; uniqueness identifies the residue, then positive square-root factorization identifies its rank with that of R.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=662), Appendix A.5.1, pp. 645–646 (range/nullspace/rank); A.5.2, p. 647 (positive square root); A.5.4, pp. 648–649 (SVD and the nonzero spectra of A^T A and A A^T); [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=62), Section 2.2, Lemma 2.2.3, p. 62; Section 2.3, Proposition 2.3.5, pp. 76–77; [OTSelector project, Actual focal simple-pole expansion](main.tex#lem:focal-simple-pole), main.tex label lem:focal-simple-pole, line 9401.

Source relation (composition): The pole expansion is an explicit input. The weighted-Gram leading coefficient and rank are local consequences of that expansion and standard finite-matrix rank theory, supporting the actual focal calculation in the cited paper label.
-/

/-!
# The actual mobility residue is the endpoint weighted Gram matrix

An actual simple inverse pole and the actual double mobility pole identify the same leading
coefficient by continuity after multiplication by squared endpoint distance. A positive
endpoint Hamiltonian weight then gives its rank without a commutativity or projection
assumption.
-/

open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The leading double-pole coefficient of an actual weighted inverse is its same inverse
residue weighted by the actual endpoint coefficient. -/
theorem doublePole_residue_eq_weightedGram
    {ε : ℝ} (hε : 0<ε) {I C B Rem : ℝ→Matrix n n ℝ} {R G : Matrix n n ℝ}
    (hC : ContinuousAt C 0) (hB : ContinuousAt B 0) (hRem : ContinuousAt Rem 0)
    (hinv : ∀s∈Ioo 0 ε, I s=s⁻¹•R+B s)
    (hpole : ∀s∈Ioo 0 ε, I s*C s*(I s)ᵀ=(s^2)⁻¹•G+Rem s) :
    G=R*C 0*Rᵀ := by
  let X : ℝ→Matrix n n ℝ := fun s ↦ R+s•B s
  let L := (Matrix.transposeLinearEquiv n n ℝ ℝ).toLinearMap.toContinuousLinearMap
  have hX : ContinuousAt X 0 := continuousAt_const.add (continuousAt_id.smul hB)
  have hXT : ContinuousAt (fun s ↦ (X s)ᵀ) 0 := L.continuous.continuousAt.comp hX
  have hgram : Tendsto (fun s ↦ X s*C s*(X s)ᵀ) (𝓝[>] 0) (𝓝 (R*C 0*Rᵀ)) := by
    have hcont : ContinuousAt (fun s ↦ X s*C s*(X s)ᵀ) 0 := (hX.mul hC).mul hXT
    simpa only [X,zero_smul,add_zero] using
      hcont.tendsto.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  have hresidue : Tendsto (fun s : ℝ ↦ G+s^2•Rem s) (𝓝[>] 0) (𝓝 G) := by
    have hcont : ContinuousAt (fun s : ℝ ↦ G+s^2•Rem s) 0 :=
      continuousAt_const.add ((continuousAt_id.pow 2).smul hRem)
    simpa only [zero_pow (by decide : 2≠0),zero_smul,add_zero] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hu : ∀ᶠs in 𝓝[>] (0:ℝ), s<ε := nhdsWithin_le_nhds (Iio_mem_nhds hε)
  have heq : (fun s ↦ X s*C s*(X s)ᵀ)=ᶠ[𝓝[>] (0:ℝ)] (fun s ↦ G+s^2•Rem s) := by
    filter_upwards [self_mem_nhdsWithin,hu] with s hs hsε
    have hs0 : s≠0 := ne_of_gt hs
    have hsI : s∈Ioo 0 ε := ⟨hs,hsε⟩
    have hscaled : s•I s=X s := by
      rw [hinv s hsI,smul_add,smul_smul,mul_inv_cancel₀ hs0,one_smul]
    calc
      X s*C s*(X s)ᵀ = s^2•(I s*C s*(I s)ᵀ) := by
        rw [←hscaled]
        simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,pow_two]
      _ = G+s^2•Rem s := by
        rw [hpole s hsI,smul_add,smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 hs0),one_smul]
  exact tendsto_nhds_unique hresidue (hgram.congr' heq)

/-- The actual positive endpoint Hamiltonian weight preserves the actual inverse residue rank. -/
theorem doublePole_residue_rank_eq_inverseResidue
    {ε : ℝ} (hε : 0<ε) {I C B Rem : ℝ→Matrix n n ℝ} {R G : Matrix n n ℝ}
    (hC : ContinuousAt C 0) (hB : ContinuousAt B 0) (hRem : ContinuousAt Rem 0)
    (hCpos : (C 0).PosDef)
    (hinv : ∀s∈Ioo 0 ε, I s=s⁻¹•R+B s)
    (hpole : ∀s∈Ioo 0 ε, I s*C s*(I s)ᵀ=(s^2)⁻¹•G+Rem s) :
    G.rank=R.rank := by
  rw [doublePole_residue_eq_weightedGram hε hC hB hRem hinv hpole]
  exact OTSelector.Probability.rank_positive_congruence R hCpos

end OTSelector.Reconstruction

end
end
