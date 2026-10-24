import OTSelector.Analysis.Asymptotics.DoublePoleRelativeMobility
import OTSelector.Analysis.Calculus.SmoothMatrixRemainderBounds
import OTSelector.Analysis.RelativeBandRatio
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.DoublePoleRelativeMobilityBounds.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.DoublePoleRelativeMobilityBounds`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.DoublePoleRelativeMobilityBounds

**Conditions:** The actual double-pole remainder is smooth near zero, the original mobility is invertible on positive times and its inverse has the explicit uniform bound H.

**Objects:** Internal positive neighborhood and constant for the relative mobility bound Cτ.

**Proof detail:** On a smaller compact interval obtain bounded remainder and derivative norms, use the mean-value estimate for its differences, and substitute these bounds into the exact relative-pole product identity.

**Sources:** [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=46), Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47; [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_metcont.html), Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem); [OTSelector project, Actual focal simple-pole expansion](main.tex#lem:focal-simple-pole), main.tex label lem:focal-simple-pole, line 9401.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Internal constants for physical relative mobility near a genuine focal endpoint

The smooth actual double-pole remainder and the actual bounded inverse field supply all
constants. The relative-time estimate uses the same full matrix product and preserves
noncommuting residues and remainders.
-/

open Set Matrix
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A genuine smooth double pole with bounded actual inverses internally yields the
uniform O(τ) physical relative-mobility estimate on every sufficiently small relative band. -/
theorem exists_doublePole_relative_mobility_bound
    {W R : ℝ→Matrix ι ι ℝ} {G : Matrix ι ι ℝ} {ε H : ℝ}
    (hε : 0<ε) (hH : 0≤H)
    (hR : ContDiffOn ℝ ∞ R (Ioo (-ε) ε))
    (hpole : ∀s∈Ioo 0 ε, W s=(s^2)⁻¹•G+R s)
    (hunit : ∀s∈Ioo 0 ε, IsUnit (W s).det)
    (hinv : ∀s∈Ioo 0 ε, ‖(W s)⁻¹‖≤H) :
    ∃ η : ℝ, η>0 ∧ η<ε ∧ ∃ C : ℝ, C>0 ∧
      ∀a∈Ioo 0 η, ∀τ∈Icc (0:ℝ) (1/2), ∀s : ℝ, |s-a|≤τ*a →
        ‖W s*(W a)⁻¹-1‖≤C*τ := by
  obtain ⟨δ,hδ,hδε,M,hM,N,hN,hMbound,hNbound⟩ := exists_smooth_pole_remainder_bounds hε hR
  let η := δ/2
  have hη : 0<η := half_pos hδ
  have hηδ : η<δ := half_lt_self hδ
  let C₀ := 10*(‖(1:Matrix ι ι ℝ)‖+M*H)+N*δ*H
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  refine ⟨η,hη,hηδ.trans hδε,C₀+1,by positivity,fun a ha τ hτ s hband ↦ ?_⟩
  obtain ⟨hslo,hshi,hcoeff⟩ := doublePole_ratio_relativeBand ha.1 hτ.1 hτ.2 hband
  have hs : 0<s := (half_pos ha.1).trans_le hslo
  have haδ : a∈Icc (-δ) δ := ⟨by linarith [ha.1],ha.2.le.trans hηδ.le⟩
  have hsδ : s∈Icc (-δ) δ := ⟨by linarith,by dsimp [η] at ha; linarith [ha.2]⟩
  have haε : a∈Ioo 0 ε := ⟨ha.1,ha.2.trans (hηδ.trans hδε)⟩
  have hsε : s∈Ioo 0 ε := ⟨hs,hsδ.2.trans_lt hδε⟩
  have hb := norm_doublePole_relative_mobility_le ha.1 haδ.2 hτ.1 hτ.2 hband hN hH
    (hMbound a haδ) (hinv a haε) (hNbound s hsδ a haδ)
    (hpole s hsε) (hpole a haε) (Matrix.mul_nonsing_inv (W a) (hunit a haε))
  exact hb.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hτ.1)

end OTSelector.Reconstruction

end
end
