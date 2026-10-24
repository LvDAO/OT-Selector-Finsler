import OTSelector.Analysis.Calculus.Whitney.MetricPotentialUpperContact
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.MetricPotentialUpperDifferentiable.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.MetricPotentialUpperDifferentiable`; the selected original proof blocks follow. -/
section

/-!
Conditions: Local C2 upper touching costs with matching calibrated values, on the stated normed-space domain.

Objects: An actual potential differential at the contact point.

Proof detail: Bound the actual Hessians on a common ball, sandwich the potential and make the quadratic error vanish after division by displacement.

Sources: Rotem Assouline, Section 4.2, Theorem 4.11, Lemmas 4.12–4.13, equations (4.6)–(4.9) (https://arxiv.org/html/2409.08001v6#S4.SS2); Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html).
Relation: Local singleton-contact differentiability consequence; finite-dimensionality is not added when absent from the signature. The cited Lagrangian theorem is used for its contact/extension method; this module proves its own stated metric hypotheses.
-/

/-!
# Actual differentiability from local smooth upper distance contacts

Local C2 regularity of two touching upper path costs constructs a common positive
closed ball and actual Hessian bounds. The singleton contact-set consumer then gives
the original potential's actual derivative and equality of the two cost covectors.
No Hessian bound, potential derivative or smoothness of the original distance is an
input. Local Hessian continuity suffices, so finite dimensionality is unnecessary.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [PseudoMetricSpace M]

/-- Local smooth upper path costs touching the original distances at calibrated
endpoints imply actual differentiability of the original potential in the given
coordinates. The common positive radius and actual Hessian bound are constructed. -/
theorem metric_potential_hasFDerivAt_of_local_upper_costs
    {φ : M → ℝ} (hφ : LipschitzWith 1 φ) (Y : E → M)
    {x : E} {a b : M} (cA cB : E → ℝ)
    (ha : φ (Y x) - φ a = dist a (Y x))
    (hb : φ b - φ (Y x) = dist (Y x) b)
    (hdomA : ∀ᶠ y in 𝓝 x, dist a (Y y) ≤ cA y)
    (hdomB : ∀ᶠ y in 𝓝 x, dist (Y y) b ≤ cB y)
    (htouchA : cA x = dist a (Y x)) (htouchB : cB x = dist (Y x) b)
    (hA : ContDiffAt ℝ 2 cA x) (hB : ContDiffAt ℝ 2 cB x) :
    HasFDerivAt (φ ∘ Y) (fderiv ℝ cA x) x ∧
      fderiv ℝ cA x = -fderiv ℝ cB x := by
  let _instLocalUpperHessianNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let _instLocalUpperHessianSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let C : ℝ≥0 := ‖fderiv ℝ (fderiv ℝ cA) x‖₊ +
    ‖fderiv ℝ (fderiv ℝ cB) x‖₊ + 1
  have hCA : ‖fderiv ℝ (fderiv ℝ cA) x‖ < (C : ℝ) := by
    dsimp [C]
    linarith [norm_nonneg (fderiv ℝ (fderiv ℝ cB) x)]
  have hCB : ‖fderiv ℝ (fderiv ℝ cB) x‖ < (C : ℝ) := by
    dsimp [C]
    linarith [norm_nonneg (fderiv ℝ (fderiv ℝ cA) x)]
  have hHA : ContinuousAt (fderiv ℝ (fderiv ℝ cA)) x :=
    (hA.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv one_ne_zero
  have hHB : ContinuousAt (fderiv ℝ (fderiv ℝ cB)) x :=
    (hB.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv one_ne_zero
  have hAbound : ∀ᶠ z in 𝓝 x, ‖fderiv ℝ (fderiv ℝ cA) z‖ ≤ (C : ℝ) :=
    have hn : ContinuousAt (fun z : E ↦ ‖fderiv ℝ (fderiv ℝ cA) z‖) x := hHA.norm
    hn.eventually (eventually_le_nhds hCA)
  have hBbound : ∀ᶠ z in 𝓝 x, ‖fderiv ℝ (fderiv ℝ cB) z‖ ≤ (C : ℝ) :=
    have hn : ContinuousAt (fun z : E ↦ ‖fderiv ℝ (fderiv ℝ cB) z‖) x := hHB.norm
    hn.eventually (eventually_le_nhds hCB)
  have hgood : ∀ᶠ z in 𝓝 x,
      ContDiffAt ℝ 2 cA z ∧ ContDiffAt ℝ 2 cB z ∧
        dist a (Y z) ≤ cA z ∧ dist (Y z) b ≤ cB z ∧
        ‖fderiv ℝ (fderiv ℝ cA) z‖ ≤ (C : ℝ) ∧
        ‖fderiv ℝ (fderiv ℝ cB) z‖ ≤ (C : ℝ) := by
    filter_upwards [hA.eventually (by norm_num), hB.eventually (by norm_num),
      hdomA, hdomB, hAbound, hBbound] with z hAz hBz hdomAz hdomBz hHazi hHbzi
    exact ⟨hAz, hBz, hdomAz, hdomBz, hHazi, hHbzi⟩
  obtain ⟨δ, hδ, hgoodδ⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp hgood
  let R := δ / 3
  have hR : 0 < R := by dsimp [R]; positivity
  have h3R : 3 * R = δ := by dsimp [R]; ring
  have hsmall : ({x} : Set E) ⊆ closedBall x R := by
    intro z hz
    rw [mem_singleton_iff.mp hz]
    exact mem_closedBall_self hR.le
  have hgoodR (z : E) (hz : z ∈ closedBall x (3 * R)) :=
    hgoodδ (by simpa only [h3R] using hz)
  obtain ⟨hactual, _, _⟩ := metric_potential_contactJet_of_upper_cost_hessians
    hφ Y hR C hsmall (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ cA) (fun _ ↦ cB)
    (by rintro z rfl; exact ha) (by rintro z rfl; exact hb)
    (fun _ _ z hz ↦ (hgoodR z hz).2.2.1)
    (fun _ _ z hz ↦ (hgoodR z hz).2.2.2.1)
    (by rintro z rfl; exact htouchA) (by rintro z rfl; exact htouchB)
    (fun _ _ z hz ↦ (hgoodR z hz).1)
    (fun _ _ z hz ↦ (hgoodR z hz).2.1)
    (fun _ _ z hz ↦ (hgoodR z hz).2.2.2.2.1)
    (fun _ _ z hz ↦ (hgoodR z hz).2.2.2.2.2)
  have h := hactual x (mem_singleton x)
  exact ⟨h.1, h.1.fderiv.symm.trans h.2⟩

end OTSelector.Geometry

end
end
