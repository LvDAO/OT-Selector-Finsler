import OTSelector.Analysis.Calculus.MetricPotentialContact
import OTSelector.Analysis.Calculus.SecondJetPolynomial
import OTSelector.Analysis.Calculus.Whitney.C11
import OTSelector.Analysis.Calculus.Whitney.Lusin
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.MetricPotentialC11.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.MetricPotentialC11`; the selected original proof blocks follow. -/
section

/-!
Conditions: A calibrated metric potential has the stated C2 endpoint-distance Hessian bounds and compact or almost-everywhere jet hypotheses.

Objects: Actual local gradient/second-jet bounds and compact C1,1 extensions.

Proof detail: Sandwich the potential between endpoint costs, derive two-sided quadratic contact and a Lipschitz gradient, then apply the actual Whitney extension/compact selection interface.

Sources: Rotem Assouline, Section 4.2, Theorem 4.11, Lemmas 4.12–4.13, equations (4.6)–(4.9) (https://arxiv.org/html/2409.08001v6#S4.SS2); Aris Daniilidis, Introduction, equation (1.1), pp. 1–2; Section 3, Theorem 3.1, pp. 6–7 (https://www.arisdaniilidis.at/DHLL.pdf#page=2); Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html).
Relation: Derived metric/contact formulation of the calibrated C1,1 method. Its hypotheses and normed-space jet output are not asserted verbatim by the Tonelli paper. The cited Lagrangian theorem is used for its contact/extension method; this module proves its own stated metric hypotheses.
-/

/-!
# C1,1 extension of an original calibrated metric potential

Actual calibrated endpoint distances give the original potential's actual first jet.
The constructed Whitney extension then matches both its value and its true derivative
on the compact contact set. Compact endpoint families and joint continuity of their
actual Hessians provide the uniform constants in the strongest consumer.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem extend_actual_contactJet {u : E → ℝ} {K : Set E}
    (hK : IsCompact K) {p q : E → E →L[ℝ] ℝ} {C : ℝ≥0}
    (hactual : ∀ x ∈ K, HasFDerivAt u (p x) x ∧ fderiv ℝ u x = q x)
    (hlip : LipschitzOnWith (6 * C) (fderiv ℝ u) K)
    (hrem : ∀ x ∈ K, ∀ y ∈ K,
      ‖u y - u x - fderiv ℝ u x (y - x)‖ ≤ (C : ℝ) * ‖y - x‖ ^ 2) :
    ∃ (G : E → ℝ) (L : ℝ≥0), ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ContDiffOn ℝ ∞ G Kᶜ ∧ LipschitzWith L (fderiv ℝ G) ∧ EqOn G u K ∧
      EqOn (fderiv ℝ G) (fderiv ℝ u) K ∧
      ∀ x ∈ K, HasFDerivAt u (fderiv ℝ G x) x ∧
        fderiv ℝ G x = p x ∧ fderiv ℝ G x = q x := by
  have hC : (C : ℝ) ≤ ((6 * C : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith [C.coe_nonneg]
  have hquad (v) (hv : v ∈ K) (w) (hw : w ∈ K) :
      ‖u v - u w - fderiv ℝ u w (v - w)‖ ≤
        ((6 * C : ℝ≥0) : ℝ) * ‖v - w‖ ^ 2 :=
    (hrem w hw v hv).trans (mul_le_mul_of_nonneg_right hC (sq_nonneg _))
  obtain ⟨G, L, hG, hsupp, hOff, hLip, hval, hder⟩ :=
    exists_contDiff_one_lipschitz_fderiv_extension hK hlip hquad
  have hmatch : EqOn (fderiv ℝ G) (fderiv ℝ u) K := fun x hx ↦ (hder x hx).fderiv
  refine ⟨G, L, hG, hsupp, hOff, hLip, hval, hmatch, ?_⟩
  intro x hx
  have hp := (hmatch hx).trans (hactual x hx).1.fderiv
  exact ⟨(hactual x hx).1.congr_fderiv hp.symm, hp, (hmatch hx).trans (hactual x hx).2⟩

variable {M : Type*} [PseudoMetricSpace M]

/-- A common bound on the actual C2 endpoint-distance Hessians produces a compactly
supported C1,1 extension of the original potential on a compact calibrated contact set.
The first jet is the actual derivative of the original potential, not supplied data. -/
theorem exists_metric_potential_C11_of_distance_hessians {φ : M → ℝ}
    (hφ : LipschitzWith 1 φ) (Y : E → M) {K : Set E} (hK : IsCompact K)
    {c : E} {R : ℝ} (hR : 0 < R) (C : ℝ≥0) (hKball : K ⊆ closedBall c R)
    (a b : E → M)
    (ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
    (hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
    (hleft : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ContDiffAt ℝ 2 (fun y ↦ dist (a x) (Y y)) z)
    (hright : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ContDiffAt ℝ 2 (fun y ↦ dist (Y y) (b x)) z)
    (hboundLeft : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ dist (a x) (Y y))) z‖ ≤ (C : ℝ))
    (hboundRight : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ dist (Y y) (b x))) z‖ ≤ (C : ℝ)) :
    ∃ (G : E → ℝ) (L : ℝ≥0), ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ContDiffOn ℝ ∞ G Kᶜ ∧ LipschitzWith L (fderiv ℝ G) ∧ EqOn G (φ ∘ Y) K ∧
      EqOn (fderiv ℝ G) (fderiv ℝ (φ ∘ Y)) K ∧
      ∀ x ∈ K, HasFDerivAt (φ ∘ Y) (fderiv ℝ G x) x ∧
        fderiv ℝ G x = fderiv ℝ (fun z ↦ dist (a x) (Y z)) x ∧
        fderiv ℝ G x = -fderiv ℝ (fun z ↦ dist (Y z) (b x)) x := by
  obtain ⟨hactual, hlip, hrem⟩ := metric_potential_contactJet_of_distance_hessians
    hφ Y hR C hKball a b ha hb hleft hright hboundLeft hboundRight
  exact extend_actual_contactJet hK hactual hlip hrem

/-- Compact calibrated endpoint families and joint continuity of their actual distance
Hessians construct all uniform constants and a genuine C1,1 extension of the original
potential. No derivative field, Taylor estimate or extension is an input. -/
theorem exists_metric_potential_C11_of_compact_distance_hessians
    {φ : M → ℝ} (hφ : LipschitzWith 1 φ) (Y : E → M)
    {K : Set E} (hK : IsCompact K) {c : E} {R : ℝ} (hR : 0 < R)
    (hKball : K ⊆ closedBall c R) (a b : E → M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (haA : MapsTo a K A) (hbB : MapsTo b K B)
    (ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
    (hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
    (hleft : ∀ a ∈ A, ∀ z ∈ closedBall c (3 * R),
      ContDiffAt ℝ 2 (fun y ↦ dist a (Y y)) z)
    (hright : ∀ b ∈ B, ∀ z ∈ closedBall c (3 * R),
      ContDiffAt ℝ 2 (fun y ↦ dist (Y y) b) z)
    (hcontLeft : ContinuousOn
      (fun q : M × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ dist q.1 (Y y))) q.2)
      (A ×ˢ closedBall c (3 * R)))
    (hcontRight : ContinuousOn
      (fun q : M × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ dist (Y y) q.1)) q.2)
      (B ×ˢ closedBall c (3 * R))) :
    ∃ (G : E → ℝ) (L : ℝ≥0), ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ContDiffOn ℝ ∞ G Kᶜ ∧ LipschitzWith L (fderiv ℝ G) ∧ EqOn G (φ ∘ Y) K ∧
      EqOn (fderiv ℝ G) (fderiv ℝ (φ ∘ Y)) K ∧
      ∀ x ∈ K, HasFDerivAt (φ ∘ Y) (fderiv ℝ G x) x ∧
        fderiv ℝ G x = fderiv ℝ (fun z ↦ dist (a x) (Y z)) x ∧
        fderiv ℝ G x = -fderiv ℝ (fun z ↦ dist (Y z) (b x)) x := by
  obtain ⟨C, hactual, hlip, hrem⟩ := metric_potential_contactJet_of_compact_distance_hessians
    hφ Y hR hKball a b hA hB haA hbB ha hb hleft hright hcontLeft hcontRight
  exact extend_actual_contactJet hK hactual hlip hrem

omit [PseudoMetricSpace M] in
/-- A derivative-matched C1,1 extension gives arbitrarily large compact cores of actual
second jets. The original derivative has the same derivative within the contact set;
no ambient second differentiability of the original potential is asserted. -/
theorem exists_metric_potential_secondJet_core
    [MeasurableSpace E] [BorelSpace E]
    {μ ν : MeasureTheory.Measure E} [μ.IsAddHaarMeasure] (hν : ν ≪ μ)
    {K : Set E} (hK : IsCompact K) (hνK : ν K ≠ ⊤)
    {φ : M → ℝ} (Y : E → M) {G : E → ℝ} {L : ℝ≥0}
    (hG : ContDiff ℝ 1 G) (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G (φ ∘ Y) K)
    (hactual : ∀ x ∈ K, HasFDerivAt (φ ∘ Y) (fderiv ℝ G x) x)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K' ⊆ K, IsCompact K' ∧ ν (K \ K') < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K' ∧
      ∀ x ∈ K',
        HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x ∧
        HasFDerivWithinAt (fderiv ℝ (φ ∘ Y))
          (fderiv ℝ (fderiv ℝ G) x) K x ∧
        ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x = φ (Y x) ∧
          HasFDerivAt P (fderiv ℝ (φ ∘ Y) x) x ∧
          HasFDerivAt (fderiv ℝ P) (fderiv ℝ (fderiv ℝ G) x) x := by
  have hder : EqOn (fderiv ℝ G) (fderiv ℝ (φ ∘ Y)) K :=
    fun x hx ↦ (hactual x hx).fderiv.symm
  obtain ⟨K', hsub, hc, hmass, hdiff, _, hcont⟩ :=
    exists_differential_lusin_compact_core_of_lipschitz_absolutelyContinuous
      hν hK.measurableSet hνK hLip hε
  refine ⟨K', hsub, hc, hmass, hcont, ?_⟩
  intro x hx
  have hsecond := (hdiff x hx).hasFDerivAt
  have hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt G (fderiv ℝ G y) y :=
    Filter.Eventually.of_forall (fun y ↦ (hG.differentiable one_ne_zero y).hasFDerivAt)
  obtain ⟨P, hP, hPx, hP₁, hP₂, _, _⟩ := exists_smooth_matching_secondJet hfirst hsecond
  refine ⟨hsecond, hsecond.hasFDerivWithinAt.congr' hder.symm (hsub hx),
    P, hP, hPx.trans (hval (hsub hx)), ?_, hP₂⟩
  exact hP₁.congr_fderiv (hder (hsub hx))

end OTSelector.Geometry

end
end
