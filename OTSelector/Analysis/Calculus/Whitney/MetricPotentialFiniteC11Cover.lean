import OTSelector.Analysis.Calculus.Whitney.MetricPotentialUpperContact
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.MetricPotentialFiniteC11Cover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.MetricPotentialFiniteC11Cover`; the selected original proof blocks follow. -/
section

/-!
Conditions: A compact contact set with the explicitly uniform local upper-cost and Hessian hypotheses.

Objects: A finite closed cover with actual C1,1 gradient jets and Whitney extensions on each piece.

Proof detail: Choose finitely many common contact neighborhoods, derive the jet bounds on their closed pieces and apply the actual Whitney C1,1 theorem.

Sources: Rotem Assouline, Section 4.2, Theorem 4.11, Lemmas 4.12–4.13, equations (4.6)–(4.9) (https://arxiv.org/html/2409.08001v6#S4.SS2); Aris Daniilidis, Introduction, equation (1.1), pp. 1–2; Section 3, Theorem 3.1, pp. 6–7 (https://www.arisdaniilidis.at/DHLL.pdf#page=2); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Compact finite-cover adaptation. It does not assume a continuous selection of endpoint partners. The cited Lagrangian theorem is used for its contact/extension method; this module proves its own stated metric hypotheses.
-/

/-!
# Finite compact C1,1 covers from uniform touching upper costs

Uniform local upper costs around each point of a compact set can be used on common
coordinate balls after a finite cover refinement. The existing Whitney construction
then extends the original potential and its actual first derivative on every compact
piece. No continuity of the selected endpoint or cost assignment is required.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [PseudoMetricSpace M]

/-- A compact set carrying uniform local touching upper costs has a finite cover
by compact pieces with genuine C1,1 extensions of the original potential's first jet. -/
theorem exists_finite_metric_potential_C11_cover_of_upper_costs
    {φ : M → ℝ} (hφ : LipschitzWith 1 φ) (Y : E → M)
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) (C : ℝ≥0)
    (a b : E → M) (cA cB : E → E → ℝ)
    (ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
    (hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
    (hdomA : ∀ x ∈ K, ∀ z ∈ ball x (2 * r), dist (a x) (Y z) ≤ cA x z)
    (hdomB : ∀ x ∈ K, ∀ z ∈ ball x (2 * r), dist (Y z) (b x) ≤ cB x z)
    (htouchA : ∀ x ∈ K, cA x x = dist (a x) (Y x))
    (htouchB : ∀ x ∈ K, cB x x = dist (Y x) (b x))
    (hA : ∀ x ∈ K, ContDiffOn ℝ ∞ (cA x) (ball x (2 * r)))
    (hB : ∀ x ∈ K, ContDiffOn ℝ ∞ (cB x) (ball x (2 * r)))
    (hHA : ∀ x ∈ K, ∀ z ∈ closedBall x r, ‖fderiv ℝ (fderiv ℝ (cA x)) z‖ ≤ (C : ℝ))
    (hHB : ∀ x ∈ K, ∀ z ∈ closedBall x r, ‖fderiv ℝ (fderiv ℝ (cB x)) z‖ ≤ (C : ℝ)) :
    ∃ J : Finset E, K ⊆ ⋃ q ∈ J, closedBall q (r / 8) ∧
      ∀ q ∈ J, IsCompact (K ∩ closedBall q (r / 8)) ∧
        ∃ (G : E → ℝ) (L : ℝ≥0), ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
          ContDiffOn ℝ ∞ G (K ∩ closedBall q (r / 8))ᶜ ∧
          LipschitzWith L (fderiv ℝ G) ∧ EqOn G (φ ∘ Y) (K ∩ closedBall q (r / 8)) ∧
          EqOn (fderiv ℝ G) (fderiv ℝ (φ ∘ Y)) (K ∩ closedBall q (r / 8)) ∧
          ∀ x ∈ K ∩ closedBall q (r / 8),
            HasFDerivAt (φ ∘ Y) (fderiv ℝ G x) x := by
  classical
  let R : ℝ := r / 8
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover (fun q : E ↦ ball q R)
    (fun _ ↦ isOpen_ball) (fun x _ ↦ mem_iUnion.mpr ⟨x, mem_ball_self hR⟩)
  refine ⟨J, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion₂.mpr ⟨q, hq, ball_subset_closedBall hxq⟩
  · intro q _
    let P := K ∩ closedBall q R
    have hP : IsCompact P := hK.inter_right isClosed_closedBall
    have hnear {x z : E} (hx : x ∈ P) (hz : z ∈ closedBall q (3 * R)) :
        z ∈ closedBall x r ∧ z ∈ ball x (2 * r) := by
      have hdx : dist x q ≤ R := mem_closedBall.mp hx.2
      have hdz : dist z q ≤ 3 * R := mem_closedBall.mp hz
      have hdist : dist z x ≤ 4 * R := by
        calc
          dist z x ≤ dist z q + dist q x := dist_triangle _ _ _
          _ ≤ 4 * R := by rw [dist_comm q x]; linarith
      constructor
      · rw [mem_closedBall]
        dsimp [R] at hdist
        linarith
      · rw [mem_ball]
        dsimp [R] at hdist
        linarith
    obtain ⟨G, L, hG, hsupp, hoff, hlip, hval, hder, hactual⟩ :=
      exists_metric_potential_C11_of_upper_cost_hessians hφ Y hP hR C
        (show P ⊆ closedBall q R from inter_subset_right) a b cA cB
        (fun x hx ↦ ha x hx.1) (fun x hx ↦ hb x hx.1)
        (fun x hx z hz ↦ hdomA x hx.1 z (hnear hx hz).2)
        (fun x hx z hz ↦ hdomB x hx.1 z (hnear hx hz).2)
        (fun x hx ↦ htouchA x hx.1) (fun x hx ↦ htouchB x hx.1)
        (fun x hx z hz ↦ ((hA x hx.1).contDiffAt
          (isOpen_ball.mem_nhds (hnear hx hz).2)).of_le (by simp))
        (fun x hx z hz ↦ ((hB x hx.1).contDiffAt
          (isOpen_ball.mem_nhds (hnear hx hz).2)).of_le (by simp))
        (fun x hx z hz ↦ hHA x hx.1 z (hnear hx hz).1)
        (fun x hx z hz ↦ hHB x hx.1 z (hnear hx hz).1)
    exact ⟨hP, G, L, hG, hsupp, hoff, hlip, hval, hder, fun x hx ↦ (hactual x hx).1⟩

end OTSelector.Geometry

end
end
