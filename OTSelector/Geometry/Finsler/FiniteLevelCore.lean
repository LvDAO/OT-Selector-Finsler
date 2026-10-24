import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFiniteLevelCore.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFiniteLevelCore`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.FiniteLevelCore

* **Conditions:** Compact original source support, a 1-Lipschitz potential and positive separation of a calibrated segment.
* **Objects:** Finitely many rational potential levels meeting every such segment inside one common compact core with two-sided reach.
* **Proof detail:** Cover the compact source clock range by rational middle-level neighborhoods, select finitely many and use properness/unit calibrated travel to contain the chosen middle points.

Mathematical sources:
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/realanal.pdf#page=31): Section 1.2.2, Theorem 1.2.4, p. 31.
- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Theorem 1.30 (Hopf–Rinow), Exercise 1.31 and proof, pp. 18–19.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.

Source relation (derived): A finite rational-level selection and compactness corollary; it preserves actual calibrated curves and their clock.
-/

/-!
# Finite original levels meeting every uniformly separated calibrated segment

Compact source support and a positive separation select finitely many rational
potential levels. Every original calibrated segment meets one of these levels
inside one common compact set with a fixed two-sided calibrated reach.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

/-- A compact scalar range admits finitely many rational levels strictly between
one third and two thirds of a common positive distance above every scalar. -/
theorem exists_finite_rational_middle_levels {I : Set ℝ} (hI : IsCompact I)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : Finset ℚ, ∀ x ∈ I, ∃ q ∈ Q, x + δ / 3 < (q : ℝ) ∧
      (q : ℝ) < x + 2 * δ / 3 := by
  let U : ℚ → Set ℝ := fun q ↦ Ioo ((q : ℝ) - 2 * δ / 3) ((q : ℝ) - δ / 3)
  have hcover : I ⊆ ⋃ q : ℚ, U q := by
    intro x _
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show x + δ / 3 < x + 2 * δ / 3 by
      linarith)
    exact mem_iUnion.mpr ⟨q, by change _ < x ∧ x < _; constructor <;> linarith⟩
  obtain ⟨Q, hQ⟩ := hI.elim_finite_subcover U (fun _ ↦ isOpen_Ioo) hcover
  refine ⟨Q, ?_⟩
  intro x hx
  obtain ⟨q, hq, hqx⟩ := mem_iUnion₂.mp (hQ hx)
  exact ⟨q, hq, by constructor <;> linarith [hqx.1, hqx.2]⟩

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Every calibrated complete unit curve starting in the original compact source
support and traveling at least `δ` meets one of finitely many rational levels in
one compact core. Every point of that core has actual calibrated partners at
exact distance `δ / 3` on both sides. -/
theorem exists_finite_calibrated_level_core (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instFiniteLevelLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {A : Set M} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ) :
    let _instFiniteLevelMetric : MetricSpace M := F.metricSpace
    ∃ (Q : Finset ℚ) (K : Set M), IsCompact K ∧
      (∀ y ∈ K, ∃ p n : M, dist p y = δ / 3 ∧ u y - u p = δ / 3 ∧
        dist y n = δ / 3 ∧ u n - u y = δ / 3) ∧
      ∀ (c : ℝ → M), F.IsEulerLagrangeOn c univ →
        (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1) →
        ∀ a b offset : ℝ, c a ∈ A → δ ≤ b - a →
          u (c a) = offset + a → u (c b) = offset + b →
          ∃ q ∈ Q, ∃ s : ℝ, a + δ / 3 < s ∧ s < a + 2 * δ / 3 ∧
            c s ∈ K ∧ u (c s) = (q : ℝ) := by
  let _instFiniteLevelMetric : MetricSpace M := F.metricSpace
  let _instFiniteLevelProper : ProperSpace M := F.properSpace_of_complete hcomplete
  obtain ⟨Q, hQ⟩ := exists_finite_rational_middle_levels (hA.image hu.continuous) hδ
  let K := cthickening δ A ∩
    (calibratedReachLevel u (δ / 3) ∩ calibratedReachLevel (-u) (δ / 3))
  have hK : IsCompact K := hA.cthickening.inter_right
    ((OTSelector.Geometry.isClosed_calibratedReachLevel hu.continuous _).inter
      (OTSelector.Geometry.isClosed_calibratedReachLevel hu.neg.continuous _))
  refine ⟨Q, K, hK, ?_, ?_⟩
  · rintro y ⟨_, ⟨n, hdn, hn⟩, ⟨p, hdp, hp⟩⟩
    exact ⟨p, n, by simpa only [dist_comm] using hdp,
      by simpa only [Pi.neg_apply, neg_sub_neg] using hp, hdn, hn⟩
  intro c hEL hunit a b offset hca hgap ha hb
  obtain ⟨q, hq, hqa, hqb⟩ := hQ (u (c a)) (mem_image_of_mem u hca)
  obtain ⟨hclock, hiso, _⟩ :=
    hF.calibrated_window_of_complete_unit_endpoints hu hEL hunit ha hb
  let s := (q : ℝ) - offset
  have hs₁ : a + δ / 3 < s := by dsimp [s]; linarith
  have hs₂ : s < a + 2 * δ / 3 := by dsimp [s]; linarith
  have hs : s ∈ Icc a b := by constructor <;> linarith
  have hsp : s - δ / 3 ∈ Icc a b := by constructor <;> linarith
  have hsn : s + δ / 3 ∈ Icc a b := by constructor <;> linarith
  have hdist (v w : ℝ) (hv : v ∈ Icc a b) (hw : w ∈ Icc a b) (hle : v ≤ w) :
      dist (c v) (c w) = w - v := by
    simpa only [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hle), neg_sub] using hiso.dist_eq ⟨v, hv⟩ ⟨w, hw⟩
  refine ⟨q, hq, s, hs₁, hs₂, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · apply mem_cthickening_of_dist_le (c s) (c a) δ A hca
      rw [dist_comm, hdist a s (left_mem_Icc.mpr (by linarith)) hs hs.1]
      linarith
    · refine ⟨c (s + δ / 3), ?_, ?_⟩
      · rw [hdist s (s + δ / 3) hs hsn (by linarith)]
        ring
      · rw [hclock _ hsn, hclock _ hs]
        ring
    · refine ⟨c (s - δ / 3), ?_, ?_⟩
      · rw [dist_comm, hdist (s - δ / 3) s hsp hs (by linarith)]
        ring
      · simp only [Pi.neg_apply, neg_sub_neg, hclock _ hsp, hclock _ hs]
        ring
  · rw [hclock _ hs]
    dsimp [s]
    ring

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
