import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedEndpointWindow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedEndpointWindow`; the selected original proof blocks follow. -/
section

/-!
Conditions: A calibrated interval contains the indicated point and the chosen radius lies in its interior range.

Objects: Rational clock/radius windows and actual two-sided calibrated partners.

Proof detail: Choose rational bounds inside the open interval and use the curve isometry to identify the distances and partners.

Sources: Rotem Assouline, Section 4, Definitions 4.1–4.2 and Proposition 4.3; Section 4.1, Definitions 4.4/4.6 and Lemma 4.5 (https://arxiv.org/html/2409.08001v6#S4.SS1); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Elementary localization of calibrated intervals; rational schedules are the library encoding.
-/

/-!
# Endpoint-adapted calibrated time windows

A positive rational radius and a nonempty time window can simultaneously contain
an original endpoint pair and stay inside its calibrated interval. Moving the
center within any calibrated isometric interval gives actual partners at every
admissible nonnegative radius.
-/

open Set Metric

namespace OTSelector.Geometry

/-- Choose one positive rational reach and a nonempty open center window inside
the original endpoints, with strict margins for both closed time segments. -/
theorem exists_rat_prescribed_reach_endpoint_window
    {δ a b : ℝ} (hδ : 0 < δ) (ha : -δ < a)
    (hab : a < b) (hb : b < δ) :
    ∃ q : ℚ, 0 < q ∧ ∃ c d : ℝ, c < d ∧
      Set.Ioo c d ⊆ Set.Ioo a b ∧
      ∀ t ∈ Set.Ioo c d,
        Set.Icc (a - t) (b - t) ⊆ Set.Ioo (-(q : ℝ)) q ∧
        Set.Icc (t - q) (t + q) ⊆ Set.Ioo (-δ) δ := by
  let m := (a + b) / 2
  let l := (b - a) / 2
  have hl : 0 < l := by dsimp [l]; linarith
  have hgap : l < min (δ + m) (δ - m) := by
    apply lt_min <;> dsimp [l, m] <;> linarith
  obtain ⟨q, hlq, hqU⟩ := exists_rat_btwn hgap
  have hq : 0 < q := by
    exact_mod_cast ((lt_min hδ hl).trans_le (min_le_right δ l)).trans hlq
  have hqleft := hqU.trans_le (min_le_left _ _)
  have hqright := hqU.trans_le (min_le_right _ _)
  let c := max a (max (b - q) (q - δ))
  let d := min b (min (a + q) (δ - q))
  have hc : c < m := by
    apply max_lt <;> dsimp [m, l] at *
    · linarith
    · apply max_lt <;> linarith
  have hd : m < d := by
    apply lt_min <;> dsimp [m, l] at *
    · linarith
    · apply lt_min <;> linarith
  refine ⟨q, hq, c, d, hc.trans hd, ?_, ?_⟩
  · intro t ht
    exact ⟨(le_max_left _ _).trans_lt ht.1, ht.2.trans_le (min_le_left _ _)⟩
  · intro t ht
    have hlow := (max_lt_iff.mp (max_lt_iff.mp ht.1).2)
    have hupp := (lt_min_iff.mp (lt_min_iff.mp ht.2).2)
    constructor <;> apply Icc_subset_Ioo <;> linarith [hlow.1, hlow.2, hupp.1, hupp.2]

/-- Interior shifts of the same calibrated minimizing curve have actual partners
at every radius whose closed time segment stays in its calibrated interval. -/
theorem mem_two_sided_calibratedReach_of_isometry
    {M : Type*} [MetricSpace M] {γ : ℝ → M} {u : M → ℝ}
    {a b c t q : ℝ}
    (hiso : Isometry (fun s : Icc a b ↦ γ s))
    (hclock : ∀ s ∈ Icc a b, u (γ s) = c + s)
    (hq : 0 ≤ q) (hseg : Icc (t - q) (t + q) ⊆ Icc a b) :
    γ t ∈ calibratedReachLevel u q ∩ calibratedReachLevel (-u) q := by
  have ht : t ∈ Icc a b := hseg ⟨by linarith, by linarith⟩
  have hlo : t - q ∈ Icc a b := hseg ⟨le_rfl, by linarith⟩
  have hhi : t + q ∈ Icc a b := hseg ⟨by linarith, le_rfl⟩
  have hdistlo : dist (γ t) (γ (t - q)) = q := by
    have hd := hiso.dist_eq ⟨t, ht⟩ ⟨t - q, hlo⟩
    simpa only [Subtype.dist_eq, Real.dist_eq, sub_sub_cancel, abs_of_nonneg hq] using hd
  have hdisthi : dist (γ t) (γ (t + q)) = q := by
    have hd := hiso.dist_eq ⟨t + q, hhi⟩ ⟨t, ht⟩
    have hback : dist (γ (t + q)) (γ t) = q := by
      simpa only [Subtype.dist_eq, Real.dist_eq, add_sub_cancel_left,
        abs_of_nonneg hq] using hd
    simpa only [dist_comm] using hback
  constructor
  · refine ⟨γ (t + q), hdisthi, ?_⟩
    rw [hclock _ hhi, hclock _ ht]
    linarith
  · refine ⟨γ (t - q), hdistlo, ?_⟩
    simp only [Pi.neg_apply, hclock _ hlo, hclock _ ht]
    linarith

end OTSelector.Geometry

end
