import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedReach.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedReach`; the selected original proof blocks follow. -/
section

/-!
Conditions: A proper metric space with a dominated potential and actual minimizing/isometric segments for shortening partners.

Objects: Closed fixed-radius reach sets, a countable description of the interior strain set and compact trimmed contact covers.

Proof detail: Extract compact convergent partners for closedness, shorten them along minimizing segments and use rational radii plus finite compact covers.

Sources: Rotem Assouline, Section 4.1, Lemma 4.9; Section 4.2, trimmed strain sets and Lemma 4.10 (https://arxiv.org/html/2409.08001v6#S4.SS2); Zhongmin Shen, Section 4, pp. 313–314, length distance, Definition 4.1 and Lemma 4.2, equations (4–1)–(4–4) (https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Derived proper-metric reach construction. It does not by itself prove that the strain set has full measure.
-/

/-!
# Closed calibrated reach levels and compact contact covers

Fixed-radius calibrated endpoint sets are closed in a proper metric space. When actual
minimizing intervals exist, calibrated endpoints can be shortened to any smaller positive
radius. Thus the points with nontrivial calibrated partners on both sides form a countable
union of compact trimmed contact sets. No full-measure assertion is included.
-/

open Set Filter Metric
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {M : Type*} [MetricSpace M]

/-- Points admitting a forward calibrated endpoint at exactly the prescribed distance. -/
def calibratedReachLevel (u : M → ℝ) (r : ℝ) : Set M :=
  {x | ∃ y, dist x y = r ∧ u y - u x = r}

/-- Points with a nontrivial original calibrated predecessor and successor. -/
def calibratedInterior (u : M → ℝ) : Set M :=
  {x | (∃ a, a ≠ x ∧ u x - u a = dist a x) ∧
    ∃ b, x ≠ b ∧ u b - u x = dist x b}

/-- An actual calibrated minimizing interval contains a calibrated endpoint at every
smaller radius, including zero. No differentiability of the potential is required. -/
theorem exists_calibrated_at_distance_of_isometry {u : M → ℝ}
    (hu : LipschitzWith 1 u) {x y : M}
    (γ : Icc (0 : ℝ) (dist x y) → M) (hγ : Isometry γ)
    (hzero : γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hend : γ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hsat : u y - u x = dist x y) {r : ℝ} (hr : 0 ≤ r) (hry : r ≤ dist x y) :
    x ∈ calibratedReachLevel u r := by
  let q : Icc (0 : ℝ) (dist x y) := ⟨r, hr, hry⟩
  have hdx : dist (γ q) x = r := by
    rw [← hzero]
    simpa only [q, Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hr] using
      hγ.dist_eq q ⟨0, ⟨le_rfl, dist_nonneg⟩⟩
  have hdy : dist y (γ q) = dist x y - r := by
    calc
      dist y (γ q) = dist (γ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩) (γ q) := by rw [hend]
      _ = dist x y - r := by
        simpa only [q, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hry)] using
          hγ.dist_eq ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ q
  have hupper := hu.le_add_mul (γ q) x
  have hlower := hu.le_add_mul y (γ q)
  simp only [NNReal.coe_one, one_mul, hdx, hdy] at hupper hlower
  exact ⟨γ q, by simpa only [dist_comm] using hdx, by linarith⟩



/-- Properness makes every fixed-radius calibrated reach level closed. Continuity of
u suffices; neither differentiability nor uniqueness of a calibrated endpoint is assumed. -/
theorem isClosed_calibratedReachLevel [ProperSpace M] {u : M → ℝ}
    (hu : Continuous u) (r : ℝ) : IsClosed (calibratedReachLevel u r) := by
  refine isSeqClosed_iff_isClosed.mp ?_
  intro a x ha hax
  choose b hb1 hb2 using ha
  have hb : ∀ᶠ n in atTop, b n ∈ closedBall x (r + 1) := by
    filter_upwards [hax.eventually (ball_mem_nhds x zero_lt_one)] with n hn
    apply mem_closedBall.mpr
    calc
      dist (b n) x ≤ dist (b n) (a n) + dist (a n) x := dist_triangle _ _ _
      _ ≤ r + 1 := by rw [dist_comm (b n), hb1]; exact add_le_add_right (le_of_lt hn) r
  obtain ⟨y, _, φ, hφmono, hby⟩ :=
    (isCompact_closedBall x (r + 1)).tendsto_subseq' hb.frequently
  have hax' : Tendsto (a ∘ φ) atTop (𝓝 x) := hax.comp hφmono.tendsto_atTop
  refine ⟨y, ?_, ?_⟩
  · apply tendsto_nhds_unique (hax'.dist hby)
    simpa only [Function.comp_apply, hb1] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ r) atTop (𝓝 r))
  · apply tendsto_nhds_unique ((hu.tendsto y |>.comp hby).sub (hu.tendsto x |>.comp hax'))
    simpa only [Function.comp_apply, hb2] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ r) atTop (𝓝 r))

variable {u : M → ℝ} (hu : LipschitzWith 1 u)
  (hsegments : ∀ x y : M, ∃ γ : Icc (0 : ℝ) (dist x y) → M,
    Isometry γ ∧ γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      γ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)

include hu hsegments

/-- Exact-radius calibrated reach is equivalent to reaching at least that distance,
using actual minimizing intervals to shorten the calibrated segment. -/
theorem calibratedReachLevel_iff_exists_ge {x : M} {r : ℝ} (hr : 0 ≤ r) :
    x ∈ calibratedReachLevel u r ↔ ∃ y, r ≤ dist x y ∧ u y - u x = dist x y := by
  constructor
  · rintro ⟨y, hd, he⟩
    exact ⟨y, hd.ge, he.trans hd.symm⟩
  · rintro ⟨y, hd, he⟩
    obtain ⟨γ, hγ, hzero, hend⟩ := hsegments x y
    exact exists_calibrated_at_distance_of_isometry hu γ hγ hzero hend he hr hd

/-- Positive two-sided calibrated reach is exhausted by common positive reciprocal
radii, so each level retains an actual predecessor and successor of controlled length. -/
theorem calibratedInterior_eq_iUnion_reachLevels :
    calibratedInterior u = ⋃ n : ℕ,
      calibratedReachLevel u (1 / (n + 1 : ℝ)) ∩
        calibratedReachLevel (-u) (1 / (n + 1 : ℝ)) := by
  ext x
  constructor
  · rintro ⟨⟨a, hax, ha⟩, ⟨b, hxb, hb⟩⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt
      (lt_min (dist_pos.mpr hax) (dist_pos.mpr hxb))
    have hr : 0 ≤ 1 / (n + 1 : ℝ) := by positivity
    refine mem_iUnion.mpr ⟨n, ?_, ?_⟩
    · exact (calibratedReachLevel_iff_exists_ge hu hsegments hr).mpr
        ⟨b, (hn.trans_le (min_le_right _ _)).le, hb⟩
    · apply (calibratedReachLevel_iff_exists_ge hu.neg hsegments hr).mpr
      refine ⟨a, ?_, ?_⟩
      · simpa only [dist_comm x a] using (hn.trans_le (min_le_left _ _)).le
      · simpa only [Pi.neg_apply, neg_sub_neg, dist_comm x a] using ha
  · intro hx
    obtain ⟨n, ⟨b, hdb, hb⟩, ⟨a, hda, ha⟩⟩ := mem_iUnion.mp hx
    have hr : 0 < 1 / (n + 1 : ℝ) := by positivity
    refine ⟨⟨a, ?_, ?_⟩, ⟨b, ?_, ?_⟩⟩
    · exact Ne.symm (dist_pos.mp (hda ▸ hr))
    · simpa only [Pi.neg_apply, neg_sub_neg, ← hda, dist_comm x a] using ha
    · exact dist_pos.mp (hdb ▸ hr)
    · exact hb.trans hdb.symm

/-- The actual positive two-sided reach set is Borel. -/
theorem measurableSet_calibratedInterior [ProperSpace M]
    [MeasurableSpace M] [BorelSpace M] : MeasurableSet (calibratedInterior u) := by
  rw [calibratedInterior_eq_iUnion_reachLevels hu hsegments]
  exact MeasurableSet.iUnion (fun n ↦
    ((isClosed_calibratedReachLevel hu.continuous _).inter
      (isClosed_calibratedReachLevel hu.neg.continuous _)).measurableSet)

/-- Actual two-sided calibrated interior points admit a countable compact contact cover.
Every piece has compact endpoint carriers and a common strictly positive reach radius.
No assertion that the covered set has full volume or marginal measure is made. -/
theorem exists_compact_trimmed_contact_cover [ProperSpace M] :
    ∃ K A : ℕ × ℕ → Set M,
      (∀ i, IsCompact (K i) ∧ IsCompact (A i)) ∧
      (⋃ i, K i) = calibratedInterior u ∧
      ∀ i x, x ∈ K i → ∃ a ∈ A i, ∃ b ∈ A i,
        dist a x = 1 / (i.1 + 1 : ℝ) ∧ u x - u a = 1 / (i.1 + 1 : ℝ) ∧
        dist x b = 1 / (i.1 + 1 : ℝ) ∧ u b - u x = 1 / (i.1 + 1 : ℝ) := by
  let S : ℕ → Set M := fun n ↦ calibratedReachLevel u (1 / (n + 1 : ℝ)) ∩
    calibratedReachLevel (-u) (1 / (n + 1 : ℝ))
  have hS (n : ℕ) : IsClosed (S n) :=
    (isClosed_calibratedReachLevel hu.continuous _).inter
      (isClosed_calibratedReachLevel hu.neg.continuous _)
  let K : ℕ × ℕ → Set M := fun i ↦ compactCovering M i.2 ∩ S i.1
  have hK (i : ℕ × ℕ) : IsCompact (K i) :=
    (isCompact_compactCovering M i.2).inter_right (hS i.1)
  refine ⟨K, fun i ↦ cthickening 1 (K i), fun i ↦ ⟨hK i, (hK i).cthickening⟩, ?_, ?_⟩
  · ext x
    rw [calibratedInterior_eq_iUnion_reachLevels hu hsegments]
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i.1, hxi.2⟩
    · intro hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      obtain ⟨m, hxm⟩ := exists_mem_compactCovering x
      exact mem_iUnion.mpr ⟨(n, m), hxm, hxn⟩
  · intro i x hx
    obtain ⟨⟨b, hdb, hb⟩, ⟨a, hda, ha⟩⟩ := hx.2
    have hr : 1 / (i.1 + 1 : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have hn : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
      linarith
    have haA : a ∈ cthickening 1 (K i) :=
      mem_cthickening_of_dist_le a x 1 (K i) hx (by rw [dist_comm, hda]; exact hr)
    have hbA : b ∈ cthickening 1 (K i) :=
      mem_cthickening_of_dist_le b x 1 (K i) hx (by rw [dist_comm, hdb]; exact hr)
    exact ⟨a, haA, b, hbA, by simpa only [dist_comm] using hda,
      by simpa only [Pi.neg_apply, neg_sub_neg] using ha, hdb, hb⟩

end OTSelector.Geometry

end
end
