import OTSelector.Geometry.Finsler.AffineTime
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FiniteLevelSeeds
import OTSelector.Geometry.Finsler.CalibratedClockShift
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.FiniteC11FamilyCover
import OTSelector.Geometry.Finsler.FiniteLevelCore
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.RationalLevelSeeds
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFiniteRationalSeeds.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFiniteRationalSeeds`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.FiniteRationalSeeds

* **Conditions:** A compact uniformly calibrated core and finitely many rational levels, or original compact separated supports.
* **Objects:** A finite family of actual level seeds covering the selected levels and representing every separated calibrated curve/pair by the same complete seed curve.
* **Proof detail:** Combine finite C1,1 core refinement with actual seed construction; identify curves by interior calibrated uniqueness and choose a rational middle level for every separated segment.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/realanal.pdf#page=31): Section 1.2.2, Theorem 1.2.4, p. 31.

Source relation (derived): A finite same-curve seed covering result; endpoint and full closed calibration identities are retained.
-/

/-!
# Finite original seeds on finitely many levels of a compact calibrated core

The finite C1,1 family cover and the existing actual seed constructor preserve
all original curves and cover every chosen level exactly.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
universe u v
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Finitely many actual seed patches cover exactly the prescribed finite set of
potential levels in the original compact core, retaining complete original curves. -/
theorem exists_finite_rational_levelSeedPatches (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instFiniteSeedsLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {A : Set M} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ)
    (hreach : let _instFiniteSeedsReach : MetricSpace M := F.metricSpace
      ∀ y ∈ A, ∃ a b : M, dist a y = δ ∧ u y - u a = δ ∧
        dist y b = δ ∧ u b - u y = δ) (Q : Finset ℚ) :
    ∃ κ : Type (max u v), Finite κ ∧ ∃ P : κ → CalibratedLevelSeedPatch F u,
      (∀ k, (P k).level ∈ Q) ∧
      (⋃ k, (fun w ↦ (P k).curve w 0) '' (P k).labels) =
        {y | y ∈ A ∧ ∃ q ∈ Q, u y = (q : ℝ)} := by
  classical
  let _instRationalSeedsMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hfinite, old, K, U, G, L, Γ, hdata, hcover, hpartners, hfamily⟩ :=
    hF.exists_finite_compact_C11_family_cover hcomplete hu hA hδ hreach
  let _instFiniteSeedsIndex : Finite ι := hfinite
  have hfinite (i : ι) (q : {q : ℚ // q ∈ Q}) :=
    hF.exists_finite_original_levelSeeds hcomplete (old i) (hdata i).1
      (hfamily i).1 (hfamily i).2.1 (hfamily i).2.2.1 hu
      (hdata i).2.2.1 (hdata i).2.2.2.2.2.1 (hdata i).2.2.2.2.2.2.1
      hδ (hpartners i) (q.val : ℝ)
  choose J a C σ hsection hslice using hfinite
  let H (i : ι) (q : {q : ℚ // q ∈ Q}) := K i ∩ {x | G i x = (q.val : ℝ)}
  let κ := Σ i : ι, Σ q : {q : ℚ // q ∈ Q}, {x : H i q // x ∈ J i q}
  have hpatch (k : κ) : ∃ A : CalibratedLevelSeedPatch F u, A.level = k.2.1.val ∧
      (fun w ↦ A.curve w 0) '' A.labels =
        (extChartAt 𝓘(ℝ, E) (old k.1)).symm ''
          (σ k.1 k.2.1 k.2.2.val ''
            (ball 0 (a k.1 k.2.1 k.2.2.val) ∩ (σ k.1 k.2.1 k.2.2.val) ⁻¹' K k.1)) := by
    obtain ⟨ha, hσ0, hσ, _, hσU, hGlevel, _, hσD, hinj, hdim, himm⟩ :=
      hsection k.1 k.2.1 k.2.2.val k.2.2.property
    exact hF.exists_levelSeedPatch_of_coreSection hcomplete (old k.1) hu
      (hdata k.1).1 (hfamily k.1).1 (hfamily k.1).2.1 (hfamily k.1).2.2.1
      (hdata k.1).2.2.1 (hdata k.1).2.2.2.2.1 (hdata k.1).2.2.2.2.2.2.1
      (hdata k.1).2.2.2.2.2.1 (hdata k.1).2.2.2.2.2.2.2
      (fun x hx ↦ ((hfamily k.1).2.2.2 x hx).2.1)
      (fun x hx ↦ ((hfamily k.1).2.2.2 x hx).1)
      (fun x hx ↦ ((hfamily k.1).2.2.2 x hx).2.2.2)
      hδ (hpartners k.1) isOpen_ball hσ hσU hinj hdim
      (Metric.mem_ball_self ha) (by rw [hσ0]; exact k.2.2.val.property.1)
      (by rw [hσ0]) hσD himm k.2.1.val hGlevel
  choose A hlevel himage using hpatch
  refine ⟨κ, inferInstance, A, fun k ↦ (hlevel k).symm ▸ k.2.1.property, ?_⟩
  apply Subset.antisymm
  · intro y hy
    obtain ⟨k, hy⟩ := mem_iUnion.mp hy
    rw [himage k] at hy
    obtain ⟨z, ⟨w, hw, rfl⟩, rfl⟩ := hy
    refine ⟨?_, k.2.1.val, k.2.1.property, ?_⟩
    · rw [← hcover]
      exact mem_iUnion.mpr ⟨k.1, σ k.1 k.2.1 k.2.2.val w, hw.2, rfl⟩
    · exact (hsection k.1 k.2.1 k.2.2.val k.2.2.property).2.2.2.2.2.2.1 w hw.1 hw.2
  · rintro y ⟨hy, q, hqQ, hq⟩
    let q' : {q : ℚ // q ∈ Q} := ⟨q, hqQ⟩
    rw [← hcover] at hy
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hy
    have hslicez : z ∈ K i ∩ {x | u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = (q : ℝ)} :=
      ⟨hz, hq⟩
    rw [hslice i q'] at hslicez
    obtain ⟨x, hx, w, hw, hwz⟩ := mem_iUnion₂.mp hslicez
    let k : κ := ⟨i, q', ⟨x, hx⟩⟩
    apply mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [himage k]
    exact ⟨z, ⟨w, hw, hwz⟩, rfl⟩



omit [BorelSpace E] in
/-- A retained original seed meeting a calibrated unit curve in its interior
recovers that entire complete curve with its actual time shift. -/
theorem seed_curve_eq_timeShift_of_calibrated_interval
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instFiniteSeedShiftLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) (P : CalibratedLevelSeedPatch F u)
    {w : P.covector.ker} (hw : w ∈ P.labels)
    {c : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    (hunit : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    {a b offset s r : ℝ} (hr : 0 < r)
    (hsub : Icc (s - r) (s + r) ⊆ Icc a b)
    (hclock : ∀ t ∈ Icc a b, u (c t) = offset + t)
    (hzero : P.curve w 0 = c s) : P.curve w = fun t ↦ c (t + s) := by
  let d : ℝ → M := fun t ↦ c (t + s)
  have hd : F.IsEulerLagrangeOn d univ := by
    simpa only [d, one_mul, sub_neg_eq_add, preimage_univ, Function.comp_def] using
      hF.isEulerLagrangeOn_affine hc (s := 1) (a := -s) zero_lt_one
  have hdunit (t : ℝ) :
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩) = 1 := by
    have hcDiff := (hF.contMDiffAt_of_isEulerLagrangeAt
      (hc (1 * (t - -s)) (mem_univ _))).mdifferentiableAt (by simp)
    have hs := F.speed_affine (s := 1) (a := -s) zero_lt_one hcDiff
    apply NNReal.coe_injective
    simpa only [d, one_mul, sub_neg_eq_add, Function.comp_def, hunit] using hs
  have hdclock : ∀ t ∈ Icc (-r) r, u (d t) = u (d 0) + t := by
    intro t ht
    have hts : t + s ∈ Icc a b := hsub ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hs : s ∈ Icc a b := hsub ⟨by linarith, by linarith⟩
    dsimp [d]
    rw [zero_add, hclock _ hts, hclock _ hs]
    ring
  have hPclock : ∀ t ∈ Icc (-P.reach) P.reach,
      u (P.curve w t) = u (P.curve w 0) + t := by
    rw [P.potential_initial hw]
    exact P.clock w hw
  have heq := hF.eq_timeShift_of_complete_unit_calibrated_clocks hcomplete hu
    hd (P.complete w hw) hdunit (P.unit w hw) hr P.reach_pos hdclock hPclock
    (s := 0) ⟨by linarith, hr⟩ (by simpa only [d, zero_add] using hzero)
  simpa only [d, add_zero] using heq

/-- Compact source support and one uniform separation give a finite family of
actual original seeds covering every complete calibrated segment, without loss. -/
theorem exists_finite_seed_cover_of_separated_calibrated_curves
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instFiniteCurveCoverLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {A : Set M} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ : Type (max u v), Finite κ ∧ ∃ P : κ → CalibratedLevelSeedPatch F u,
      ∀ (c : ℝ → M), F.IsEulerLagrangeOn c univ →
        (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1) →
        ∀ a b offset : ℝ, c a ∈ A → δ ≤ b - a →
          u (c a) = offset + a → u (c b) = offset + b →
          ∃ k, ∃ w ∈ (P k).labels, ∃ s : ℝ,
            a + δ / 3 < s ∧ s < a + 2 * δ / 3 ∧
            (P k).curve w = (fun t ↦ c (t + s)) := by
  let _instFiniteCurveCoverMetric : MetricSpace M := F.metricSpace
  obtain ⟨Q, K, hK, hreach, hcross⟩ :=
    hF.exists_finite_calibrated_level_core hcomplete hu hA hδ
  obtain ⟨κ, hfinite, P, _, hcover⟩ :=
    hF.exists_finite_rational_levelSeedPatches hcomplete hu hK
      (by positivity : 0 < δ / 3) hreach Q
  refine ⟨κ, hfinite, P, ?_⟩
  intro c hc hunit a b offset hca hgap ha hb
  obtain ⟨q, hq, s, hs₁, hs₂, hsK, hslevel⟩ := hcross c hc hunit a b offset hca hgap ha hb
  have hmem : c s ∈ ⋃ k, (fun w ↦ (P k).curve w 0) '' (P k).labels := by
    rw [hcover]
    exact ⟨hsK, q, hq, hslevel⟩
  obtain ⟨k, w, hw, hzero⟩ := mem_iUnion.mp hmem
  refine ⟨k, w, hw, s, hs₁, hs₂, ?_⟩
  apply hF.seed_curve_eq_timeShift_of_calibrated_interval hcomplete hu (P k) hw hc hunit
    (r := δ / 3) (by positivity) (a := a) (b := b) (offset := offset) ?_
    (hF.calibrated_window_of_complete_unit_endpoints hu hc hunit ha hb).1 hzero
  intro t ht
  constructor <;> linarith [ht.1, ht.2]


/-- A compact original source carrier and a positive distance gap give finitely
many actual seeds recovering both endpoints of every calibrated pair. Endpoint
differentiability and a preassigned atlas are unnecessary. -/
theorem exists_finite_seed_cover_of_separated_calibrated_pairs
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instFinitePairCoverLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {A : Set M} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ) :
    let _instFinitePairCoverMetric : MetricSpace M := F.metricSpace
    ∃ κ : Type (max u v), Finite κ ∧ ∃ P : κ → CalibratedLevelSeedPatch F u,
      ∀ x ∈ A, ∀ y : M, δ ≤ dist x y → u y - u x = dist x y →
        ∃ k, ∃ w ∈ (P k).labels,
          (P k).curve w (u x - ((P k).level : ℝ)) = x ∧
          (P k).curve w (u y - ((P k).level : ℝ)) = y ∧
          ∀ t ∈ Icc (u x - ((P k).level : ℝ)) (u y - ((P k).level : ℝ)),
            u ((P k).curve w t) = ((P k).level : ℝ) + t := by
  let _instFinitePairCoverMetric : MetricSpace M := F.metricSpace
  obtain ⟨κ, hfinite, P, hcover⟩ :=
    hF.exists_finite_seed_cover_of_separated_calibrated_curves hcomplete hu hA hδ
  refine ⟨κ, hfinite, P, ?_⟩
  intro x hx y hgap hsat
  have hxy : x ≠ y := dist_pos.mp (hδ.trans_le hgap)
  obtain ⟨c, hc0, hcy, hc, _, hunit, _, _⟩ :=
    hF.exists_smooth_lengthMetric_minimizer hcomplete hxy
  have hca : u (c 0) = u x + 0 := by rw [hc0, add_zero]
  have hcb : u (c (dist x y)) = u x + dist x y := by rw [hcy]; linarith
  have hclock := (hF.calibrated_window_of_complete_unit_endpoints hu hc hunit hca hcb).1
  obtain ⟨k, w, hw, s, hs₁, hs₂, heq⟩ := hcover c hc hunit 0 (dist x y) (u x)
    (hc0.symm ▸ hx) (by simpa only [sub_zero] using hgap) hca hcb
  have hs : s ∈ Icc (0 : ℝ) (dist x y) := by constructor <;> linarith
  have hlevel : ((P k).level : ℝ) = u x + s := by
    calc
      ((P k).level : ℝ) = u ((P k).curve w 0) := ((P k).potential_initial hw).symm
      _ = u (c s) := by simp only [heq, zero_add]
      _ = u x + s := hclock s hs
  refine ⟨k, w, hw, ?_, ?_, ?_⟩
  · simp only [heq, hlevel]
    rw [show u x - (u x + s) + s = 0 by ring, hc0]
  · simp only [heq, hlevel]
    rw [show u y - (u x + s) + s = dist x y by linarith, hcy]
  · intro t ht
    rw [heq, hclock (t + s) (by constructor <;> linarith [ht.1, ht.2]), hlevel]
    ring


/-- Disjoint compact original supports supply the positive separation used by
the finite whole-segment seed cover. No distance-gap parameter is assumed. -/
theorem exists_finite_seed_cover_of_disjoint_compact_supports
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instFiniteSupportsLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) :
    let _instFiniteSupportsMetric : MetricSpace M := F.metricSpace
    ∃ δ : ℝ, 0 < δ ∧ (∀ x ∈ A, ∀ y ∈ B, δ ≤ dist x y) ∧
      ∃ κ : Type (max u v), Finite κ ∧ ∃ P : κ → CalibratedLevelSeedPatch F u,
        ∀ x ∈ A, ∀ y ∈ B, u y - u x = dist x y →
          ∃ k, ∃ w ∈ (P k).labels,
            (P k).curve w (u x - ((P k).level : ℝ)) = x ∧
            (P k).curve w (u y - ((P k).level : ℝ)) = y ∧
            ∀ t ∈ Icc (u x - ((P k).level : ℝ)) (u y - ((P k).level : ℝ)),
              u ((P k).curve w t) = ((P k).level : ℝ) + t := by
  let _instFiniteSupportsMetric : MetricSpace M := F.metricSpace
  obtain ⟨δ, hδ, hgap⟩ := Metric.exists_pos_forall_lt_edist hA hB.isClosed hAB
  have hgap' (x : M) (hx : x ∈ A) (y : M) (hy : y ∈ B) : (δ : ℝ) ≤ dist x y := by
    have h := hgap x hx y hy
    rw [edist_nndist, ENNReal.coe_lt_coe] at h
    exact_mod_cast h.le
  obtain ⟨κ, hfinite, P, hP⟩ := hF.exists_finite_seed_cover_of_separated_calibrated_pairs
    hcomplete hu hA (NNReal.coe_pos.mpr hδ)
  exact ⟨δ, NNReal.coe_pos.mpr hδ, hgap', κ, hfinite, P,
    fun x hx y hy hsat ↦ hP x hx y (hgap' x hx y hy) hsat⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
