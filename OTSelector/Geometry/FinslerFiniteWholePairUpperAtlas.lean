import OTSelector.Geometry.FinslerFiniteUpperSeedCubes
import OTSelector.Geometry.Finsler.FiniteRationalSeeds

/-!
# Finite actual upper seeds covering the full original calibrated population

Disjoint compact original supports provide the separation, finite calibrated
levels and finite C1,1 families. The same chosen sections supply exact endpoint
recovery and cube coordinates with one common quadratic upper bound.
-/

open Set Metric Manifold Bundle Module
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
universe u v
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The same finite actual seeds cover every original calibrated support pair
and have continuous injective labels in the common `(dim E - 1)`-cube. One
constant bounds all original costs with separated endpoint clocks. -/
theorem exists_finite_wholePair_upperAtlas (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instWholePairLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) :
    let _instWholePairMetric : MetricSpace M := F.metricSpace
    ∃ δ R C : ℝ, 0 < δ ∧ 0 < R ∧ 0 < C ∧
      (∀ x ∈ A, ∀ y ∈ B, δ ≤ dist x y) ∧
      ∃ ι : Type (max u v), Finite ι ∧ ∃ P : ι → CalibratedLevelSeedPatch F u,
        ∃ Q : ∀ i, (P i).covector.ker → Fin (Module.finrank ℝ E - 1) → Icc (0 : ℝ) 1,
          (∀ i, Continuous (Q i) ∧ InjOn (Q i) (P i).labels ∧
            ∀ x ∈ A ∪ B, |u x - ((P i).level : ℝ)| ≤ R) ∧
          (∀ x ∈ A, ∀ y ∈ B, u y - u x = dist x y →
            ∃ i, ∃ w ∈ (P i).labels,
              (P i).curve w (u x - ((P i).level : ℝ)) = x ∧
              (P i).curve w (u y - ((P i).level : ℝ)) = y ∧
              ∀ t ∈ Icc (u x - ((P i).level : ℝ)) (u y - ((P i).level : ℝ)),
                u ((P i).curve w t) = ((P i).level : ℝ) + t) ∧
          ∀ i, ∀ w ∈ (P i).labels, ∀ z ∈ (P i).labels,
            ∀ s t : ℝ, -R ≤ s → t ≤ R → δ / 2 ≤ t - s →
            (F.lengthEDist ((P i).curve w s) ((P i).curve z t)).toReal - (t - s) ≤
              C * ‖(fun j ↦ (Q i z j : ℝ)) - (fun j ↦ (Q i w j : ℝ))‖ ^ 2 := by
  classical
  let _instWholePairMetric : MetricSpace M := F.metricSpace
  obtain ⟨δ, hδ, hgap⟩ := Metric.exists_pos_forall_lt_edist hA hB.isClosed hAB
  have hδ' : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hgap' (x : M) (hx : x ∈ A) (y : M) (hy : y ∈ B) : (δ : ℝ) ≤ dist x y := by
    have h := hgap x hx y hy
    rw [edist_nndist, ENNReal.coe_lt_coe] at h
    exact_mod_cast h.le
  obtain ⟨levels, K₀, hK₀, hreach, hcross⟩ :=
    hF.exists_finite_calibrated_level_core hcomplete hu hA hδ'
  have htimeCompact : IsCompact
      ((fun p : ℝ × ℝ ↦ p.1 - p.2) ''
        ((u '' (A ∪ B)) ×ˢ ((fun q : ℚ ↦ (q : ℝ)) '' (levels : Set ℚ)))) :=
    (((hA.union hB).image hu.continuous).prod
      (levels.finite_toSet.image (fun q : ℚ ↦ (q : ℝ))).isCompact).image
        (continuous_fst.sub continuous_snd)
  obtain ⟨R, hR, htime⟩ := htimeCompact.isBounded.subset_closedBall_lt 0 0
  have htime' (q : ℚ) (hq : q ∈ levels) (x : M) (hx : x ∈ A ∪ B) :
      |u x - (q : ℝ)| ≤ R := by
    have ht := htime ⟨(u x, (q : ℝ)),
      ⟨mem_image_of_mem u hx, mem_image_of_mem _ hq⟩, rfl⟩
    simpa only [mem_closedBall, Real.dist_eq, sub_zero] using ht
  obtain ⟨κ, hκ, old, K, U, G, L, Γ, hdata, hcover, hpartners, hfamily⟩ :=
    hF.exists_finite_compact_C11_family_cover hcomplete hu hK₀
      (by positivity : 0 < (δ : ℝ) / 3) hreach
  let _instWholePairCoreFinite : Finite κ := hκ
  let Level := {q : ℚ // q ∈ levels}
  have hlocal (i : κ) (q : Level) :=
    hF.exists_finite_original_upperSeedCubes hcomplete (old i) (hdata i).1
      (hfamily i).1 (hfamily i).2.1 (hfamily i).2.2.1 hu
      (hdata i).2.2.1 (hdata i).2.2.2.2.1 (hdata i).2.2.2.2.2.2.1
      (hdata i).2.2.2.2.2.1 (hdata i).2.2.2.2.2.2.2
      (by positivity : 0 < (δ : ℝ) / 3) (hpartners i)
      (fun y hy ↦ ⟨((hfamily i).2.2.2 y hy).1,
        ((hfamily i).2.2.2 y hy).2.1, ((hfamily i).2.2.2 y hy).2.2.2⟩)
      (-R) R q.val (by positivity : 0 < (δ : ℝ) / 2)
  choose J hJ P Q C hC hPQ hImage hUpper using hlocal
  let _instWholePairPatchFinite (i : κ) (q : Level) : Finite (J i q) := hJ i q
  let ι := Σ i : κ, Σ q : Level, J i q
  let _instWholePairFintype : Fintype ι := Fintype.ofFinite ι
  let seed : ι → CalibratedLevelSeedPatch F u := fun i ↦ P i.1 i.2.1 i.2.2
  let cube (i : ι) := Q i.1 i.2.1 i.2.2
  let C₀ := (∑ i : ι, C i.1 i.2.1) + 1
  have hC₀ : 0 < C₀ := by
    have hsum : 0 ≤ ∑ i : ι, C i.1 i.2.1 :=
      Finset.sum_nonneg (fun i _ ↦ (hC i.1 i.2.1).le)
    dsimp only [C₀]
    linarith
  have hCle (i : ι) : C i.1 i.2.1 ≤ C₀ := by
    have hsum := Finset.single_le_sum (f := fun i : ι ↦ C i.1 i.2.1)
      (fun i _ ↦ (hC i.1 i.2.1).le) (Finset.mem_univ i)
    dsimp only [C₀]
    linarith
  have hseedCover : (⋃ i, (fun w ↦ (seed i).curve w 0) '' (seed i).labels) =
      {y | y ∈ K₀ ∧ ∃ q ∈ levels, u y = (q : ℝ)} := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      have hi' : y ∈ ⋃ j, (fun w ↦ (P i.1 i.2.1 j).curve w 0) ''
          (P i.1 i.2.1 j).labels := mem_iUnion.mpr ⟨i.2.2, hi⟩
      rw [hImage i.1 i.2.1] at hi'
      obtain ⟨x, hx, rfl⟩ := hi'
      refine ⟨?_, i.2.1.val, i.2.1.property, ?_⟩
      · rw [← hcover]
        exact mem_iUnion.mpr ⟨i.1, x, hx.1, rfl⟩
      · exact ((hdata i.1).2.2.2.2.2.1 hx.1).symm.trans hx.2
    · rintro y ⟨hy, q, hq, hyq⟩
      rw [← hcover] at hy
      obtain ⟨i, x, hx, hxy⟩ := mem_iUnion.mp hy
      let q' : Level := ⟨q, hq⟩
      have hxq : G i x = (q : ℝ) :=
        ((hdata i).2.2.2.2.2.1 hx).trans ((congrArg u hxy).trans hyq)
      have hy' : y ∈ ⋃ j, (fun w ↦ (P i q' j).curve w 0) '' (P i q' j).labels := by
        rw [hImage i q']
        exact ⟨x, ⟨hx, hxq⟩, hxy⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp hy'
      exact mem_iUnion.mpr ⟨⟨i, q', j⟩, hj⟩
  refine ⟨δ, R, C₀, hδ', hR, hC₀, hgap', ι, inferInstance, seed, cube, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hlevel, hcont, hinj⟩ := hPQ i.1 i.2.1 i.2.2
    refine ⟨hcont, hinj, fun x hx ↦ ?_⟩
    change |u x - ((P i.1 i.2.1 i.2.2).level : ℝ)| ≤ R
    rw [hlevel]
    exact htime' i.2.1.val i.2.1.property x hx
  · intro x hx y hy hsat
    have hxy : x ≠ y := dist_pos.mp (hδ'.trans_le (hgap' x hx y hy))
    obtain ⟨c, hc0, hcy, hc, _, hunit, _, _⟩ :=
      hF.exists_smooth_lengthMetric_minimizer hcomplete hxy
    have hca : u (c 0) = u x + 0 := by rw [hc0, add_zero]
    have hcb : u (c (dist x y)) = u x + dist x y := by rw [hcy]; linarith
    have hclock := (hF.calibrated_window_of_complete_unit_endpoints hu hc hunit hca hcb).1
    obtain ⟨q, hq, s, hs₁, hs₂, hsK, hslevel⟩ :=
      hcross c hc hunit 0 (dist x y) (u x) (hc0.symm ▸ hx)
        (by simpa only [sub_zero] using hgap' x hx y hy) hca hcb
    have hs : s ∈ Icc (0 : ℝ) (dist x y) := by constructor <;> linarith [hgap' x hx y hy]
    have hsSeed : c s ∈ ⋃ i, (fun w ↦ (seed i).curve w 0) '' (seed i).labels := by
      rw [hseedCover]
      exact ⟨hsK, q, hq, hslevel⟩
    obtain ⟨i, w, hw, hzero⟩ := mem_iUnion.mp hsSeed
    have heq : (seed i).curve w = fun t ↦ c (t + s) :=
      hF.seed_curve_eq_timeShift_of_calibrated_interval hcomplete hu (seed i) hw hc hunit
        (r := (δ : ℝ) / 3) (by positivity) (a := 0) (b := dist x y) (by
          intro t ht
          constructor <;> linarith [ht.1, ht.2, hgap' x hx y hy]) hclock hzero
    have hlevel : ((seed i).level : ℝ) = u x + s := by
      calc
        ((seed i).level : ℝ) = u ((seed i).curve w 0) := ((seed i).potential_initial hw).symm
        _ = u (c s) := by simp only [heq, zero_add]
        _ = u x + s := hclock s hs
    refine ⟨i, w, hw, ?_, ?_, ?_⟩
    · simp only [heq, hlevel]
      rw [show u x - (u x + s) + s = 0 by ring, hc0]
    · simp only [heq, hlevel]
      rw [show u y - (u x + s) + s = dist x y by linarith, hcy]
    · intro t ht
      rw [heq, hclock (t + s) (by constructor <;> linarith [ht.1, ht.2]), hlevel]
      ring
  · intro i w hw z hz s t hlo hhi hst
    exact (hUpper i.1 i.2.1 i.2.2 w hw z hz s t hlo hhi hst).trans
      (mul_le_mul_of_nonneg_right (hCle i) (sq_nonneg _))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
