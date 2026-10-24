import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Whitney covering construction

Main declarations: exists_whitney_ball_cover; exists_locallyFinite_whitney_cover.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.Cover`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** A nonempty closed set in a real normed space; the final constructed cover and packing/local-finiteness results use finite dimension. Basic distance-scale helpers use their weaker metric hypotheses.
* **Objects:** Capped radius min(1,dist(x,K)/16), a finite-color disjoint ball cover, locally finite doubled balls and a constructed enlarged-overlap bound.
* **Proof detail:** Use distance-to-set Lipschitz control for scale comparison; select disjoint color families by Besicovitch, estimate enlarged overlap by finite-dimensional packing, and use an enlargement margin for local finiteness.

## Mathematical sources

* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 472A–472B, pp. 19–21 (finite-color Besicovitch covering and packing).
  https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=19

**Relationship to the sources:** A ball-based Whitney decomposition. The original paper uses cubes; the cited Besicovitch proof supplies finite-color selection, while all displayed scale/packing constants are established locally.
-/

/-!
# A quantitative Whitney ball cover of the complement of a closed set

The radius is a capped fixed fraction of the actual distance to the closed set.
Besicovitch selection constructs finitely many colors of disjoint original balls.
Packing controls enlarged overlaps, and an enlargement margin proves local finiteness
on the complement. No covering, separation, or multiplicity bound is an input.
-/

open Set Metric Filter
open scoped Topology NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E]

/-- The positive scale used off the closed set, capped to meet the bounded-radius
hypothesis of the Besicovitch selection theorem. -/
def whitneyCoverRadius (K : Set E) (x : E) : ℝ := min 1 (infDist x K / 16)

/-- The radius is positive at every point outside a nonempty closed set. -/
theorem whitneyCoverRadius_pos {K : Set E} (hK : IsClosed K) (hne : K.Nonempty)
    {x : E} (hx : x ∉ K) : 0 < whitneyCoverRadius K x := by
  exact lt_min zero_lt_one (div_pos ((hK.notMem_iff_infDist_pos hne).mp hx) (by norm_num))

/-- The capped radius changes by at most one sixteenth of the center displacement. -/
theorem abs_whitneyCoverRadius_sub_le (K : Set E) (x y : E) :
    |whitneyCoverRadius K x - whitneyCoverRadius K y| ≤ dist x y / 16 := by
  have hm := abs_min_sub_min_le_max (1 : ℝ) (infDist x K / 16) 1 (infDist y K / 16)
  simp only [sub_self, abs_zero,
    max_eq_right (abs_nonneg (infDist x K / 16 - infDist y K / 16))] at hm
  have hd := (lipschitz_infDist_pt K).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hd
  change |min 1 (infDist x K / 16) - min 1 (infDist y K / 16)| ≤ _
  refine hm.trans ?_
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 16)).mpr hd

/-- Enlarged-ball incidence makes its center scale comparable to the evaluation scale. -/
theorem whitneyCoverRadius_comparable {K : Set E} {x c : E}
    (hx : x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)) :
    (4 / 5 : ℝ) * whitneyCoverRadius K x ≤ whitneyCoverRadius K c ∧
      whitneyCoverRadius K c ≤ (6 / 5 : ℝ) * whitneyCoverRadius K x := by
  have h := abs_whitneyCoverRadius_sub_le K x c
  have hlo := (abs_le.mp h).1
  have hhi := (abs_le.mp h).2
  have hd := mem_closedBall.mp hx
  constructor <;> linarith

/-- The doubled closed ball stays strictly outside the original closed set. -/
theorem whitneyCoverRadius_closedBall_subset {K : Set E} (hK : IsClosed K)
    (hne : K.Nonempty) {c : E} (hc : c ∉ K) :
    closedBall c (2 * whitneyCoverRadius K c) ⊆ Kᶜ := by
  have hr := whitneyCoverRadius_pos hK hne hc
  have hrδ : whitneyCoverRadius K c ≤ infDist c K / 16 := min_le_right _ _
  have hlt : 2 * whitneyCoverRadius K c < infDist c K := by linarith
  exact (closedBall_subset_ball hlt).trans ball_infDist_subset_compl

/-- The original distance to the closed set is comparable throughout a doubled ball. -/
theorem infDist_comparable_on_whitneyCoverRadius_ball {K : Set E} {x c : E}
    (hx : x ∈ closedBall c (2 * whitneyCoverRadius K c)) :
    (7 / 8 : ℝ) * infDist c K ≤ infDist x K ∧
      infDist x K ≤ (9 / 8 : ℝ) * infDist c K := by
  have h := (lipschitz_infDist_pt K).dist_le_mul x c
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  have hlo := (abs_le.mp h).1
  have hhi := (abs_le.mp h).2
  have hdist := mem_closedBall.mp hx
  have hr : whitneyCoverRadius K c ≤ infDist c K / 16 := min_le_right _ _
  constructor <;> linarith

variable [NormedSpace ℝ E]

private theorem separated_of_disjoint_closedBall {c d : E} {r s ρ : ℝ}
    (h : Disjoint (closedBall c r) (closedBall d s)) (hr : ρ ≤ r) (hs : ρ ≤ s) :
    2 * ρ < dist c d := by
  by_contra! hd
  have hm : dist (midpoint ℝ c d) c = (1 / 2 : ℝ) * dist c d := by
    simp [dist_midpoint_left]
  have hn : dist (midpoint ℝ c d) d = (1 / 2 : ℝ) * dist c d := by
    simp [dist_midpoint_right]
  exact Set.disjoint_left.mp h (show midpoint ℝ c d ∈ closedBall c r by
    rw [mem_closedBall, hm]; linarith) (show midpoint ℝ c d ∈ closedBall d s by
    rw [mem_closedBall, hn]; linarith)

private theorem card_enlarged_subfamily_le [FiniteDimensional ℝ E]
    {K S : Set E} {x : E} (hx : 0 < whitneyCoverRadius K x)
    (hdisj : S.PairwiseDisjoint (fun c ↦ closedBall c (whitneyCoverRadius K c)))
    (s : Finset E) (hs : (s : Set E) ⊆ S)
    (hcover : ∀ c ∈ s, x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)) :
    s.card ≤ 5 ^ Module.finrank ℝ E := by
  classical
  let R := whitneyCoverRadius K x
  let f : E → E := fun c ↦ (5 / (8 * R)) • (c - x)
  have hf : Function.Injective f := by
    intro c d hcd
    have hscalar : (5 / (8 * R) : ℝ) ≠ 0 := by dsimp [R]; positivity
    exact sub_left_injective (smul_right_injective E hscalar hcd)
  have hR : 0 < R := hx
  have hnorm : ∀ c ∈ s.image f, ‖c‖ ≤ 2 := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    have hcomp := (whitneyCoverRadius_comparable (hcover c hc)).2
    have hdist := mem_closedBall.mp (hcover c hc)
    have hcx : ‖c - x‖ ≤ 3 * R := by
      rw [← dist_eq_norm, dist_comm]
      dsimp [R]
      linarith
    dsimp [f]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 5 / (8 * R))]
    have hh := mul_le_mul_of_nonneg_left hcx (by positivity : 0 ≤ 5 / (8 * R))
    calc
      _ ≤ (5 / (8 * R)) * (3 * R) := hh
      _ ≤ 2 := by field_simp; nlinarith
  have hsep : ∀ c ∈ s.image f, ∀ d ∈ s.image f, c ≠ d → 1 ≤ ‖c - d‖ := by
    intro z hz w hw hzw
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
    have hcd : c ≠ d := fun heq ↦ hzw (congrArg f heq)
    have hsep := separated_of_disjoint_closedBall (hdisj (hs hc) (hs hd) hcd)
      (whitneyCoverRadius_comparable (hcover c hc)).1
      (whitneyCoverRadius_comparable (hcover d hd)).1
    have hnorm : (8 / 5 : ℝ) * R ≤ ‖c - d‖ := by
      rw [← dist_eq_norm]
      dsimp [R]
      linarith
    have heq : f c - f d = (5 / (8 * R)) • (c - d) := by
      dsimp [f]
      rw [← smul_sub]
      congr 1
      abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 5 / (8 * R))]
    calc
      1 = (5 / (8 * R)) * ((8 / 5) * R) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hc := (Besicovitch.card_le_multiplicity hnorm hsep).trans
    (Besicovitch.multiplicity_le (E := E))
  rwa [Finset.card_image_of_injective _ hf] at hc

private theorem enlarged_overlap_finite [FiniteDimensional ℝ E]
    {K S : Set E} {x : E} (hx : 0 < whitneyCoverRadius K x)
    (hdisj : S.PairwiseDisjoint (fun c ↦ closedBall c (whitneyCoverRadius K c))) :
    {c ∈ S | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}.Finite ∧
      {c ∈ S | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}.ncard ≤
        5 ^ Module.finrank ℝ E := by
  classical
  let A := {c ∈ S | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}
  have hb : ∀ s : Finset E, (s : Set E) ⊆ A → s.card ≤ 5 ^ Module.finrank ℝ E := by
    intro s hs
    exact card_enlarged_subfamily_le hx hdisj s (fun c hc ↦ (hs hc).1)
      (fun c hc ↦ (hs hc).2)
  have hA : A.Finite := by
    by_contra hi
    have hi' : A.Infinite := hi
    obtain ⟨s, hs, hc⟩ := hi'.exists_subset_card_eq (5 ^ Module.finrank ℝ E + 1)
    have h := hb s hs
    omega
  refine ⟨hA, ?_⟩
  change A.ncard ≤ _
  rw [Set.ncard_eq_toFinset_card A hA]
  exact hb hA.toFinset (by simp)

omit [NormedSpace ℝ E] in
private theorem enlarged_meets_nearby {K : Set E} {x y c : E}
    (hy : dist y x < whitneyCoverRadius K x / 8)
    (hc : y ∈ closedBall c (2 * whitneyCoverRadius K c)) :
    x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c) := by
  have ht : dist x c ≤ dist y x + 2 * whitneyCoverRadius K c := by
    calc
      _ ≤ dist x y + dist y c := dist_triangle x y c
      _ ≤ _ := by rw [dist_comm x y]; exact add_le_add le_rfl (mem_closedBall.mp hc)
  have h := (abs_le.mp (abs_whitneyCoverRadius_sub_le K x c)).2
  have hn := dist_nonneg (x := y) (y := c)
  have hrc := mem_closedBall.mp hc
  rw [mem_closedBall]
  linarith

private theorem locallyFinite_enlarged [FiniteDimensional ℝ E]
    {K S : Set E} (hK : IsClosed K) (hne : K.Nonempty)
    (hdisj : S.PairwiseDisjoint (fun c ↦ closedBall c (whitneyCoverRadius K c))) :
    LocallyFinite (fun c : S ↦
      {y : ↥(Kᶜ) | (y : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)}) := by
  intro x
  have hr := whitneyCoverRadius_pos hK hne x.property
  let A := {c ∈ S | (x : E) ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}
  have hA : A.Finite := (enlarged_overlap_finite hr hdisj).1
  refine ⟨ball x (whitneyCoverRadius K x / 8), ball_mem_nhds x (by positivity), ?_⟩
  have hp : (Subtype.val ⁻¹' A : Set S).Finite := hA.preimage Subtype.val_injective.injOn
  refine hp.subset ?_
  intro c hc
  obtain ⟨y, hy, hyx⟩ := hc
  exact ⟨c.property, enlarged_meets_nearby (mem_ball.mp hyx) hy⟩

/-- A genuine finite-color cover of the complement of a nonempty closed set. The
original balls cover, doubled supports stay in the complement and are locally finite
there, and each color has at most `5^dim E` enlarged overlaps at any point. -/
theorem exists_whitney_ball_cover [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsClosed K) (hne : K.Nonempty) :
    ∃ (N : ℕ) (S : Fin N → Set E),
      (∀ i, S i ⊆ Kᶜ) ∧
      (∀ i, (S i).PairwiseDisjoint (fun c ↦ closedBall c (whitneyCoverRadius K c))) ∧
      (Kᶜ ⊆ ⋃ i, ⋃ c ∈ S i, ball c (whitneyCoverRadius K c)) ∧
      (∀ i, ∀ c ∈ S i, closedBall c (2 * whitneyCoverRadius K c) ⊆ Kᶜ) ∧
      (∀ i, LocallyFinite (fun c : S i ↦
        {x : ↥(Kᶜ) | (x : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)})) ∧
      ∀ (x : E), x ∉ K → ∀ i,
        {c ∈ S i | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}.Finite ∧
        {c ∈ S i | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}.ncard ≤
          5 ^ Module.finrank ℝ E := by
  classical
  let q : Besicovitch.BallPackage ↥(Kᶜ) E :=
    { c := Subtype.val
      r := fun c ↦ whitneyCoverRadius K c
      rpos := fun c ↦ whitneyCoverRadius_pos hK hne c.property
      r_bound := 1
      r_le := fun _ ↦ min_le_left _ _ }
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := E)
  obtain ⟨s, hdisj, hcover⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  let S : Fin N → Set E := fun i ↦ Subtype.val '' s i
  have hS (i : Fin N) : S i ⊆ Kᶜ := by
    rintro c ⟨z, hz, rfl⟩
    exact z.property
  have hd (i : Fin N) : (S i).PairwiseDisjoint
      (fun c ↦ closedBall c (whitneyCoverRadius K c)) := by
    rintro c ⟨z, hz, rfl⟩ d ⟨w, hw, rfl⟩ hzw
    exact hdisj i hz hw (fun heq ↦ hzw (congrArg Subtype.val heq))
  refine ⟨N, S, hS, hd, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := hcover (show x ∈ range q.c from ⟨⟨x, hx⟩, rfl⟩)
    simp only [mem_iUnion] at h ⊢
    obtain ⟨i, z, hz, hball⟩ := h
    exact ⟨i, z, ⟨z, hz, rfl⟩, hball⟩
  · exact fun i c hc ↦ whitneyCoverRadius_closedBall_subset hK hne (hS i hc)
  · exact fun i ↦ locallyFinite_enlarged hK hne (hd i)
  · exact fun x hx i ↦ enlarged_overlap_finite (whitneyCoverRadius_pos hK hne hx) (hd i)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem ncard_finite_iUnion_le {N B : ℕ} (A : Fin N → Set E)
    (hA : ∀ i, (A i).Finite) (hcard : ∀ i, (A i).ncard ≤ B) :
    (⋃ i, A i).ncard ≤ N * B := by
  classical
  have hfin := Set.finite_iUnion hA
  have heq : hfin.toFinset = Finset.univ.biUnion (fun i ↦ (hA i).toFinset) := by
    ext x
    simp
  rw [Set.ncard_eq_toFinset_card _ hfin, heq]
  calc
    _ ≤ ∑ i : Fin N, (hA i).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ ↦ by
      simpa only [← Set.ncard_eq_toFinset_card _ (hA i)] using hcard i
    _ = N * B := by simp

/-- A single center set for subsequent locally finite gluing, with a constructed uniform
finite overlap bound. It is obtained by merging the finitely many disjoint colors. -/
theorem exists_locallyFinite_whitney_cover [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsClosed K) (hne : K.Nonempty) :
    ∃ (M : ℕ) (C : Set E), C ⊆ Kᶜ ∧
      (Kᶜ ⊆ ⋃ c ∈ C, ball c (whitneyCoverRadius K c)) ∧
      (∀ c ∈ C, closedBall c (2 * whitneyCoverRadius K c) ⊆ Kᶜ) ∧
      LocallyFinite (fun c : C ↦
        {x : ↥(Kᶜ) | (x : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)}) ∧
      ∀ (x : E), x ∉ K →
        {c ∈ C | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}.Finite ∧
        {c ∈ C | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}.ncard ≤ M := by
  classical
  obtain ⟨N, S, hS, _, hcover, hsub, _, hover⟩ := exists_whitney_ball_cover hK hne
  let C := ⋃ i, S i
  have hCS : C ⊆ Kᶜ := iUnion_subset hS
  have hpoint (x : E) (hx : x ∉ K) :
      {c ∈ C | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}.Finite ∧
      {c ∈ C | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}.ncard ≤
        N * 5 ^ Module.finrank ℝ E := by
    let A := fun i ↦ {c ∈ S i | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}
    have heq : {c ∈ C | x ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)} =
        ⋃ i, A i := by
      ext c
      simp only [C, A, mem_ofPred_eq, mem_iUnion, exists_and_right]
    rw [heq]
    exact ⟨Set.finite_iUnion (fun i ↦ (hover x hx i).1),
      ncard_finite_iUnion_le A (fun i ↦ (hover x hx i).1) (fun i ↦ (hover x hx i).2)⟩
  refine ⟨N * 5 ^ Module.finrank ℝ E, C, hCS, ?_, ?_, ?_, hpoint⟩
  · intro x hx
    obtain ⟨i, c, hc, hball⟩ := by simpa only [mem_iUnion] using hcover hx
    exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨mem_iUnion.mpr ⟨i, hc⟩, hball⟩⟩
  · intro c hc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    exact hsub i c hi
  · intro x
    have hr := whitneyCoverRadius_pos hK hne x.property
    let A := {c ∈ C | (x : E) ∈ closedBall c ((5 / 2 : ℝ) * whitneyCoverRadius K c)}
    have hA : A.Finite := (hpoint x x.property).1
    refine ⟨ball x (whitneyCoverRadius K x / 8), ball_mem_nhds x (by positivity), ?_⟩
    have hp : (Subtype.val ⁻¹' A : Set C).Finite := hA.preimage Subtype.val_injective.injOn
    refine hp.subset ?_
    intro c hc
    obtain ⟨y, hy, hyx⟩ := hc
    exact ⟨c.property, enlarged_meets_nearby (mem_ball.mp hyx) hy⟩

end OTSelector.Geometry

end
end
