import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
## Lemma skeleton

* **Conditions:** Finite real coordinate products, a positive cell length L and positive natural number m for probability/decomposition results; the floor and coordinate definitions exist for every L.
* **Objects:** A uniform cube decomposes exactly into a uniform grid label and an independent uniform local cube position.
* **Proof detail:** In one dimension split (0,m L) into half-open floor blocks, translate each block to the local interval and sum its Dirac-label product law. Normalize, take finite products and regroup coordinates. Endpoints are Lebesgue-null.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 441A (invariant measure definition) and 441J (integration under an invariant action), pp. 2 and 6; Section 443A, pp. 19–20 (Haar measurability).
  https://www1.essex.ac.uk/maths/people/fremlin/chap44.pdf#page=6
* D. H. Fremlin, *Measure Theory, Volume 2*, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19

**Relationship to the sources:** Concrete floor/block implementation of translation-invariant product volume. The independent label/local law is proved as an exact pushforward identity, not assumed. Positivity is imposed only on the probability and transport statements.
-/

/-!
# Decomposition of a cube into equal subcubes

This file formalizes the spatial half of the finite-volume pressure block comparison:
the uniform law on a cube of side length `m * L` is the image of the product of the
uniform block label and the uniform local position, and the local position is
independent of the label.

The one-dimensional block map sends `x` to `(⌊x / L⌋₊, x - ⌊x / L⌋₊ * L)`.  On the
`b`-th block `[bL, (b+1)L)` it is the affine map `x ↦ (b, x - bL)`, so Lebesgue
measure restricted to the block pushes forward to `dirac b` times Lebesgue measure
on `[0, L)`.  Summing these identities over the blocks and normalizing gives the
one-dimensional decomposition.  Taking finite products yields the corresponding
decomposition of an `ι`-indexed cube, and for `ι = Fin q` the cube measure is the
normalized restriction of Lebesgue measure to `[0, L)^q`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace OTSelector.Probability

/-- The index of the block of mesh `L` containing `x`, i.e. `⌊x / L⌋₊`. -/
noncomputable def blockIndex (L : ℝ) (x : ℝ) : ℕ := ⌊x / L⌋₊

/-- The local coordinate of `x` inside its block of mesh `L`, i.e. `x - bL` where
`b = blockIndex L x`. -/
noncomputable def localCoord (L : ℝ) (x : ℝ) : ℝ := x - (blockIndex L x : ℝ) * L

theorem measurable_blockIndex (L : ℝ) : Measurable (blockIndex L) := by
  unfold blockIndex
  fun_prop

theorem measurable_localCoord (L : ℝ) : Measurable (localCoord L) := by
  unfold localCoord
  have hnat : Measurable (fun n : ℕ => (n : ℝ)) := measurable_of_countable _
  exact measurable_id.sub ((hnat.comp (measurable_blockIndex L)).mul_const L)

theorem measurable_block_local (L : ℝ) :
    Measurable (fun x : ℝ => (blockIndex L x, localCoord L x)) :=
  (measurable_blockIndex L).prodMk (measurable_localCoord L)

/-- The `b`-th block `[bL, (b+1)L)` of the grid of mesh `L`. -/
def blockRange (L : ℝ) (b : ℕ) : Set ℝ :=
  Set.Ico ((b : ℝ) * L) (((b : ℝ) + 1) * L)

/-- On the `b`-th block, the block map is `x ↦ (b, x - bL)`.  The intersection with
`[0, ∞)` is necessary because `Nat.floor` maps negative arguments to `0`. -/
theorem preimage_block_local (hL : 0 < L) (b : ℕ) (s : Set ℝ) :
    (fun x : ℝ => (blockIndex L x, localCoord L x)) ⁻¹' ({b} ×ˢ s) ∩ Set.Ici (0 : ℝ)
      = (fun y : ℝ => y + (b : ℝ) * L) '' s ∩ blockRange L b := by
  ext x
  simp only [blockRange, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
    Set.mem_singleton_iff, Set.mem_Ici, Set.mem_image, Set.mem_Ico]
  constructor
  · rintro ⟨⟨hb, hs⟩, hx0⟩
    refine ⟨⟨x - (b : ℝ) * L, ?_, by ring⟩, ?_, ?_⟩
    · simpa [localCoord, hb] using hs
    · have h := Nat.floor_le (div_nonneg hx0 hL.le)
      unfold blockIndex at hb
      rw [hb] at h
      rwa [le_div_iff₀ hL] at h
    · have h := Nat.lt_floor_add_one (x / L)
      unfold blockIndex at hb
      rw [hb] at h
      rw [div_lt_iff₀ hL] at h
      exact h
  · rintro ⟨⟨y, hy, hxy⟩, hb0, hb1⟩
    have hx_eq : x = y + (b : ℝ) * L := hxy.symm
    have hx0 : 0 ≤ x := by
      rw [hx_eq]
      have hb0' : 0 ≤ (b : ℝ) * L := mul_nonneg (Nat.cast_nonneg b) hL.le
      linarith
    have hdiv0 : 0 ≤ x / L := div_nonneg hx0 hL.le
    have hfloor : blockIndex L x = b := by
      unfold blockIndex
      rw [Nat.floor_eq_iff hdiv0]
      constructor
      · rw [le_div_iff₀ hL]; exact hb0
      · rw [div_lt_iff₀ hL]; exact hb1
    refine ⟨?_, hx0⟩
    refine ⟨hfloor, ?_⟩
    unfold localCoord
    rw [hfloor, hx_eq]
    convert hy using 2
    ring

private lemma map_block_local_single (hL : 0 < L) (b : ℕ) :
    (volume.restrict (blockRange L b)).map
        (fun x : ℝ => (blockIndex L x, localCoord L x))
      = (Measure.dirac b).prod (volume.restrict (Set.Ioo (0 : ℝ) L)) := by
  have hshift : Measurable (fun y : ℝ => y + (b : ℝ) * L) := measurable_add_const _
  have htrans : volume.restrict (blockRange L b)
      = (volume.restrict (Set.Ico (0 : ℝ) L)).map (fun y : ℝ => y + (b : ℝ) * L) := by
    ext u hu
    rw [Measure.map_apply hshift hu, Measure.restrict_apply hu,
      Measure.restrict_apply (hshift hu)]
    have himg : (fun y : ℝ => y + (b : ℝ) * L) ''
          ((fun y : ℝ => y + (b : ℝ) * L) ⁻¹' u ∩ Set.Ico (0 : ℝ) L)
        = u ∩ blockRange L b := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, blockRange, Set.mem_Ico]
      constructor
      · rintro ⟨y, ⟨hyu, hy0, hyL⟩, hyx⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [← hyx]; simpa using hyu
        · rw [← hyx]
          have hb0' : 0 ≤ (b : ℝ) * L := mul_nonneg (Nat.cast_nonneg b) hL.le
          linarith
        · rw [← hyx]; nlinarith
      · rintro ⟨hxu, hb0, hb1⟩
        refine ⟨x - (b : ℝ) * L, ⟨?_, ?_, ?_⟩, by ring⟩
        · convert hxu using 2
          ring
        · linarith
        · nlinarith
    rw [← himg, Set.image_add_right]
    exact measure_preimage_add_right volume (-((b : ℝ) * L)) _
  rw [htrans, Measure.map_map (measurable_block_local L) hshift]
  have hae : (fun y : ℝ => (blockIndex L (y + (b : ℝ) * L),
        localCoord L (y + (b : ℝ) * L)))
      =ᵐ[volume.restrict (Set.Ico (0 : ℝ) L)] (fun y => (b, y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    have hy0 : 0 ≤ y := hy.1
    have hyL : y < L := hy.2
    have hx0 : 0 ≤ y + (b : ℝ) * L := by
      have hb0' : 0 ≤ (b : ℝ) * L := mul_nonneg (Nat.cast_nonneg b) hL.le
      linarith
    have hfloor : blockIndex L (y + (b : ℝ) * L) = b := by
      unfold blockIndex
      rw [Nat.floor_eq_iff (div_nonneg hx0 hL.le)]
      constructor
      · rw [le_div_iff₀ hL]
        have hb0' : 0 ≤ (b : ℝ) * L := mul_nonneg (Nat.cast_nonneg b) hL.le
        linarith
      · rw [div_lt_iff₀ hL]
        nlinarith
    refine Prod.ext hfloor ?_
    unfold localCoord
    rw [hfloor]
    ring
  change Measure.map (fun y : ℝ => (blockIndex L (y + (b : ℝ) * L),
      localCoord L (y + (b : ℝ) * L))) (volume.restrict (Set.Ico (0 : ℝ) L)) =
    (Measure.dirac b).prod (volume.restrict (Set.Ioo (0 : ℝ) L))
  rw [Measure.map_congr hae]
  rw [show (fun y : ℝ => (b, y)) = Prod.mk b from rfl]
  rw [← Measure.dirac_prod]
  rw [restrict_Ioo_eq_restrict_Ico]

/-! ### Decomposing an interval into blocks -/


private lemma blockRange_subset_Ico (hL : 0 < L) {m b : ℕ} (hb : b < m) :
    blockRange L b ⊆ Set.Ico (0 : ℝ) ((m : ℝ) * L) := by
  intro x hx
  simp only [blockRange, Set.mem_Ico] at hx ⊢
  constructor
  · have hb0 : 0 ≤ (b : ℝ) * L := mul_nonneg (Nat.cast_nonneg b) hL.le
    linarith [hx.1]
  · have hbm : (b : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hb
    have hmul : ((b : ℝ) + 1) * L ≤ (m : ℝ) * L := mul_le_mul_of_nonneg_right hbm hL.le
    linarith [hx.2]

private lemma blockRange_disjoint_Ico_of_le (hL : 0 < L) {m b : ℕ} (hb : m ≤ b) :
    blockRange L b ∩ Set.Ico (0 : ℝ) ((m : ℝ) * L) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [Set.mem_inter_iff, blockRange, Set.mem_Ico] at hx
  obtain ⟨⟨hb0, hb1⟩, hT0, hT1⟩ := hx
  have hmb : (m : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hmul : (m : ℝ) * L ≤ (b : ℝ) * L := mul_le_mul_of_nonneg_right hmb hL.le
  linarith

/-- Decomposition of unnormalized Lebesgue measure on `(0, mL)` under the block map:
the block label is distributed as the sum of the Dirac masses at `0, …, m-1`, and
the local coordinate is Lebesgue measure restricted to `(0, L)`. -/
theorem map_block_local_restrict (m : ℕ) (hm : 0 < m) (hL : 0 < L) :
    (volume.restrict (Set.Ioo (0 : ℝ) ((m : ℝ) * L))).map
        (fun x : ℝ => (blockIndex L x, localCoord L x))
      = (Measure.sum (fun b : ℕ => if b < m then Measure.dirac b else 0)).prod
          (volume.restrict (Set.Ioo (0 : ℝ) L)) := by
  classical
  have _hmpos := hm
  set T : Set ℝ := Set.Ico (0 : ℝ) ((m : ℝ) * L) with hT_def
  set s : ℕ → Set ℝ := fun b => blockRange L b ∩ T with hs_def
  have hmeasT : MeasurableSet T := measurableSet_Ico
  have hmeas : ∀ b, MeasurableSet (s b) := fun b => (measurableSet_Ico).inter hmeasT
  have hdisj : Pairwise fun b₁ b₂ => Disjoint (s b₁) (s b₂) := by
    intro b₁ b₂ hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [Set.disjoint_left]
      intro x hx hy
      simp only [s, Set.mem_inter_iff, blockRange, Set.mem_Ico] at hx hy
      have hbm : (b₁ : ℝ) + 1 ≤ (b₂ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      have hmul : ((b₁ : ℝ) + 1) * L ≤ (b₂ : ℝ) * L := mul_le_mul_of_nonneg_right hbm hL.le
      linarith [hx.1.2, hy.1.1]
    · rw [Set.disjoint_left]
      intro x hx hy
      simp only [s, Set.mem_inter_iff, blockRange, Set.mem_Ico] at hx hy
      have hbm : (b₂ : ℝ) + 1 ≤ (b₁ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      have hmul : ((b₂ : ℝ) + 1) * L ≤ (b₁ : ℝ) * L := mul_le_mul_of_nonneg_right hbm hL.le
      linarith [hx.1.1, hy.1.2]
  have hunion : (⋃ b, s b) = T := by
    apply le_antisymm
    · exact Set.iUnion_subset fun b => Set.inter_subset_right
    · intro x hx
      simp only [Set.mem_iUnion]
      have hx' : 0 ≤ x ∧ x < (m : ℝ) * L := by
        simpa only [hT_def, Set.mem_Ico] using hx
      refine ⟨blockIndex L x, ?_, hx⟩
      simp only [blockRange, Set.mem_Ico]
      constructor
      · have h := Nat.floor_le (div_nonneg hx'.1 hL.le)
        unfold blockIndex
        rwa [le_div_iff₀ hL] at h
      · have h := Nat.lt_floor_add_one (x / L)
        unfold blockIndex
        rw [div_lt_iff₀ hL] at h
        exact h
  have hpart : volume.restrict T = Measure.sum (fun b => volume.restrict (s b)) := by
    rw [← hunion]
    exact Measure.restrict_iUnion hdisj hmeas
  have hSFinite : SFinite (volume.restrict (Set.Ioo (0 : ℝ) L)) := inferInstance
  have hSFiniteI := hSFinite
  calc
    (volume.restrict (Set.Ioo (0 : ℝ) ((m : ℝ) * L))).map
          (fun x : ℝ => (blockIndex L x, localCoord L x))
        = (volume.restrict T).map (fun x : ℝ => (blockIndex L x, localCoord L x)) := by
          rw [hT_def, restrict_Ioo_eq_restrict_Ico]
    _ = (Measure.sum (fun b => volume.restrict (s b))).map
          (fun x : ℝ => (blockIndex L x, localCoord L x)) := by rw [hpart]
    _ = Measure.sum (fun b => (volume.restrict (s b)).map
          (fun x : ℝ => (blockIndex L x, localCoord L x))) := by
          rw [Measure.map_sum (measurable_block_local L).aemeasurable]
    _ = Measure.sum (fun b : ℕ => if b < m then
          (volume.restrict (blockRange L b)).map
            (fun x : ℝ => (blockIndex L x, localCoord L x)) else 0) := by
          apply Measure.sum_congr
          intro b
          by_cases hb : b < m
          · simp only [hb, ite_true]
            have hsub : s b = blockRange L b := by
              rw [hs_def, hT_def]
              exact Set.inter_eq_left.mpr (blockRange_subset_Ico hL hb)
            rw [hsub]
          · simp only [hb, ite_false]
            have hsub : s b = ∅ := by
              rw [hs_def, hT_def]
              exact blockRange_disjoint_Ico_of_le hL (Nat.le_of_not_lt hb)
            rw [hsub, Measure.restrict_empty]
            simp
    _ = Measure.sum (fun b : ℕ => if b < m then
          (Measure.dirac b).prod (volume.restrict (Set.Ioo (0 : ℝ) L)) else 0) := by
          apply Measure.sum_congr
          intro b
          by_cases hb : b < m
          · simp only [hb, ite_true]
            rw [map_block_local_single hL b]
          · simp only [hb, ite_false]
    _ = Measure.sum (fun b : ℕ => (if b < m then Measure.dirac b else 0).prod
          (volume.restrict (Set.Ioo (0 : ℝ) L))) := by
          apply Measure.sum_congr
          intro b
          by_cases hb : b < m <;> simp [hb]
    _ = (Measure.sum (fun b : ℕ => if b < m then Measure.dirac b else 0)).prod
          (volume.restrict (Set.Ioo (0 : ℝ) L)) := by
          rw [Measure.prod_sum_left]


/-- The uniform probability measure on the interval `(0, L)`. -/
noncomputable def uniformInterval (L : ℝ) : Measure ℝ :=
  (volume (Set.Ioo (0 : ℝ) L))⁻¹ • volume.restrict (Set.Ioo (0 : ℝ) L)

/-- The uniform probability measure on `{0, …, m-1}`. -/
noncomputable def uniformGrid (m : ℕ) : Measure ℕ :=
  ((m : ℝ≥0∞)⁻¹) • Measure.sum (fun b : ℕ => if b < m then Measure.dirac b else 0)

theorem isProbabilityMeasure_uniformInterval {L : ℝ} (hL : 0 < L) :
    IsProbabilityMeasure (uniformInterval L) := by
  constructor
  rw [uniformInterval, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioo, sub_zero]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hL).ne' ENNReal.ofReal_ne_top

private theorem tsum_ite_lt (m : ℕ) :
    (∑' b : ℕ, (if b < m then (1 : ℝ≥0∞) else 0)) = (m : ℝ≥0∞) := by
  rw [tsum_eq_sum (s := Finset.range m) ?_]
  · have h : ∀ b ∈ Finset.range m, (if b < m then (1 : ℝ≥0∞) else 0) = 1 := by
      intro b hb
      simp only [Finset.mem_range.mp hb, ite_true]
    rw [Finset.sum_congr rfl h]
    simp
  · intro b hb
    simp only [Finset.mem_range, not_lt] at hb
    simp [hb]

theorem isProbabilityMeasure_uniformGrid {m : ℕ} (hm : 0 < m) :
    IsProbabilityMeasure (uniformGrid m) := by
  constructor
  rw [uniformGrid, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ MeasurableSet.univ]
  have hsum : (∑' b : ℕ, (if b < m then Measure.dirac b else 0 : Measure ℕ) Set.univ)
      = (m : ℝ≥0∞) := by
    have hterm : ∀ b : ℕ,
        (if b < m then Measure.dirac b else 0 : Measure ℕ) Set.univ = if b < m then 1 else 0 := by
      intro b
      by_cases hb : b < m <;> simp [hb]
    simp only [hterm]
    exact tsum_ite_lt m
  rw [hsum]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hm.ne') (ENNReal.natCast_ne_top m)


/-- The uniform law on `(0, mL)` splits into the uniform block label on
`{0, …, m-1}` and the uniform local position on `(0, L)`. -/
theorem map_block_local_uniformInterval (m : ℕ) (hm : 0 < m) (hL : 0 < L) :
    (uniformInterval ((m : ℝ) * L)).map
        (fun x : ℝ => (blockIndex L x, localCoord L x))
      = (uniformGrid m).prod (uniformInterval L) := by
  have hcML : volume (Set.Ioo (0 : ℝ) ((m : ℝ) * L)) =
      (m : ℝ≥0∞) * volume (Set.Ioo (0 : ℝ) L) := by
    rw [Real.volume_Ioo, Real.volume_Ioo, sub_zero]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
    congr 1
    ring
  have hcL0 : volume (Set.Ioo (0 : ℝ) L) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hL).ne'
  have hinv : (volume (Set.Ioo (0 : ℝ) ((m : ℝ) * L)))⁻¹ =
      (m : ℝ≥0∞)⁻¹ * (volume (Set.Ioo (0 : ℝ) L))⁻¹ := by
    rw [hcML, ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr hm.ne'))
      (Or.inl (ENNReal.natCast_ne_top m))]
  have hBfin : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) L)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioo,
      sub_zero]; exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top⟩
  have hBfinI := hBfin
  have hBs : SFinite (volume.restrict (Set.Ioo (0 : ℝ) L)) := inferInstance
  have hBsI := hBs
  have heB : SFinite ((volume (Set.Ioo (0 : ℝ) L))⁻¹ •
      volume.restrict (Set.Ioo (0 : ℝ) L)) := by
    have hfin : IsFiniteMeasure ((volume (Set.Ioo (0 : ℝ) L))⁻¹ •
        volume.restrict (Set.Ioo (0 : ℝ) L)) :=
      Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hcL0)
    infer_instance
  have heBI := heB
  simp only [uniformInterval, uniformGrid]
  rw [Measure.map_smul, map_block_local_restrict m hm hL, hinv]
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

/-- The uniform probability measure on the cube `(0, L)^ι`. -/
noncomputable def cubeMeasure (ι : Type*) [Fintype ι] (L : ℝ) : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => uniformInterval L)

/-- The coordinatewise block map on `(ι → ℝ)`. -/
noncomputable def blockMap (ι : Type*) [Fintype ι] (L : ℝ) (x : ι → ℝ) :
    (ι → ℕ) × (ι → ℝ) :=
  (fun i => blockIndex L (x i), fun i => localCoord L (x i))

/-- The uniform probability measure on the grid `{0, …, m-1}^ι`. -/
noncomputable def gridMeasure (ι : Type*) [Fintype ι] (m : ℕ) : Measure (ι → ℕ) :=
  Measure.pi (fun _ : ι => uniformGrid m)

/-- The uniform measure on the cube `(0, L)^ι` is a probability measure. -/
theorem isProbabilityMeasure_cubeMeasure {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) :
    IsProbabilityMeasure (cubeMeasure ι L) := by
  have h : IsProbabilityMeasure (uniformInterval L) := isProbabilityMeasure_uniformInterval hL
  constructor
  rw [cubeMeasure, Measure.pi_univ]
  simp [measure_univ]

/-- Coordinatewise decomposition of the uniform law on the cube `(0, mL)^ι`: the
block-label vector and the local-position vector are independent, with laws
`gridMeasure ι m` and `cubeMeasure ι L`. -/
theorem map_blockMap_cubeMeasure {ι : Type*} [Fintype ι] (m : ℕ) (hm : 0 < m) (hL : 0 < L) :
    (cubeMeasure ι ((m : ℝ) * L)).map (blockMap ι L)
      = (gridMeasure ι m).prod (cubeMeasure ι L) := by
  classical
  have hmL : 0 < (m : ℝ) * L := mul_pos (Nat.cast_pos.mpr hm) hL
  have hprobML : IsProbabilityMeasure (uniformInterval ((m : ℝ) * L)) :=
    isProbabilityMeasure_uniformInterval hmL
  have hprobGrid : IsProbabilityMeasure (uniformGrid m) := isProbabilityMeasure_uniformGrid hm
  have hprobL : IsProbabilityMeasure (uniformInterval L) := isProbabilityMeasure_uniformInterval hL
  have hF : Measurable (fun x : ι → ℝ => fun i => (blockIndex L (x i), localCoord L (x i))) :=
    measurable_pi_lambda _ fun i => (measurable_block_local L).comp (measurable_pi_apply i)
  have hpi : (Measure.pi (fun _ : ι => uniformInterval ((m : ℝ) * L))).map
        (fun x : ι → ℝ => fun i => (blockIndex L (x i), localCoord L (x i)))
      = Measure.pi (fun _ : ι => (uniformGrid m).prod (uniformInterval L)) := by
    have h := Measure.pi_map_pi (μ := fun _ : ι => uniformInterval ((m : ℝ) * L))
      (f := fun _ (x : ℝ) => (blockIndex L x, localCoord L x))
      (fun _ => (measurable_block_local L).aemeasurable)
    simpa only [map_block_local_uniformInterval m hm hL] using h
  have hE : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℕ ℝ ι)
      (Measure.pi (fun _ : ι => (uniformGrid m).prod (uniformInterval L)))
      ((gridMeasure ι m).prod (cubeMeasure ι L)) :=
    measurePreserving_arrowProdEquivProdArrow ℕ ℝ ι
      (fun _ => uniformGrid m) (fun _ => uniformInterval L)
  have hcomp : blockMap ι L =
      (MeasurableEquiv.arrowProdEquivProdArrow ℕ ℝ ι) ∘
        (fun x : ι → ℝ => fun i => (blockIndex L (x i), localCoord L (x i))) := by
    funext x
    rfl
  calc
    (cubeMeasure ι ((m : ℝ) * L)).map (blockMap ι L)
        = (Measure.pi (fun _ : ι => uniformInterval ((m : ℝ) * L))).map
            ((MeasurableEquiv.arrowProdEquivProdArrow ℕ ℝ ι) ∘
              fun x : ι → ℝ => fun i => (blockIndex L (x i), localCoord L (x i))) := by
          rw [cubeMeasure, hcomp]
    _ = ((Measure.pi (fun _ : ι => uniformInterval ((m : ℝ) * L))).map
            (fun x : ι → ℝ => fun i => (blockIndex L (x i), localCoord L (x i)))).map
              (MeasurableEquiv.arrowProdEquivProdArrow ℕ ℝ ι) := by
          rw [← Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow ℕ ℝ ι).measurable hF]
    _ = (Measure.pi (fun _ : ι => (uniformGrid m).prod (uniformInterval L))).map
          (MeasurableEquiv.arrowProdEquivProdArrow ℕ ℝ ι) := by rw [hpi]
    _ = (gridMeasure ι m).prod (cubeMeasure ι L) := hE.map_eq

private lemma Measure.pi_const_smul {ι : Type*} [Fintype ι] (c : ℝ≥0∞)
    (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] [∀ i, SigmaFinite (c • ν i)] :
    Measure.pi (fun i => c • ν i) = (c ^ Fintype.card ι) • Measure.pi ν := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- The uniform measure on `(0, L)^q` is the normalized restriction of Lebesgue
measure to the cube. -/
theorem cubeMeasure_eq_normalized_volume (q : ℕ) (hL : 0 < L) :
    (cubeMeasure (Fin q) L) =
      (volume (Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) L)))⁻¹ •
        volume.restrict (Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) L)) := by
  have hc0 : volume (Set.Ioo (0 : ℝ) L) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hL).ne'
  have hBfin : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) L)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioo,
      sub_zero]; exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top⟩
  have hBfinI := hBfin
  have hBs : SFinite (volume.restrict (Set.Ioo (0 : ℝ) L)) := inferInstance
  have hBsI := hBs
  have hsm : SigmaFinite ((volume (Set.Ioo (0 : ℝ) L))⁻¹ •
      volume.restrict (Set.Ioo (0 : ℝ) L)) := by
    have hfin : IsFiniteMeasure ((volume (Set.Ioo (0 : ℝ) L))⁻¹ •
        volume.restrict (Set.Ioo (0 : ℝ) L)) :=
      Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hc0)
    infer_instance
  have hsmI := hsm
  calc
    (cubeMeasure (Fin q) L)
        = Measure.pi (fun _ : Fin q => (volume (Set.Ioo (0 : ℝ) L))⁻¹ •
            volume.restrict (Set.Ioo (0 : ℝ) L)) := rfl
    _ = ((volume (Set.Ioo (0 : ℝ) L))⁻¹ ^ q) •
          Measure.pi (fun _ : Fin q => volume.restrict (Set.Ioo (0 : ℝ) L)) := by
        rw [Measure.pi_const_smul]
        simp only [Fintype.card_fin]
    _ = ((volume (Set.Ioo (0 : ℝ) L))⁻¹ ^ q) •
          volume.restrict (Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) L)) := by
        rw [← Measure.restrict_pi_pi (fun _ : Fin q => (volume : Measure ℝ))
          (fun _ : Fin q => Set.Ioo (0 : ℝ) L), ← volume_pi]
    _ = (volume (Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) L)))⁻¹ •
          volume.restrict (Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) L)) := by
        congr 1
        rw [volume_pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact ENNReal.inv_pow.symm

end OTSelector.Probability
