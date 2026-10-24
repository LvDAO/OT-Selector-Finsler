import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Order.OrderClosed

/-!
# Analysis.Calculus.CompactUniformQuadraticCore

Conditions: A finite inner-regular measure, compact-center continuous sections, and almost-everywhere arbitrarily small quadratic error radii; endpoint sections need no measurable endpoint index.

Objects: A large compact subset with one positive radius for each requested accuracy, uniform over centers and the stated endpoints.

Proof detail: Use closed sublevel sets of the continuous sections, cover almost every center by countably many radius choices, select sufficiently large choices by measure continuity, and intersect over countably many accuracies while controlling total mass loss.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3): Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11.
- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation: Locally proved closed-set/countable-core construction. It is not an invocation of Egorov for an assumed measurable sequence indexed by endpoints.
-/

/-!
# Uniform remainder radii on large compact cores

With fixed absolute endpoints, the remainder inequality defines closed sets of
centers. Countable compact approximation supplies one compact core on which every
positive accuracy has a common radius, without measurability of the endpoint set.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace OTSelector.Reconstruction

private theorem exists_compact_uniform_radius
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {H : Set X} (hH : IsCompact H) (hfinite : μ H ≠ ∞)
    (error distance weight : X → Y → ℝ)
    (he : ∀ y, ContinuousOn (fun x ↦ error x y) H)
    (hd : ∀ y, ContinuousOn (fun x ↦ distance x y) H)
    (hb : ∀ y, ContinuousOn (fun x ↦ weight x y) H)
    (η : ℝ)
    (hpoint : ∀ᵐ x ∂μ.restrict H, ∃ r > 0, ∀ y,
      distance x y < r → |error x y| ≤ η * weight x y)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ μ (H \ K) < ε ∧
      ∃ r > 0, ∀ x ∈ K, ∀ y, distance x y < r → |error x y| ≤ η * weight x y := by
  let r : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  let K : ℕ → Set X := fun n ↦ H ∩ {x | ∀ y,
    r n ≤ distance x y ∨ |error x y| ≤ η * weight x y}
  have hclosed (n : ℕ) : IsClosed (K n) := by
    have hy (y : Y) : IsClosed {x | x ∈ H ∧
        (r n ≤ distance x y ∨ |error x y| ≤ η * weight x y)} := by
      convert (hH.isClosed.isClosed_le (f := fun _ ↦ r n) continuousOn_const (hd y)).union
        (hH.isClosed.isClosed_le (g := fun x ↦ η * weight x y)
          (he y).abs (continuousOn_const.mul (hb y))) using 1
      ext x
      simp only [mem_union, mem_ofPred_eq, and_or_left]
    convert hH.isClosed.inter (isClosed_iInter hy) using 1
    ext x
    simp only [K, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    exact and_congr_right fun hx ↦ ⟨fun h y ↦ ⟨hx, h y⟩, fun h y ↦ (h y).2⟩
  have hsub (n : ℕ) : K n ⊆ H := inter_subset_left
  have hrmono : Antitone r := by
    intro n m hnm
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hKmono : Monotone K := by
    intro n m hnm x hx
    refine ⟨hx.1, fun y ↦ ?_⟩
    exact (hx.2 y).imp_left fun hy ↦ (hrmono hnm).trans hy
  have hcover : ∀ᵐ x ∂μ.restrict H, x ∈ ⋃ n, K n := by
    filter_upwards [hpoint, ae_restrict_mem hH.measurableSet] with x hx hxH
    obtain ⟨s, hs, hbound⟩ := hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hs
    refine mem_iUnion.mpr ⟨n, hxH, fun y ↦ ?_⟩
    by_cases hdist : distance x y < r n
    · exact Or.inr (hbound y (hdist.trans hn))
    · exact Or.inl (le_of_not_gt hdist)
  have hzero : μ (⋂ n, H \ K n) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [(ae_restrict_iff' hH.measurableSet).mp hcover] with x hx
    intro hxall
    have hxH := (mem_iInter.mp hxall 0).1
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hx hxH)
    exact (mem_iInter.mp hxall n).2 hn
  have hanti : Antitone (fun n ↦ H \ K n) := fun n m hnm ↦
    sdiff_subset_sdiff_right (hKmono hnm)
  rw [hanti.measure_iInter
    (fun n ↦ (hH.measurableSet.diff (hclosed n).measurableSet).nullMeasurableSet)
    ⟨0, ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)⟩] at hzero
  obtain ⟨n, hn⟩ := iInf_lt_iff.mp (hzero ▸ pos_iff_ne_zero.mpr hε)
  refine ⟨K n, hsub n, hH.of_isClosed_subset (hclosed n) (hsub n), hn, r n, ?_, ?_⟩
  · dsimp [r]
    positivity
  · intro x hx y hxy
    exact (hx.2 y).resolve_left (not_le_of_gt hxy)

/-- Pointwise small remainders with continuous center sections have a single large compact
core on which every accuracy admits a radius uniform over all the fixed endpoints. -/
theorem exists_compact_uniform_remainder_of_continuous_sections
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {H : Set X} (hH : IsCompact H) (hfinite : μ H ≠ ∞)
    (error distance weight : X → Y → ℝ)
    (he : ∀ y, ContinuousOn (fun x ↦ error x y) H)
    (hd : ∀ y, ContinuousOn (fun x ↦ distance x y) H)
    (hb : ∀ y, ContinuousOn (fun x ↦ weight x y) H)
    (hbzero : ∀ x ∈ H, ∀ y, 0 ≤ weight x y)
    (hpoint : ∀ᵐ x ∂μ.restrict H, ∀ η > 0, ∃ r > 0, ∀ y,
      distance x y < r → |error x y| ≤ η * weight x y)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ μ (H \ K) < ε ∧
      ∀ η > 0, ∃ r > 0, ∀ x ∈ K, ∀ y,
        distance x y < r → |error x y| ≤ η * weight x y := by
  classical
  obtain ⟨τ, hτ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hex (n : ℕ) := exists_compact_uniform_radius hH hfinite error distance weight he hd hb
    (1 / (n + 1 : ℝ)) (hpoint.mono fun x hx ↦ hx _ (by positivity)) (hτ n).ne'
  choose K hsub hK hmass r hr hbound using hex
  let L := H ∩ ⋂ n, K n
  have hL : IsCompact L := hH.inter_right (isClosed_iInter fun n ↦ (hK n).isClosed)
  refine ⟨L, inter_subset_left, hL, ?_, ?_⟩
  · have hdiff : H \ L ⊆ ⋃ n, H \ K n := by
      intro x hx
      by_contra hn
      apply hx.2
      refine ⟨hx.1, mem_iInter.mpr fun n ↦ ?_⟩
      by_contra hxK
      exact hn (mem_iUnion.mpr ⟨n, hx.1, hxK⟩)
    exact ((measure_mono hdiff).trans (measure_iUnion_le _)).trans_lt
      ((ENNReal.tsum_le_tsum fun n ↦ (hmass n).le).trans_lt hsum)
  · intro η hη
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
    refine ⟨r n, hr n, fun x hx y hxy ↦ ?_⟩
    exact (hbound n x (mem_iInter.mp hx.2 n) y hxy).trans
      (mul_le_mul_of_nonneg_right hn.le (hbzero x hx.1 y))

/-- Fixed absolute endpoints give a common quadratic remainder radius on one large compact
root core. Only the center and quadratic coefficient need to vary continuously in the root. -/
theorem exists_compact_uniform_fixedEndpoint_quadratic_remainder
    {X W I : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup W]
    {μ : Measure X} {H : Set X} (hH : IsCompact H) (hfinite : μ H ≠ ∞)
    (center : X → W) (hc : ContinuousOn center H)
    (L : Set W) (T : Set I) (cost : I → W × W → ℝ) (q : X → I → W × W → ℝ)
    (hq : ∀ t ∈ T, ∀ y₁ ∈ L, ∀ y₂ ∈ L,
      ContinuousOn (fun x ↦ q x t (y₁ - center x, y₂ - center x)) H)
    (hpoint : ∀ᵐ x ∂μ.restrict H, ∀ η > 0, ∃ r > 0,
      ∀ t ∈ T, ∀ y₁ ∈ L, ∀ y₂ ∈ L,
        ‖(y₁ - center x, y₂ - center x)‖ < r →
          |cost t (y₁, y₂) - q x t (y₁ - center x, y₂ - center x)| ≤
            η * ‖(y₁ - center x, y₂ - center x)‖ ^ 2)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ μ (H \ K) < ε ∧
      ∀ η > 0, ∃ r > 0, ∀ x ∈ K, ∀ t ∈ T, ∀ y₁ ∈ L, ∀ y₂ ∈ L,
        ‖(y₁ - center x, y₂ - center x)‖ < r →
          |cost t (y₁, y₂) - q x t (y₁ - center x, y₂ - center x)| ≤
            η * ‖(y₁ - center x, y₂ - center x)‖ ^ 2 := by
  let Y := T × (L × L)
  let d : X → Y → ℝ := fun x y ↦ ‖(y.2.1.val - center x, y.2.2.val - center x)‖
  let e : X → Y → ℝ := fun x y ↦ cost y.1.val (y.2.1.val, y.2.2.val) -
    q x y.1.val (y.2.1.val - center x, y.2.2.val - center x)
  have hd (y : Y) : ContinuousOn (fun x ↦ d x y) H :=
    ((continuousOn_const.sub hc).prodMk (continuousOn_const.sub hc)).norm
  have he (y : Y) : ContinuousOn (fun x ↦ e x y) H :=
    continuousOn_const.sub (hq y.1.val y.1.property
      y.2.1.val y.2.1.property y.2.2.val y.2.2.property)
  have hp : ∀ᵐ x ∂μ.restrict H, ∀ η > 0, ∃ r > 0, ∀ y : Y,
      d x y < r → |e x y| ≤ η * (d x y) ^ 2 := by
    filter_upwards [hpoint] with x hx
    intro η hη
    obtain ⟨r, hr, hb⟩ := hx η hη
    exact ⟨r, hr, fun y ↦ hb y.1.val y.1.property
      y.2.1.val y.2.1.property y.2.2.val y.2.2.property⟩
  obtain ⟨K, hsub, hK, hmass, hb⟩ :=
    exists_compact_uniform_remainder_of_continuous_sections hH hfinite e d
      (fun x y ↦ (d x y) ^ 2) he hd (fun y ↦ (hd y).pow 2)
      (fun _ _ _ ↦ sq_nonneg _) hp hε
  refine ⟨K, hsub, hK, hmass, fun η hη ↦ ?_⟩
  obtain ⟨r, hr, hbound⟩ := hb η hη
  exact ⟨r, hr, fun x hx t ht y₁ hy₁ y₂ hy₂ ↦
    hbound x hx (⟨t, ht⟩, ⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩)⟩

end OTSelector.Reconstruction
