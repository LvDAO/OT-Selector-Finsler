import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Topology.MetricSpace.IsometricSplice

## Lemma skeleton

* **Conditions:** Two isometric real segments meet at their common endpoint; the outer endpoint distance is the sum of their parameter lengths.

* **Objects:** An isometric concatenation of the two given segments.

* **Proof detail:** Treat pairs on each side by the original isometries and crossing pairs by the triangle inequality. Outer endpoint saturation forces the reverse inequality for every intermediate pair.

## Mathematical sources

- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Proposition 1.29 and its preceding compact approximate-midpoint argument, p. 18; Section I, p. 13, defines a geodesic as an isometric interval.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): Elementary equality-case triangle argument for actual segments, not an existence or continuation theorem for geodesics.
-/

/-!
# Isometric segments joined at a saturated endpoint pair

Two isometric real segments with a common joining value give a one-Lipschitz concatenation.
If the distance between the outer endpoints equals the full parameter length, the triangle
inequality forces every subsegment of the concatenation to preserve distance.
-/

open Set

namespace OTSelector.Geometry

variable {X : Type*}

/-- The literal splice agrees with its first curve on the left closed segment. -/
theorem isometricSplice_eqOn_left {c d : ℝ → X} {a b : ℝ} :
    EqOn (fun t ↦ if t ≤ b then c t else d t) c (Icc a b) := by
  intro t ht
  exact ite_eq_left ht.2

/-- Agreement at the joining point makes the splice equal to its second curve on
the entire right closed segment, including the join. -/
theorem isometricSplice_eqOn_right {c d : ℝ → X} {b e : ℝ} (hjoin : c b = d b) :
    EqOn (fun t ↦ if t ≤ b then c t else d t) d (Icc b e) := by
  intro t ht
  by_cases htb : t ≤ b
  · have hteq : t = b := le_antisymm htb ht.1
    simp only [hteq, le_refl, ↓reduceIte, hjoin]
  · exact ite_eq_right htb

variable [PseudoMetricSpace X]

/-- A join of two isometric segments is itself isometric when the distance between
the outer endpoints saturates their total parameter length. Degenerate segments are allowed. -/
theorem isometry_Icc_splice_of_dist_eq {c d : ℝ → X} {a b e : ℝ}
    (hab : a ≤ b) (hbe : b ≤ e)
    (hc : Isometry (fun t : Icc a b ↦ c t))
    (hd : Isometry (fun t : Icc b e ↦ d t))
    (hjoin : c b = d b) (hend : dist (c a) (d e) = e - a) :
    Isometry (fun t : Icc a e ↦ if (t : ℝ) ≤ b then c t else d t) := by
  let p : ℝ → X := fun t ↦ if t ≤ b then c t else d t
  have hleft : EqOn p c (Icc a b) := isometricSplice_eqOn_left
  have hright : EqOn p d (Icc b e) := isometricSplice_eqOn_right hjoin
  have hupper (s t : ℝ) (hs : s ∈ Icc a e) (ht : t ∈ Icc a e)
      (hst : s ≤ t) : dist (p s) (p t) ≤ t - s := by
    by_cases htb : t ≤ b
    · have hs' : s ∈ Icc a b := ⟨hs.1, hst.trans htb⟩
      have ht' : t ∈ Icc a b := ⟨ht.1, htb⟩
      rw [hleft hs', hleft ht', hc.dist_eq ⟨s, hs'⟩ ⟨t, ht'⟩]
      simp only [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]
      linarith
    · by_cases hbs : b ≤ s
      · have hs' : s ∈ Icc b e := ⟨hbs, hs.2⟩
        have ht' : t ∈ Icc b e := ⟨hbs.trans hst, ht.2⟩
        rw [hright hs', hright ht', hd.dist_eq ⟨s, hs'⟩ ⟨t, ht'⟩]
        simp only [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]
        linarith
      · have hs' : s ∈ Icc a b := ⟨hs.1, (lt_of_not_ge hbs).le⟩
        have ht' : t ∈ Icc b e := ⟨(lt_of_not_ge htb).le, ht.2⟩
        have hbL : b ∈ Icc a b := ⟨hab, le_rfl⟩
        have hbR : b ∈ Icc b e := ⟨le_rfl, hbe⟩
        have hsb := hc.dist_eq ⟨s, hs'⟩ ⟨b, hbL⟩
        have hbt := hd.dist_eq ⟨b, hbR⟩ ⟨t, ht'⟩
        simp only [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hs'.2)] at hsb
        simp only [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr ht'.1)] at hbt
        have htriangle := dist_triangle (c s) (c b) (d t)
        rw [hjoin] at htriangle
        rw [hleft hs', hright ht']
        rw [hjoin] at hsb
        linarith
  have ha : a ∈ Icc a e := ⟨le_rfl, hab.trans hbe⟩
  have he : e ∈ Icc a e := ⟨hab.trans hbe, le_rfl⟩
  have hsat : dist (p a) (p e) = e - a := by
    rw [hleft ⟨le_rfl, hab⟩, hright ⟨hbe, le_rfl⟩, hend]
  have heq (s t : ℝ) (hs : s ∈ Icc a e) (ht : t ∈ Icc a e)
      (hst : s ≤ t) : dist (p s) (p t) = t - s := by
    apply le_antisymm (hupper s t hs ht hst)
    have h₁ := hupper a s ha hs hs.1
    have h₂ := hupper t e ht he ht.2
    have h₃ := dist_triangle (p a) (p s) (p e)
    have h₄ := dist_triangle (p s) (p t) (p e)
    rw [hsat] at h₃
    linarith
  apply Isometry.of_dist_eq
  intro s t
  change dist (p s) (p t) = dist (s : ℝ) (t : ℝ)
  rcases le_total (s : ℝ) (t : ℝ) with hst | hts
  · rw [heq s t s.property t.property hst, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hst)]
    exact neg_sub _ _ |>.symm
  · rw [dist_comm (p s), heq t s t.property s.property hts, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hts)]

end OTSelector.Geometry
