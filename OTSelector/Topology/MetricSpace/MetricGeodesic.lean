import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import OTSelector.Topology.MetricSpace.ProperMetricMidpoint

/-!
## Lemma skeleton

* **Conditions:** A metric space with exact or arbitrarily accurate approximate subdivisions at every radius. Properness is used for the isometric interval construction; finite interpolation itself does not require it.
* **Objects:** A finite isometric interpolation and an isometric copy of [0,d(x,y)] with the prescribed endpoints.
* **Proof detail:** Induct on finite sets of ordered parameters. In the product of compact comparison balls, impose pairwise distance equalities as closed constraints and use the finite intersection property. Approximate splits first become exact by compactness.

## Mathematical sources

* Anton Petrunin, *Lectures on metric geometry*, Lecture 1, Section L, Lemma 1.27 (Menger), pp. 17–18.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=17
* Anton Petrunin, *Lectures on metric geometry*, Lecture 1, Section L, Proposition 1.29 and its preceding compact approximate-midpoint argument, p. 18; Section I, p. 13, defines a geodesic as an isometric interval.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18

**Relationship to the sources:** Alternative implementation of the Menger midpoint/geodesic principle and proper length-space geodesic existence. The source uses dyadic completion; the code uses finite interpolation and product compactness.
-/

/-!
# Metric geodesics from exact subdivisions

Exact subdivisions first give isometric interpolation on every finite set of real
parameters. Properness then supplies compactness of the product of comparison balls;
the finite intersection property produces an isometric interval joining the endpoints.
This construction uses the original metric, without prescribed coordinates or a
pre-existing geodesic family.
-/

open Set Metric

namespace OTSelector.Geometry

variable {X : Type*} [MetricSpace X]

/-- Exact subdivisions give a consistent isometric interpolation on any finite collection
of parameters between zero and the distance between the prescribed endpoints. -/
theorem exists_finite_isometric_interpolation
    (hsplit : ∀ x y : X, ∀ r : ℝ, 0 ≤ r → r ≤ dist x y →
      ∃ z : X, dist x z = r ∧ dist z y = dist x y - r)
    (s : Finset ℝ) (x y : X) (hs : ∀ t ∈ s, t ∈ Icc 0 (dist x y)) :
    ∃ f : ℝ → X,
      (∀ t ∈ s, dist x (f t) = t ∧ dist (f t) y = dist x y - t) ∧
      ∀ a ∈ s, ∀ b ∈ s, dist (f a) (f b) = |a - b| := by
  classical
  induction s using Finset.induction_on_max generalizing x y with
  | empty => exact ⟨fun _ ↦ x, by simp, by simp⟩
  | insert a s hlt ih =>
    have ha := hs a (Finset.mem_insert_self _ _)
    obtain ⟨z, hxz, hzy⟩ := hsplit x y a ha.1 ha.2
    obtain ⟨g, hgrad, hgdist⟩ := ih x z (by
      intro t ht
      exact ⟨(hs t (Finset.mem_insert_of_mem ht)).1, hxz ▸ (hlt t ht).le⟩)
    let f : ℝ → X := fun t ↦ if t = a then z else g t
    have hfa : f a = z := by simp [f]
    have hfs : ∀ t ∈ s, f t = g t := by
      intro t ht
      simp [f, ne_of_lt (hlt t ht)]
    have hrad : ∀ t ∈ s, dist x (f t) = t ∧ dist (f t) y = dist x y - t := by
      intro t ht
      rw [hfs t ht]
      obtain ⟨hxt, htz⟩ := hgrad t ht
      rw [hxz] at htz
      refine ⟨hxt, ?_⟩
      have hupper := dist_triangle (g t) z y
      have hlower := dist_triangle x (g t) y
      rw [htz, hzy] at hupper
      rw [hxt] at hlower
      linarith
    refine ⟨f, ?_, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · simpa only [hfa] using ⟨hxz, hzy⟩
      · exact hrad t ht
    · intro t ht u hu
      by_cases ht0 : t = a
      · by_cases hu0 : u = a
        · simp [ht0, hu0]
        · have hus : u ∈ s := by simpa [hu0] using hu
          rw [ht0, hfa, hfs u hus, dist_comm, (hgrad u hus).2, hxz,
            abs_of_nonneg (sub_nonneg.mpr (hlt u hus).le)]
      · have hts : t ∈ s := by simpa [ht0] using ht
        by_cases hu0 : u = a
        · rw [hu0, hfs t hts, hfa, (hgrad t hts).2, hxz,
            abs_of_nonpos (sub_nonpos.mpr (hlt t hts).le)]
          ring
        · have hus : u ∈ s := by simpa [hu0] using hu
          rw [hfs t hts, hfs u hus]
          exact hgdist t hts u hus

/-- In a proper metric space, exact subdivisions produce a unit-speed isometric interval
between any two points. The interval has length equal to their original distance. -/
theorem exists_isometric_interval_of_exact_split [ProperSpace X]
    (hsplit : ∀ x y : X, ∀ r : ℝ, 0 ≤ r → r ≤ dist x y →
      ∃ z : X, dist x z = r ∧ dist z y = dist x y - r) (x y : X) :
    ∃ γ : Icc (0 : ℝ) (dist x y) → X, Isometry γ ∧
      γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      γ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  classical
  let J := Icc (0 : ℝ) (dist x y)
  let K : Set (J → X) := Set.pi univ (fun _ ↦ closedBall x (dist x y))
  let C : J × J → Set (J → X) := fun p ↦
    {f | dist x (f p.1) = (p.1 : ℝ) ∧
      dist (f p.1) y = dist x y - (p.1 : ℝ) ∧
      dist (f p.1) (f p.2) = |(p.1 : ℝ) - (p.2 : ℝ)|}
  have hK : IsCompact K := isCompact_univ_pi fun _ ↦ isCompact_closedBall _ _
  have hC : ∀ p, IsClosed (C p) := by
    intro p
    exact (isClosed_eq (continuous_const.dist (continuous_apply p.1)) continuous_const).inter
      ((isClosed_eq ((continuous_apply p.1).dist continuous_const) continuous_const).inter
        (isClosed_eq ((continuous_apply p.1).dist (continuous_apply p.2)) continuous_const))
  have hfinite : ∀ u : Finset (J × J), (K ∩ ⋂ p ∈ u, C p).Nonempty := by
    intro u
    let s : Finset ℝ := (u.image fun p ↦ (p.1 : ℝ)) ∪ (u.image fun p ↦ (p.2 : ℝ))
    have hs : ∀ t ∈ s, t ∈ Icc 0 (dist x y) := by
      intro t ht
      rcases Finset.mem_union.mp ht with ht | ht <;>
        rcases Finset.mem_image.mp ht with ⟨p, _, rfl⟩
      · exact p.1.property
      · exact p.2.property
    obtain ⟨g, hgrad, hgdist⟩ := exists_finite_isometric_interpolation hsplit s x y hs
    let f : J → X := fun t ↦ if (t : ℝ) ∈ s then g t else x
    have hf : ∀ t : J, (t : ℝ) ∈ s → f t = g t := by
      intro t ht
      simp [f, ht]
    refine ⟨f, ?_, ?_⟩
    · intro t _
      change dist (f t) x ≤ dist x y
      by_cases ht : (t : ℝ) ∈ s
      · rw [hf t ht, dist_comm, (hgrad t ht).1]
        exact t.property.2
      · simp [f, ht]
    · simp only [mem_iInter]
      intro p hp
      have hp₁ : (p.1 : ℝ) ∈ s := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)
      have hp₂ : (p.2 : ℝ) ∈ s := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
      change dist x (f p.1) = (p.1 : ℝ) ∧
        dist (f p.1) y = dist x y - (p.1 : ℝ) ∧
        dist (f p.1) (f p.2) = |(p.1 : ℝ) - (p.2 : ℝ)|
      rw [hf p.1 hp₁, hf p.2 hp₂]
      exact ⟨(hgrad _ hp₁).1, (hgrad _ hp₁).2, hgdist _ hp₁ _ hp₂⟩
  obtain ⟨γ, _, hγ⟩ := hK.inter_iInter_nonempty C hC hfinite
  have hγp : ∀ p, γ ∈ C p := mem_iInter.mp hγ
  refine ⟨γ, Isometry.of_dist_eq (fun s t ↦ ?_), ?_, ?_⟩
  · exact (hγp (s, t)).2.2
  · exact (dist_eq_zero.mp (hγp (⟨0, ⟨le_rfl, dist_nonneg⟩⟩,
      ⟨0, ⟨le_rfl, dist_nonneg⟩⟩)).1).symm
  · apply dist_eq_zero.mp
    simpa only [sub_self] using
      (hγp (⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩,
        ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩)).2.1

/-- Approximate subdivisions suffice for global metric geodesics in a proper metric space. -/
theorem exists_isometric_interval_of_approximate_split [ProperSpace X]
    (hsplit : ∀ x y : X, ∀ r : ℝ, 0 ≤ r → r ≤ dist x y →
      ∀ ε > (0 : ℝ), ∃ z : X,
        dist x z < r + ε ∧ dist z y < dist x y - r + ε) (x y : X) :
    ∃ γ : Icc (0 : ℝ) (dist x y) → X, Isometry γ ∧
      γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      γ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y :=
  exists_isometric_interval_of_exact_split
    (fun u v r hr hrd ↦ exists_dist_eq_of_approximate_split u v r (hsplit u v r hr hrd)) x y

end OTSelector.Geometry
