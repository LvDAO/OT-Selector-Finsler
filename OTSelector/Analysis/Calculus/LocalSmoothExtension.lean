import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
## Lemma skeleton

* **Conditions:** A smooth map on an open subset of a finite-dimensional real normed space, with any normed vector target.
* **Objects:** A globally smooth compactly supported map equal to the original germ.
* **Proof detail:** Choose a smooth bump supported inside the open set, multiply the original map, and use local zero agreement outside its support.

## Mathematical sources

* John M. Lee, *Introduction to Smooth Manifolds, second edition (2013)*, Chapter 2, section “Partitions of Unity”, pp. 40–47.
  https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** The precise vector-valued normed-space germ extension is proved with mathlib finite-dimensional bump functions. Lee’s section is cited for the cutoff/partition method; only its section location was accessible, not an exact numbered theorem.
-/

/-!
# Compactly supported smooth representatives of local maps

A map smooth on an open subset of a finite-dimensional real normed space agrees near
any point of that subset with a globally smooth map of compact support. The support of
the extension remains inside the original domain. The construction multiplies the map
by a smooth cutoff equal to one on a smaller ball, using mathlib's finite-dimensional
bump functions without selecting an inner product in the statement.

For vector fields this supplies a global smooth representative to which an ODE theorem
can be applied. Equality on the returned neighborhood is exact; no flow or trajectory
claim is made by this localization result.
-/

open Set Filter Metric
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth map on an open set admits a globally smooth compactly supported extension
of its germ, with support contained in the original set. -/
theorem exists_contDiff_compactlySupported_extension
    {U : Set E} {p : E} {X : E → F}
    (hU : IsOpen U) (hp : p ∈ U) (hX : ContDiffOn ℝ ∞ X U) :
    ∃ (V : Set E) (Y : E → F),
      IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ ContDiff ℝ ∞ Y ∧
      HasCompactSupport Y ∧ tsupport Y ⊆ U ∧ EqOn Y X V := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let χ : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hsupp : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    intro x hx
    apply hball
    exact lt_of_le_of_lt hx (by change r / 2 < r; linarith)
  refine ⟨ball p χ.rIn, fun x ↦ χ x • X x, isOpen_ball,
    mem_ball_self χ.rIn_pos, ?_, ?_, χ.hasCompactSupport.smul_right, ?_, ?_⟩
  · intro x hx
    apply hball
    exact lt_trans hx (by change r / 4 < r; linarith)
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact χ.contDiffAt.smul (hX.contDiffAt (hU.mem_nhds hx))
    · have hz : χ =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hsupp h))
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp only [hy, Pi.zero_apply, zero_smul]
  · exact (tsupport_smul_subset_left χ X).trans hsupp
  · intro x hx
    simp only [χ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]

end OTSelector.Geometry
