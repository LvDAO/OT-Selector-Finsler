import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Analysis.Calculus.ShortTimeLipschitz

Conditions: A jointly C1 map with zero initial spatial slice, or a prescribed initial linear slice.

Objects: An arbitrarily small spatial Lipschitz bound on a common short time and spatial ball.

Proof detail: The spatial derivative at the central slice is zero after subtracting the initial linear map. Continuity keeps its norm small in a product neighborhood, and the vector mean-value bound gives Lipschitz control.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=46): Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.
- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.

Source relation: Direct C1/mean-value consequence in the stated normed spaces; no finite-dimensional compactness premise is added.
-/

/-!
# Uniform small spatial Lipschitz constants near a zero time slice

A jointly C1 map whose time-zero slice vanishes has arbitrarily small spatial
Lipschitz constants on a common short-time neighborhood. The estimate uses the
actual partial derivative, without requiring finite-dimensional or compact domains.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {W E : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual spatial Lipschitz constant becomes uniformly small near a zero
time slice of a jointly C1 function. The returned closed product lies in its domain. -/
theorem exists_shortTime_lipschitz_of_zeroSlice
    {R : W × ℝ → E} {O : Set (W × ℝ)} {w₀ : W}
    (hO : IsOpen O) (hR : ContDiffOn ℝ 1 R O) (h0 : (w₀, 0) ∈ O)
    (hzero : ∀ᶠ w in 𝓝 w₀, R (w, 0) = 0) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ r τ : ℝ, 0 < r ∧ 0 < τ ∧
      closedBall w₀ r ×ˢ Icc (-τ) τ ⊆ O ∧
      ∀ t ∈ Icc (-τ) τ, LipschitzOnWith ε (fun w ↦ R (w, t))
        (closedBall w₀ r) := by
  let D : W × ℝ → W →L[ℝ] E := fun q ↦
    (fderiv ℝ R q).comp (ContinuousLinearMap.inl ℝ W ℝ)
  have hdiff (q : W × ℝ) (hq : q ∈ O) : DifferentiableAt ℝ R q :=
    (hR.differentiableOn_one q hq).differentiableAt (hO.mem_nhds hq)
  have hpartial (w : W) (t : ℝ) (hwt : (w, t) ∈ O) :
      HasFDerivAt (fun v ↦ R (v, t)) (D (w, t)) w :=
    (hdiff (w, t) hwt).hasFDerivAt.comp w (hasFDerivAt_prodMk_left w t)
  have hD0 : D (w₀, 0) = 0 := by
    have hz : HasFDerivAt (fun w ↦ R (w, 0)) 0 w₀ :=
      (hasFDerivAt_const (𝕜 := ℝ) (0 : E) w₀).congr_of_eventuallyEq hzero
    exact (hpartial w₀ 0 h0).unique hz
  have hD : ContinuousAt D (w₀, 0) :=
    ((hR.continuousOn_fderiv_of_isOpen hO le_rfl).continuousAt
      (hO.mem_nhds h0)).clm_comp continuousAt_const
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have hnear : ∀ᶠ q in 𝓝 (w₀, (0 : ℝ)), q ∈ O ∧ ‖D q‖ < ε := by
    filter_upwards [hO.mem_nhds h0,
      hD.norm.eventually (gt_mem_nhds (show ‖D (w₀, 0)‖ < (ε : ℝ) by
        rw [hD0, norm_zero]; exact hε'))] with q hq hnorm
    exact ⟨hq, hnorm⟩
  obtain ⟨s, hs, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hbox : closedBall w₀ (s / 2) ×ˢ Icc (-(s / 2)) (s / 2) ⊆
      {q | q ∈ O ∧ ‖D q‖ < ε} := by
    intro q hq
    apply hsub
    rw [mem_ball, Prod.dist_eq]
    apply max_lt
    · exact (mem_closedBall.mp hq.1).trans_lt (by linarith)
    · rw [Real.dist_eq, sub_zero]
      exact (abs_le.mpr hq.2).trans_lt (by linarith)
  refine ⟨s / 2, s / 2, by positivity, by positivity,
    (fun q hq ↦ (hbox hq).1), ?_⟩
  intro t ht
  apply (convex_closedBall w₀ (s / 2)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun w hw ↦ (hpartial w t (hbox ⟨hw, ht⟩).1).hasFDerivWithinAt)
  intro w hw
  exact_mod_cast (hbox ⟨hw, ht⟩).2.le

/-- A jointly C1 family with an initial linear map has a uniformly small spatial
Lipschitz residual from that same linear map for short positive and negative times. -/
theorem exists_shortTime_lipschitz_of_initial_linear
    {Ψ : W × ℝ → E} {O : Set (W × ℝ)} {w₀ : W}
    (hO : IsOpen O) (hΨ : ContDiffOn ℝ 1 Ψ O) (h0 : (w₀, 0) ∈ O)
    (A : W →L[ℝ] E) (hzero : ∀ᶠ w in 𝓝 w₀, Ψ (w, 0) = A w)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ r τ : ℝ, 0 < r ∧ 0 < τ ∧
      closedBall w₀ r ×ˢ Icc (-τ) τ ⊆ O ∧
      ∀ t ∈ Icc (-τ) τ, LipschitzOnWith ε (fun w ↦ Ψ (w, t) - A w)
        (closedBall w₀ r) := by
  apply exists_shortTime_lipschitz_of_zeroSlice hO
    (hΨ.sub (A.contDiff.comp contDiff_fst).contDiffOn) h0 _ ε hε
  filter_upwards [hzero] with w hw
  exact sub_eq_zero.mpr hw

end OTSelector.Geometry
