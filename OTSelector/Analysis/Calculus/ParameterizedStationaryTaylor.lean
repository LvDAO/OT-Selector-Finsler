import OTSelector.Analysis.CubicTaylor
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ParameterizedStationaryTaylor.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ParameterizedStationaryTaylor`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C3 action is defined near a compact parameter/center family and its state differential vanishes at each center.

Objects: Common cubic Taylor bounds and arbitrarily small quadratic remainder bounds.

Proof detail: Thicken the compact trace inside the smooth domain, bound third derivatives there and use Taylor; stationarity removes the linear term.

Sources: Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46).
Relation: Uniform normed-space stationary Taylor consequence, including the stated ContDiffAt localization adapter.
-/

/-!
# Uniform stationary Taylor bounds with retained parameters

A joint C3 scalar action supplies a common remainder radius on compact sets of
parameters and centers. Only the state variable is displaced; stationarity is
required in that variable alone. All quadratic coefficients are the actual joint
Hessian restricted to state directions. This analytic result does not assert that
an original Finsler deficit already has a common C3 representation.
-/

open Set
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
/-- Stationarity of the state slice identifies the restriction of the actual joint
first derivative. Parameter derivatives need not vanish. -/
theorem state_fderiv_eq_zero_of_hasFDerivAt
    {f : P × E → ℝ} {z : P × E} (hf : DifferentiableAt ℝ f z)
    (hstate : HasFDerivAt (fun y : E ↦ f (z.1, y)) (0 : E →L[ℝ] ℝ) z.2) :
    ∀ h : E, fderiv ℝ f z (0, h) = 0 := by
  have hpair := (hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) z.2)
  have hcomp := hf.hasFDerivAt.comp z.2 hpair
  have heq := hcomp.unique hstate
  intro h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun L : E →L[ℝ] ℝ ↦ L h) heq

/-- A common joint C3 action gives a uniform cubic remainder in its stationary
state directions, without any stationarity assumption in the parameter directions. -/
theorem exists_uniform_parameterized_stationary_cubic_bound
    {f : P × E → ℝ} {U K : Set (P × E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hstationary : ∀ z ∈ K, ∀ h : E, fderiv ℝ f z (0, h) = 0) :
    ∃ r > 0, ∃ C ≥ 0, ∀ z ∈ K, ∀ h : E, ‖h‖ ≤ r →
      ‖f (z.1, z.2 + h) - f z -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) z (0, h) (0, h)‖ ≤
          C * ‖h‖ ^ 3 := by
  obtain ⟨r, hr, C, hC, hbound⟩ :=
    exists_uniform_quadratic_taylor_remainder_bound hU hf hK hKU
  refine ⟨r, hr, C, hC, ?_⟩
  intro z hz h hh
  have hnorm : ‖((0 : P), h)‖ = ‖h‖ := by simp
  have hb := hbound z hz (0, h) (by simpa only [hnorm] using hh)
  have heq : z + (0, h) = (z.1, z.2 + h) := by ext <;> simp
  simpa only [heq, hstationary z hz, sub_zero, hnorm] using hb

/-- On the same compact parameter-center set, the stationary quadratic remainder
has one epsilon-radius for every center and every state displacement. -/
theorem exists_uniform_parameterized_stationary_quadratic_remainder
    {f : P × E → ℝ} {U K : Set (P × E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hstationary : ∀ z ∈ K, ∀ h : E, fderiv ℝ f z (0, h) = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ z ∈ K, ∀ h : E, ‖h‖ < r →
      ‖f (z.1, z.2 + h) - f z -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) z (0, h) (0, h)‖ ≤
          η * ‖h‖ ^ 2 := by
  obtain ⟨r₀, hr₀, C, hC, hbound⟩ :=
    exists_uniform_parameterized_stationary_cubic_bound hU hf hK hKU hstationary
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨min r₀ (η / (C + 1)), lt_min hr₀ (div_pos hη hC1), ?_⟩
  intro z hz h hh
  have hr : ‖h‖ ≤ r₀ := (hh.trans_le (min_le_left _ _)).le
  have heta : (C + 1) * ‖h‖ ≤ η := by
    have hdiv := (lt_div_iff₀ hC1).mp (hh.trans_le (min_le_right _ _))
    nlinarith
  have hCh : C * ‖h‖ ≤ η := by nlinarith [norm_nonneg h]
  calc
    _ ≤ C * ‖h‖ ^ 3 := hbound z hz h hr
    _ = (C * ‖h‖) * ‖h‖ ^ 2 := by ring
    _ ≤ η * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_right hCh (sq_nonneg _)


/-- Pointwise C3 regularity of one joint action at compactly many centers suffices:
the local domains may vary with the center. No common tube is an input. -/
theorem exists_uniform_parameterized_stationary_remainder_of_contDiffAt
    {f : P × E → ℝ} {K : Set (P × E)} (hK : IsCompact K)
    (hf : ∀ z ∈ K, ContDiffAt ℝ 3 f z)
    (hstationary : ∀ z ∈ K, ∀ h : E, fderiv ℝ f z (0, h) = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ z ∈ K, ∀ h : E, ‖h‖ < r →
      ‖f (z.1, z.2 + h) - f z -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) z (0, h) (0, h)‖ ≤
          η * ‖h‖ ^ 2 := by
  let U : Set (P × E) := {z | ContDiffAt ℝ 3 f z}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun z hz ↦
    (show ContDiffAt ℝ 3 f z from hz).eventually (by norm_num)
  have hfU : ContDiffOn ℝ 3 f U := fun z hz ↦
    (show ContDiffAt ℝ 3 f z from hz).contDiffWithinAt
  exact exists_uniform_parameterized_stationary_quadratic_remainder
    hU hfU hK hf hstationary hη

end OTSelector.Geometry

end
end
