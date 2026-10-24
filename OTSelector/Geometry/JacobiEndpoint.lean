import OTSelector.Analysis.ODE.HamiltonianGronwall
import OTSelector.Geometry.JacobiPrimitive
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Topology.ExtendFrom

/-!
Conditions: An actual derivative is bounded by L times the state norm on an open interval; L is nonnegative.

Objects: Uniform exponential state bound and the explicit norm bound for a linear Hamiltonian matrix pair.

Proof detail: Apply Grönwall in either direction from the center; estimate the Hamiltonian blocks by submultiplicativity and the product norm.

Sources: Gerald Teschl, Section 2.4, Lemma 2.7 and Theorem 2.8, pp. 42–44, equations (2.38)–(2.43) (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=53); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Local interval/matrix specialization of Grönwall; the exact sum of block norms is derived algebraically.
-/

/-!
# Continuous Jacobi endpoint extensions

An actual solution of `‖f'‖ ≤ L * ‖f‖` on a finite open interval has a uniform
Gronwall bound and hence a uniform derivative bound. The mean value theorem makes it
Lipschitz on the entire interval. Completeness then provides limits at both endpoints
and a continuous extension to the closed interval.

For the Hamiltonian matrix system, continuous coefficients on the closed interval
supply the growth bound by compactness. This extends both the original Jacobi pair
and the second pair constructed from the actual compliance integral. Determinant
cancellation consequently bounds `|det (1 ± T)| * |det J|` throughout the interior.
No endpoint inverse, nonsingularity, or finite endpoint limit of `T` is required.

This module proves continuous endpoint extension, not differentiability at the
endpoints or smooth extension to a larger interval. Identifying the matrix system
with genuine Finsler Jacobi data remains a separate geometric step.
-/

open Set Filter
open scoped Topology NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



/-- Linear growth bounds imply a Lipschitz bound on the entire open interval. -/
theorem exists_lipschitzOnWith_of_norm_deriv_le_mul
    {f f' : ℝ → E} {a b c L : ℝ}
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hL : 0 ≤ L) (hg : ∀ t ∈ Ioo a b, ‖f' t‖ ≤ L * ‖f t‖)
    (hc : c ∈ Ioo a b) : ∃ M : ℝ≥0, LipschitzOnWith M f (Ioo a b) := by
  let M : ℝ≥0 := ⟨L * (‖f c‖ * Real.exp (L * (b - a))), by positivity⟩
  refine ⟨M, (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht ↦ (hf t ht).hasDerivWithinAt) ?_⟩
  intro t ht
  apply NNReal.coe_le_coe.mp
  exact (hg t ht).trans (mul_le_mul_of_nonneg_left
    (norm_le_exp_of_norm_deriv_le_mul hf hL hg hc ht) hL)

variable [CompleteSpace E]

omit [NormedSpace ℝ E] in
/-- Uniform continuity on an open interval supplies a continuous extension to its endpoints. -/
theorem exists_continuousOn_Icc_extension_of_uniformContinuousOn
    {f : ℝ → E} {a b : ℝ} (hab : a < b) (hf : UniformContinuousOn f (Ioo a b)) :
    ∃ F : ℝ → E, ContinuousOn F (Icc a b) ∧ EqOn F f (Ioo a b) := by
  refine ⟨extendFrom (Ioo a b) f, continuousOn_extendFrom ?_ ?_,
    extendFrom_extends hf.continuousOn⟩
  · rw [closure_Ioo hab.ne]
  · intro t ht
    have hcl : t ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
    have : NeBot (𝓝[Ioo a b] t) := mem_closure_iff_nhdsWithin_neBot.mp hcl
    apply cauchy_map_iff_exists_tendsto.mp
    have hn : Cauchy (𝓝[Ioo a b] t) := cauchy_nhds.mono nhdsWithin_le_nhds
    exact hn.map_of_le hf inf_le_right

/-- An actual solution with a uniform linear-growth derivative bound extends continuously
across both finite endpoints; no endpoint values of the original solution are used. -/
theorem exists_continuousOn_Icc_extension_of_norm_deriv_le_mul
    {f f' : ℝ → E} {a b c L : ℝ}
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hL : 0 ≤ L) (hg : ∀ t ∈ Ioo a b, ‖f' t‖ ≤ L * ‖f t‖)
    (hc : c ∈ Ioo a b) :
    ∃ F : ℝ → E, ContinuousOn F (Icc a b) ∧ EqOn F f (Ioo a b) := by
  obtain ⟨M, hM⟩ := exists_lipschitzOnWith_of_norm_deriv_le_mul hf hL hg hc
  exact exists_continuousOn_Icc_extension_of_uniformContinuousOn
    (hc.1.trans hc.2) hM.uniformContinuousOn

open Matrix
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]



/-- Continuous coefficients on the closed interval extend every actual interior Hamiltonian
solution continuously to both endpoints, irrespective of any singular Jacobi matrices. -/
theorem exists_continuous_hamiltonian_extension
    {K R A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hK : ∀ t ∈ Ioo a b, HasDerivAt K (B t * K t + C t * R t) t)
    (hR : ∀ t ∈ Ioo a b, HasDerivAt R (-A t * K t - (B t)ᵀ * R t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b)) (hc : c ∈ Ioo a b) :
    ∃ Kbar Rbar : ℝ → Matrix n n ℝ,
      ContinuousOn Kbar (Icc a b) ∧ ContinuousOn Rbar (Icc a b) ∧
      EqOn Kbar K (Ioo a b) ∧ EqOn Rbar R (Ioo a b) := by
  have hBT : ContinuousOn (fun t ↦ (B t)ᵀ) (Icc a b) :=
    continuous_id.matrix_transpose.comp_continuousOn hB
  have hg : ContinuousOn (fun t ↦ ‖A t‖ + ‖B t‖ + ‖C t‖ + ‖(B t)ᵀ‖) (Icc a b) :=
    ((hA.norm.add hB.norm).add hC.norm).add hBT.norm
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image hg
  let f : ℝ → Matrix n n ℝ × Matrix n n ℝ := fun t ↦ (K t, R t)
  let f' : ℝ → Matrix n n ℝ × Matrix n n ℝ :=
    fun t ↦ (B t * K t + C t * R t, -A t * K t - (B t)ᵀ * R t)
  have hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t := fun t ht ↦
    (hK t ht).prodMk (hR t ht)
  have hbound : ∀ t ∈ Ioo a b, ‖f' t‖ ≤ max L 0 * ‖f t‖ := by
    intro t ht
    exact (norm_hamiltonian_pair_le (A t) (B t) (C t) (K t) (R t)).trans
      (mul_le_mul_of_nonneg_right
        ((hL (mem_image_of_mem _ ⟨ht.1.le, ht.2.le⟩)).trans (le_max_left _ _))
        (norm_nonneg _))
  obtain ⟨F, hFcont, hFeq⟩ := exists_continuousOn_Icc_extension_of_norm_deriv_le_mul
    hf (le_max_right L 0) hbound hc
  exact ⟨fun t ↦ (F t).1, fun t ↦ (F t).2, hFcont.fst, hFcont.snd,
    fun t ht ↦ congrArg Prod.fst (hFeq ht), fun t ht ↦ congrArg Prod.snd (hFeq ht)⟩


/-- The second solution built from the actual compliance integral has continuous endpoint
extensions even when the compliance primitive itself diverges there. -/
theorem exists_continuous_integral_second_jacobi_extension
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c) :
    ∃ Kbar Rbar : ℝ → Matrix n n ℝ,
      ContinuousOn Kbar (Icc a b) ∧ ContinuousOn Rbar (Icc a b) ∧
      EqOn Kbar (fun t ↦ J t * jacobiCompliancePrimitive J C c t) (Ioo a b) ∧
      EqOn Rbar (fun t ↦ P t * jacobiCompliancePrimitive J C c t + (J t)⁻¹ᵀ)
        (Ioo a b) := by
  have hsol := fun t (ht : t ∈ Ioo a b) ↦
    hasDerivAt_integral_second_jacobi_solution
      hJ hP hAsym hCsym (hC.mono Ioo_subset_Icc_self) hd hc hinit ht
  exact exists_continuous_hamiltonian_extension
    (fun t ht ↦ (hsol t ht).1) (fun t ht ↦ (hsol t ht).2) hA hB hC hc

/-- The actual compliance integral satisfies the endpoint-uniform weighted determinant bounds.
Continuity of the Hamiltonian coefficients supplies both matrix extensions; nonsingularity is
required only in the open interval, and the primitive need not have finite endpoint limits. -/
theorem exists_integral_weighted_det_bound
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c) :
    ∃ M : ℝ, ∀ t ∈ Ioo a b,
      |(1 + jacobiCompliancePrimitive J C c t).det| * |(J t).det| ≤ M ∧
      |(1 - jacobiCompliancePrimitive J C c t).det| * |(J t).det| ≤ M := by
  obtain ⟨Jbar, Pbar, hJbar, _, hJeq, _⟩ :=
    exists_continuous_hamiltonian_extension hJ hP hA hB hC hc
  obtain ⟨Kbar, Rbar, hKbar, _, hKeq, _⟩ :=
    exists_continuous_integral_second_jacobi_extension
      hJ hP hA hB hC hAsym hCsym hd hc hinit
  have hKT : ∀ t ∈ Ioo a b, Kbar t = Jbar t * jacobiCompliancePrimitive J C c t := by
    intro t ht
    rw [hJeq ht]
    exact hKeq ht
  obtain ⟨M, hM⟩ := exists_weighted_det_cancellation_bound hJbar hKbar hKT
  refine ⟨M, fun t ht ↦ ?_⟩
  simpa only [hJeq ht] using hM t ht

end OTSelector.Geometry
