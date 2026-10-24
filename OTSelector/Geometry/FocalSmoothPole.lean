import OTSelector.Geometry.FocalAsymptotics
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Smooth inverse poles at regular focal crossings

For a real matrix curve smooth on an open neighborhood of zero, a regular kernel-to-cokernel
crossing yields an exact inverse expansion `J(s)⁻¹ = s⁻¹ • R + B(s)` on a smaller punctured
neighborhood. The remainder is smooth through zero and the residue has rank equal to the
nullity of `J(0)`. The projection and the invertibility of the rescaled matrix are derived.

The analytic ingredient is smooth division of `f(s) - f(0)` by `s`. Its proof identifies the
filled quotient with the integral of `f'(t*s)` over the unit interval. Smoothness of that
parameter integral follows from the parameterized convolution theorem with restricted
Lebesgue measure and a compact cutoff. A local cutoff transfers the result to curves smooth
on an actual open neighborhood, retaining one common neighborhood for all derivative orders.

The final corollary multiplies the inverse by any smooth second-solution curve. These are
finite-dimensional curve results; identifying the curves and crossing with genuine Finsler
Jacobi fields is a separate geometric interface.
-/

open Set Filter Matrix MeasureTheory Metric
open scoped Topology Matrix.Norms.Operator Convolution Interval ContDiff

namespace OTSelector.Geometry.FocalSmoothPole

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A compact parameter integral of a globally smooth curve is smooth. -/
theorem contDiff_average_deriv {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun s : ℝ ↦ ∫ t in (0 : ℝ)..1, deriv f (t * s)) := by
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let g : ℝ → ℝ → E := fun s x ↦ χ x • deriv f (-x * s)
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
    exact (χ.contDiff.comp contDiff_snd).smul
      (hd.comp (contDiff_snd.neg.mul contDiff_fst))
  have hgs : ∀ p x, p ∈ (univ : Set ℝ) → x ∉ closedBall (0 : ℝ) 2 → g p x = 0 := by
    intro p x _ hx
    have hz : χ x = 0 := χ.zero_of_le_dist (le_of_lt (not_le.mp hx))
    simp only [g, hz, zero_smul]
  have hi : Integrable (fun _ : ℝ ↦ (1 : ℝ)) μ := integrable_const 1
  have hconv := contDiffOn_convolution_right_with_param
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    isOpen_univ (isCompact_closedBall (0 : ℝ) 2) hgs hi.locallyIntegrable hg.contDiffOn
  have hfull : ContDiff ℝ ∞
      (fun q : ℝ × ℝ ↦ ((fun _ : ℝ ↦ (1 : ℝ)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, μ] g q.1) q.2) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using hconv
  have hs := hfull.comp (contDiff_id.prodMk (contDiff_const (c := (0 : ℝ))))
  convert hs using 1
  funext s
  simp only [Function.comp_def, convolution, ContinuousLinearMap.lsmul_apply,
    one_smul, zero_sub, g, neg_neg, id_eq, μ]
  rw [intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have hχ : χ (-t) = 1 := χ.one_of_mem_closedBall (by
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht.1.le]
    exact ht.2)
  simp only [hχ, one_smul]

/-- The smooth average of the derivative is exactly the continuously filled difference quotient. -/
theorem dslope_eq_average_deriv {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (s : ℝ) :
    dslope f 0 s = ∫ t in (0 : ℝ)..1, deriv f (t * s) := by
  by_cases hs : s = 0
  · subst s
    simp
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ f (t * s))
      (s • deriv f (t * s)) t := by
    intro t
    have h := ((hf.differentiable (by simp)) (t * s)).hasDerivAt.scomp t
      ((hasDerivAt_id t).mul_const s)
    simpa only [Function.comp_def, one_mul, id_eq] using h
  have hint : IntervalIntegrable (fun t : ℝ ↦ s • deriv f (t * s)) volume 0 1 :=
    ((hd.continuous.comp (continuous_id.mul_const s)).const_smul s).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t) hint
  simp only [zero_mul, one_mul, intervalIntegral.integral_smul] at h
  rw [dslope_of_ne f hs, slope_def_module, sub_zero, ← h]
  simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- Division of a smooth vanishing difference by its scalar increment remains smooth. -/
theorem contDiff_dslope_zero {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dslope f 0) := by
  convert contDiff_average_deriv hf using 1
  funext s
  exact dslope_eq_average_deriv hf s

omit [CompleteSpace E] in
/-- A curve smooth on a neighborhood has a globally smooth representative of its germ. -/
theorem exists_smooth_germ_representative {f : ℝ → E} {U : Set ℝ}
    (hU : IsOpen U) (h0 : 0 ∈ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : ℝ → E, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 0] f := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let χ : ContDiffBump (0 : ℝ) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hsupp : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    intro x hx
    apply hball
    exact lt_of_le_of_lt hx (by change r / 2 < r; linarith)
  refine ⟨fun x ↦ χ x • f x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact χ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have hz : χ =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hsupp h))
      apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp only [hy, Pi.zero_apply, zero_smul]
  · filter_upwards [χ.eventuallyEq_one] with x hx
    simp only [hx, Pi.one_apply, one_smul]

/-- Smoothness of the filled difference quotient is local in the original curve. -/
theorem contDiffAt_dslope_zero {f : ℝ → E} {U : Set ℝ}
    (hU : IsOpen U) (h0 : 0 ∈ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffAt ℝ ∞ (dslope f 0) 0 := by
  obtain ⟨g, hg, heq⟩ := exists_smooth_germ_representative hU h0 hf
  have hderiv : deriv g 0 = deriv f 0 := heq.deriv_eq
  have hzero : g 0 = f 0 := heq.eq_of_nhds
  apply (contDiff_dslope_zero hg).contDiffAt.congr_of_eventuallyEq
  filter_upwards [heq] with s hs
  by_cases hs0 : s = 0
  · subst s
    simpa only [dslope_same] using hderiv.symm
  · simp only [dslope_of_ne _ hs0, slope_def_module, hs, hzero]

/-- Smooth scalar division holds on the whole open neighborhood of the base point. -/
theorem contDiffOn_dslope_zero {f : ℝ → E} {U : Set ℝ}
    (hU : IsOpen U) (h0 : 0 ∈ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (dslope f 0) U := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact (contDiffAt_dslope_zero hU h0 hf).contDiffWithinAt
  · have h := (contDiffAt_id.inv hx0).smul
      ((hf.contDiffAt (hU.mem_nhds hx)).sub (contDiffAt_const (c := f 0)))
    have hd : ContDiffAt ℝ ∞ (dslope f 0) x := by
      apply h.congr_of_eventuallyEq
      filter_upwards [dslope_eventuallyEq_slope_of_ne f hx0] with s hs
      simpa only [slope_def_module, sub_zero, Pi.smul_apply, Pi.inv_apply, id_eq] using! hs
    exact hd.contDiffWithinAt

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The kernel columns are divided by the scalar variable and smoothly filled at zero. -/
noncomputable def desingularizedCurve (J : ℝ → Matrix n n ℝ) (P : Matrix n n ℝ) :
    ℝ → Matrix n n ℝ :=
  fun s ↦ J s * (1 - P) + dslope J 0 s * P

/-- The filled matrix rescaling is smooth on the original neighborhood. -/
theorem contDiffOn_desingularizedCurve {J : ℝ → Matrix n n ℝ} {U : Set ℝ}
    (hU : IsOpen U) (h0 : 0 ∈ U) (hJ : ContDiffOn ℝ ∞ J U) (P : Matrix n n ℝ) :
    ContDiffOn ℝ ∞ (desingularizedCurve J P) U := by
  exact (hJ.mul contDiffOn_const).add
    ((contDiffOn_dslope_zero hU h0 hJ).mul contDiffOn_const)

/-- At the crossing the filled rescaling is the crossing isomorphism. -/
theorem desingularizedCurve_zero (J : ℝ → Matrix n n ℝ) (P : Matrix n n ℝ)
    (hJP : J 0 * P = 0) :
    desingularizedCurve J P 0 = J 0 + deriv J 0 * P := by
  simp [desingularizedCurve, Matrix.mul_sub, hJP]
  rfl

/-- Away from the base point this rescaling gives the original matrix exactly. -/
theorem desingularizedCurve_factorization (J : ℝ → Matrix n n ℝ) (P : Matrix n n ℝ)
    (hPP : P * P = P) (hJP : J 0 * P = 0) {s : ℝ} (hs : s ≠ 0) :
    desingularizedCurve J P s * ((1 - P) + s • P) = J s := by
  simpa only [desingularizedCurve, dslope_of_ne J hs, slope_def_module, sub_zero,
    smul_mul_assoc, Matrix.sub_mul, hJP, sub_zero] using
    FocalAsymptotics.desingularized_factorization (J s) P hPP hs

/-- Nonsingular real matrices have a smooth inverse in the operator norm topology. -/
theorem contDiffAt_matrix_inverse {A : Matrix n n ℝ} (hA : A.det ≠ 0) :
    ContDiffAt ℝ ∞ (fun M : Matrix n n ℝ ↦ M⁻¹) A := by
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)
  rcases hu with ⟨u, rfl⟩
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  exact contDiffAt_ringInverse ℝ u

/-- Smoothness of a matrix curve passes to its inverse where its determinant is nonzero. -/
theorem contDiffOn_matrix_inverse {A : ℝ → Matrix n n ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hdet : ∀ s ∈ U, (A s).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun s ↦ (A s)⁻¹) U := by
  intro s hs
  exact ((contDiffAt_matrix_inverse (hdet s hs)).comp s
    (hA.contDiffAt (hU.mem_nhds hs))).contDiffWithinAt

/-- An idempotent appearing in a nonsingular crossing desingularization projects onto
exactly the kernel of the singular matrix. -/
theorem matrix_projection_range_eq_ker (P J D : Matrix n n ℝ)
    (hP : P * P = P) (hJP : J * P = 0) (hA : (J + D * P).det ≠ 0) :
    LinearMap.range P.mulVecLin = LinearMap.ker J.mulVecLin := by
  have hAJ : (J + D * P) * (1 - P) = J := by
    simp [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_assoc, hP, hJP]
  have hQ : 1 - P = (J + D * P)⁻¹ * J := by
    calc
      1 - P = ((J + D * P)⁻¹ * (J + D * P)) * (1 - P) := by
        rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mul]
      _ = (J + D * P)⁻¹ * J := by rw [Matrix.mul_assoc, hAJ]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change J *ᵥ (P *ᵥ y) = 0
    rw [Matrix.mulVec_mulVec, hJP, Matrix.zero_mulVec]
  · intro hx
    refine ⟨x, ?_⟩
    have hz : (1 - P) *ᵥ x = 0 := by
      rw [hQ, ← Matrix.mulVec_mulVec]
      change (J + D * P)⁻¹ *ᵥ (J.mulVecLin x) = 0
      rw [LinearMap.mem_ker.mp hx, Matrix.mulVec_zero]
    have hxP : x - P *ᵥ x = 0 := by
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hz
    exact (sub_eq_zero.mp hxP).symm

/-- The projection rank is the nullity of the singular matrix. -/
theorem matrix_projection_rank_eq_finrank_ker (P J D : Matrix n n ℝ)
    (hP : P * P = P) (hJP : J * P = 0) (hA : (J + D * P).det ≠ 0) :
    P.rank = Module.finrank ℝ (LinearMap.ker J.mulVecLin) := by
  rw [Matrix.rank, matrix_projection_range_eq_ker P J D hP hJP hA]

/-- The inverse residue has the same rank as the kernel projection. -/
theorem matrix_residue_rank_eq_finrank_ker (P J D : Matrix n n ℝ)
    (hP : P * P = P) (hJP : J * P = 0) (hA : (J + D * P).det ≠ 0) :
    (P * (J + D * P)⁻¹).rank = Module.finrank ℝ (LinearMap.ker J.mulVecLin) := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ P
    (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hA))]
  exact matrix_projection_rank_eq_finrank_ker P J D hP hJP hA


end OTSelector.Geometry.FocalSmoothPole

namespace OTSelector.Geometry

open FocalSmoothPole

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A smooth regular crossing has an exact simple inverse pole with a smooth remainder.
Both the desingularization and local nonsingularity are derived from the crossing. -/
theorem exists_smooth_focal_inverse_pole {J : ℝ → Matrix n n ℝ} {U : Set ℝ}
    (hU : IsOpen U) (h0 : 0 ∈ U) (hJ : ContDiffOn ℝ ∞ J U)
    (hcross : ∀ u, J 0 *ᵥ u = 0 →
      deriv J 0 *ᵥ u ∈ LinearMap.range (J 0).mulVecLin → u = 0) :
    ∃ (V : Set ℝ) (R : Matrix n n ℝ) (B : ℝ → Matrix n n ℝ),
      IsOpen V ∧ 0 ∈ V ∧ V ⊆ U ∧ ContDiffOn ℝ ∞ B V ∧
      (∀ s ∈ V, s ≠ 0 → (J s).det ≠ 0 ∧ (J s)⁻¹ = s⁻¹ • R + B s) ∧
      R.rank = Module.finrank ℝ (LinearMap.ker (J 0).mulVecLin) ∧
      (0 < Module.finrank ℝ (LinearMap.ker (J 0).mulVecLin) → R ≠ 0) := by
  obtain ⟨P, hPP, hJP, hdet, hscale, hPzero⟩ :=
    FocalAsymptotics.exists_projection (J 0) (deriv J 0) hcross
  let A := desingularizedCurve J P
  have hA : ContDiffOn ℝ ∞ A U := contDiffOn_desingularizedCurve hU h0 hJ P
  have hA0 : A 0 = J 0 + deriv J 0 * P := desingularizedCurve_zero J P hJP
  let V := U ∩ (fun s ↦ (A s).det) ⁻¹' ({0}ᶜ)
  have hV : IsOpen V :=
    (continuous_id.matrix_det.comp_continuousOn hA.continuousOn).isOpen_inter_preimage
      hU isClosed_singleton.isOpen_compl
  have hV0 : 0 ∈ V := ⟨h0, by simpa only [mem_preimage, mem_compl_iff,
    mem_singleton_iff, hA0] using hdet⟩
  have hVU : V ⊆ U := inter_subset_left
  have hAdet : ∀ s ∈ V, (A s).det ≠ 0 := fun s hs ↦ hs.2
  have hAi : ContDiffOn ℝ ∞ (fun s ↦ (A s)⁻¹) V :=
    contDiffOn_matrix_inverse hV (hA.mono hVU) hAdet
  let L : ℝ → Matrix n n ℝ := fun s ↦ (s • (1 - P) + P) * (A s)⁻¹
  have hL : ContDiffOn ℝ ∞ L V :=
    ((contDiffOn_id.smul contDiffOn_const).add contDiffOn_const).mul hAi
  have hL0 : L 0 = P * (J 0 + deriv J 0 * P)⁻¹ := by
    simp only [L, zero_smul, zero_add, hA0]
  refine ⟨V, L 0, dslope L 0, hV, hV0, hVU,
    contDiffOn_dslope_zero hV hV0 hL, ?_, ?_, ?_⟩
  · intro s hs hs0
    have hfac : A s * ((1 - P) + s • P) = J s :=
      desingularizedCurve_factorization J P hPP hJP hs0
    have hJs : (J s).det ≠ 0 := by
      rw [← hfac, Matrix.det_mul, hscale]
      exact mul_ne_zero (hAdet s hs) (pow_ne_zero _ hs0)
    refine ⟨hJs, ?_⟩
    have hscaled : s • (J s)⁻¹ = L s := by
      rw [← hfac]
      exact FocalAsymptotics.matrix_scaled_inverse_factorization P (A s) hPP s hs0
    have hsplit : s • dslope L 0 s = L s - L 0 := by
      simpa only [sub_zero] using sub_smul_dslope L 0 s
    have heq : s • (s⁻¹ • L 0 + dslope L 0 s) = s • (J s)⁻¹ := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hs0, one_smul, hsplit, hscaled]
      abel
    exact (smul_right_injective _ hs0 heq).symm
  · rw [hL0]
    exact matrix_residue_rank_eq_finrank_ker P (J 0) (deriv J 0) hPP hJP hdet
  · intro hk
    rw [hL0]
    apply FocalAsymptotics.matrix_mul_inverse_ne_zero P _ _ hdet
    intro hp
    have hz : Module.finrank ℝ (LinearMap.ker (J 0).mulVecLin) = 0 :=
      Submodule.finrank_eq_zero.mpr (hPzero hp)
    omega

/-- In particular the inverse pole has a locally bounded remainder, not only an `o(1/s)` error. -/
theorem exists_bounded_focal_inverse_remainder {J : ℝ → Matrix n n ℝ} {U : Set ℝ}
    (hU : IsOpen U) (h0 : 0 ∈ U) (hJ : ContDiffOn ℝ ∞ J U)
    (hcross : ∀ u, J 0 *ᵥ u = 0 →
      deriv J 0 *ᵥ u ∈ LinearMap.range (J 0).mulVecLin → u = 0) :
    ∃ (R : Matrix n n ℝ) (C : ℝ), 0 < C ∧
      R.rank = Module.finrank ℝ (LinearMap.ker (J 0).mulVecLin) ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℝ), ‖(J s)⁻¹ - s⁻¹ • R‖ ≤ C := by
  obtain ⟨V, R, B, hV, hV0, _, hB, hpole, hrank, _⟩ :=
    exists_smooth_focal_inverse_pole hU h0 hJ hcross
  have hcont : ContinuousAt B 0 := (hB.continuousOn.continuousAt (hV.mem_nhds hV0))
  have hb : ∀ᶠ s in 𝓝 (0 : ℝ), ‖B s‖ < ‖B 0‖ + 1 :=
    hcont.norm (gt_mem_nhds (by linarith : ‖B 0‖ < ‖B 0‖ + 1))
  have hVs : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ V := hV.mem_nhds hV0
  refine ⟨R, ‖B 0‖ + 1, by positivity, hrank, ?_⟩
  filter_upwards [hb.filter_mono nhdsWithin_le_nhds,
    hVs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hVs hs0
  rw [(hpole s hVs hs0).2]
  simpa only [add_sub_cancel_left] using hs.le

/-- Multiplication by any smooth second solution retains a simple pole and a smooth remainder.
The residue is the inverse residue times the endpoint value of the second solution. -/
theorem exists_smooth_focal_product_pole {J K : ℝ → Matrix n n ℝ} {U : Set ℝ}
    (hU : IsOpen U) (h0 : 0 ∈ U) (hJ : ContDiffOn ℝ ∞ J U)
    (hK : ContDiffOn ℝ ∞ K U)
    (hcross : ∀ u, J 0 *ᵥ u = 0 →
      deriv J 0 *ᵥ u ∈ LinearMap.range (J 0).mulVecLin → u = 0) :
    ∃ (V : Set ℝ) (R : Matrix n n ℝ) (B : ℝ → Matrix n n ℝ),
      IsOpen V ∧ 0 ∈ V ∧ V ⊆ U ∧ ContDiffOn ℝ ∞ B V ∧
      R.rank = Module.finrank ℝ (LinearMap.ker (J 0).mulVecLin) ∧
      ∀ s ∈ V, s ≠ 0 → (J s)⁻¹ * K s = s⁻¹ • (R * K 0) + B s := by
  obtain ⟨V, R, B, hV, hV0, hVU, hB, hpole, hrank, _⟩ :=
    exists_smooth_focal_inverse_pole hU h0 hJ hcross
  refine ⟨V, R, fun s ↦ R * dslope K 0 s + B s * K s,
    hV, hV0, hVU, ?_, hrank, ?_⟩
  · exact (contDiffOn_const.mul (contDiffOn_dslope_zero hV hV0 (hK.mono hVU))).add
      (hB.mul (hK.mono hVU))
  · intro s hs hs0
    change (J s)⁻¹ * K s = s⁻¹ • (R * K 0) + (R * dslope K 0 s + B s * K s)
    rw [(hpole s hs hs0).2, Matrix.add_mul, dslope_of_ne K hs0, slope_def_module,
      sub_zero, Matrix.mul_smul, Matrix.mul_sub, smul_sub, Matrix.smul_mul]
    abel

end OTSelector.Geometry
