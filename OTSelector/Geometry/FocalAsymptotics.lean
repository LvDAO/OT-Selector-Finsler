import OTSelector.Geometry.Jacobi.RegularCrossingAlgebra
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Determinant and inverse asymptotics at a regular focal endpoint

A one-sided derivative and an injective kernel-to-cokernel crossing give the exact
limits `det J(s) / s^k → d ≠ 0` and `s • J(s)⁻¹ → R`, where `k` is the endpoint kernel
dimension. If `k > 0`, the residue is nonzero, so both determinant and inverse operator
norm admit two-sided power bounds.

The proof chooses an algebraic complement of the endpoint kernel. Its projection `P`
gives `J(s) = A(s) * ((1 - P) + s • P)` and a nonsingular limit `A(s) → J(0) + D * P`.
Neither the projection nor this invertibility is an additional hypothesis. Nearby
invertibility of `J` follows from the resulting nonzero determinant-ratio limit.

The statements use the inward parameter `s → 0+`. The Hamiltonian wrapper consumes
an actual one-sided derivative, the Wronskian, full phase rank and a positive velocity
Hessian, as provided by the preceding Jacobi modules. This is a matrix-curve theorem;
it does not identify a particular Finsler Jacobi frame or assert uniformity across roots.
-/

open LinearMap Set Filter Matrix
open scoped Topology Matrix.Norms.Operator

namespace OTSelector.Geometry
namespace FocalAsymptotics

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Scale the kernel component while fixing a chosen complementary component. -/
noncomputable def scaleKernel (N Q : Submodule ℝ E) (h : IsCompl N Q) (s : ℝ) :
    E →ₗ[ℝ] E :=
  (LinearMap.id - N.projection Q h) + s • N.projection Q h

/-- Kernel scaling contributes precisely its dimension to the determinant exponent. -/
theorem det_scaleKernel (N Q : Submodule ℝ E) (h : IsCompl N Q) (s : ℝ) :
    (scaleKernel N Q h s).det = s ^ Module.finrank ℝ N := by
  let e := N.prodEquivOfIsCompl Q h
  have heq : e.symm.toLinearMap.comp ((scaleKernel N Q h s).comp e.toLinearMap) =
      (s • (LinearMap.id : N →ₗ[ℝ] N)).prodMap (LinearMap.id : Q →ₗ[ℝ] Q) := by
    apply LinearMap.ext
    intro v
    apply e.injective
    simp [e, scaleKernel, LinearMap.prodMap_apply]
  have hd := LinearMap.det_conj (scaleKernel N Q h s) e.symm
  simp only [LinearEquiv.symm_symm] at hd
  rw [heq] at hd
  simpa only [LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, mul_one] using hd.symm

/-- The factorization does not require J to be invertible. -/
theorem desingularized_factorization {R : Type*} [Ring R] [Algebra ℝ R] (J P : R) (hP : P * P = P)
    {s : ℝ} (hs : s ≠ 0) :
    (J * (1 - P) + s⁻¹ • (J * P)) * ((1 - P) + s • P) = J := by
  simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc]
  have hPP : (1 - P) * P = 0 := by noncomm_ring [hP]
  have hPP' : P * (1 - P) = 0 := by noncomm_ring [hP]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by noncomm_ring [hP]
  simp only [mul_assoc, hPP, hPP', hQQ, hP, mul_zero, smul_zero,
    add_zero, zero_add]
  simp only [smul_smul, mul_inv_cancel₀ hs, one_smul]
  noncomm_ring

omit [FiniteDimensional ℝ E] in
/-- Quotient crossing injectivity suffices for the desingularized limiting map. -/
theorem limit_injective (J D : E →ₗ[ℝ] E) (Q : Submodule ℝ E)
    (h : IsCompl (LinearMap.ker J) Q)
    (hcross : ∀ u, J u = 0 → D u ∈ LinearMap.range J → u = 0) :
    Function.Injective (J + D * (LinearMap.ker J).projection Q h) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  let P := (LinearMap.ker J).projection Q h
  have hPv : J (P v) = 0 := (LinearMap.ker J).projection_apply_mem h v
  have heq : J v + D (P v) = 0 := hv
  have hzero : P v = 0 := hcross (P v) hPv ⟨-v, by
    rw [map_neg]
    exact neg_eq_iff_add_eq_zero.mpr heq⟩
  have hJv : J v = 0 := by simpa only [hzero, map_zero, add_zero] using heq
  have hp : P v = v := Submodule.projection_apply_of_mem_left h hJv
  exact hp.symm.trans hzero

/-- In finite dimension, the desingularized limiting determinant is nonzero. -/
theorem limit_det_ne_zero (J D : E →ₗ[ℝ] E) (Q : Submodule ℝ E)
    (h : IsCompl (LinearMap.ker J) Q)
    (hcross : ∀ u, J u = 0 → D u ∈ LinearMap.range J → u = 0) :
    (J + D * (LinearMap.ker J).projection Q h).det ≠ 0 := by
  intro hdet
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet)
    (LinearMap.ker_eq_bot.mpr (limit_injective J D Q h hcross))

/-- One-sided endpoint differentiability is enough for the slope limit. -/
theorem slope_right {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : ℝ → F} {D : F} (h : HasDerivWithinAt J D (Ioi 0) 0) :
    Tendsto (fun s : ℝ ↦ s⁻¹ • (J s - J 0)) (𝓝[>] 0) (𝓝 D) := by
  have hh :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp h
  convert! hh using 1
  funext s
  simp only [slope_def_module, sub_zero]

/-- All analytic desingularization is slope convergence and continuous matrix multiplication. -/
theorem desingularized_tendsto {n : Type*} [Fintype n] [DecidableEq n]
    {J : ℝ → Matrix n n ℝ} {J0 D0 P : Matrix n n ℝ} {l : Filter ℝ}
    (hJ : Tendsto J l (𝓝 J0))
    (hD : Tendsto (fun s : ℝ ↦ s⁻¹ • (J s - J0)) l (𝓝 D0))
    (hJP : J0 * P = 0) :
    Tendsto (fun s : ℝ ↦ J s * (1 - P) + s⁻¹ • (J s * P)) l
      (𝓝 (J0 + D0 * P)) := by
  have h := (hJ.mul_const (1 - P)).add (hD.mul_const P)
  simpa only [smul_mul_assoc, sub_mul, hJP, sub_zero, mul_sub, mul_one] using! h

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Projection algebra provides the determinant scaling without orthogonality. -/
theorem exists_projection (J D : Matrix n n ℝ)
    (hcross : ∀ u, J *ᵥ u = 0 → D *ᵥ u ∈ LinearMap.range J.mulVecLin → u = 0) :
    ∃ P : Matrix n n ℝ,
      P * P = P ∧ J * P = 0 ∧ (J + D * P).det ≠ 0 ∧
      (∀ s : ℝ, ((1 - P) + s • P).det = s ^ Module.finrank ℝ (ker J.mulVecLin)) ∧
      (P = 0 → ker J.mulVecLin = ⊥) := by
  obtain ⟨Q, hQ⟩ := (ker J.mulVecLin).exists_isCompl
  let p := (ker J.mulVecLin).projection Q hQ
  let P := LinearMap.toMatrix' p
  have hpp : p * p = p := Submodule.isIdempotentElem_projection hQ
  have hjp : J.mulVecLin * p = 0 := by
    apply LinearMap.ext
    intro v
    exact (ker J.mulVecLin).projection_apply_mem hQ v
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [P, ← LinearMap.toMatrix'_mul] using congrArg LinearMap.toMatrix' hpp
  · apply Matrix.toLin'.injective
    change Matrix.toLin' (J * LinearMap.toMatrix' p) = Matrix.toLin' 0
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_apply', map_zero]
    exact hjp
  · have hd := limit_det_ne_zero J.mulVecLin D.mulVecLin Q hQ hcross
    rw [← LinearMap.det_toLin']
    change (Matrix.toLin' (J + D * LinearMap.toMatrix' p)).det ≠ 0
    rw [map_add, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact hd
  · intro s
    rw [← LinearMap.det_toLin']
    simpa only [map_add, map_sub, map_smul, Matrix.toLin'_one,
      Matrix.toLin'_toMatrix', scaleKernel, P, p] using
      det_scaleKernel (ker J.mulVecLin) Q hQ s
  · intro hp
    have hp' : p = 0 := by
      apply LinearMap.toMatrix'.injective
      simpa only [map_zero] using hp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hfix : p v = v := Submodule.projection_apply_of_mem_left hQ hv
    simpa only [hp', LinearMap.zero_apply] using hfix.symm
/-- Projection rescaling turns the endpoint derivative into a nonsingular determinant limit. -/
theorem det_ratio_tendsto {J : ℝ → Matrix n n ℝ} {D P : Matrix n n ℝ} {k : ℕ}
    (hJ : HasDerivWithinAt J D (Ioi 0) 0) (hPP : P * P = P)
    (hJP : J 0 * P = 0)
    (hS : ∀ s : ℝ, ((1 - P) + s • P).det = s ^ k) :
    Tendsto (fun s : ℝ ↦ (J s).det / s ^ k) (𝓝[>] 0) (𝓝 (J 0 + D * P).det) := by
  have hA := desingularized_tendsto hJ.continuousWithinAt (slope_right hJ) hJP
  have hd := continuous_id.matrix_det.continuousAt.tendsto.comp hA
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hf := desingularized_factorization (J s) P hPP hs0
  change (J s * (1 - P) + s⁻¹ • (J s * P)).det = (J s).det / s ^ k
  have hdet := congrArg Matrix.det hf
  rw [Matrix.det_mul, hS] at hdet
  rw [← hdet]
  exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hs0)).symm

/-- The original curve is nonsingular sufficiently near every regular crossing. -/
theorem eventually_det_ne_zero_of_ratio_tendsto {J : ℝ → Matrix n n ℝ}
    {k : ℕ} {d : ℝ}
    (hd : Tendsto (fun s : ℝ ↦ (J s).det / s ^ k) (𝓝[>] 0) (𝓝 d)) (hd0 : d ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (J s).det ≠ 0 := by
  have he := hd.eventually (isOpen_ne.mem_nhds hd0)
  filter_upwards [he] with s hs
  intro hzero
  exact hs (by simp [hzero])
/-- Scaling an idempotent by a nonzero scalar has an explicit inverse. -/
theorem matrix_idempotent_scale_inverse (P : Matrix n n ℝ)
    (hP : P * P = P) (s : ℝ) (hs : s ≠ 0) :
    ((1 - P) + s • P)⁻¹ = (1 - P) + s⁻¹ • P := by
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp [Matrix.sub_mul, Matrix.mul_sub, hP]
  have hQP : (1 - P) * P = 0 := by
    simp [Matrix.sub_mul, hP]
  have hPQ : P * (1 - P) = 0 := by
    simp [Matrix.mul_sub, hP]
  apply Matrix.inv_eq_left_inv
  calc
    ((1 - P) + s⁻¹ • P) * ((1 - P) + s • P) =
        (1 - P) + (s * s⁻¹) • P := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        hQQ, hQP, hPQ, hP, smul_zero, add_zero, zero_add, smul_smul]
    _ = 1 := by simp [hs]

/-- The inverse of the factored matrix has an exact desingularized expression. -/
theorem matrix_scaled_inverse_factorization (P A : Matrix n n ℝ)
    (hP : P * P = P) (s : ℝ) (hs : s ≠ 0) :
    s • (A * ((1 - P) + s • P))⁻¹ = (s • (1 - P) + P) * A⁻¹ := by
  rw [Matrix.mul_inv_rev, matrix_idempotent_scale_inverse P hP s hs,
    ← Matrix.smul_mul, smul_add, smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- Multiplication by an invertible matrix cannot annihilate a nonzero matrix. -/
theorem matrix_mul_inverse_ne_zero (P A : Matrix n n ℝ)
    (hP : P ≠ 0) (hA : A.det ≠ 0) : P * A⁻¹ ≠ 0 := by
  intro hzero
  apply hP
  have h := congrArg (fun M : Matrix n n ℝ ↦ M * A) hzero
  simpa only [Matrix.nonsing_inv_mul_cancel_right A P (isUnit_iff_ne_zero.mpr hA),
    Matrix.zero_mul] using h

/-- The scaled inverse converges to an explicit residue obtained from the kernel projection. -/
theorem scaled_inverse_tendsto {J : ℝ → Matrix n n ℝ} {D P : Matrix n n ℝ}
    (hJ : HasDerivWithinAt J D (Ioi 0) 0) (hPP : P * P = P)
    (hJP : J 0 * P = 0) (hdet : (J 0 + D * P).det ≠ 0) :
    Tendsto (fun s : ℝ ↦ s • (J s)⁻¹) (𝓝[>] 0) (𝓝 (P * (J 0 + D * P)⁻¹)) := by
  have hA := desingularized_tendsto hJ.continuousWithinAt (slope_right hJ) hJP
  have hi : ContinuousAt (fun A : Matrix n n ℝ ↦ A⁻¹) (J 0 + D * P) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)
  have ht : Tendsto (fun s : ℝ ↦ s) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun s : ℝ ↦ s • (1 - P) + P) (𝓝[>] 0) (𝓝 P) := by
    simpa only [zero_smul, zero_add] using
      (ht.smul_const (1 - P)).add_const P
  have h := hs.mul (hi.tendsto.comp hA)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hf := desingularized_factorization (J s) P hPP hs0
  have hi := matrix_scaled_inverse_factorization P
    (J s * (1 - P) + s⁻¹ • (J s * P)) hPP s hs0
  rw [hf] at hi
  exact hi.symm

end FocalAsymptotics

open FocalAsymptotics

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A regular one-sided crossing has a nonzero normalized determinant limit and a finite
scaled-inverse residue. A positive-dimensional kernel makes the residue nonzero. The
projection and its limiting invertibility are constructed, not assumptions. -/
theorem exists_regular_focal_limits {J : ℝ → Matrix n n ℝ} {D : Matrix n n ℝ}
    (hJ : HasDerivWithinAt J D (Ioi 0) 0)
    (hcross : ∀ u, J 0 *ᵥ u = 0 → D *ᵥ u ∈ LinearMap.range (J 0).mulVecLin → u = 0) :
    ∃ d : ℝ, ∃ R : Matrix n n ℝ, d ≠ 0 ∧
      Tendsto (fun s : ℝ ↦ (J s).det / s ^ Module.finrank ℝ (ker (J 0).mulVecLin))
        (𝓝[>] 0) (𝓝 d) ∧
      Tendsto (fun s : ℝ ↦ s • (J s)⁻¹) (𝓝[>] 0) (𝓝 R) ∧
      (0 < Module.finrank ℝ (ker (J 0).mulVecLin) → R ≠ 0) := by
  obtain ⟨P, hPP, hJP, hdet, hS, hker⟩ := exists_projection (J 0) D hcross
  refine ⟨(J 0 + D * P).det, P * (J 0 + D * P)⁻¹, hdet,
    det_ratio_tendsto hJ hPP hJP hS, scaled_inverse_tendsto hJ hPP hJP hdet, ?_⟩
  intro hk
  apply matrix_mul_inverse_ne_zero _ _ ?_ hdet
  intro hp
  have hz : Module.finrank ℝ (ker (J 0).mulVecLin) = 0 :=
    Submodule.finrank_eq_zero.mpr (hker hp)
  omega
/-- A nonzero limit supplies positive eventual lower and upper bounds for the norm. -/
theorem eventually_norm_sandwich_of_tendsto_ne_zero
    {α E : Type*} [NormedAddCommGroup E] {l : Filter α}
    {f : α → E} {a : E} (hf : Tendsto f l (𝓝 a)) (ha : a ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ s in l, c ≤ ‖f s‖ ∧ ‖f s‖ ≤ C := by
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  refine ⟨‖a‖ / 2, ‖a‖ + 1, half_pos ha', by positivity, ?_⟩
  exact (hf.norm.eventually_const_le (half_lt_self ha')).and
    (hf.norm.eventually_le_const (by linarith))

/-- A nonzero limit of `s • f s` gives two-sided inverse-rate bounds as `s → 0+`. -/
theorem eventually_inverse_rate_sandwich_of_smul_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a : E}
    (hf : Tendsto (fun s ↦ s • f s) (𝓝[>] (0 : ℝ)) (𝓝 a)) (ha : a ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), c / |s| ≤ ‖f s‖ ∧ ‖f s‖ ≤ C / |s| := by
  obtain ⟨c, C, hc, hC, hb⟩ := eventually_norm_sandwich_of_tendsto_ne_zero hf ha
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hb, self_mem_nhdsWithin] with s hs hsp
  have habs : 0 < |s| := abs_pos.mpr (ne_of_gt hsp)
  simp only [norm_smul, Real.norm_eq_abs] at hs
  constructor
  · exact (div_le_iff₀ habs).mpr (by simpa only [mul_comm] using hs.1)
  · exact (le_div_iff₀ habs).mpr (by simpa only [mul_comm] using hs.2)

/-- A nonzero limit of `f s / s ^ k` gives two-sided order-`k` bounds as `s → 0+`. -/
theorem eventually_power_sandwich_of_div_tendsto
    {f : ℝ → ℝ} {a : ℝ} (k : ℕ)
    (hf : Tendsto (fun s ↦ f s / s ^ k) (𝓝[>] (0 : ℝ)) (𝓝 a)) (ha : a ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), c * |s| ^ k ≤ |f s| ∧ |f s| ≤ C * |s| ^ k := by
  obtain ⟨c, C, hc, hC, hb⟩ := eventually_norm_sandwich_of_tendsto_ne_zero hf ha
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hb, self_mem_nhdsWithin] with s hs hsp
  have habs : 0 < |s| ^ k := pow_pos (abs_pos.mpr (ne_of_gt hsp)) k
  simp only [norm_div, norm_pow, Real.norm_eq_abs] at hs
  exact ⟨(le_div_iff₀ habs).mp hs.1, (div_le_iff₀ habs).mp hs.2⟩

/-- A nonzero matrix residue supplies two-sided inverse-norm bounds in the operator norm. -/
theorem matrix_inverse_sandwich_of_residue_tendsto
    {n : Type*} [Fintype n] [DecidableEq n]
    {J : ℝ → Matrix n n ℝ} {R : Matrix n n ℝ}
    (hJ : Tendsto (fun s ↦ s • (J s)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 R)) (hR : R ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), c / |s| ≤ ‖(J s)⁻¹‖ ∧ ‖(J s)⁻¹‖ ≤ C / |s| :=
  eventually_inverse_rate_sandwich_of_smul_tendsto hJ hR

/-- A nonzero determinant-ratio limit supplies two-sided determinant bounds. -/
theorem matrix_det_sandwich_of_ratio_tendsto
    {n : Type*} [Fintype n] [DecidableEq n]
    {J : ℝ → Matrix n n ℝ} {a : ℝ} (k : ℕ)
    (hJ : Tendsto (fun s ↦ (J s).det / s ^ k) (𝓝[>] (0 : ℝ)) (𝓝 a)) (ha : a ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        c * |s| ^ k ≤ |(J s).det| ∧ |(J s).det| ≤ C * |s| ^ k :=
  eventually_power_sandwich_of_div_tendsto k hJ ha

/-- At a regular focal endpoint of multiplicity `k > 0`, the determinant has exact order `k`
and the inverse operator norm has exact order one. No nonsingularity near the endpoint is
assumed; it follows from the determinant bound. -/
theorem regular_focal_two_sided_bounds {J : ℝ → Matrix n n ℝ} {D : Matrix n n ℝ}
    (hJ : HasDerivWithinAt J D (Ioi 0) 0)
    (hcross : ∀ u, J 0 *ᵥ u = 0 → D *ᵥ u ∈ LinearMap.range (J 0).mulVecLin → u = 0)
    (hk : 0 < Module.finrank ℝ (ker (J 0).mulVecLin)) :
    ∃ cdet Cdet cinv Cinv : ℝ,
      0 < cdet ∧ 0 < Cdet ∧ 0 < cinv ∧ 0 < Cinv ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        cdet * |s| ^ Module.finrank ℝ (ker (J 0).mulVecLin) ≤ |(J s).det| ∧
        |(J s).det| ≤ Cdet * |s| ^ Module.finrank ℝ (ker (J 0).mulVecLin) ∧
        cinv / |s| ≤ ‖(J s)⁻¹‖ ∧ ‖(J s)⁻¹‖ ≤ Cinv / |s| := by
  obtain ⟨d, R, hd, hdt, hRt, hR⟩ := exists_regular_focal_limits hJ hcross
  obtain ⟨cdet, Cdet, hcd, hCd, hdB⟩ := matrix_det_sandwich_of_ratio_tendsto _ hdt hd
  obtain ⟨cinv, Cinv, hci, hCi, hiB⟩ :=
    matrix_inverse_sandwich_of_residue_tendsto hRt (hR hk)
  refine ⟨cdet, Cdet, cinv, Cinv, hcd, hCd, hci, hCi, ?_⟩
  filter_upwards [hdB, hiB] with s hs hi
  exact ⟨hs.1, hs.2, hi⟩

/-- The intrinsic quotient crossing is enough to apply the limit theorem. -/
theorem exists_regular_focal_limits_of_bijective_crossing
    {J : ℝ → Matrix n n ℝ} {D : Matrix n n ℝ}
    (hJ : HasDerivWithinAt J D (Ioi 0) 0)
    (hcross : Function.Bijective (focalCrossingMap (J 0) D)) :
    ∃ d : ℝ, ∃ R : Matrix n n ℝ, d ≠ 0 ∧
      Tendsto (fun s : ℝ ↦ (J s).det / s ^ Module.finrank ℝ (ker (J 0).mulVecLin))
        (𝓝[>] 0) (𝓝 d) ∧
      Tendsto (fun s : ℝ ↦ s • (J s)⁻¹) (𝓝[>] 0) (𝓝 R) ∧
      (0 < Module.finrank ℝ (ker (J 0).mulVecLin) → R ≠ 0) := by
  apply exists_regular_focal_limits hJ
  intro u hu hr
  have hz : focalCrossingMap (J 0) D ⟨u, hu⟩ = 0 := by
    change Submodule.Quotient.mk (D *ᵥ u) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hr
  have he := hcross.1 (hz.trans (map_zero (focalCrossingMap (J 0) D)).symm)
  exact congrArg Subtype.val he

/-- Positive-Hessian Hamiltonian endpoint data supply the crossing input automatically.
The derivative is the actual one-sided derivative of the position curve. -/
theorem hamiltonian_regular_focal_two_sided_bounds
    {J : ℝ → Matrix n n ℝ} {P B C : Matrix n n ℝ}
    (hJ : HasDerivWithinAt J (B * J 0 + C * P) (Ici 0) 0)
    (hW : (J 0)ᵀ * P = Pᵀ * J 0)
    (hphase : ∀ u, J 0 *ᵥ u = 0 → P *ᵥ u = 0 → u = 0) (hC : C.PosDef)
    (hk : 0 < Module.finrank ℝ (ker (J 0).mulVecLin)) :
    ∃ cdet Cdet cinv Cinv : ℝ,
      0 < cdet ∧ 0 < Cdet ∧ 0 < cinv ∧ 0 < Cinv ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        cdet * |s| ^ Module.finrank ℝ (ker (J 0).mulVecLin) ≤ |(J s).det| ∧
        |(J s).det| ≤ Cdet * |s| ^ Module.finrank ℝ (ker (J 0).mulVecLin) ∧
        cinv / |s| ≤ ‖(J s)⁻¹‖ ∧ ‖(J s)⁻¹‖ ≤ Cinv / |s| := by
  exact regular_focal_two_sided_bounds (hJ.mono Ioi_subset_Ici_self)
    (fun _ hu hr ↦ focal_crossing_kernel_eq_zero hW hphase hC hu hr) hk

/-- Every regular crossing, including a zero-dimensional kernel, gives the determinant
comparison and an inverse upper bound. -/
theorem regular_crossing_bounds {J : ℝ → Matrix n n ℝ} {D : Matrix n n ℝ}
    (hJ : HasDerivWithinAt J D (Ioi 0) 0)
    (hcross : ∀ u, J 0 *ᵥ u = 0 → D *ᵥ u ∈ LinearMap.range (J 0).mulVecLin → u = 0) :
    ∃ cdet Cdet Cinv : ℝ, 0 < cdet ∧ 0 < Cdet ∧ 0 < Cinv ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        cdet * |s| ^ Module.finrank ℝ (ker (J 0).mulVecLin) ≤ |(J s).det| ∧
        |(J s).det| ≤ Cdet * |s| ^ Module.finrank ℝ (ker (J 0).mulVecLin) ∧
        ‖(J s)⁻¹‖ ≤ Cinv / |s| := by
  obtain ⟨d, R, hd, hdt, hRt, _⟩ := exists_regular_focal_limits hJ hcross
  obtain ⟨cdet, Cdet, hcd, hCd, hdB⟩ := matrix_det_sandwich_of_ratio_tendsto _ hdt hd
  have hiB := hRt.norm.eventually_le_const (show ‖R‖ < ‖R‖ + 1 by linarith)
  refine ⟨cdet, Cdet, ‖R‖ + 1, hcd, hCd, by positivity, ?_⟩
  filter_upwards [hdB, hiB, self_mem_nhdsWithin] with s hs hi hsp
  refine ⟨hs.1, hs.2, ?_⟩
  have hpos : 0 < |s| := abs_pos.mpr (ne_of_gt hsp)
  rw [norm_smul, Real.norm_eq_abs] at hi
  exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hi)
/-- Translation to inward distance preserves the derivative at the left endpoint. -/
theorem hasDerivWithinAt_left_inward_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : ℝ → E} {D : E} {a : ℝ}
    (hJ : HasDerivWithinAt J D (Ici a) a) :
    HasDerivWithinAt (fun s : ℝ ↦ J (a + s)) D (Ioi 0) 0 := by
  have hs : HasDerivWithinAt (fun s : ℝ ↦ a + s) 1 (Ioi 0) 0 :=
    ((hasDerivAt_id 0).const_add a).hasDerivWithinAt
  have hm : MapsTo (fun s : ℝ ↦ a + s) (Ioi 0) (Ici a) := by
    intro s hs
    change a ≤ a + s
    change 0 < s at hs
    exact le_add_of_nonneg_right hs.le
  simpa only [Function.comp_def, one_smul] using
    hJ.scomp_of_eq 0 hs hm (by simp)

/-- Reversing to inward distance negates the derivative at the right endpoint. -/
theorem hasDerivWithinAt_right_inward_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : ℝ → E} {D : E} {b : ℝ}
    (hJ : HasDerivWithinAt J D (Iic b) b) :
    HasDerivWithinAt (fun s : ℝ ↦ J (b - s)) (-D) (Ioi 0) 0 := by
  have hs : HasDerivWithinAt (fun s : ℝ ↦ b - s) (-1) (Ioi 0) 0 :=
    ((hasDerivAt_id 0).const_sub b).hasDerivWithinAt
  have hm : MapsTo (fun s : ℝ ↦ b - s) (Ioi 0) (Iic b) := by
    intro s hs
    change b - s ≤ b
    change 0 < s at hs
    exact sub_le_self b hs.le
  simpa only [Function.comp_def, neg_smul, one_smul] using
    hJ.scomp_of_eq 0 hs hm (by simp)

/-- Reversing the derivative preserves the kernel crossing condition. -/
theorem matrix_crossing_kernel_condition_neg
    {n : Type*} [Fintype n] [DecidableEq n] {J D : Matrix n n ℝ}
    (hcross : ∀ u, J *ᵥ u = 0 → D *ᵥ u ∈ LinearMap.range J.mulVecLin → u = 0) :
    ∀ u, J *ᵥ u = 0 → (-D) *ᵥ u ∈ LinearMap.range J.mulVecLin → u = 0 := by
  intro u hu hr
  apply hcross u hu
  simpa only [Matrix.neg_mulVec, neg_neg] using (LinearMap.range J.mulVecLin).neg_mem hr

/-- The focal comparison in inward coordinates at an arbitrary left endpoint. -/
theorem regular_focal_bounds_left_endpoint
    {J : ℝ → Matrix n n ℝ} {D : Matrix n n ℝ} {a : ℝ}
    (hJ : HasDerivWithinAt J D (Ici a) a)
    (hcross : ∀ u, J a *ᵥ u = 0 → D *ᵥ u ∈ LinearMap.range (J a).mulVecLin → u = 0)
    (hk : 0 < Module.finrank ℝ (ker (J a).mulVecLin)) :
    ∃ cdet Cdet cinv Cinv : ℝ,
      0 < cdet ∧ 0 < Cdet ∧ 0 < cinv ∧ 0 < Cinv ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        cdet * |s| ^ Module.finrank ℝ (ker (J a).mulVecLin) ≤ |(J (a + s)).det| ∧
        |(J (a + s)).det| ≤ Cdet * |s| ^ Module.finrank ℝ (ker (J a).mulVecLin) ∧
        cinv / |s| ≤ ‖(J (a + s))⁻¹‖ ∧ ‖(J (a + s))⁻¹‖ ≤ Cinv / |s| := by
  have hc : ∀ u, J (a + 0) *ᵥ u = 0 →
      D *ᵥ u ∈ LinearMap.range (J (a + 0)).mulVecLin → u = 0 := by
    simpa only [add_zero] using hcross
  have hk' : 0 < Module.finrank ℝ (ker (J (a + 0)).mulVecLin) := by
    rw [add_zero]
    exact hk
  have h := regular_focal_two_sided_bounds
    (hasDerivWithinAt_left_inward_parameter hJ) hc hk'
  rw [add_zero] at h
  exact h

/-- The focal comparison in inward coordinates at an arbitrary right endpoint. -/
theorem regular_focal_bounds_right_endpoint
    {J : ℝ → Matrix n n ℝ} {D : Matrix n n ℝ} {b : ℝ}
    (hJ : HasDerivWithinAt J D (Iic b) b)
    (hcross : ∀ u, J b *ᵥ u = 0 → D *ᵥ u ∈ LinearMap.range (J b).mulVecLin → u = 0)
    (hk : 0 < Module.finrank ℝ (ker (J b).mulVecLin)) :
    ∃ cdet Cdet cinv Cinv : ℝ,
      0 < cdet ∧ 0 < Cdet ∧ 0 < cinv ∧ 0 < Cinv ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        cdet * |s| ^ Module.finrank ℝ (ker (J b).mulVecLin) ≤ |(J (b - s)).det| ∧
        |(J (b - s)).det| ≤ Cdet * |s| ^ Module.finrank ℝ (ker (J b).mulVecLin) ∧
        cinv / |s| ≤ ‖(J (b - s))⁻¹‖ ∧ ‖(J (b - s))⁻¹‖ ≤ Cinv / |s| := by
  have hc : ∀ u, J (b - 0) *ᵥ u = 0 →
      (-D) *ᵥ u ∈ LinearMap.range (J (b - 0)).mulVecLin → u = 0 := by
    simpa only [sub_zero] using matrix_crossing_kernel_condition_neg hcross
  have hk' : 0 < Module.finrank ℝ (ker (J (b - 0)).mulVecLin) := by
    rw [sub_zero]
    exact hk
  have h := regular_focal_two_sided_bounds
    (hasDerivWithinAt_right_inward_parameter hJ) hc hk'
  rw [sub_zero] at h
  exact h

end OTSelector.Geometry
