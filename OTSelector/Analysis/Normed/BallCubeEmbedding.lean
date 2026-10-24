import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.ProjIcc

/-!
# Analysis.Normed.BallCubeEmbedding

## Lemma skeleton

* **Conditions:** A finite-dimensional real normed label space with a chosen basis and a positive radius.

* **Objects:** An explicit affine embedding of a bounded label ball into a fixed unit cube with an inverse Lipschitz bound.

* **Proof detail:** Bound basis coordinates on the ball, rescale and translate them into [0,1], and use the bounded inverse basis map for the lower metric bound. Clamp the global coordinate map to the unit cube and restrict to the ball, where clamping changes nothing.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (corollary): Explicit finite-dimensional affine coding; the constants depend on the chosen basis, and no isometry is claimed.
-/

/-!
# Actual bounded label balls in a fixed unit cube

An explicit affine coordinate map sends each original finite level-section ball
into the closed unit cube. Its inverse Lipschitz constant converts the actual
label cost to the squared cube-coordinate cost without changing the label law.
-/

open Set Metric Module
open scoped Topology

noncomputable section
namespace OTSelector.Reconstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {ι : Type*} [Fintype ι]

/-- Affine coordinates relative to the original label basis and a positive radius. -/
def labelCubeCoordinates (b : Basis ι ℝ W) (R : ℝ) (w : W) : ι → ℝ :=
  fun i ↦ (b.equivFun w i + R) / (2 * R)

/-- Actual cube coordinates depend continuously on the original label. -/
theorem continuous_labelCubeCoordinates (b : Basis ι ℝ W) (R : ℝ) :
    Continuous (labelCubeCoordinates b R) := by
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp b.equivFunL.continuous).add_const R |>.div_const (2 * R)

/-- The scaled difference is exactly the original basis coordinate difference. -/
theorem labelCubeCoordinates_sub (b : Basis ι ℝ W) {R : ℝ} (hR : 0 < R)
    (w z : W) :
    (2 * R) • (labelCubeCoordinates b R w - labelCubeCoordinates b R z) =
      b.equivFun (w - z) := by
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, labelCubeCoordinates, map_sub]
  field_simp
  ring

/-- The affine coordinates distinguish all original labels. -/
theorem injective_labelCubeCoordinates (b : Basis ι ℝ W) {R : ℝ} (hR : 0 < R) :
    Function.Injective (labelCubeCoordinates b R) := by
  intro w z hwz
  have hd := labelCubeCoordinates_sub b hR w z
  rw [hwz, sub_self, smul_zero, map_sub, eq_comm, sub_eq_zero] at hd
  exact b.equivFun.injective hd

/-- A bound on the actual basis coordinates puts the original label in the cube. -/
theorem labelCubeCoordinates_mem_unitCube (b : Basis ι ℝ W) {R : ℝ} (hR : 0 < R)
    {w : W} (hw : ‖b.equivFun w‖ ≤ R) :
    labelCubeCoordinates b R w ∈ Icc (0 : ι → ℝ) 1 := by
  constructor
  · intro i
    have hi := (norm_le_pi_norm (b.equivFun w) i).trans hw
    rw [Real.norm_eq_abs] at hi
    exact div_nonneg (by linarith [(abs_le.mp hi).1]) (by positivity)
  · intro i
    have hi := (norm_le_pi_norm (b.equivFun w) i).trans hw
    rw [Real.norm_eq_abs] at hi
    change (b.equivFun w i + R) / (2 * R) ≤ 1
    apply (div_le_iff₀ (by positivity : 0 < 2 * R)).mpr
    linarith [(abs_le.mp hi).2]

/-- The original label displacement is controlled by the actual affine coordinate
change. No distribution or balancing condition is involved. -/
theorem norm_sub_le_labelCubeCoordinates (b : Basis ι ℝ W) {R : ℝ} (hR : 0 < R)
    (w z : W) :
    ‖w - z‖ ≤ (‖b.equivFunL.symm.toContinuousLinearMap‖ * (2 * R)) *
      ‖labelCubeCoordinates b R w - labelCubeCoordinates b R z‖ := by
  have hb := b.equivFunL.symm.toContinuousLinearMap.le_opNorm (b.equivFun (w - z))
  have he : b.equivFunL.symm (b.equivFun (w - z)) = w - z := b.equivFunL.symm_apply_apply _
  change ‖b.equivFunL.symm (b.equivFun (w - z))‖ ≤ _ at hb
  rw [he, ← labelCubeCoordinates_sub b hR w z, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2 * R)] at hb
  simpa only [mul_assoc] using hb

/-- Every actual level-section ball has fixed continuous injective cube coordinates
and a finite common inverse Lipschitz constant. -/
theorem exists_labelCubeCoordinates_on_ball (b : Basis ι ℝ W) {r : ℝ} (hr : 0 < r) :
    ∃ (Q : W → ι → ℝ) (L : ℝ), Continuous Q ∧ Function.Injective Q ∧ 0 < L ∧
      MapsTo Q (ball 0 r) (Icc (0 : ι → ℝ) 1) ∧
      ∀ w z, ‖w - z‖ ≤ L * ‖Q w - Q z‖ := by
  let R := ‖b.equivFunL.toContinuousLinearMap‖ * r + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let L := ‖b.equivFunL.symm.toContinuousLinearMap‖ * (2 * R) + 1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨labelCubeCoordinates b R, L, continuous_labelCubeCoordinates b R,
    injective_labelCubeCoordinates b hR, hL, ?_, ?_⟩
  · intro w hw
    apply labelCubeCoordinates_mem_unitCube b hR
    have hw' : ‖w‖ < r := by simpa only [mem_ball, dist_zero_right] using hw
    exact (b.equivFunL.toContinuousLinearMap.le_opNorm w).trans
      ((mul_le_mul_of_nonneg_left hw'.le (norm_nonneg _)).trans (by dsimp [R]; linarith))
  · intro w z
    exact (norm_sub_le_labelCubeCoordinates b hR w z).trans
      (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (norm_nonneg _))

/-- A globally continuous cube-valued completion of any label coordinates.
It equals the original coordinates wherever those already lie in the cube. -/
def unitCubeCompletion (Q : W → ι → ℝ) (w : W) : ι → Icc (0 : ℝ) 1 :=
  fun i ↦ projIcc 0 1 zero_le_one (Q w i)

omit [NormedSpace ℝ W] [Fintype ι] in
/-- Cube completion preserves continuity of the original label coordinates. -/
theorem continuous_unitCubeCompletion {Q : W → ι → ℝ} (hQ : Continuous Q) :
    Continuous (unitCubeCompletion Q) := by
  apply continuous_pi
  intro i
  exact continuous_projIcc.comp ((continuous_apply i).comp hQ)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype ι] in
/-- On every actual cube label the completion is exactly the original map. -/
theorem unitCubeCompletion_eq {Q : W → ι → ℝ} {w : W}
    (hw : Q w ∈ Icc (0 : ι → ℝ) 1) :
    (fun i ↦ (unitCubeCompletion Q w i : ℝ)) = Q w := by
  ext i
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨hw.1 i, hw.2 i⟩)

/-- Actual level-section labels admit a globally continuous map into the subtype
unit cube used by iid matching, with a common inverse bound on the original ball. -/
theorem exists_labelUnitCubeMap_on_ball (b : Basis ι ℝ W) {r : ℝ} (hr : 0 < r) :
    ∃ (Q : W → ι → Icc (0 : ℝ) 1) (L : ℝ), Continuous Q ∧
      InjOn Q (ball 0 r) ∧ 0 < L ∧ ∀ w ∈ ball 0 r, ∀ z ∈ ball 0 r,
        ‖w - z‖ ≤ L * ‖(fun i ↦ (Q w i : ℝ)) - (fun i ↦ (Q z i : ℝ))‖ := by
  obtain ⟨Q, L, hQ, hinj, hL, hmap, hbound⟩ := exists_labelCubeCoordinates_on_ball b hr
  refine ⟨unitCubeCompletion Q, L, continuous_unitCubeCompletion hQ, ?_, hL, ?_⟩
  · intro w hw z hz he
    apply hinj
    rw [← unitCubeCompletion_eq (hmap hw), ← unitCubeCompletion_eq (hmap hz), he]
  · intro w hw z hz
    rw [unitCubeCompletion_eq (hmap hw), unitCubeCompletion_eq (hmap hz)]
    exact hbound w z

end OTSelector.Reconstruction
