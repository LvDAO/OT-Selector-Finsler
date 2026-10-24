import OTSelector.Analysis.SecondOrderPeano
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.SecondJetTransfer.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.SecondJetTransfer`; the selected original proof blocks follow. -/
section

/-!
Conditions: Actual first/second Peano jets, a bounded bilinear form and the stated matching or small displacement errors.

Objects: Quadratic diagonal difference bounds and transfer of stationary second-order expansions, including within-set variants.

Proof detail: Expand the difference of bilinear diagonals, apply operator-norm estimates and compose the little-o remainder with the controlled displacement.

Sources: Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html); Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37).
Relation: Quantitative normed-space Taylor/Peano consequences, proved locally with the exact stated scales.
-/

/-!
# Transfer of the actual second jet across matching parameterizations

At a stationary point, a scalar function with a genuine quadratic Peano expansion has
identical second-order values along parameterizations with the same value and first
derivative. The argument only uses bounded bilinearity and the actual small remainders.
-/

open Asymptotics Filter
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {A E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ W] in
/-- A bounded bilinear form has the same quadratic value up to a second-order little-o
error on two first-order matching maps. No symmetry of the form is required. -/
theorem bilinear_diagonal_sub_isLittleO (B : E →L[ℝ] E →L[ℝ] ℝ)
    {X Y : A → E} {v : A → W} {l : Filter A}
    (hXY : (fun t ↦ X t - Y t) =o[l] v) (hX : X =O[l] v) (hY : Y =O[l] v) :
    (fun t ↦ B (X t) (X t) - B (Y t) (Y t)) =o[l] fun t ↦ ‖v t‖ ^ 2 := by
  have h₁ : (fun t ↦ B (X t - Y t) (X t)) =o[l] fun t ↦ ‖v t‖ * ‖v t‖ :=
    B.isBoundedBilinearMap.isBigO_comp.trans_isLittleO
      (hXY.norm_norm.mul_isBigO hX.norm_norm)
  have h₂ : (fun t ↦ B (Y t) (X t - Y t)) =o[l] fun t ↦ ‖v t‖ * ‖v t‖ :=
    B.isBoundedBilinearMap.isBigO_comp.trans_isLittleO
      (hY.norm_norm.mul_isLittleO hXY.norm_norm)
  simpa only [map_sub, sub_apply, sub_add_sub_cancel, pow_two] using h₁.add h₂

/-- A quadratic remainder stays second order along a map differentiable only within
the allowed parameter set, without assuming a smooth extension of that map. -/
theorem quadratic_remainder_comp_isLittleO_within {r : E → ℝ} {x : E}
    (hr : r =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2) {X : W → E} {t : W} {S : Set W}
    (hX : DifferentiableWithinAt ℝ X S t) (hx : X t = x) :
    (fun s ↦ r (X s)) =o[𝓝[S] t] fun s ↦ ‖s - t‖ ^ 2 := by
  have hcont : Tendsto X (𝓝[S] t) (𝓝 x) := by simpa only [hx] using hX.continuousWithinAt.tendsto
  have hbound : (fun s ↦ ‖X s - x‖ ^ 2) =O[𝓝[S] t] fun s ↦ ‖s - t‖ ^ 2 := by
    simpa only [hx] using hX.isBigO_sub.norm_norm.pow 2
  exact (hr.comp_tendsto hcont).trans_isBigO hbound

/-- The stationary Peano transfer also holds along an arbitrary allowed endpoint set.
Matching within-derivatives suffice; no interior or derivative uniqueness is assumed. -/
theorem stationary_peano_comp_sub_isLittleO_within {e : E → ℝ} {x : E}
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (he : (fun y ↦ e y - e x - (1 / 2 : ℝ) * B (y - x) (y - x))
      =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2)
    {X Y : W → E} {t : W} {S : Set W} {D : W →L[ℝ] E}
    (hX : HasFDerivWithinAt X D S t) (hY : HasFDerivWithinAt Y D S t)
    (hx : X t = x) (hy : Y t = x) :
    (fun s ↦ e (X s) - e (Y s)) =o[𝓝[S] t] fun s ↦ ‖s - t‖ ^ 2 := by
  have hXY : (fun s ↦ (X s - x) - (Y s - x)) =o[𝓝[S] t] fun s ↦ s - t := by
    have h := (hX.sub hY).isLittleO
    simpa only [Pi.sub_apply, hx, hy, sub_self, sub_zero, zero_apply,
      sub_sub_sub_cancel_right] using h
  have hX' : (fun s ↦ X s - x) =O[𝓝[S] t] fun s ↦ s - t := by
    simpa only [hx] using hX.isBigO_sub
  have hY' : (fun s ↦ Y s - x) =O[𝓝[S] t] fun s ↦ s - t := by
    simpa only [hy] using hY.isBigO_sub
  have hq := (bilinear_diagonal_sub_isLittleO B hXY hX' hY').const_mul_left (1 / 2 : ℝ)
  have hrX := quadratic_remainder_comp_isLittleO_within he hX.differentiableWithinAt hx
  have hrY := quadratic_remainder_comp_isLittleO_within he hY.differentiableWithinAt hy
  exact ((hrX.sub hrY).add hq).congr_left fun s ↦ by ring

/-- A second-order little-o remainder remains second order along an actual differentiable
parameterization taking its center to the remainder's center. -/
theorem quadratic_remainder_comp_isLittleO {r : E → ℝ} {x : E}
    (hr : r =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2) {X : W → E} {t : W}
    (hX : DifferentiableAt ℝ X t) (hx : X t = x) :
    (fun s ↦ r (X s)) =o[𝓝 t] fun s ↦ ‖s - t‖ ^ 2 := by
  simpa only [nhdsWithin_univ] using
    quadratic_remainder_comp_isLittleO_within (S := Set.univ) hr hX.differentiableWithinAt hx

/-- At a stationary Peano expansion, replacing endpoint parameterizations with the same
value and first derivative changes the scalar defect only by a second-order little-o. -/
theorem stationary_peano_comp_sub_isLittleO {e : E → ℝ} {x : E}
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (he : (fun y ↦ e y - e x - (1 / 2 : ℝ) * B (y - x) (y - x))
      =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2)
    {X Y : W → E} {t : W} {D : W →L[ℝ] E}
    (hX : HasFDerivAt X D t) (hY : HasFDerivAt Y D t)
    (hx : X t = x) (hy : Y t = x) :
    (fun s ↦ e (X s) - e (Y s)) =o[𝓝 t] fun s ↦ ‖s - t‖ ^ 2 := by
  simpa only [nhdsWithin_univ] using
    stationary_peano_comp_sub_isLittleO_within (S := Set.univ) B he
      hX.hasFDerivWithinAt hY.hasFDerivWithinAt hx hy

/-- Two actual scalar Peano expansions with the same value, linear coefficient and
quadratic coefficient differ by a second-order little-o at the common center. -/
theorem matched_second_peano_sub_isLittleO {f g : E → ℝ} {x : E}
    (L : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) (hvalue : f x = g x)
    (hf : (fun y ↦ f y - f x - L (y - x) - (1 / 2 : ℝ) * B (y - x) (y - x))
      =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2)
    (hg : (fun y ↦ g y - g x - L (y - x) - (1 / 2 : ℝ) * B (y - x) (y - x))
      =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2) :
    (fun y ↦ f y - g y) =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2 := by
  exact (hf.sub hg).congr_left fun y ↦ by rw [hvalue]; ring

/-- A stationary scalar function whose actual first derivative is differentiable at
its center has the same second-order values along matching first-order endpoint maps. -/
theorem stationary_second_order_comp_sub_isLittleO {e : E → ℝ}
    {e' : E → E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt e (e' y) y)
    (hsecond : HasFDerivAt e' B x) (hstationary : e' x = 0)
    {X Y : W → E} {t : W} {D : W →L[ℝ] E}
    (hX : HasFDerivAt X D t) (hY : HasFDerivAt Y D t)
    (hx : X t = x) (hy : Y t = x) :
    (fun s ↦ e (X s) - e (Y s)) =o[𝓝 t] fun s ↦ ‖s - t‖ ^ 2 := by
  have he := second_order_peano_of_hasFDerivAt hfirst hsecond
  simp only [hstationary, zero_apply, sub_zero] at he
  exact stationary_peano_comp_sub_isLittleO B he hX hY hx hy

/-- The actual stationary second jet transfers along an allowed endpoint set using
only matching within-derivatives of its parameterizations. -/
theorem stationary_second_order_comp_sub_isLittleO_within {e : E → ℝ}
    {e' : E → E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt e (e' y) y)
    (hsecond : HasFDerivAt e' B x) (hstationary : e' x = 0)
    {X Y : W → E} {t : W} {S : Set W} {D : W →L[ℝ] E}
    (hX : HasFDerivWithinAt X D S t) (hY : HasFDerivWithinAt Y D S t)
    (hx : X t = x) (hy : Y t = x) :
    (fun s ↦ e (X s) - e (Y s)) =o[𝓝[S] t] fun s ↦ ‖s - t‖ ^ 2 := by
  have he := second_order_peano_of_hasFDerivAt hfirst hsecond
  simp only [hstationary, zero_apply, sub_zero] at he
  exact stationary_peano_comp_sub_isLittleO_within B he hX hY hx hy

/-- Matching actual values, first derivatives and derivatives of those first derivatives
implies a second-order little-o difference; no neighborhood second derivative is needed. -/
theorem matched_second_jets_sub_isLittleO {f g : E → ℝ}
    {f' g' : E → E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hg : ∀ᶠ y in 𝓝 x, HasFDerivAt g (g' y) y)
    (hf' : HasFDerivAt f' B x) (hg' : HasFDerivAt g' B x)
    (hvalue : f x = g x) (hfirst : f' x = g' x) :
    (fun y ↦ f y - g y) =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2 := by
  apply matched_second_peano_sub_isLittleO (f' x) B hvalue
    (second_order_peano_of_hasFDerivAt hf hf')
  rw [hfirst]
  exact second_order_peano_of_hasFDerivAt hg hg'


end OTSelector.Geometry

end
end
