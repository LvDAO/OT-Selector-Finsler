import OTSelector.Analysis.Calculus.ParameterizedStationaryTaylor
import OTSelector.Analysis.Calculus.UniformStationaryComposition
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.UniformStationaryCompositionJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.UniformStationaryCompositionJet`; the selected original proof blocks follow. -/
section

/-!
Conditions: One state germ has an actual Fréchet derivative at its center and a compact C3 action family is stationary there.

Objects: A common quadratic action expansion for that germ using the actual state derivative.

Proof detail: Combine the one-point first-order remainder with the uniform stationary action Taylor bound and bilinear continuity.

Sources: Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html); Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: One-point jet composition consequence; no smooth extension of the state germ is required.
-/

/-!
# Uniform stationary actions along one actual first jet

A state germ differentiable at its center suffices for a common quadratic radius
on a compact set of action parameters. No smooth extension of that germ is needed.
-/

open Set Filter Asymptotics
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {P Z W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- One state first jet gives a uniform quadratic expansion for all parameters in a
compact set of stationary centers of the same joint action. -/
theorem uniform_parameterized_stationary_composition_of_hasFDerivAt
    {f : P × Z → ℝ} {T : Set P} (hT : IsCompact T) {z₀ : Z}
    (hf : ∀ p ∈ T, ContDiffAt ℝ 3 f (p, z₀))
    (hstationary : ∀ p ∈ T, HasFDerivAt (fun z ↦ f (p, z)) (0 : Z →L[ℝ] ℝ) z₀)
    {Y : W → Z} {D : W →L[ℝ] Z} (hY : HasFDerivAt Y D 0) (hY₀ : Y 0 = z₀) :
    ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ p ∈ T, ∀ w, ‖w‖ < r →
      ‖f (p, Y w) - f (p, z₀) -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (p, z₀) (0, D w) (0, D w)‖ ≤
          ε * ‖w‖ ^ 2 := by
  have hrem : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ w : W, ‖w‖ < r →
      ‖Y w - z₀ - D w‖ ≤ η * ‖w‖ := by
    intro η hη
    obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp (hY.isLittleO.def hη)
    refine ⟨r, hr, fun w hw ↦ ?_⟩
    simpa only [mem_ofPred_eq, hY₀, sub_zero] using hb
      (show w ∈ Metric.ball 0 r by simpa only [Metric.mem_ball, dist_zero_right] using hw)
  obtain ⟨R, hR, hb⟩ := hrem 1 zero_lt_one
  let A := 1 + ‖D‖
  have hsize (w : W) (hw : ‖w‖ < R) :
      ‖Y w - z₀‖ ≤ A * ‖w‖ ∧ ‖D w‖ ≤ A * ‖w‖ := by
    have hd := D.le_opNorm w
    have hr := hb w hw
    have htri := norm_add_le (Y w - z₀ - D w) (D w)
    rw [sub_add_cancel] at htri
    constructor <;> dsimp [A] <;> nlinarith [norm_nonneg w]
  let K : Set (P × Z) := (fun p ↦ (p, z₀)) '' T
  have hK : IsCompact K := hT.image (continuous_id.prodMk continuous_const)
  have hfK : ∀ q ∈ K, ContDiffAt ℝ 3 f q := by
    rintro q ⟨p, hp, rfl⟩
    exact hf p hp
  have hsK : ∀ q ∈ K, ∀ h : Z, fderiv ℝ f q (0, h) = 0 := by
    rintro q ⟨p, hp, rfl⟩
    exact state_fderiv_eq_zero_of_hasFDerivAt ((hf p hp).differentiableAt (by norm_num))
      (hstationary p hp)
  intro ε hε
  obtain ⟨r, hr, hh⟩ := uniform_parameterized_stationary_composition_within hK hfK hsK
    T (fun p ↦ (p, z₀)) (fun p hp ↦ ⟨p, hp, rfl⟩)
    (fun _ ↦ Y) (fun _ ↦ D) (fun _ _ ↦ True)
    (show 0 ≤ A by dsimp [A]; positivity) hR
    (fun _ _ w hw _ ↦ hsize w hw)
    (fun η hη ↦ by
      obtain ⟨r, hr, hh⟩ := hrem η hη
      exact ⟨r, hr, fun _ _ w hw _ ↦ hh w hw⟩) ε hε
  exact ⟨r, hr, fun p hp w hw ↦ hh p hp w hw trivial⟩

end OTSelector.Geometry

end
end
