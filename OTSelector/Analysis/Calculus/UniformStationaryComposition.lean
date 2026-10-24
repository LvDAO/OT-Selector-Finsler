import OTSelector.Analysis.Calculus.CompactUniformLabelJet
import OTSelector.Analysis.Calculus.ParameterizedStationaryTaylor
import OTSelector.Analysis.Calculus.UniformParameterizedActionTransfer
import OTSelector.Analysis.Calculus.UniformQuadraticComposition
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.UniformStationaryComposition.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.UniformStationaryComposition`; the selected original proof blocks follow. -/
section

/-!
Conditions: A compact C3 action family is stationary at its centers and the states have the stated uniform first-order approximation.

Objects: A uniform quadratic action expansion with the actual Hessian coefficient.

Proof detail: Apply common stationary Taylor bounds, substitute the controlled first-order states and estimate the bilinear diagonal difference.

Sources: Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46).
Relation: Uniform stationary composition consequence, including the actual C1-family variant.
-/

/-!
# Uniform stationary composition along first-order state approximations

A common C3 action at compactly many stationary centers gives a uniform quadratic
expansion after a uniformly first-order state approximation. The quadratic term
uses the actual joint Hessian and the supplied linear state differential.
-/

open Set
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {P Z I W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Uniform first-order state approximation pulls a stationary action back to its
actual Hessian quadratic form, on the unchanged allowed parameter set. -/
theorem uniform_parameterized_stationary_composition_within
    {f : P × Z → ℝ} {K : Set (P × Z)} (hK : IsCompact K)
    (hf : ∀ q ∈ K, ContDiffAt ℝ 3 f q)
    (hstationary : ∀ q ∈ K, ∀ h : Z, fderiv ℝ f q (0, h) = 0)
    (S : Set I) (z : I → P × Z) (hz : ∀ i ∈ S, z i ∈ K)
    (Y : I → W → Z) (D : I → W →L[ℝ] Z) (allowed : I → W → Prop)
    {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hsize : ∀ i ∈ S, ∀ w, ‖w‖ < R → allowed i w →
      ‖Y i w - (z i).2‖ ≤ A * ‖w‖ ∧ ‖D i w‖ ≤ A * ‖w‖)
    (hrem : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ i ∈ S, ∀ w, ‖w‖ < r →
      allowed i w → ‖Y i w - (z i).2 - D i w‖ ≤ η * ‖w‖) :
    ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ i ∈ S, ∀ w, ‖w‖ < r → allowed i w →
      ‖f ((z i).1, Y i w) - f (z i) -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (z i) (0, D i w) (0, D i w)‖ ≤
          ε * ‖w‖ ^ 2 := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  let model : I → W → Z := fun i w ↦ (z i).2 + D i w
  have hsizeModel : ∀ i ∈ S, ∀ w, ‖w‖ < R → allowed i w →
      ‖Y i w - (z i).2‖ ≤ A * ‖w‖ ∧ ‖model i w - (z i).2‖ ≤ A * ‖w‖ := by
    intro i hi w hw ha
    simpa only [model, add_sub_cancel_left] using hsize i hi w hw ha
  have hmatch : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ i ∈ S, ∀ w, ‖w‖ < r →
      allowed i w → ‖Y i w - model i w‖ ≤ η * ‖w‖ := by
    simpa only [model, sub_add_eq_sub_sub] using hrem
  obtain ⟨rM, hrM, hM⟩ := uniform_parameterized_stationary_action_transfer_within
    hK hf hstationary S z hz Y model (fun w ↦ ‖w‖) (fun _ ↦ norm_nonneg _)
    allowed hA hR hsizeModel hmatch hhalf
  let error : I → Z → ℝ := fun i h ↦ f ((z i).1, (z i).2 + h) - f (z i) -
    (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (z i) (0, h) (0, h)
  have hTaylor : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ i ∈ S, ∀ h : Z, ‖h‖ < r →
      ‖error i (0 + h)‖ ≤ η * ‖h‖ ^ 2 := by
    intro η hη
    obtain ⟨r, hr, hb⟩ :=
      exists_uniform_parameterized_stationary_remainder_of_contDiffAt hK hf hstationary hη
    exact ⟨r, hr, fun i hi h hh ↦ by simpa only [zero_add] using hb (z i) (hz i hi) h hh⟩
  obtain ⟨rT, hrT, hT⟩ := uniform_quadratic_error_of_linear_displacement S
    (fun _ ↦ (0 : Z)) error (fun i w ↦ D i w) allowed hTaylor hA hR
    (fun i hi w hw ha ↦ by simpa only [sub_zero] using (hsize i hi w hw ha).2) hhalf
  refine ⟨min rM rT, lt_min hrM hrT, ?_⟩
  intro i hi w hw ha
  have hm := hM i hi w (hw.trans_le (min_le_left _ _)) ha
  have ht := hT i hi w (hw.trans_le (min_le_right _ _)) ha
  calc
    _ = ‖(f ((z i).1, Y i w) - f ((z i).1, model i w)) + error i (D i w)‖ := by
      congr 1
      dsimp only [error, model]
      ring
    _ ≤ ‖f ((z i).1, Y i w) - f ((z i).1, model i w)‖ + ‖error i (D i w)‖ :=
      norm_add_le _ _
    _ ≤ (ε / 2) * ‖w‖ ^ 2 + (ε / 2) * ‖w‖ ^ 2 := add_le_add hm ht
    _ = ε * ‖w‖ ^ 2 := by ring

/-- A single joint C1 state family supplies its own uniform linear bounds and
first-order approximation, so only the actual label derivative enters the action
quadratic form. The external index map need not be differentiable. -/
theorem uniform_parameterized_stationary_composition_of_contDiffOn
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {f : P × Z → ℝ} {K : Set (P × Z)} (hK : IsCompact K)
    (hf : ∀ p ∈ K, ContDiffAt ℝ 3 f p)
    (hstationary : ∀ p ∈ K, ∀ h : Z, fderiv ℝ f p (0, h) = 0)
    (S : Set I) (z : I → P × Z) (hz : ∀ i ∈ S, z i ∈ K)
    {g : Q × W → Z} {U : Set (Q × W)} {J : Set Q}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (hJ : IsCompact J)
    (hJU : ∀ p ∈ J, (p, (0 : W)) ∈ U)
    (q : I → Q) (hq : ∀ i ∈ S, q i ∈ J)
    (hcenter : ∀ i ∈ S, g (q i, 0) = (z i).2) :
    let D : I → W →L[ℝ] Z := fun i ↦
      (fderiv ℝ g (q i, 0)).comp (ContinuousLinearMap.inr ℝ Q W)
    ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ i ∈ S, ∀ w, ‖w‖ < r →
      ‖f ((z i).1, g (q i, w)) - f (z i) -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (z i) (0, D i w) (0, D i w)‖ ≤
          ε * ‖w‖ ^ 2 := by
  dsimp only
  obtain ⟨⟨A, hA, R, hR, hsize⟩, hrem⟩ := exists_uniform_label_firstJet hU hg hJ hJU
  let Y : I → W → Z := fun i w ↦ g (q i, w)
  let D : I → W →L[ℝ] Z := fun i ↦
    (fderiv ℝ g (q i, 0)).comp (ContinuousLinearMap.inr ℝ Q W)
  have hbound : ∀ i ∈ S, ∀ w, ‖w‖ < R → True →
      ‖Y i w - (z i).2‖ ≤ A * ‖w‖ ∧ ‖D i w‖ ≤ A * ‖w‖ := by
    intro i hi w hw _
    simpa only [hcenter i hi] using (hsize (q i) (hq i hi) w hw).2
  have hmatch : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ i ∈ S, ∀ w, ‖w‖ < r →
      True → ‖Y i w - (z i).2 - D i w‖ ≤ η * ‖w‖ := by
    intro η hη
    obtain ⟨r, hr, hb⟩ := hrem η hη
    refine ⟨r, hr, ?_⟩
    intro i hi w hw _
    simpa only [hcenter i hi] using hb (q i) (hq i hi) w hw
  intro ε hε
  obtain ⟨r, hr, hb⟩ := uniform_parameterized_stationary_composition_within
    hK hf hstationary S z hz Y D (fun _ _ ↦ True) hA hR hbound hmatch ε hε
  exact ⟨r, hr, fun i hi w hw ↦ hb i hi w hw trivial⟩

end OTSelector.Geometry

end
end
