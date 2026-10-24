import OTSelector.Geometry.FinslerPolynomialPhaseModel
import OTSelector.Analysis.Calculus.UniformStationaryComposition

/-!
# Uniform quadratic expansion of the actual polynomial model deficit

The actual normalized polynomial pair is one joint C1 family on a common open
domain. Its stationary phase-action expansion is therefore uniform over compact
original centers and times. Equal polynomial levels and unit speed identify this
action with the original distance deficit throughout a common label neighborhood.
-/

open Set Manifold Metric
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

private theorem uniform_composition_of_frozen_stationarity
    {P Z I W Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {f : P × Z → ℝ} {K : Set (P × Z)} (hK : IsCompact K)
    (hf : ∀ p ∈ K, ContDiffAt ℝ 3 f p)
    (hs : ∀ p ∈ K, HasFDerivAt (fun y ↦ f (p.1, y)) (0 : Z →L[ℝ] ℝ) p.2)
    (S : Set I) (z : I → P × Z) (hz : ∀ i ∈ S, z i ∈ K)
    {g : Q × W → Z} {U : Set (Q × W)} {J : Set Q}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (hJ : IsCompact J)
    (hJU : ∀ p ∈ J, (p, (0 : W)) ∈ U)
    (q : I → Q) (hq : ∀ i ∈ S, q i ∈ J)
    (hcenter : ∀ i ∈ S, g (q i, 0) = (z i).2) :
    ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ i ∈ S, ∀ w, ‖w‖ < r →
      ‖f ((z i).1, g (q i, w)) - f (z i) -
        stationaryLabelQuadratic f g (z i).1 (q i) (z i).2 w‖ ≤ ε * ‖w‖ ^ 2 := by
  exact uniform_parameterized_stationary_composition_of_contDiffOn hK hf
    (fun p hp ↦ state_fderiv_eq_zero_of_hasFDerivAt
      ((hf p hp).differentiableAt (by norm_num)) (hs p hp))
    S z hz hU hg hJ hJU q hq hcenter

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The same actual polynomial model has a uniform quadratic distance-deficit
expansion, with the actual phase Hessian and the actual normalized label derivative. -/
theorem uniform_polynomial_model_quadratic (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {K : Set E} (hK : IsCompact K)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) K)
    (hlegal : ∀ x ∈ K, (x, fderiv ℝ G x) ∈ eL.target)
    (henergy : ∀ x ∈ K, F.chartEnergy old (eL.symm (x, fderiv ℝ G x)) = 1 / 2)
    {O : Set (ScalarSecondJet E)} {B : Set W}
    (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : W) ∈ B)
    (hKj : ∀ x ∈ K, (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    {σ : ScalarSecondJet E × W → E} (hσ : ContDiffOn ℝ 1 σ (O ×ˢ B))
    (hσ₀ : ∀ j ∈ O, σ (j, 0) = j.1)
    (hσlevel : ∀ j ∈ O, ∀ w ∈ B,
      scalarSecondJetPolynomial j (σ (j, w)) = j.2.1)
    (Φ : (E × E) → ℝ → M) {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (hC3 : ∀ x ∈ K, ∀ t ∈ T,
      ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction old Φ)
        (((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), t),
          (eL.symm (x, fderiv ℝ G x), eL.symm (x, fderiv ℝ G x))))
    (hstationary : ∀ x ∈ K, ∀ t ∈ T,
      HasFDerivAt (F.phaseLengthAction old Φ
        (scalarSecondJetPolynomial (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x))
        t.1 t.2) (0 : ((E × E) × (E × E)) →L[ℝ] ℝ)
        (eL.symm (x, fderiv ℝ G x), eL.symm (x, fderiv ℝ G x)))
    (hcentralDistance : ∀ x ∈ K, ∀ t ∈ T,
      (F.lengthEDist (Φ (eL.symm (x, fderiv ℝ G x)) t.1)
        (Φ (eL.symm (x, fderiv ℝ G x)) t.2)).toReal = t.2 - t.1) :
    let j : E → ScalarSecondJet E :=
      fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ t ∈ T,
      ∀ w : W × W, ‖w‖ < r →
        let pair := F.polynomialPhasePair old eL σ (j x, w)
        ‖((F.lengthEDist (Φ pair.1 t.1) (Φ pair.2 t.2)).toReal - (t.2 - t.1)) -
          F.polynomialPhaseQuadratic old Φ eL σ (j x) t w‖ ≤ η * ‖w‖ ^ 2 := by
  dsimp only
  let j : E → ScalarSecondJet E :=
    fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let J := j '' K
  have hj : ContinuousOn j K := continuousOn_id.prodMk
    (hG.continuous.continuousOn.prodMk
      ((hG.continuous_fderiv one_ne_zero).continuousOn.prodMk hHess))
  have hJ : IsCompact J := hK.image_of_continuousOn hj
  have hJO : J ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKj x hx
  have hJlegal : ∀ a ∈ J, (a.1, a.2.2.1) ∈ eL.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact hlegal x hx
  obtain ⟨V, hV, hJV, hg, hVspec⟩ := hF.exists_open_polynomialPhasePair_domain
    old heL hsource hInv hO hB h0B hJO hσ hσ₀ hJlegal
  let g := F.polynomialPhasePair old eL σ
  obtain ⟨_, _, hNspec⟩ := hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hlength (q : E × (E →L[ℝ] ℝ)) (hq : q ∈ eL.target) :
      (F.chartLength old (F.covectorNormalization old eL (1 / 2) q) : ℝ) = 1 := by
    rw [F.chartLength_eq_sqrt_energy, (hNspec q hq).2.2.1]
    norm_num
  let s : E → E × E := fun x ↦ eL.symm (x, fderiv ℝ G x)
  have hcenter (x : E) (hx : x ∈ K) : g (j x, 0) = (s x, s x) := by
    change (F.covectorNormalization old eL (1 / 2)
        (σ (j x, 0), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, 0))),
      F.covectorNormalization old eL (1 / 2)
        (σ (j x, 0), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, 0)))) = _
    rw [hσ₀ (j x) (hKj x hx), (hasFDerivAt_scalarSecondJetPolynomial_center (j x)).fderiv]
    exact congrArg (fun a : E × E ↦ (a, a))
      ((hNspec _ (hlegal x hx)).2.2.2.2 (henergy x hx))
  let z : E × (ℝ × ℝ) → PhaseActionParameters E :=
    fun i ↦ ((j i.1, i.2), (s i.1, s i.1))
  let S := K ×ˢ T
  let C := z '' S
  have hC : IsCompact C :=
    isCompact_original_phaseAction_parameters hG hK hHess hT eL hlegal
  have hf : ∀ a ∈ C, ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction old Φ) a := by
    rintro _ ⟨i, hi, rfl⟩
    exact hC3 i.1 hi.1 i.2 hi.2
  have hs : ∀ a ∈ C,
      HasFDerivAt (fun y ↦ F.parameterizedPhaseLengthAction old Φ (a.1, y))
        (0 : ((E × E) × (E × E)) →L[ℝ] ℝ) a.2 := by
    rintro _ ⟨i, hi, rfl⟩
    exact hstationary i.1 hi.1 i.2 hi.2
  have composition := uniform_composition_of_frozen_stationarity
    (P := ScalarSecondJet E × (ℝ × ℝ)) (Z := (E × E) × (E × E))
    (I := E × (ℝ × ℝ)) (Q := ScalarSecondJet E) (W := W × W)
    (f := F.parameterizedPhaseLengthAction old Φ) (K := C) (g := g) (U := V) (J := J)
  have composition₁ := composition hC
  have composition₂ := composition₁ hf
  have composition₃ := composition₂ hs
  have composition₄ := composition₃ S z (fun i hi ↦ mem_image_of_mem z hi)
    hV hg hJ hJV (fun i ↦ j i.1) (fun i hi ↦ mem_image_of_mem j hi.1)
    (fun i hi ↦ hcenter i.1 hi.1)
  have firstJet := exists_uniform_label_firstJet
    (P := ScalarSecondJet E) (W := W × W) (Z := (E × E) × (E × E))
    (g := g) (U := V) (K := J)
  have firstJet₁ := firstJet hV
  have firstJet₂ := firstJet₁ hg
  have firstJet₃ := firstJet₂ hJ
  obtain ⟨⟨_, _, rV, hrV, hVsmall⟩, _⟩ := firstJet₃ hJV
  have hmodel (a : ScalarSecondJet E) (w : W × W) (haw : (a, w) ∈ V) (t : ℝ × ℝ) :
      F.parameterizedPhaseLengthAction old Φ ((a, t), g (a, w)) =
        (F.lengthEDist (Φ (g (a, w)).1 t.1) (Φ (g (a, w)).2 t.2)).toReal -
          (t.2 - t.1) := by
    obtain ⟨hd₁, hd₂, hl₁, hl₂⟩ := hVspec (a, w) haw
    have hb₁ : (g (a, w)).1.1 = σ (a, w.1) := rfl
    have hb₂ : (g (a, w)).2.1 = σ (a, w.2) := rfl
    have hu₁ : (F.chartLength old (g (a, w)).1 : ℝ) = 1 := hlength _ hl₁
    have hu₂ : (F.chartLength old (g (a, w)).2 : ℝ) = 1 := hlength _ hl₂
    dsimp only [parameterizedPhaseLengthAction, phaseLengthAction]
    rw [hb₁, hb₂, hσlevel a hd₁.1 w.1 hd₁.2, hσlevel a hd₂.1 w.2 hd₂.2, hu₁, hu₂]
    ring
  have hzero (x : E) (hx : x ∈ K) (t : ℝ × ℝ) (ht : t ∈ T) :
      F.parameterizedPhaseLengthAction old Φ (z (x, t)) = 0 := by
    have h := hmodel (j x) 0 (hJV _ (mem_image_of_mem j hx)) t
    rw [hcenter x hx] at h
    change F.parameterizedPhaseLengthAction old Φ (z (x, t)) =
      (F.lengthEDist (Φ (s x) t.1) (Φ (s x) t.2)).toReal - (t.2 - t.1) at h
    rw [h, hcentralDistance x hx t ht]
    exact sub_self _
  intro η hη
  obtain ⟨rA, hrA, hA⟩ := composition₄ η hη
  refine ⟨min rV rA, lt_min hrV hrA, ?_⟩
  intro x hx t ht w hw
  have hlegalPair : (j x, w) ∈ V :=
    (hVsmall (j x) (mem_image_of_mem j hx) w (hw.trans_le (min_le_left rV rA))).1
  have hb := hA (x, t) ⟨hx, ht⟩ w (hw.trans_le (min_le_right rV rA))
  change ‖F.parameterizedPhaseLengthAction old Φ ((j x, t), g (j x, w)) -
    F.parameterizedPhaseLengthAction old Φ (z (x, t)) -
    F.polynomialPhaseQuadratic old Φ eL σ (j x) t w‖ ≤ η * ‖w‖ ^ 2 at hb
  rw [hzero x hx t ht, sub_zero, hmodel (j x) w hlegalPair t] at hb
  exact hb

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
