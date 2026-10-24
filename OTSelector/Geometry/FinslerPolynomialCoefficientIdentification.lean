import OTSelector.Geometry.FinslerModelQuadraticRemainder
import OTSelector.Geometry.FinslerTubeLengthQuadraticRemainder

/-!
# Identifying the actual polynomial coefficient with the length response

The normalized polynomial family and its smooth calibrated tube describe the same
nearby curves. Their two distance expansions therefore have the same homogeneous
quadratic coefficient. Joint action regularity and stationarity come from the
actual calibrated tube; the coefficient is its integrated restricted length Hessian.
-/

open Set Filter Metric Manifold Asymptotics
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The actual action-Hessian coefficient equals the actual integrated length
coefficient of the same normalized polynomial tube. No coefficient identity or
distance-expansion hypothesis is supplied. -/
theorem polynomialPhaseQuadratic_eq_tubeLengthQuadratic
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {x : E}
    (hlegal : (x, fderiv ℝ G x) ∈ eL.target)
    (henergy : F.chartEnergy old (eL.symm (x, fderiv ℝ G x)) = 1 / 2)
    {O : Set (ScalarSecondJet E)} {B : Set W}
    (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : W) ∈ B)
    (hj : (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    {σ : ScalarSecondJet E × W → E} (hσ : ContDiffOn ℝ 1 σ (O ×ˢ B))
    (hσ₀ : ∀ j ∈ O, σ (j, 0) = j.1)
    (hσlevel : ∀ j ∈ O, ∀ w ∈ B,
      scalarSecondJetPolynomial j (σ (j, w)) = j.2.1)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hPhi : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hfamily : ∀ w ∈ B,
      Λ w = Φ (F.covectorNormalization old eL (1 / 2)
        (σ ((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), w),
          fderiv ℝ (scalarSecondJetPolynomial
            (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x))
            (σ ((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), w)))))
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ y ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) y,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) y v)
        (F.toFun ⟨y, v⟩ : ℝ))
    {a b : ℝ} (hab : a < b)
    (hstay : ∀ t ∈ Icc a b, (t, (0 : W)) ∈ Y.source)
    (hmin : letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
      F.lengthEDist (Λ 0 a) (Λ 0 b) = Manifold.pathELength 𝓘(ℝ, E) (Λ 0) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Λ 0 b) - u (Λ 0 a) = dist (Λ 0 a) (Λ 0 b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Λ 0 a)) (w : W × W) :
    F.polynomialPhaseQuadratic old Φ eL σ
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) (a, b) w =
      F.tubeLengthQuadratic Y (Λ 0) a b w := by
  let j : ScalarSecondJet E := (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let z := eL.symm (x, fderiv ℝ G x)
  have hz : z ∈ chartEnergyDomain old := hsource (eL.map_target hlegal)
  have hnormal := ((hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)).2.2 _ hlegal).2.2.2.2 henergy
  have hsame : Φ z = Λ 0 := by
    have h := hfamily 0 h0B
    rw [hσ₀ j hj, (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv] at h
    exact (h.trans (congrArg Φ hnormal)).symm
  have hΛ : F.IsEulerLagrangeOn (Λ 0) univ := by
    rw [← hsame]
    exact hEL z hz
  have hmatch := hF.scalarSecondJetPolynomial_matches_unit_inverse_length_covector
    old heL hsource (j := j) hlegal henergy
  have hjet := hF.parameterizedPhaseLengthAction_jet_of_calibrated_curve
    hcomplete old hEL hinit hPhi hz hmatch hY hi heq hhalf t₀ hbound hab hΛ
    hsame hstay hmin hu hsat hdu
  have hd := hF.tubeCoordinateDistance_jet_of_calibrated_curve
    hcomplete hY hi heq hhalf t₀ hbound hab hΛ hstay hmin hu hsat hdu
  have hdist : (F.lengthEDist (Φ z a) (Φ z b)).toReal = b - a := by
    simpa only [tubeCoordinateDistance, heq, hsame] using hd.2.1
  have hmodel := hF.polynomial_model_quadratic_remainder_isLittleO
    old heL hsource hInv hG hlegal henergy hO hB h0B hj hσ hσ₀ hσlevel
    Φ (a, b) hjet.1 hjet.2 hdist
  have htube := hF.selected_tube_distance_sub_lengthQuadratic_isLittleO
    hcomplete hY hi heq hhalf t₀ hbound hab hΛ hstay hmin hu hsat hdu
  let f : W × W → ℝ := fun q ↦
    let pair := F.polynomialPhasePair old eL σ (j, q)
    (F.lengthEDist (Φ pair.1 a) (Φ pair.2 b)).toReal - (b - a)
  have htube' : (fun q ↦ f q - F.tubeLengthQuadratic Y (Λ 0) a b q)
      =o[𝓝 (0 : W × W)] (fun q ↦ ‖q‖ ^ 2) := by
    apply htube.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [(hB.prod hB).mem_nhds (show (0 : W × W) ∈ B ×ˢ B from ⟨h0B, h0B⟩)]
      with q hq
    simp only [zero_add, hfamily q.1 hq.1, hfamily q.2 hq.2,
      f, polynomialPhasePair, j]
  exact quadratic_expansion_unique
    (F.polynomialPhaseQuadratic_smul old Φ eL σ j (a, b))
    (F.tubeLengthQuadratic_smul Y (Λ 0) a b) hmodel htube' w

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
