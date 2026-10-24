import OTSelector.Geometry.FinslerUniformOriginalDeficit
import OTSelector.Geometry.FinslerUniformModelQuadratic

/-!
# Uniform quadratic expansion of the original Finsler distance deficit

One retained original compact core carries the original/model comparison and the
model's actual Hessian expansion. Original calibration supplies the central
elapsed-time distance. Their combination gives a common radius for the original
potential deficit with its actual pulled-back quadratic coefficient.
-/

open Set MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The actual original deficit has a uniform quadratic expansion on one large
compact core. The coefficient is the original action Hessian pulled back along
the normalized polynomial label differential. -/
theorem exists_compact_uniform_original_quadratic
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hLip : LipschitzWith L (fderiv ℝ G))
    {C H U : Set E} (hHC : H ⊆ C) (hHU : H ⊆ U)
    {ν : Measure E} (hH : IsCompact H) (hνH : ν H ≠ ⊤)
    (hsecond : ∀ x ∈ H, DifferentiableAt ℝ (fderiv ℝ G) x)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) H)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    (p₀ : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0)
    {O : Set (ScalarSecondJet E)} {B Bσ : Set p₀.ker}
    (hU : IsOpen U) (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : p₀.ker) ∈ B)
    (hBσ : IsOpen Bσ) (h0Bσ : (0 : p₀.ker) ∈ Bσ)
    (hHj : ∀ x ∈ H, (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    (hp : ∀ x ∈ H, (fderiv ℝ G x) v₀ ≠ 0)
    {ρ : E × p₀.ker → E} {σ : ScalarSecondJet E × p₀.ker → E}
    (hρ : ContDiffOn ℝ 1 ρ (U ×ˢ B)) (hσ : ContDiffOn ℝ 1 σ (O ×ˢ Bσ))
    (hρ₀ : ∀ x ∈ H, ρ (x, 0) = x) (hσ₀ : ∀ j ∈ O, σ (j, 0) = j.1)
    (hρlevel : ∀ x ∈ H, ∀ w ∈ B, G (ρ (x, w)) = G x)
    (hσlevel : ∀ j ∈ O, ∀ w ∈ Bσ,
      scalarSecondJetPolynomial j (σ (j, w)) = j.2.1)
    (hρproj : ∀ x ∈ H, ∀ w ∈ B,
      ((covectorSplitting p₀ v₀ hp₀).symm (ρ (x, w) - x)).1 = w)
    (hσproj : ∀ j ∈ O, ∀ w ∈ Bσ,
      ((covectorSplitting p₀ v₀ hp₀).symm (σ (j, w) - j.1)).1 = w)
    (Φ : (E × E) → ℝ → M) {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (hC3 : ∀ x ∈ H, ∀ t ∈ T,
      ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction old Φ)
        (((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), t),
          (eL.symm (x, fderiv ℝ G x), eL.symm (x, fderiv ℝ G x))))
    (hstationary : ∀ x ∈ H, ∀ t ∈ T,
      HasFDerivAt (F.phaseLengthAction old Φ
        (scalarSecondJetPolynomial (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x))
        t.1 t.2) (0 : ((E × E) × (E × E)) →L[ℝ] ℝ)
        (eL.symm (x, fderiv ℝ G x), eL.symm (x, fderiv ℝ G x)))
    {u : M → ℝ} (hu : let _instDeficitLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) C)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instDeficitPartners : MetricSpace M := F.metricSpace
      ∀ y ∈ C, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    (hTreach : T ⊆ Icc (-δ) δ ×ˢ Icc (-δ) δ)
    (hTorder : ∀ t ∈ T, t.1 ≤ t.2)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    let j : E → ScalarSecondJet E :=
      fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let X : E → p₀.ker → E × E :=
      fun x w ↦ eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w)))
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ t ∈ T,
        ∀ w : p₀.ker × p₀.ker, ‖w‖ < r → ρ (x, w.1) ∈ C → ρ (x, w.2) ∈ C →
          ‖((F.lengthEDist (Φ (X x w.1) t.1) (Φ (X x w.2) t.2)).toReal -
              u (Φ (X x w.2) t.2) + u (Φ (X x w.1) t.1)) -
            F.polynomialPhaseQuadratic old Φ eL σ (j x) t w‖ ≤ η * ‖w‖ ^ 2 := by
  have deficit := hF.exists_compact_uniform_original_deficit hcomplete old
    (eL := eL) (G := G) (L := L) (C := C) (H := H) (U := U) (ν := ν)
    (O := O) (B := B) (Bσ := Bσ) (ρ := ρ) (σ := σ) (T := T) (u := u) (δ := δ)
    (ε := ε)
  have deficit₁ := deficit heL hsource hInv hG hLip hHC hHU
  have deficit₂ := deficit₁ hH hνH hsecond hHess hlegal v₀ hp₀
  have deficit₃ := deficit₂ hU hO hB h0B hBσ h0Bσ hHj hp
  have deficit₄ := deficit₃ hρ hσ hρ₀ hσ₀ hρlevel hσlevel hρproj hσproj
  have deficit₅ := deficit₄ Φ hT hC3 hstationary hu hCt hval hactual hEL hinit
    hδ hpartners hTreach hε
  obtain ⟨K, hKH, hK, hloss, hHK, hcompare⟩ := deficit₅
  have hcore := hF.original_core_unit_energy_and_clock hcomplete old hu
    hCt hval hactual hEL hinit heL hsource hlegal hδ hpartners
  have hdistance := hF.original_core_ordered_distance hcomplete old hu
    hCt hval hactual hEL hinit heL hsource hlegal hδ hpartners
  have hcenter : ∀ x ∈ K, ∀ t ∈ T,
      (F.lengthEDist (Φ (eL.symm (x, fderiv ℝ G x)) t.1)
        (Φ (eL.symm (x, fderiv ℝ G x)) t.2)).toReal = t.2 - t.1 := by
    intro x hx t ht
    exact hdistance x (hHC (hKH hx)) t.1 (hTreach ht).1 t.2 (hTreach ht).2
      (hTorder t ht)
  have model := hF.uniform_polynomial_model_quadratic old
    (eL := eL) (G := G) (K := K) (O := O) (B := Bσ) (σ := σ) (T := T)
  have model₁ := model heL hsource hInv hG hK hHK
  have model₂ := model₁ (fun x hx ↦ hlegal x (hHC (hKH hx)))
    (fun x hx ↦ (hcore x (hHC (hKH hx))).2.1)
  have model₃ := model₂ hO hBσ h0Bσ (fun x hx ↦ hHj x (hKH hx)) hσ hσ₀ hσlevel
  have model₄ := model₃ Φ hT (fun x hx ↦ hC3 x (hKH hx))
    (fun x hx ↦ hstationary x (hKH hx)) hcenter
  dsimp only
  refine ⟨K, hKH, hK, hloss, hHK, ?_⟩
  intro η hη
  obtain ⟨r₁, hr₁, h₁⟩ := hcompare (η / 2) (half_pos hη)
  obtain ⟨r₂, hr₂, h₂⟩ := model₄ (η / 2) (half_pos hη)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
  intro x hx t ht w hw hC₁ hC₂
  have hc := h₁ x hx t ht w (hw.trans_le (min_le_left _ _)) hC₁ hC₂
  have hm := h₂ x hx t ht w (hw.trans_le (min_le_right _ _))
  have hb := (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hc hm)
  have heq : η / 2 * ‖w‖ ^ 2 + η / 2 * ‖w‖ ^ 2 = η * ‖w‖ ^ 2 := by ring
  exact hb.trans_eq heq

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
