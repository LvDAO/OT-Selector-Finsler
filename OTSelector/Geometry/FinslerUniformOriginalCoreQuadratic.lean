import OTSelector.Geometry.FinslerUniformOriginalLengthQuadratic
import OTSelector.Geometry.FinslerPolynomialTubeExistence

/-!
# Uniform original length expansion from the actual calibrated core

The existing good-core properties construct a calibrated tube for each actual
normalized polynomial family and inner time interval. They therefore supply the
uniform original distance expansion with its integrated length-Hessian coefficient.
No tube choice or separate flow regularity is an input.
-/

open Set MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Actual good-core jets construct the pointwise polynomial tubes needed for one
uniform original distance expansion on a compact set of arbitrarily large mass. -/
theorem exists_compact_uniform_original_core_lengthQuadratic
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure m]
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hLip : LipschitzWith L (fderiv ℝ G))
    {C H U : Set E} (hHC : H ⊆ C) (hHU : H ⊆ U)
    {ν : Measure E} (hH : IsCompact H) (hνH : ν H ≠ ⊤)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) H)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    (p₀ : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0)
    {O : Set (ScalarSecondJet E)} {B Bσ : Set p₀.ker}
    (hU : IsOpen U) (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : p₀.ker) ∈ B)
    (hBσ : IsOpen Bσ) (h0Bσ : (0 : p₀.ker) ∈ Bσ)
    (hHj : ∀ x ∈ H, (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    (hp : ∀ x ∈ H, (fderiv ℝ G x) v₀ ≠ 0)
    {ρ : E × p₀.ker → E} {σ : ScalarSecondJet E × p₀.ker → E}
    (hρ : ContDiffOn ℝ 1 ρ (U ×ˢ B)) (hσ : ContDiffOn ℝ ∞ σ (O ×ˢ Bσ))
    (hρ₀ : ∀ x ∈ H, ρ (x, 0) = x) (hσ₀ : ∀ j ∈ O, σ (j, 0) = j.1)
    (hρlevel : ∀ x ∈ H, ∀ w ∈ B, G (ρ (x, w)) = G x)
    (hσlevel : ∀ j ∈ O, ∀ w ∈ Bσ,
      scalarSecondJetPolynomial j (σ (j, w)) = j.2.1)
    (hρproj : ∀ x ∈ H, ∀ w ∈ B,
      ((covectorSplitting p₀ v₀ hp₀).symm (ρ (x, w) - x)).1 = w)
    (hσproj : ∀ j ∈ O, ∀ w ∈ Bσ,
      ((covectorSplitting p₀ v₀ hp₀).symm (σ (j, w) - j.1)).1 = w)
    (Φ : (E × E) → ℝ → M) {T : Set (ℝ × ℝ)} (hT : IsCompact T)
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
    {A : E → ℝ → M}
    (hgood : ∀ x ∈ H, F.HasC11PotentialFamilyAt m old 0 u G C x ∧
      F.HasC11LevelPositionComparisonAt old G A δ x)
    (hTreach : T ⊆ Ioo (-δ) δ ×ˢ Ioo (-δ) δ)
    (hTorder : ∀ t ∈ T, t.1 < t.2)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    let j : E → ScalarSecondJet E :=
      fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let X : E → p₀.ker → E × E :=
      fun x w ↦ eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w)))
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      (∀ x ∈ K, ∀ t ∈ T,
        Nonempty (F.CalibratedTube (F.polynomialPhaseFamily old Φ eL σ (j x))
          t.1 t.2 u)) ∧
      ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ t ∈ T,
        ∀ D : F.CalibratedTube (F.polynomialPhaseFamily old Φ eL σ (j x)) t.1 t.2 u,
        ∀ w : p₀.ker × p₀.ker, ‖w‖ < r → ρ (x, w.1) ∈ C → ρ (x, w.2) ∈ C →
          ‖((F.lengthEDist (Φ (X x w.1) t.1) (Φ (X x w.2) t.2)).toReal -
              u (Φ (X x w.2) t.2) + u (Φ (X x w.1) t.1)) -
            D.quadratic w‖ ≤ η * ‖w‖ ^ 2 := by
  have hinterior : letI : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm C
        (OTSelector.Geometry.calibratedInterior u) := by
    let _instCoreQuadraticMetric : MetricSpace M := F.metricSpace
    intro x hx
    obtain ⟨l, r, hl, hul, hr, hur⟩ := hpartners x hx
    exact ⟨⟨l, dist_pos.mp (hl.symm ▸ hδ), hul.trans hl.symm⟩,
      ⟨r, dist_pos.mp (hr.symm ▸ hδ), hur.trans hr.symm⟩⟩
  have hsecond : ∀ x ∈ H, DifferentiableAt ℝ (fderiv ℝ G) x :=
    fun x hx ↦ (hgood x hx).1.2.2.2.1.differentiableAt
  have htube (x : E) (hx : x ∈ H) (t : ℝ × ℝ) (ht : t ∈ T) :
      Nonempty (F.CalibratedTube (F.polynomialPhaseFamily old Φ eL σ
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)) t.1 t.2 u) := by
    exact hF.exists_polynomial_calibratedTube_of_original_core hcomplete old m
      hCt hu hinterior hG hval hactual (hHC hx) (hgood x hx).1.2.1
      (hgood x hx).1.2.2.2.1 heL hsource hInv hlegal hEL hinit hδ hpartners
      (hgood x hx).2 p₀ v₀ hp₀ (hp x hx) hO hBσ h0Bσ (hHj x hx) hσ
      (hσ₀ _ (hHj x hx)) (hσlevel _ (hHj x hx)) (hσproj _ (hHj x hx))
      (hTorder t ht) (hTreach ht).1 (hTreach ht).2
  have original := hF.exists_compact_uniform_original_lengthQuadratic hcomplete old
    (eL := eL) (G := G) (L := L) (C := C) (H := H) (U := U) (ν := ν)
    (O := O) (B := B) (Bσ := Bσ) (ρ := ρ) (σ := σ) (T := T) (u := u) (δ := δ)
    (ε := ε)
  have original₁ := original heL hsource hInv hG hLip hHC hHU
  have original₂ := original₁ hH hνH hsecond hHess hlegal v₀ hp₀
  have original₃ := original₂ hU hO hB h0B hBσ h0Bσ hHj hp
  have original₄ := original₃ hρ (hσ.of_le (by simp)) hρ₀ hσ₀
    hρlevel hσlevel hρproj hσproj
  obtain ⟨K, hKH, hK, hloss, hHK, hrem⟩ :=
    original₄ Φ hT hu hCt hval hactual hEL hinit hδ hpartners
      (hTreach.trans (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)) htube hε
  exact ⟨K, hKH, hK, hloss, hHK, fun x hx ↦ htube x (hKH hx), hrem⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
