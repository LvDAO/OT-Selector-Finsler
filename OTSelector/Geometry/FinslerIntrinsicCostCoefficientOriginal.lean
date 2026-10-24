import OTSelector.Geometry.FinslerIntrinsicCostCoefficientUniform
import OTSelector.Geometry.FinslerIntrinsicCostCoefficientSeed
import OTSelector.Analysis.Calculus.CommonLevelSection

/-!
# Uniform original distance expansion with the original family's kernel

The original and polynomial level sections have the same fixed-projection first
jet. Their true tangent seeds therefore produce identical intrinsic Hessians along
the same prescribed flow. The uniform distance expansion uses the literal original
family's inverse Hessian integral, with no comparison coefficient left to identify.
-/

open Set Filter MeasureTheory Manifold Bundle Module
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The original good-core data give a uniform distance expansion with the actual
intrinsic compliance coefficient and no supplied tube or coefficient equality. -/
theorem exists_compact_uniform_original_core_intrinsicSeedQuadratic
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
    (p₀ : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0) (bW : Basis ι ℝ p₀.ker)
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
    let X : E → p₀.ker → E × E :=
      fun x w ↦ eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w)))
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ t ∈ T,
        ∀ w : p₀.ker × p₀.ker, ‖w‖ < r → ρ (x, w.1) ∈ C → ρ (x, w.2) ∈ C →
          ‖((F.lengthEDist (Φ (X x w.1) t.1) (Φ (X x w.2) t.2)).toReal -
              u (Φ (X x w.2) t.2) + u (Φ (X x w.1) t.1)) -
            F.intrinsicLengthQuadratic bW (fun z r ↦ Φ (X x z) r) 0 t.1 t.2 w‖ ≤ η * ‖w‖ ^ 2 := by
  obtain ⟨K, hKH, hK, hloss, hHK, hrem⟩ :=
    hF.exists_compact_uniform_original_core_intrinsicQuadratic hcomplete old m
      heL hsource hInv hG hLip hHC hHU hH hνH hHess hlegal p₀ v₀ hp₀ bW
      hU hO hB h0B hBσ h0Bσ hHj hp hρ hσ hρ₀ hσ₀ hρlevel hσlevel hρproj hσproj
      Φ hT hu hCt hval hactual hEL hinit hδ hpartners hgood hTreach hTorder hε
  have hinterior : letI : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm C
        (OTSelector.Geometry.calibratedInterior u) := by
    let _instOriginalSeedMetric : MetricSpace M := F.metricSpace
    intro x hx
    obtain ⟨l, r, hl, hul, hr, hur⟩ := hpartners x hx
    exact ⟨⟨l, dist_pos.mp (hl.symm ▸ hδ), hul.trans hl.symm⟩,
      ⟨r, dist_pos.mp (hr.symm ▸ hδ), hur.trans hr.symm⟩⟩
  have hcore := hF.original_core_unit_energy_and_clock hcomplete old hu
    hCt hval hactual hEL hinit heL hsource hlegal hδ hpartners
  have hcoeff (x : E) (hx : x ∈ H) :
      let j : ScalarSecondJet E :=
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
      let X : p₀.ker → E × E := fun w ↦ eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w)))
      ∀ (a b : ℝ) (w : p₀.ker × p₀.ker),
        F.intrinsicLengthQuadratic bW (F.polynomialPhaseFamily old Φ eL σ j) 0 a b w =
        F.intrinsicLengthQuadratic bW (fun z t ↦ Φ (X z) t) 0 a b w := by
    let j : ScalarSecondJet E :=
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let R := p₀.ker.subtypeL - ((fderiv ℝ G x).comp p₀.ker.subtypeL).smulRight
      (((fderiv ℝ G x) v₀)⁻¹ • v₀)
    have hρat : ContDiffAt ℝ 1 (fun w ↦ ρ (x, w)) 0 :=
      (hρ.contDiffAt ((hU.prod hB).mem_nhds ⟨hHU hx, h0B⟩)).comp 0
        (contDiffAt_const.prodMk contDiffAt_id)
    have hσat : ContDiffAt ℝ 1 (fun w ↦ σ (j, w)) 0 :=
      ((hσ.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).contDiffAt
        ((hO.prod hBσ).mem_nhds ⟨hHj x hx, h0Bσ⟩)).comp 0
          (contDiffAt_const.prodMk contDiffAt_id)
    have hρD : HasFDerivAt (fun w ↦ ρ (x, w)) R 0 := by
      apply hasFDerivAt_levelSection_of_fixedProjection p₀ v₀ hp₀
        (hG.differentiable one_ne_zero x).hasFDerivAt (hp x hx)
        (hρat.differentiableAt one_ne_zero) (hρ₀ x hx)
      · filter_upwards [hB.mem_nhds h0B] with w hw
        exact hρlevel x hx w hw
      · filter_upwards [hB.mem_nhds h0B] with w hw
        exact hρproj x hx w hw
    have hσD : HasFDerivAt (fun w ↦ σ (j, w)) R 0 := by
      apply hasFDerivAt_levelSection_of_fixedProjection p₀ v₀ hp₀
        (hasFDerivAt_scalarSecondJetPolynomial_center j) (hp x hx)
        (hσat.differentiableAt one_ne_zero) (hσ₀ _ (hHj x hx))
      · filter_upwards [hBσ.mem_nhds h0Bσ] with w hw
        exact (hσlevel j (hHj x hx) w hw).trans
          (by simp only [scalarSecondJetPolynomial, j, secondJetPolynomial_self])
      · filter_upwards [hBσ.mem_nhds h0Bσ] with w hw
        exact hσproj j (hHj x hx) w hw
    have hρmatch : HasFDerivAt (fun w ↦ ρ (x, w))
        (fderiv ℝ (fun w ↦ σ (j, w)) 0) 0 := by
      rw [hσD.fderiv]
      exact hρD
    exact (hF.polynomial_intrinsic_data_eq_original_of_core bW hcomplete old m
      hCt hu hinterior hG hactual (hHC hx) (hgood x hx).1.2.1
      (hgood x hx).1.2.2.2.1 heL hsource hInv (hlegal x (hHC hx))
      (hcore x (hHC hx)).2.1 hO hBσ h0Bσ (hHj x hx)
      (hσ.of_le (by simp)) (hσ₀ _ (hHj x hx)) hρmatch (hρ₀ x hx) hEL hinit).2
  refine ⟨K, hKH, hK, hloss, hHK, ?_⟩
  intro η hη
  obtain ⟨r, hr, hbound⟩ := hrem η hη
  refine ⟨r, hr, ?_⟩
  intro x hx t ht w hw hw₁ hw₂
  rw [← hcoeff x (hKH hx) t.1 t.2 w]
  exact hbound x hx t ht w hw hw₁ hw₂

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
