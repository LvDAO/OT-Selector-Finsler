import OTSelector.Geometry.FinslerUniformOriginalQuadratic
import OTSelector.Geometry.FinslerPolynomialTubeData

/-!
# Uniform original distance expansion with the actual length coefficient

Pointwise calibrated tubes supply the action regularity and stationary derivative.
The existing compact original expansion and exact coefficient identification then
give one quadratic error radius for every tube describing the same polynomial
family. No uniform or measurable choice of tubes is required.
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

/-- The original deficit has the actual integrated length-Hessian coefficient on
one retained compact core. The same radius works for every admissible pointwise
tube; action smoothness and stationarity are derived from its geometric data. -/
theorem exists_compact_uniform_original_lengthQuadratic
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
    (htube : ∀ x ∈ H, ∀ t ∈ T,
      Nonempty (F.CalibratedTube
        (F.polynomialPhaseFamily old Φ eL σ
          (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)) t.1 t.2 u))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    let j : E → ScalarSecondJet E :=
      fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let X : E → p₀.ker → E × E :=
      fun x w ↦ eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w)))
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ t ∈ T,
        ∀ D : F.CalibratedTube (F.polynomialPhaseFamily old Φ eL σ (j x)) t.1 t.2 u,
        ∀ w : p₀.ker × p₀.ker, ‖w‖ < r → ρ (x, w.1) ∈ C → ρ (x, w.2) ∈ C →
          ‖((F.lengthEDist (Φ (X x w.1) t.1) (Φ (X x w.2) t.2)).toReal -
              u (Φ (X x w.2) t.2) + u (Φ (X x w.1) t.1)) -
            D.quadratic w‖ ≤ η * ‖w‖ ^ 2 := by
  have hcore := hF.original_core_unit_energy_and_clock hcomplete old hu
    hCt hval hactual hEL hinit heL hsource hlegal hδ hpartners
  have hdata (x : E) (hx : x ∈ H) (t : ℝ × ℝ) (_ht : t ∈ T)
      (D : F.CalibratedTube (F.polynomialPhaseFamily old Φ eL σ
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)) t.1 t.2 u) :=
    hF.polynomialPhase_data_of_calibratedTube hcomplete old
      heL hsource hInv hG (hlegal x (hHC hx)) (hcore x (hHC hx)).2.1
      hO hBσ h0Bσ (hHj x hx) hσ hσ₀ hσlevel hEL hinit hu D
  have hC3 (x : E) (hx : x ∈ H) (t : ℝ × ℝ) (ht : t ∈ T) :=
    (hdata x hx t ht (htube x hx t ht).some).1
  have hstationary (x : E) (hx : x ∈ H) (t : ℝ × ℝ) (ht : t ∈ T) :=
    (hdata x hx t ht (htube x hx t ht).some).2.1
  have horder (t : ℝ × ℝ) (ht : t ∈ T) (x : E) (hx : x ∈ H) : t.1 ≤ t.2 :=
    (htube x hx t ht).some.ordered.le
  by_cases hHempty : H = ∅
  · refine ⟨∅, empty_subset _, isCompact_empty, ?_, continuousOn_empty _, ?_⟩
    · simpa only [hHempty, sdiff_empty, measure_empty] using (pos_iff_ne_zero.mpr hε)
    · intro η hη
      exact ⟨1, zero_lt_one, fun x hx ↦ False.elim (notMem_empty x hx)⟩
  have hHnonempty := Set.nonempty_iff_ne_empty.mpr hHempty
  have hTorder (t : ℝ × ℝ) (ht : t ∈ T) : t.1 ≤ t.2 :=
    horder t ht hHnonempty.some hHnonempty.some_mem
  have original := hF.exists_compact_uniform_original_quadratic hcomplete old
    (eL := eL) (G := G) (L := L) (C := C) (H := H) (U := U) (ν := ν)
    (O := O) (B := B) (Bσ := Bσ) (ρ := ρ) (σ := σ) (T := T) (u := u) (δ := δ)
    (ε := ε)
  have original₁ := original heL hsource hInv hG hLip hHC hHU
  have original₂ := original₁ hH hνH hsecond hHess hlegal v₀ hp₀
  have original₃ := original₂ hU hO hB h0B hBσ h0Bσ hHj hp
  have original₄ := original₃ hρ hσ hρ₀ hσ₀ hρlevel hσlevel hρproj hσproj
  obtain ⟨K, hKH, hK, hloss, hHK, hrem⟩ := original₄ Φ hT hC3 hstationary
    hu hCt hval hactual hEL hinit hδ hpartners hTreach hTorder hε
  refine ⟨K, hKH, hK, hloss, hHK, ?_⟩
  intro η hη
  obtain ⟨r, hr, hb⟩ := hrem η hη
  refine ⟨r, hr, ?_⟩
  intro x hx t ht D w hw h₁ h₂
  rw [← (hdata x (hKH hx) t ht D).2.2 w]
  exact hb x hx t ht w hw h₁ h₂

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
