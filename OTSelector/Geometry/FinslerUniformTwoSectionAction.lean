import OTSelector.Geometry.FinslerUniformTwoSectionSeed
import OTSelector.Geometry.FinslerUniformPhaseAction

/-!
# Uniform action comparison for the actual two-section Finsler seeds

The initial states, their center displacement bounds, and their uniform first-order
comparison are all derived from the original core and its actual jet polynomials.
Only the action regularity and stationarity supplied by calibrated tubes are retained
as geometric inputs. The same original distance and allowed labels are used.
-/

open Set MeasureTheory Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- One large compact original core supports a common second-order action comparison
for both original and polynomial level sections, throughout a compact set of times. -/
theorem exists_compact_uniform_twoSection_phaseAction
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target) {c : ℝ} (hc : 0 < c)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hLip : LipschitzWith L (fderiv ℝ G))
    {C H U : Set E} (hHC : H ⊆ C) (hHU : H ⊆ U)
    {ν : Measure E} (hH : IsCompact H) (hνH : ν H ≠ ⊤)
    (hsecond : ∀ x ∈ H, DifferentiableAt ℝ (fderiv ℝ G) x)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) H)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    (henergy : ∀ y ∈ C, F.chartEnergy old (eL.symm (y, fderiv ℝ G y)) = c)
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
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    let j : E → ScalarSecondJet E :=
      fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let X : E → p₀.ker → E × E :=
      fun x w ↦ eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w)))
    let Y : E → p₀.ker → E × E := fun x w ↦ F.covectorNormalization old eL c
      (σ (j x, w), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, w)))
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      (∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
        ‖G (x + h) - scalarSecondJetPolynomial (j x) (x + h)‖ ≤ η * ‖h‖ ^ 2) ∧
      ∃ A : ℝ≥0,
        (∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ w : p₀.ker,
          ‖w‖ < r → ρ (x, w) ∈ C →
            (x, w) ∈ U ×ˢ B ∧ (j x, w) ∈ O ×ˢ Bσ ∧
            X x w ∈ chartEnergyDomain old ∧
            (σ (j x, w), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, w))) ∈
              eL.target ∧
            Y x w ∈ chartEnergyDomain old ∧
            ‖X x w - eL.symm (x, fderiv ℝ G x)‖ ≤ (A : ℝ) * ‖w‖ ∧
            ‖Y x w - eL.symm (x, fderiv ℝ G x)‖ ≤ (A : ℝ) * ‖w‖ ∧
            ‖X x w - Y x w‖ ≤ η * ‖w‖) ∧
      ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ t ∈ T,
        ∀ w : p₀.ker × p₀.ker, ‖w‖ < r → ρ (x, w.1) ∈ C → ρ (x, w.2) ∈ C →
          ‖F.phaseLengthAction old Φ (scalarSecondJetPolynomial (j x)) t.1 t.2
              (X x w.1, X x w.2) -
            F.phaseLengthAction old Φ (scalarSecondJetPolynomial (j x)) t.1 t.2
              (Y x w.1, Y x w.2)‖ ≤ η * ‖w‖ ^ 2 := by
  have seed := hF.exists_compact_uniform_twoSection_seed old
    (eL := eL) (c := c) (G := G) (L := L) (C := C) (H := H) (U := U) (ν := ν)
    (O := O) (B := B) (Bσ := Bσ) (ρ := ρ) (σ := σ) (ε := ε)
  have seed₁ := seed heL hsource hInv hc hG hLip hHC hHU
  have seed₂ := seed₁ hH hνH hsecond hHess hlegal henergy v₀ hp₀
  have seed₃ := seed₂ hU hO hB h0B hBσ h0Bσ hHj hp
  have seed₄ := seed₃ hρ hσ hρ₀ hσ₀ hρlevel hσlevel hρproj hσproj hε
  obtain ⟨K, hKH, hK, hloss, hHK, hScalar, A, hcontrol⟩ := seed₄
  dsimp only
  refine ⟨K, hKH, hK, hloss, hHK, hScalar, A, hcontrol, ?_⟩
  intro η hη
  obtain ⟨R, hR, hbase⟩ := hcontrol 1 zero_lt_one
  let j : E → ScalarSecondJet E :=
    fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let X : E → p₀.ker → E × E :=
    fun x w ↦ eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w)))
  let Y : E → p₀.ker → E × E := fun x w ↦ F.covectorNormalization old eL c
    (σ (j x, w), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, w)))
  let allowed : E → p₀.ker → Prop := fun x w ↦ ρ (x, w) ∈ C
  have hsize : ∀ x ∈ K, ∀ w, ‖w‖ < R → allowed x w →
      ‖X x w - eL.symm (x, fderiv ℝ G x)‖ ≤ (A : ℝ) * ‖w‖ ∧
      ‖Y x w - eL.symm (x, fderiv ℝ G x)‖ ≤ (A : ℝ) * ‖w‖ := by
    intro x hx w hw hC
    have hd := (hbase x hx w hw hC).2.2.2.2.2
    exact ⟨hd.1, hd.2.1⟩
  have hmis : ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ x ∈ K, ∀ w, ‖w‖ < r →
      allowed x w → ‖X x w - Y x w‖ ≤ δ * ‖w‖ := by
    intro δ hδ
    obtain ⟨r, hr, hb⟩ := hcontrol δ hδ
    exact ⟨r, hr, fun x hx w hw hC ↦ (hb x hx w hw hC).2.2.2.2.2.2.2⟩
  have action := F.uniform_phaseLengthAction_transfer_of_original_seeds old Φ
    (W := p₀.ker) (G := G) (K := K) (T := T) (A := A) (R := R) (η := η)
  have action₁ := action hG hK hHK hT eL
  have action₂ := action₁ (fun x hx ↦ hlegal x (hHC (hKH hx)))
    (fun x hx ↦ hC3 x (hKH hx)) (fun x hx ↦ hstationary x (hKH hx))
  have action₃ := action₂ X Y allowed hR
  exact action₃ hsize hmis hη

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
