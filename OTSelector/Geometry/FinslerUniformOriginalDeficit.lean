import OTSelector.Geometry.FinslerUniformTwoSectionAction
import OTSelector.Geometry.Finsler.OriginalCoreClock
import OTSelector.Geometry.FinslerDeficitActionBound
import OTSelector.Analysis.Calculus.UniformQuadraticComposition

/-!
# Uniform comparison of the original Finsler distance deficit

A single large compact core carries the original scalar remainder and the
second-order phase-action comparison. Calibrated original covectors supply unit
energy and the exact potential clock, so the same estimates control the original
distance deficit for every allowed pair of labels and every legal time pair.
-/

open Set MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- On one large compact original core, the true calibrated distance deficit and
the normalized polynomial model differ by a uniformly vanishing quadratic error.
The supplied action regularity and stationarity are the calibrated-tube inputs. -/
theorem exists_compact_uniform_original_deficit
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
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    let j : E → ScalarSecondJet E :=
      fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let X : E → p₀.ker → E × E :=
      fun x w ↦ eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w)))
    let Y : E → p₀.ker → E × E := fun x w ↦ F.covectorNormalization old eL (1 / 2)
      (σ (j x, w), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, w)))
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ t ∈ T,
        ∀ w : p₀.ker × p₀.ker, ‖w‖ < r → ρ (x, w.1) ∈ C → ρ (x, w.2) ∈ C →
          ‖((F.lengthEDist (Φ (X x w.1) t.1) (Φ (X x w.2) t.2)).toReal -
              u (Φ (X x w.2) t.2) + u (Φ (X x w.1) t.1)) -
            ((F.lengthEDist (Φ (Y x w.1) t.1) (Φ (Y x w.2) t.2)).toReal -
              (t.2 - t.1))‖ ≤ η * ‖w‖ ^ 2 := by
  have hcore := hF.original_core_unit_energy_and_clock hcomplete old hu
    hCt hval hactual hEL hinit heL hsource hlegal hδ hpartners
  have henergy : ∀ y ∈ C, F.chartEnergy old (eL.symm (y, fderiv ℝ G y)) = 1 / 2 :=
    fun y hy ↦ (hcore y hy).2.1
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  have action := hF.exists_compact_uniform_twoSection_phaseAction old
    (eL := eL) (c := 1 / 2) (G := G) (L := L) (C := C) (H := H) (U := U) (ν := ν)
    (O := O) (B := B) (Bσ := Bσ) (ρ := ρ) (σ := σ) (T := T) (ε := ε)
  have action₁ := action heL hsource hInv hc hG hLip hHC hHU
  have action₂ := action₁ hH hνH hsecond hHess hlegal henergy v₀ hp₀
  have action₃ := action₂ hU hO hB h0B hBσ h0Bσ hHj hp
  have action₄ := action₃ hρ hσ hρ₀ hσ₀ hρlevel hσlevel hρproj hσproj
  have action₅ := action₄ Φ hT hC3 hstationary hε
  obtain ⟨K, hKH, hK, hloss, hHK, hScalar, A, hcontrol, haction⟩ := action₅
  dsimp only
  refine ⟨K, hKH, hK, hloss, hHK, ?_⟩
  let j : E → ScalarSecondJet E :=
    fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let X : E → p₀.ker → E × E :=
    fun x w ↦ eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w)))
  let Y : E → p₀.ker → E × E := fun x w ↦ F.covectorNormalization old eL (1 / 2)
    (σ (j x, w), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, w)))
  let allowed : E → p₀.ker → Prop := fun x w ↦ ρ (x, w) ∈ C
  obtain ⟨R, hR, hbase⟩ := hcontrol 1 zero_lt_one
  have hfst (x : E) (w : p₀.ker) (hC : ρ (x, w) ∈ C) :
      (X x w).1 = ρ (x, w) :=
    (parametricLegendre_inverse_components heL (hlegal _ hC)).1
  have hsize : ∀ x ∈ K, ∀ w, ‖w‖ < R → allowed x w →
      ‖ρ (x, w) - x‖ ≤ (A : ℝ) * ‖w‖ := by
    intro x hx w hw hC
    have hcenter := (parametricLegendre_inverse_components heL
      (hlegal x (hHC (hKH hx)))).1
    have hproj := norm_fst_le (X x w - eL.symm (x, fderiv ℝ G x))
    simp only [Prod.fst_sub, hfst x w hC, hcenter] at hproj
    exact hproj.trans (hbase x hx w hw hC).2.2.2.2.2.1
  have hscalar : ∀ ζ : ℝ, 0 < ζ → ∃ r > 0, ∀ x ∈ K, ∀ w : p₀.ker,
      ‖w‖ < r → allowed x w →
        ‖G (ρ (x, w)) - scalarSecondJetPolynomial (j x) (ρ (x, w))‖ ≤ ζ * ‖w‖ ^ 2 := by
    intro ζ hζ
    exact uniform_quadratic_error_of_linear_displacement K id
      (fun x y ↦ G y - scalarSecondJetPolynomial (j x) y)
      (fun x w ↦ ρ (x, w)) allowed hScalar A.coe_nonneg hR hsize hζ
  have hnorm := (hF.covectorNormalization_spec old heL hsource hInv hc).2.2
  intro η hη
  have hη3 : 0 < η / 3 := div_pos hη (by norm_num)
  obtain ⟨rA, hrA, hA⟩ := haction (η / 3) hη3
  obtain ⟨rS, hrS, hS⟩ := hscalar (η / 3) hη3
  refine ⟨min R (min rA rS), lt_min hR (lt_min hrA hrS), ?_⟩
  intro x hx t ht w hw hC₁ hC₂
  have hwR := hw.trans_le (min_le_left R (min rA rS))
  have hwA := (hw.trans_le (min_le_right R (min rA rS))).trans_le (min_le_left rA rS)
  have hwS := (hw.trans_le (min_le_right R (min rA rS))).trans_le (min_le_right rA rS)
  have hb₁ := hbase x hx w.1 ((norm_fst_le w).trans_lt hwR) hC₁
  have hb₂ := hbase x hx w.2 ((norm_snd_le w).trans_lt hwR) hC₂
  have hy₁ : (F.chartLength old (Y x w.1) : ℝ) = 1 := by
    rw [F.chartLength_eq_sqrt_energy, (hnorm _ hb₁.2.2.2.1).2.2.1]
    norm_num
  have hy₂ : (F.chartLength old (Y x w.2) : ℝ) = 1 := by
    rw [F.chartLength_eq_sqrt_energy, (hnorm _ hb₂.2.2.2.1).2.2.1]
    norm_num
  have hclock₁ : u (Φ (X x w.1) t.1) = G (X x w.1).1 + t.1 := by
    rw [hfst x w.1 hC₁]
    exact (hcore _ hC₁).2.2 t.1 (hTreach ht).1
  have hclock₂ : u (Φ (X x w.2) t.2) = G (X x w.2).1 + t.2 := by
    rw [hfst x w.2 hC₂]
    exact (hcore _ hC₂).2.2 t.2 (hTreach ht).2
  have hlevel : scalarSecondJetPolynomial (j x) (Y x w.1).1 =
      scalarSecondJetPolynomial (j x) (Y x w.2).1 :=
    (hσlevel (j x) hb₁.2.1.1 w.1 hb₁.2.1.2).trans
      (hσlevel (j x) hb₂.2.1.1 w.2 hb₂.2.1.2).symm
  have he := F.original_deficit_sub_model_norm_le_phaseAction old Φ G
    (scalarSecondJetPolynomial (j x)) u t.1 t.2
    (X x w.1, X x w.2) (Y x w.1, Y x w.2)
    (hcore _ hC₁).1 (hcore _ hC₂).1 hy₁ hy₂ hclock₁ hclock₂ hlevel
  have hs₁ := hS x hx w.1 ((norm_fst_le w).trans_lt hwS) hC₁
  have hs₂ := hS x hx w.2 ((norm_snd_le w).trans_lt hwS) hC₂
  have he₁ : ‖G (X x w.1).1 - scalarSecondJetPolynomial (j x) (X x w.1).1‖ ≤
      η / 3 * ‖w‖ ^ 2 := by
    rw [hfst x w.1 hC₁]
    exact hs₁.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le w) 2) hη3.le)
  have he₂ : ‖G (X x w.2).1 - scalarSecondJetPolynomial (j x) (X x w.2).1‖ ≤
      η / 3 * ‖w‖ ^ 2 := by
    rw [hfst x w.2 hC₂]
    exact hs₂.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le w) 2) hη3.le)
  have hsum := add_le_add (add_le_add (hA x hx t ht w hwA hC₁ hC₂) he₁) he₂
  have htotal : η / 3 * ‖w‖ ^ 2 + η / 3 * ‖w‖ ^ 2 + η / 3 * ‖w‖ ^ 2 =
      η * ‖w‖ ^ 2 := by ring
  exact he.trans (hsum.trans_eq htotal)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
