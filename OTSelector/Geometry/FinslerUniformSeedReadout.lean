import OTSelector.Geometry.FinslerUniformSeedNormalization
import OTSelector.Analysis.Calculus.UniformParameterizedSeedNormalization
import OTSelector.Analysis.Calculus.FlowJetMatching

/-!
# Uniform readout of normalized original and polynomial Finsler seeds

The same actual normalization and a supplied smooth readout retain a compact
independent parameter set. One large original compact subcore is chosen before
all comparison tolerances. Both readout states remain in its actual open domain.
-/

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M P V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- Actual normalized polynomial seeds approximate the original inverse states
uniformly through one C1 readout on a compact parameter set. -/
theorem exists_compact_uniform_normalized_polynomial_readout
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {c : ℝ} (hc : 0 < c)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hLip : LipschitzWith L (fderiv ℝ G))
    {C H : Set E} (hHC : H ⊆ C)
    {ν : Measure E} (hH : IsCompact H) (hνH : ν H ≠ ⊤)
    (hsecond : ∀ x ∈ H, DifferentiableAt ℝ (fderiv ℝ G) x)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) H)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    (henergy : ∀ y ∈ C, F.chartEnergy old (eL.symm (y, fderiv ℝ G y)) = c)
    {T : Set P} (hT : IsCompact T)
    {R : (E × E) × P → V} {D : Set ((E × E) × P)}
    (hD : IsOpen D) (hR : ContDiffOn ℝ 1 R D)
    (hread : ∀ x ∈ H, ∀ t ∈ T, (eL.symm (x, fderiv ℝ G x), t) ∈ D)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      ∀ η : ℝ, 0 < η → ∃ r > 0,
        ∀ x ∈ K, ∀ h : E, ‖h‖ < r → x + h ∈ C → ∀ t ∈ T,
          let Q := scalarSecondJetPolynomial
            (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
          (x + h, fderiv ℝ Q (x + h)) ∈ eL.target ∧
          (eL.symm (x + h, fderiv ℝ G (x + h)), t) ∈ D ∧
          (F.covectorNormalization old eL c (x + h, fderiv ℝ Q (x + h)), t) ∈ D ∧
          ‖R (eL.symm (x + h, fderiv ℝ G (x + h)), t) -
            R (F.covectorNormalization old eL c (x + h, fderiv ℝ Q (x + h)), t)‖ ≤
              η * ‖h‖ := by
  obtain ⟨K, hKH, hK, hloss, hHK, hrem⟩ :=
    exists_compact_uniform_ambient_secondJet hH hνH hG hsecond hHess hε
  obtain ⟨_, hN, hspec⟩ := hF.covectorNormalization_spec old heL hsource hInv hc
  let A : Set ((E × (E →L[ℝ] ℝ)) × P) := eL.target ×ˢ univ
  let Ψ : (E × (E →L[ℝ] ℝ)) × P → (E × E) × P :=
    fun q ↦ (F.covectorNormalization old eL c q.1, q.2)
  have hA : IsOpen A := eL.open_target.prod isOpen_univ
  have hΨ : ContDiffOn ℝ 1 Ψ A :=
    ((hN.of_le (by simp)).comp contDiffOn_fst (fun q hq ↦ hq.1)).prodMk contDiffOn_snd
  let U : Set ((E × (E →L[ℝ] ℝ)) × P) := A ∩ Ψ ⁻¹' D
  have hU : IsOpen U := hΨ.continuousOn.isOpen_inter_preimage hA hD
  have hNR : ContDiffOn ℝ 1 (R ∘ Ψ) U :=
    hR.comp (hΨ.mono inter_subset_left) (fun q hq ↦ hq.2)
  have hgraph : ∀ x ∈ K, ∀ t ∈ T, ((x, fderiv ℝ G x), t) ∈ U := by
    intro x hx t ht
    have hxC := hHC (hKH hx)
    have hfixed := (hspec (x, fderiv ℝ G x) (hlegal x hxC)).2.2.2.2 (henergy x hxC)
    refine ⟨⟨hlegal x hxC, mem_univ _⟩, ?_⟩
    change (F.covectorNormalization old eL c (x, fderiv ℝ G x), t) ∈ D
    rw [hfixed]
    exact hread x (hKH hx) t ht
  have hfirstRem : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
      ‖fderiv ℝ G (x + h) - fderiv ℝ G x -
        fderiv ℝ (fderiv ℝ G) x h‖ ≤ η * ‖h‖ := by
    intro η hη
    obtain ⟨r, hr, hb⟩ := hrem η hη
    exact ⟨r, hr, fun x hx h hh ↦ (hb x hx h hh).1⟩
  refine ⟨K, hKH, hK, hloss, hHK, ?_⟩
  intro η hη
  obtain ⟨r, hr, hb⟩ := uniform_parameterized_original_seed_normalization
    hG hLip hK hHK hfirstRem hT hU hNR hgraph hη
  refine ⟨r, hr, ?_⟩
  intro x hx h hh hy t ht
  let B := fderiv ℝ (fderiv ℝ G) x
  let Q := scalarSecondJetPolynomial (x, G x, fderiv ℝ G x, B)
  have hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt G (fderiv ℝ G y) y :=
    Filter.Eventually.of_forall fun y ↦ (hG.differentiable one_ne_zero y).hasFDerivAt
  have hsym : ∀ v w : E, B v w = B w v :=
    second_derivative_symmetric_of_eventually hfirst (hsecond x (hKH hx)).hasFDerivAt
  have hDQ : fderiv ℝ Q (x + h) = fderiv ℝ G x + B h := by
    simpa only [Q, scalarSecondJetPolynomial, add_sub_cancel_left] using
      (hasFDerivAt_secondJetPolynomial x (G x) (fderiv ℝ G x) B hsym (x + h)).fderiv
  have hfixed := (hspec (x + h, fderiv ℝ G (x + h)) (hlegal (x + h) hy)).2.2.2.2
    (henergy (x + h) hy)
  obtain ⟨hactual, hmodel, hbound⟩ := hb x hx h hh t ht
  change (x + h, fderiv ℝ Q (x + h)) ∈ eL.target ∧
    (eL.symm (x + h, fderiv ℝ G (x + h)), t) ∈ D ∧
    (F.covectorNormalization old eL c (x + h, fderiv ℝ Q (x + h)), t) ∈ D ∧
    ‖R (eL.symm (x + h, fderiv ℝ G (x + h)), t) -
      R (F.covectorNormalization old eL c (x + h, fderiv ℝ Q (x + h)), t)‖ ≤ η * ‖h‖
  change ((x + h, fderiv ℝ G (x + h)), t) ∈ A ∧
    (F.covectorNormalization old eL c (x + h, fderiv ℝ G (x + h)), t) ∈ D at hactual
  change ((x + h, fderiv ℝ G x + B h), t) ∈ A ∧
    (F.covectorNormalization old eL c (x + h, fderiv ℝ G x + B h), t) ∈ D at hmodel
  change ‖R (F.covectorNormalization old eL c (x + h, fderiv ℝ G (x + h)), t) -
    R (F.covectorNormalization old eL c (x + h, fderiv ℝ G x + B h), t)‖ ≤ η * ‖h‖
    at hbound
  rw [hfixed] at hactual hbound
  rw [hDQ]
  exact ⟨hmodel.1.1, hactual.2, hmodel.2, hbound⟩

/-- The same complete original flow carries the seed comparison to actual chart
positions and energy momenta, uniformly over a compact set of legal times. -/
theorem exists_compact_uniform_normalized_polynomial_flow_readout
    (hF : F.IsSmoothStronglyConvex) (old out : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {c : ℝ} (hc : 0 < c)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hLip : LipschitzWith L (fderiv ℝ G))
    {C H : Set E} (hHC : H ⊆ C)
    {ν : Measure E} (hH : IsCompact H) (hνH : ν H ≠ ⊤)
    (hsecond : ∀ x ∈ H, DifferentiableAt ℝ (fderiv ℝ G) x)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) H)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    (henergy : ∀ y ∈ C, F.chartEnergy old (eL.symm (y, fderiv ℝ G y)) = c)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hΦ : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {T : Set ℝ} (hT : IsCompact T)
    (hchart : ∀ x ∈ H, ∀ t ∈ T,
      Φ (eL.symm (x, fderiv ℝ G x)) t ∈ (extChartAt 𝓘(ℝ, E) out).source)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      ∀ η : ℝ, 0 < η → ∃ r > 0,
        ∀ x ∈ K, ∀ h : E, ‖h‖ < r → x + h ∈ C → ∀ t ∈ T,
          let Q := scalarSecondJetPolynomial
            (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
          let z := F.covectorNormalization old eL c (x + h, fderiv ℝ Q (x + h))
          (x + h, fderiv ℝ Q (x + h)) ∈ eL.target ∧
          Φ (eL.symm (x + h, fderiv ℝ G (x + h))) t ∈
            (extChartAt 𝓘(ℝ, E) out).source ∧
          Φ z t ∈ (extChartAt 𝓘(ℝ, E) out).source ∧
          ‖F.chartMomentumFamily out Φ (eL.symm (x + h, fderiv ℝ G (x + h)), t) -
            F.chartMomentumFamily out Φ (z, t)‖ ≤ η * ‖h‖ := by
  let D := (chartEnergyDomain old ×ˢ (univ : Set ℝ)) ∩
    (fun q : (E × E) × ℝ ↦ Φ q.1 q.2) ⁻¹' (extChartAt 𝓘(ℝ, E) out).source
  have hD : IsOpen D :=
    (contMDiffOn_positionFamily_of_tangentFamily hΦ).continuousOn.isOpen_inter_preimage
      ((isOpen_chartEnergyDomain old).prod isOpen_univ) (isOpen_extChartAt_source out)
  have hR : ContDiffOn ℝ 1 (F.chartMomentumFamily out Φ) D :=
    (hF.contDiffOn_chartMomentumFamily out
      (fun q hq ↦ hEL q.1 hq.1.1 q.2 (mem_univ _))
      (hΦ.mono (show D ⊆ chartEnergyDomain old ×ˢ univ from inter_subset_left))
      (fun _ hq ↦ hq.2)).of_le (by norm_num)
  have hread : ∀ x ∈ H, ∀ t ∈ T, (eL.symm (x, fderiv ℝ G x), t) ∈ D := by
    intro x hx t ht
    exact ⟨⟨hsource (eL.map_target (hlegal x (hHC hx))), mem_univ _⟩, hchart x hx t ht⟩
  obtain ⟨K, hKH, hK, hloss, hHK, hbound⟩ :=
    hF.exists_compact_uniform_normalized_polynomial_readout old heL hsource hInv hc
      hG hLip hHC hH hνH hsecond hHess hlegal henergy hT hD hR hread hε
  refine ⟨K, hKH, hK, hloss, hHK, ?_⟩
  intro η hη
  obtain ⟨r, hr, hb⟩ := hbound η hη
  refine ⟨r, hr, ?_⟩
  intro x hx h hh hy t ht
  obtain ⟨hp, ha, hm, hd⟩ := hb x hx h hh hy t ht
  exact ⟨hp, ha.2, hm.2, hd⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
