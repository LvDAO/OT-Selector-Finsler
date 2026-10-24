import OTSelector.Analysis.Calculus.ParameterizedSecondJetLevel
import OTSelector.Geometry.Finsler.Calibration.PotentialNormalData
import OTSelector.Geometry.Finsler.LegendreInjectivity

/-!
# Jointly smooth Finsler seeds from explicit polynomial second jets

A fixed reference slit state constructs common polynomial level coordinates and one
actual Legendre inverse branch. The true polynomial differential is normalized on a
common open product, preserving the original reference energy. Equal-energy actual
centers retain their velocities and have scale one; independent jet parameters need
not have that normalization at their own centers.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] in
/-- Positive collinear momenta at equal original energy have identical velocity and scale. -/
private theorem equal_energy_scaled_momentum
    (hF : F.IsSmoothStronglyConvex) (old : M) {x v v₁ : E} {a : ℝ}
    (hv : (x, v) ∈ chartEnergyDomain old)
    (hv₁ : (x, v₁) ∈ chartEnergyDomain old) (ha : 0 < a)
    (hp : fiberLegendre (F.chartEnergy old) (x, v) =
      a • fiberLegendre (F.chartEnergy old) (x, v₁))
    (henergy : F.chartEnergy old (x, v) = F.chartEnergy old (x, v₁)) :
    a = 1 ∧ v = v₁ := by
  have hav₁ : a • v₁ ≠ 0 := smul_ne_zero ha.ne' hv₁.2
  have hvelocity : v = a • v₁ :=
    hF.injOn_chartEnergy_legendre old hv.1 hv.2 hav₁
      (hp.trans (hF.chartLegendre_pos_smul old hv₁.1 hv₁.2 ha).symm)
  have hpos : 0 < F.chartEnergy old (x, v₁) := F.chartEnergy_pos old hv₁
  have hsquare : a ^ 2 = 1 := by
    rw [hvelocity, F.chartEnergy_smul old hv₁.1] at henergy
    exact mul_right_cancel₀ hpos.ne' (by simpa only [one_mul] using henergy)
  have haone : a = 1 := by nlinarith
  exact ⟨haone, by simpa only [haone, one_smul] using hvelocity⟩


/-- Independent polynomial jets admit one jointly smooth family of actual Finsler
constant-energy seeds, with the same constructed level and Legendre inverse branches. -/
theorem exists_smooth_secondJet_normalized_seed
    (hF : F.IsSmoothStronglyConvex) (old : M)
    (j₀ : ScalarSecondJet E) (v₀ : E)
    (hz₀ : (j₀.1, v₀) ∈ chartEnergyDomain old)
    (hmatch : j₀.2.2.1 = fiberLegendre (F.chartEnergy old) (j₀.1, v₀)) :
    ∃ hpv : j₀.2.2.1 v₀ ≠ 0,
      let p₀ := j₀.2.2.1
      let π₀ : E →L[ℝ] p₀.ker :=
        (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
          (covectorSplitting p₀ v₀ hpv).symm.toContinuousLinearMap
      let Φ : ScalarSecondJet E × E → ScalarSecondJet E × (p₀.ker × ℝ) :=
        fun z ↦ (z.1, (π₀ (z.2 - z.1.1),
          (scalarSecondJetPolynomial z.1 z.2 - z.1.2.1) / p₀ v₀))
      ∃ (eS : OpenPartialHomeomorph
          (ScalarSecondJet E × E) (ScalarSecondJet E × (p₀.ker × ℝ)))
        (eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
        (O : Set (ScalarSecondJet E)) (B : Set p₀.ker),
        let σ : ScalarSecondJet E × p₀.ker → E :=
          fun z ↦ (eS.symm (z.1, (z.2, 0))).2
        let q : ScalarSecondJet E × p₀.ker → E →L[ℝ] ℝ :=
          fun z ↦ fderiv ℝ (scalarSecondJetPolynomial z.1) (σ z)
        ∃ (v : ScalarSecondJet E × p₀.ker → E)
          (a : ScalarSecondJet E × p₀.ker → ℝ),
          (eS : ScalarSecondJet E × E → ScalarSecondJet E × (p₀.ker × ℝ)) = Φ ∧
          (j₀, j₀.1) ∈ eS.source ∧ ContDiffOn ℝ ∞ eS.symm eS.target ∧
          (eL : E × E → E × (E →L[ℝ] ℝ)) =
            parametricLegendre (F.chartEnergy old) ∧
          (j₀.1, v₀) ∈ eL.source ∧ eL.source ⊆ chartEnergyDomain old ∧
          ContDiffOn ℝ ∞ eL.symm eL.target ∧
          IsOpen O ∧ j₀ ∈ O ∧ IsOpen B ∧ (0 : p₀.ker) ∈ B ∧
          ContDiffOn ℝ ∞ σ (O ×ˢ B) ∧ ContDiffOn ℝ ∞ q (O ×ˢ B) ∧
          ContDiffOn ℝ ∞ v (O ×ˢ B) ∧ ContDiffOn ℝ ∞ a (O ×ˢ B) ∧
          v (j₀, 0) = v₀ ∧ a (j₀, 0) = 1 ∧
          (∀ j ∈ O, j.2.2.1 v₀ ≠ 0 ∧ (j, j.1) ∈ eS.source ∧
            σ (j, 0) = j.1 ∧ q (j, 0) = j.2.2.1 ∧
            InjOn (fun w ↦ σ (j, w)) B ∧
            (fun w ↦ σ (j, w)) '' B =
              {y | (j, y) ∈ eS.source ∧ π₀ (y - j.1) ∈ B ∧
                scalarSecondJetPolynomial j y = j.2.1}) ∧
          (∀ j ∈ O, ∀ w ∈ B,
            (j, (w, 0)) ∈ eS.target ∧
            scalarSecondJetPolynomial j (σ (j, w)) = j.2.1 ∧
            π₀ (σ (j, w) - j.1) = w ∧
            (σ (j, w), q (j, w)) ∈ eL.target ∧
            (σ (j, w), v (j, w)) ∈ eL.source ∧ 0 < a (j, w) ∧
            F.chartEnergy old (σ (j, w), v (j, w)) =
              F.chartEnergy old (j₀.1, v₀) ∧
            fiberLegendre (F.chartEnergy old) (σ (j, w), v (j, w)) =
              a (j, w) • q (j, w) ∧
            eL.symm (σ (j, w), a (j, w) • q (j, w)) =
              (σ (j, w), v (j, w))) ∧
          (∀ j ∈ O, ∀ v₁ : E,
            (j.1, v₁) ∈ chartEnergyDomain old →
            j.2.2.1 = fiberLegendre (F.chartEnergy old) (j.1, v₁) →
            F.chartEnergy old (j.1, v₁) = F.chartEnergy old (j₀.1, v₀) →
            a (j, 0) = 1 ∧ v (j, 0) = v₁) := by
  classical
  have hpvpos : 0 < j₀.2.2.1 v₀ := by
    rw [hmatch, hF.chartEnergy_euler old hz₀]
    exact mul_pos (by norm_num) (F.chartEnergy_pos old hz₀)
  have hpv : j₀.2.2.1 v₀ ≠ 0 := hpvpos.ne'
  refine ⟨hpv, ?_⟩
  dsimp only
  let p₀ := j₀.2.2.1
  let π₀ : E →L[ℝ] p₀.ker :=
    (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
      (covectorSplitting p₀ v₀ hpv).symm.toContinuousLinearMap
  obtain ⟨eS, heS, hS₀, _, hSInv, _⟩ :=
    exists_smooth_secondJet_levelCoordinates j₀ v₀ hpv
  obtain ⟨O₀, B₀, hO₀, hj₀, hB₀, hzero₀, hOdata, hStarget, hσ, hsection⟩ :=
    exists_smooth_secondJet_levelChart_product j₀ v₀ hpv eS heS hS₀ hSInv
  let σ : ScalarSecondJet E × p₀.ker → E :=
    fun z ↦ (eS.symm (z.1, (z.2, 0))).2
  let q : ScalarSecondJet E × p₀.ker → E →L[ℝ] ℝ :=
    fun z ↦ fderiv ℝ (scalarSecondJetPolynomial z.1) (σ z)
  have hcenter (j : ScalarSecondJet E) (hj : j ∈ O₀) : σ (j, 0) = j.1 :=
    (hsection j hj).1
  have hqcenter (j : ScalarSecondJet E) (hj : j ∈ O₀) : q (j, 0) = j.2.2.1 := by
    change fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, 0)) = j.2.2.1
    rw [hcenter j hj]
    exact (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv
  have hq : ContDiffOn ℝ ∞ q (O₀ ×ˢ B₀) := by
    apply (hO₀.prod hB₀).contDiffOn_iff.mpr
    intro z hz
    have hσAt : ContDiffAt ℝ ∞ σ z :=
      hσ.contDiffAt ((hO₀.prod hB₀).mem_nhds hz)
    exact (contDiffAt_fiberLegendre
      (contDiff_scalarSecondJetPolynomial_joint.contDiffAt)).comp z
        (contDiffAt_fst.prodMk hσAt)
  obtain ⟨eL, heL, hL₀, _, hLsub, hLInv, _, _, _⟩ :=
    hF.exists_smooth_chartHamiltonian old hz₀
  let V := (O₀ ×ˢ B₀) ∩ (fun z ↦ (σ z, q z)) ⁻¹' eL.target
  have hV : IsOpen V :=
    (hσ.prodMk hq).continuousOn.isOpen_inter_preimage (hO₀.prod hB₀) eL.open_target
  have hσ₀ : σ (j₀, 0) = j₀.1 := hcenter j₀ hj₀
  have hqmatch : q (j₀, 0) =
      fiberLegendre (F.chartEnergy old) (σ (j₀, 0), v₀) := by
    rw [hσ₀, hqcenter j₀ hj₀]
    exact hmatch
  have hphase₀ : (σ (j₀, 0), q (j₀, 0)) =
      parametricLegendre (F.chartEnergy old) (j₀.1, v₀) :=
    Prod.ext hσ₀ ((hqcenter j₀ hj₀).trans hmatch)
  have hmemV : (j₀, (0 : p₀.ker)) ∈ V := by
    refine ⟨⟨hj₀, hzero₀⟩, ?_⟩
    change (σ (j₀, 0), q (j₀, 0)) ∈ eL.target
    rw [hphase₀, ← heL]
    exact eL.map_source hL₀
  have hseed₀ : (σ (j₀, 0), v₀) ∈ eL.source := by
    simpa only [hσ₀] using hL₀
  obtain ⟨U, v, a, hU, hmemU, hUV, hv, ha, hv₀, ha₀, hdata⟩ :=
    hF.exists_constantEnergy_covectorData_on_branch old hV hmemV
      (hσ.mono inter_subset_left) (hq.mono inter_subset_left)
      heL hseed₀ hLsub hLInv hqmatch
  change ∀ z ∈ U, (σ z, v z) ∈ eL.source ∧ 0 < a z ∧
    F.chartEnergy old (σ z, v z) = F.chartEnergy old (σ (j₀, 0), v₀) ∧
    fiberLegendre (F.chartEnergy old) (σ z, v z) = a z • q z ∧
    eL.symm (σ z, a z • q z) = (σ z, v z) at hdata
  obtain ⟨O₁, B₁, hO₁, hj₁, hB₁, hzero₁, hprod⟩ :=
    mem_nhds_prod_iff'.mp (hU.mem_nhds hmemU)
  let O := O₁ ∩ O₀
  let B := B₁ ∩ B₀
  have hO : IsOpen O := hO₁.inter hO₀
  have hjO : j₀ ∈ O := ⟨hj₁, hj₀⟩
  have hB : IsOpen B := hB₁.inter hB₀
  have hzeroB : (0 : p₀.ker) ∈ B := ⟨hzero₁, hzero₀⟩
  have hprodU : O ×ˢ B ⊆ U := fun z hz ↦ hprod ⟨hz.1.1, hz.2.1⟩
  have hprod₀ : O ×ˢ B ⊆ O₀ ×ˢ B₀ := fun _ hz ↦ ⟨hz.1.2, hz.2.2⟩
  refine ⟨eS, eL, O, B, v, a, heS, hS₀, hSInv, heL, hL₀, hLsub, hLInv,
    hO, hjO, hB, hzeroB, hσ.mono hprod₀, hq.mono hprod₀,
    hv.mono hprodU, ha.mono hprodU, hv₀, ha₀, ?_, ?_, ?_⟩
  · intro j hj
    have hc := hsection j hj.2
    refine ⟨(hOdata j hj.2).1, (hOdata j hj.2).2, hc.1, hqcenter j hj.2, ?_, ?_⟩
    · intro w hw z hz heq
      exact hc.2.2.1 hw.2 hz.2 heq
    · ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hy : σ (j, w) ∈ (fun w ↦ σ (j, w)) '' B₀ := ⟨w, hw.2, rfl⟩
        rw [hc.2.2.2] at hy
        refine ⟨hy.1, ?_, hy.2.2⟩
        rwa [(hc.2.1 w hw.2).2]
      · rintro ⟨hys, hyB, hyP⟩
        have hy : y ∈ (fun w ↦ σ (j, w)) '' B₀ := by
          rw [hc.2.2.2]
          exact ⟨hys, hyB.2, hyP⟩
        rcases hy with ⟨w, hw, rfl⟩
        refine ⟨w, ?_, rfl⟩
        have hprojection : π₀ (σ (j, w) - j.1) = w := (hc.2.1 w hw).2
        change π₀ (σ (j, w) - j.1) ∈ B at hyB
        simpa only [hprojection] using hyB
  · intro j hj w hw
    have hzU := hprodU (show (j, w) ∈ O ×ˢ B from ⟨hj, hw⟩)
    have hn := hdata (j, w) hzU
    have hl := (hsection j hj.2).2.1 w hw.2
    refine ⟨hStarget j hj.2 w hw.2, hl.1, hl.2, (hUV hzU).2,
      hn.1, hn.2.1, ?_, hn.2.2.2.1, hn.2.2.2.2⟩
    simpa only [hσ₀] using hn.2.2.1
  · intro j hj v₁ hv₁ hp₁ hE₁
    have hzU := hprodU (show (j, (0 : p₀.ker)) ∈ O ×ˢ B from ⟨hj, hzeroB⟩)
    have hn := hdata (j, 0) hzU
    have hstate : (j.1, v (j, 0)) ∈ chartEnergyDomain old := by
      have hs := hLsub hn.1
      simpa only [hcenter j hj.2] using hs
    have henergy : F.chartEnergy old (j.1, v (j, 0)) =
        F.chartEnergy old (j.1, v₁) := by
      have heq := hn.2.2.1
      rw [hcenter j hj.2, hσ₀] at heq
      exact heq.trans hE₁.symm
    have hmomentum : fiberLegendre (F.chartEnergy old) (j.1, v (j, 0)) =
        a (j, 0) • fiberLegendre (F.chartEnergy old) (j.1, v₁) := by
      have heq := hn.2.2.2.1
      rw [hcenter j hj.2, hqcenter j hj.2, hp₁] at heq
      exact heq
    exact equal_energy_scaled_momentum hF old hstate hv₁ hn.2.1 hmomentum henergy

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
