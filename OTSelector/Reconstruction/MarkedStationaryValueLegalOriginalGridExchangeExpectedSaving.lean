import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalGridExchangeSourceReadout

/-! The actual glued original-grid competitor has a strictly lower expected cost. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {probe : ℝ → ℝ → ℝ} {t : ℝ}
  {ell ε : ℝ}

/-- Original Campbell integrability supplies actual integrability in almost
every whole original edge scene, before any cell exchange is performed. -/
theorem LegalWeightedStationaryPoissonMatching.ae_integrable_sourceWindow_cost
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry probe))
    {w : (Fin q → ℝ) → ℝ} (hwm : Measurable w)
    (hw : Integrable w (volume : Measure (Fin q → ℝ))) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable (fun e : LegalMarkedPhysicalEdge q ↦
        w e.1.1 * originalWeightedEdgeCost kin probe t e)
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
  let P := (legalMarkedInputPairLaw q M.law :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
  let f : PhysicalPairPalmMark (Fin q) → ℝ :=
    fun m ↦ kin m.1.1 m.1.2 m.2 + t * probe m.1.1 m.1.2
  have hf : Integrable f (legalMarkedJointPalm q M.law) :=
    M.kinetic_integrable.add (M.probe_integrable.const_mul t)
  have hm : Measurable f := hk.add ((hg.comp measurable_fst).const_mul t)
  let F : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → ℝ :=
    fun p ↦ w p.1 * f p.2
  have hFm : Measurable F := (hwm.comp measurable_fst).mul (hm.comp measurable_snd)
  have hi : Integrable F (physicalScenePairKernel ∘ₘ P) := by
    change Integrable F (physicalScenePairCampbell P)
    rw [M.campbell_eq_volume_prod_palm]
    exact hw.mul_prod hf
  have hae := Measure.ae_integrable_of_integrable_comp hi
  have hscene : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable F (physicalScenePairKernel s.1) :=
    ae_of_ae_map measurable_fst.aemeasurable hae
  filter_upwards [hscene] with s hs
  rw [physicalScenePairKernel_apply] at hs
  have hmap := (integrable_map_measure hFm.aestronglyMeasurable
    measurable_physicalPairAnchor.aemeasurable).mp hs
  exact hmap

/-- The exact expected saving is read directly on the literal glued scene;
new-law integrability and no auxiliary moment or selection premise are supplied. -/
theorem LegalWeightedStationaryPoissonMatching.gridExchange_sourceReadout_integrable_and_integral
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G) [hell : Fact (0 < ell)]
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    {w : (Fin q → ℝ) → ℝ} (hwm : Measurable w)
    (hw : Integrable w (volume : Measure (Fin q → ℝ)))
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hwK : ∀ x ∉ K, w x = 0) :
    Integrable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      originalWeightedSourceReadout kin probe t w (originalGridExchangeScene S (p.2, p.1)))
      ((cavityGridPhaseLaw (Fin q) ell).prod
        (M.law : Measure (LegalMarkedOptimalInputScene q))) ∧
      (∫ p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q,
        originalWeightedSourceReadout kin probe t w (originalGridExchangeScene S (p.2, p.1))
        ∂(cavityGridPhaseLaw (Fin q) ell).prod
          (M.law : Measure (LegalMarkedOptimalInputScene q))) =
        (∫ x, w x) * M.value t -
          ((ENNReal.ofReal ell ^ q)⁻¹).toReal * (∫ x, w x) *
            ∫ s, S.gain s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  let P := (cavityGridPhaseLaw (Fin q) ell).prod
    (M.law : Measure (LegalMarkedOptimalInputScene q))
  let old : (Fin q → ℝ) × LegalMarkedOptimalInputScene q → ℝ :=
    fun p ↦ originalWeightedSourceReadout kin probe t w p.2
  let gain : (Fin q → ℝ) × LegalMarkedOptimalInputScene q → ℝ :=
    fun p ↦ ∑' k : CavityGridLattice (Fin q) ell, S.sourceWindowGain w (k +ᵥ p.1, p.2)
  have hold := M.weightedSourceReadout_integrable_and_integral hk hg t hwm hw
  have hproj : MeasurePreserving Prod.snd P
      (M.law : Measure (LegalMarkedOptimalInputScene q)) := measurePreserving_snd
  have holdi : Integrable old P := hproj.integrable_comp_of_integrable hold.1
  have hgain := M.phaseSourceWindowGain_integrable_and_integral hk hg hC hkb hgb S hwm hw
  have hfull : ∀ᵐ p ∂P, IsFullOriginalInputMatching q p.2 := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hproj.map_eq]
    exact M.full_matching
  have hfiber : ∀ᵐ p ∂P, Integrable
      (fun e : LegalMarkedPhysicalEdge q ↦ w e.1.1 * originalWeightedEdgeCost kin probe t e)
      (p.2.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
    have h : ∀ᵐ s ∂P.map Prod.snd, Integrable
        (fun e : LegalMarkedPhysicalEdge q ↦ w e.1.1 * originalWeightedEdgeCost kin probe t e)
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
      rw [hproj.map_eq]
      exact M.ae_integrable_sourceWindow_cost hk hg hwm hw
    exact ae_of_ae_map measurable_snd.aemeasurable h
  have heq : (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      originalWeightedSourceReadout kin probe t w (originalGridExchangeScene S (p.2, p.1)))
      =ᵐ[P] old - gain := by
    filter_upwards [hfull, hfiber] with p hp hi
    have h := hp.gridExchange_sourceWindow_integrable_and_gain hell.out S p.1 w hK hwK hi
    dsimp only [old, gain, Pi.sub_apply]
    linarith [h.2]
  refine ⟨(holdi.sub hgain.1).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  change (∫ p, old p - gain p ∂P) = _
  rw [integral_sub holdi hgain.1, hgain.2]
  congr 1
  have hm : AEStronglyMeasurable (originalWeightedSourceReadout kin probe t w)
      (P.map Prod.snd) := by rw [hproj.map_eq]; exact hold.1.aestronglyMeasurable
  have he := integral_map measurable_snd.aemeasurable hm
  rw [hproj.map_eq] at he
  exact he.symm.trans hold.2

/-- The literal globally exchanged original scene has strictly smaller mean
cost in the actual physical unit window whenever a certified pair occurs
with positive original probability. -/
theorem LegalWeightedStationaryPoissonMatching.gridExchange_unitSourceReadout_strict_decrease
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G) [hell : Fact (0 < ell)] (hε : 0 < ε)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (hA : 0 < (M.law : Measure (LegalMarkedOptimalInputScene q)) S.active) :
    Integrable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      originalWeightedSourceReadout kin probe t (legalMarkedUnitWindowWeight q)
        (originalGridExchangeScene S (p.2, p.1)))
      ((cavityGridPhaseLaw (Fin q) ell).prod
        (M.law : Measure (LegalMarkedOptimalInputScene q))) ∧
      (∫ p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q,
        originalWeightedSourceReadout kin probe t (legalMarkedUnitWindowWeight q)
          (originalGridExchangeScene S (p.2, p.1))
        ∂(cavityGridPhaseLaw (Fin q) ell).prod
          (M.law : Measure (LegalMarkedOptimalInputScene q))) < M.value t := by
  have hwm : Measurable (legalMarkedUnitWindowWeight q) :=
    measurable_const.indicator (measurableSet_palmUnitCube (Fin q))
  have hw := integrable_legalMarkedUnitWindowWeight q
  have hK : IsCompact (palmUnitCube (Fin q)) := isCompact_Icc
  have hwK : ∀ x ∉ palmUnitCube (Fin q), legalMarkedUnitWindowWeight q x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem hx _
  have hread := M.gridExchange_sourceReadout_integrable_and_integral
    hk hg hC hkb hgb S hwm hw hK hwK
  have hsave := M.phaseSourceWindowGain_integral_pos
    hk hg hC hkb hgb hε S hA hwm hw (by rw [integral_legalMarkedUnitWindowWeight]; norm_num)
  have hformula := M.phaseSourceWindowGain_integrable_and_integral hk hg hC hkb hgb S hwm hw
  rw [hformula.2, integral_legalMarkedUnitWindowWeight, mul_one] at hsave
  refine ⟨hread.1, ?_⟩
  rw [hread.2, integral_legalMarkedUnitWindowWeight, one_mul, mul_one]
  exact sub_lt_self _ hsave

end OTSelector.Reconstruction
