import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalOriginCycleGain
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalRelativeSourceMean

/-! Exact signed source-cell mean savings on the original random Haar grid. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

variable {q : ℕ} {c : LegalMarkedPhysicalEdge q → ℝ} {ell ε : ℝ}

/-- The signed exchange gain at the two unchanged original source atoms,
as seen in a physical source window from the actual cell root. -/
def OriginalOriginCycleSelector.sourceWindowGain
    (S : OriginalOriginCycleSelector q c ell ε) (w : (Fin q → ℝ) → ℝ)
    (p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q) : ℝ :=
  let r := legalMarkedInputSceneReroot q p.1 p.2
  w (p.1 + (S.pair r).1.1.1) * S.firstGain r +
    w (p.1 + (S.pair r).2.1.1) * S.secondGain r

theorem OriginalOriginCycleSelector.measurable_sourceWindowGain
    (S : OriginalOriginCycleSelector q c ell ε) (hc : Measurable c)
    {w : (Fin q → ℝ) → ℝ} (hw : Measurable w) : Measurable (S.sourceWindowGain w) := by
  have hr := measurable_legalMarkedInputSceneReroot_joint q
  have hp := S.measurable_pair.comp hr
  exact ((hw.comp (measurable_fst.add hp.fst.fst.fst)).mul
    ((S.measurable_firstGain hc).comp hr)).add
      ((hw.comp (measurable_fst.add hp.snd.fst.fst)).mul
        ((S.measurable_secondGain hc).comp hr))

variable {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
  {probe : ℝ → ℝ → ℝ} {t : ℝ}

/-- The actual cell readout is exactly the pair of signed differences at
the transported original source atoms, including inactivity. -/
theorem OriginalOriginCycleSelector.sourceWindowGain_eq_relativePair
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (w : (Fin q → ℝ) → ℝ) (b : Fin q → ℝ) (s : LegalMarkedOptimalInputScene q) :
    S.sourceWindowGain w (b, s) =
      if (b, s) ∈ S.relativeActive then
        w (S.relativePair (b, s)).1.1.1 *
          (originalWeightedEdgeCost kin probe t (S.relativePair (b, s)).1 -
            originalWeightedEdgeCost kin probe t
              ((S.relativePair (b, s)).1.1, (S.relativePair (b, s)).2.2)) +
        w (S.relativePair (b, s)).2.1.1 *
          (originalWeightedEdgeCost kin probe t (S.relativePair (b, s)).2 -
            originalWeightedEdgeCost kin probe t
              ((S.relativePair (b, s)).2.1, (S.relativePair (b, s)).1.2))
      else 0 := by
  by_cases ha : (b, s) ∈ S.relativeActive
  · rw [ite_eq_left ha]
    have ha' : legalMarkedInputSceneReroot q b s ∈ S.active := ha
    simp only [sourceWindowGain, firstGain, secondGain, Set.indicator_of_mem ha', relativePair]
    have hcross (e f : LegalMarkedPhysicalEdge q) :
        ((physicalSceneEdgeReroot (-b) e).1, (physicalSceneEdgeReroot (-b) f).2) =
          physicalSceneEdgeReroot (-b) (e.1, f.2) := rfl
    simp only [hcross]
    simp only [originalWeightedEdgeCost_reroot]
    have hsource (e : LegalMarkedPhysicalEdge q) :
        (physicalSceneEdgeReroot (-b) e).1.1 = b + e.1.1 := by
      change e.1.1 - -b = b + e.1.1
      simp only [sub_neg_eq_add, add_comm]
    simp only [hsource]
  · rw [ite_eq_right ha]
    have ha' : legalMarkedInputSceneReroot q b s ∉ S.active := ha
    simp only [sourceWindowGain, firstGain, secondGain,
      Set.indicator_of_notMem ha', mul_zero, add_zero]

/-- All environment dependence of the selected two sources is retained.
The full Haar/original-scene integral equals the physical window mass times
the actual total origin-cell gain. -/
theorem LegalWeightedStationaryPoissonMatching.sourceWindowGain_integrable_and_integral
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G) (hell : 0 ≤ ell)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    {w : (Fin q → ℝ) → ℝ} (hw : Integrable w (volume : Measure (Fin q → ℝ))) :
    Integrable (S.sourceWindowGain w)
      ((volume : Measure (Fin q → ℝ)).prod
        (M.law : Measure (LegalMarkedOptimalInputScene q))) ∧
      (∫ p, S.sourceWindowGain w p
        ∂(volume : Measure (Fin q → ℝ)).prod
          (M.law : Measure (LegalMarkedOptimalInputScene q))) =
        (∫ b, w b) * ∫ s, S.gain s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨ha, hb⟩ := S.atomGains_integrable t hk hg hC hkb hgb hell M.law
  have h₁ := M.relativeSourceAtom_integrable_and_integral
    (fun s ↦ (S.pair s).1.1.1) S.measurable_pair.fst.fst.fst S.firstGain ha hw
  have h₂ := M.relativeSourceAtom_integrable_and_integral
    (fun s ↦ (S.pair s).2.1.1) S.measurable_pair.snd.fst.fst S.secondGain hb hw
  refine ⟨h₁.1.add h₂.1, ?_⟩
  simp only [OriginalOriginCycleSelector.sourceWindowGain]
  rw [integral_add h₁.1 h₂.1, h₁.2, h₂.2]
  simp only [OriginalOriginCycleSelector.gain]
  rw [integral_add ha hb, mul_add]

/-- Exact mean saving on the actual normalized randomly shifted Ioc grid.
Absolute integrability is proved internally from the original coefficient bound. -/
theorem LegalWeightedStationaryPoissonMatching.phaseSourceWindowGain_integrable_and_integral
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G) [hell : Fact (0 < ell)]
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    {w : (Fin q → ℝ) → ℝ} (hwm : Measurable w)
    (hw : Integrable w (volume : Measure (Fin q → ℝ))) :
    Integrable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      ∑' k : CavityGridLattice (Fin q) ell, S.sourceWindowGain w (k +ᵥ p.1, p.2))
      ((cavityGridPhaseLaw (Fin q) ell).prod
        (M.law : Measure (LegalMarkedOptimalInputScene q))) ∧
      (∫ p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q,
        ∑' k : CavityGridLattice (Fin q) ell, S.sourceWindowGain w (k +ᵥ p.1, p.2)
        ∂(cavityGridPhaseLaw (Fin q) ell).prod
          (M.law : Measure (LegalMarkedOptimalInputScene q))) =
        ((ENNReal.ofReal ell ^ q)⁻¹).toReal * (∫ b, w b) *
          ∫ s, S.gain s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  have hread := M.sourceWindowGain_integrable_and_integral hk hg hC hkb hgb hell.out.le S hw
  have hm := S.measurable_sourceWindowGain
    (measurable_originalWeightedEdgeCost kin hk probe hg t) hwm
  have hp := integrable_integral_cavityGridPhaseLaw_prod_periodization (Fin q) ell
    (M.law : Measure (LegalMarkedOptimalInputScene q)) (S.sourceWindowGain w) hm hread.1
  refine ⟨hp.1, ?_⟩
  rw [hp.2, hread.2, Fintype.card_fin, mul_assoc]

/-- A positive mass of certified original pairs yields a strict decrease of
the expected source-window cost on the actual random grid. -/
theorem LegalWeightedStationaryPoissonMatching.phaseSourceWindowGain_integral_pos
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G) [hell : Fact (0 < ell)] (hε : 0 < ε)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (hA : 0 < (M.law : Measure (LegalMarkedOptimalInputScene q)) S.active)
    {w : (Fin q → ℝ) → ℝ} (hwm : Measurable w)
    (hw : Integrable w (volume : Measure (Fin q → ℝ))) (hwp : 0 < ∫ b, w b) :
    0 < (∫ p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q,
      ∑' k : CavityGridLattice (Fin q) ell, S.sourceWindowGain w (k +ᵥ p.1, p.2)
      ∂(cavityGridPhaseLaw (Fin q) ell).prod
        (M.law : Measure (LegalMarkedOptimalInputScene q))) := by
  have he := M.phaseSourceWindowGain_integrable_and_integral hk hg hC hkb hgb S hwm hw
  rw [he.2]
  obtain ⟨ha, hb⟩ := S.atomGains_integrable t hk hg hC hkb hgb hell.out.le M.law
  have hgain := S.integral_gain_pos M.law hε (ha.add hb) hA
  apply mul_pos (mul_pos ?_ hwp) hgain
  apply ENNReal.toReal_pos
  · exact ENNReal.inv_ne_zero.mpr (by finiteness)
  · exact (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr
      (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hell.out))))).ne

/-- At each actual swapped cell the source-window cost difference is
precisely the two signed gains at its unchanged source atoms. -/
theorem integral_originalTwoEdgeSwapPlan_sourceWindow_gain
    (μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    {e f : LegalMarkedPhysicalEdge q} (hne : e ≠ f)
    (he : (μ : Measure (LegalMarkedPhysicalEdge q)) {e} = 1)
    (hf : (μ : Measure (LegalMarkedPhysicalEdge q)) {f} = 1)
    (c : LegalMarkedPhysicalEdge q → ℝ) (w : (Fin q → ℝ) → ℝ)
    (hi : Integrable (fun x : LegalMarkedPhysicalEdge q ↦ w x.1.1 * c x)
      (μ : Measure (LegalMarkedPhysicalEdge q))) :
    (∫ x : LegalMarkedPhysicalEdge q, w x.1.1 * c x
      ∂(μ : Measure (LegalMarkedPhysicalEdge q))) -
      (∫ x : LegalMarkedPhysicalEdge q, w x.1.1 * c x
        ∂(originalTwoEdgeSwapPlan μ e f : Measure (LegalMarkedPhysicalEdge q))) =
      w e.1.1 * (c e - c (e.1, f.2)) + w f.1.1 * (c f - c (f.1, e.2)) := by
  rw [integral_originalTwoEdgeSwapPlan μ hne he hf hi]
  ring

end OTSelector.Reconstruction
