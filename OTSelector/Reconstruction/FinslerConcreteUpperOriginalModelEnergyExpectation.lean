import OTSelector.Probability.SubcouplingTypedIID
import OTSelector.Reconstruction.FinslerConcreteUpperDependentModelFamilyBound
import OTSelector.Reconstruction.FinslerConcreteUpperFineEnergyBudget
import OTSelector.Reconstruction.FinslerConcreteUpperRetainedCompactTruncation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalTruncatedForwardCoreCellProperties
import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentModelMean
import OTSelector.Probability.NormalizedEnergyDefectBound

/-! Actual original-model means spend one old-type hierarchy energy budget. -/
open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace OTSelector.Reconstruction.PopulationLocalPressureCore
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)

/-- The literal model observable is fixed before the compact good/bad approximation. -/
def originalClockClassOldModelValue
    {Cell T : Type*} [Fintype Cell] {q n : ℕ}
    (coreIndex : Cell → Fin D.haar.continuous.count) {I : Set ℝ} {gap : ℝ}
    (Q : Cell → FiniteScalarBins I gap)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (classify : ∀ c, ℝ → Fin (Q c).count) (cell : Cell → Set (ℚ → M))
    (f : M × M →ᵇ ℝ) (tilt : ℝ)
    (sample : (Fin n → M × Option (Bool × T)) × (Fin n → M × Option (Bool × T))) : ℝ :=
  let model := fun c x y ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
    D.originalClockClassKinetic (coreIndex c) (Q c) (reference c) (classify c) x y +
    tilt * D.originalClockClassProbe (coreIndex c) (Q c) (reference c) (classify c) f x y
  ∑ c, (originalRetainedCellOptimizer a cell
    (originalSubplanPhysicalGraph (fun c ↦ D.originalClockClassAllowed (coreIndex c) (Q c) (classify c)))
    (fun c sample j k ↦ model c (sample.1 j).1 (sample.2 k).1) c sample).cost
      (fun j k ↦ model c (sample.1 j).1 (sample.2 k).1)

/-- A compact approximation is fixed before every truncation and every sample
size. Only its small discarded mass sees the fine cell count in the energy. -/
theorem exists_original_model_energy_expectation_bound
    {Cell T : Type*} [Fintype Cell] [Fintype T] [DecidableEq T] (coreIndex : Cell → Fin D.haar.continuous.count)
    (f : M × M →ᵇ ℝ)
    {A B : Set M} {I : Set ℝ} {globalGap ε : ℝ}
    (Q : Cell → FiniteScalarBins I globalGap)
    (U : Cell → Set (ℚ → M))
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (hsmall : 3 * ε + 2 * ε ^ 2 < 1)
    (houter : ∀ c j k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j k →
      ∀ s ∈ (Q c).cell j, ∀ t ∈ (Q c).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
          (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
          (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1)
    (hregion : ∀ c,
      ∀ z ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ z' ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
        (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1,
      ∀ t ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
        (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1,
      s < t → D.corePoint (coreIndex c) (z, s) ∈ A → D.corePoint (coreIndex c) (z', t) ∈ B →
        (s, t) ∈ (D.haar.continuous.coefficient (coreIndex c)).window.region)
    (hkin : ∀ c,
      ∀ z ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ z' ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ j k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j k →
      ∀ s ∈ (Q c).cell j, ∀ t ∈ (Q c).cell k,
      D.corePoint (coreIndex c) (z, s) ∈ A → D.corePoint (coreIndex c) (z', t) ∈ B →
      let C := D.haar.continuous.coefficient (coreIndex c)
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let vec := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
      |populationSeedPairDeficit S (s, t) (R z, R z') -
        C.clockClassKinetic (Q c) (reference c).val j k vec| ≤
          (3 * ε + 2 * ε ^ 2) * C.clockClassKinetic (Q c) (reference c).val j k vec)
    (classify : ∀ c, ℝ → Fin (Q c).count)
    (hclassify : ∀ c, Measurable (classify c))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (Cell × T))] [MeasurableSingletonClass (Option (Cell × T))]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType Cell T))]
    [MeasurableSingletonClass (Option (CellRefinedType Cell T))]
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (hπ : Vlasov.IsCoupling (χ + ξ) μ ν) {q : ℕ}
    (Cst : PopulationTypedCostData (χ + ξ) μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
    (hq : 4 < q)
    (hcal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂χ + ξ, u p.2 - u p.1 = dist p.1 p.2)
    {forwardGap : ℝ} (hgap : 0 < forwardGap)
    (hforward : ∀ t x y, Cst.sourceGood t x → Cst.targetGood t y → forwardGap ≤ u y - u x)
    (cell : Cell → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c)
    (hcover : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c)
    (hsource : ∀ᵐ x ∂χ.map Prod.fst, x ∈ A ∧ ∀ c, a x ∈ cell c →
      D.corePoint (coreIndex c) (a x,u x) = x ∧
      u x ∈ (Q c).cell (classify c (u x)) ∧
      ∃ k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) (classify c (u x)) k)
    (htarget : ∀ᵐ y ∂χ.map Prod.snd, y ∈ B ∧ ∀ c, a y ∈ cell c →
      D.corePoint (coreIndex c) (a y,u y) = y ∧
      u y ∈ (Q c).cell (classify c (u y)) ∧
      ∃ j, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j (classify c (u y))) :
    ∃ edgeBound : Cell → ℝ, (∀ c, 0 ≤ edgeBound c) ∧
    ∀ θ : ℝ, 0 < θ → ∃ depth : ℕ, 0 < depth ∧
    ∀ (G : Set (ℚ → M)) (hG : MeasurableSet G) (n : ℕ), 0 < n → ∀ tilt : ℝ,
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let RV := D.originalClockClassOldModelValue (q := q) (n := n)
      coreIndex Q reference classify cell f tilt (T := T)
    Integrable RV ((Cst.refineSubplan η hη).markedLaw n) ∧
    (∫ sample, RV sample ∂(Cst.refineSubplan η hη).markedLaw n) / n ≤
      (Cst.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) +
        Cst.quadraticConstant * dyadicMatchingConstant q * (Fintype.card (Cell × T) : ℝ) ^ (2 / (q : ℝ)) *
          θ ^ (1 - 2 / (q : ℝ)) +
        Cst.globalBound * (Real.sqrt (2 * Fintype.card T) + Real.sqrt (2 * Fintype.card (Cell × T))) *
          (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2)) / (1 - (3 * ε + 2 * ε ^ 2)) +
      |tilt| * ‖f‖ +
      (∑ c, (2 * ((Q c).count + 1 : ℝ) + 1) *
        ((n : ℝ) ^ (2 / (q : ℝ)) * edgeBound c + |tilt| * ‖f‖)) *
        ((Fintype.card T : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ depth + 1) ^ q) +
         (Fintype.card (Cell × T) : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q)) / n := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨edgeBound,hB,hfamily⟩ := D.original_dependent_model_family_bound_of_geometry
    coreIndex f Q U reference hsmall houter hregion hkin classify
  refine ⟨edgeBound,hB,?_⟩
  intro θ hθ
  have hsreg : ∀ᵐ p ∂χ + ξ, p.1 ∈ F.potentialRegularDomain u :=
    ae_of_ae_map measurable_fst.aemeasurable (hπ.1.symm ▸ hμreg)
  have htreg : ∀ᵐ p ∂χ + ξ, p.2 ∈ F.potentialRegularDomain u :=
    ae_of_ae_map measurable_snd.aemeasurable (hπ.2.symm ▸ hνreg)
  obtain ⟨K,depth,hd,hK,hsep,hall⟩ := Cst.exists_original_retained_compact_truncation_splits
    χ ξ rfl hF hcomplete hu ha horder (hsreg.and htreg) hcal cell hcell hdisj hcover hθ
  refine ⟨depth,hd,?_⟩
  intro G hG n hn tilt
  dsimp only
  let η := restrictOriginalRetainedResidual χ ξ a G
  let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
  let cost := fun x y ↦ (F.lengthEDist x y).toReal - u y + u x
  let coord := fun t (p : M × M) ↦ Cst.sourceCoordinate t p.1
  let good := Cst.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell K
  let bad := Cst.types.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell K
  obtain ⟨hsplit,hbad,hcarriers⟩ := hall G hG
  let R := Cst.types.rnCellRefinedTypes η hη good bad hsplit
  let law := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
  have hprob := R.marked_probabilities hπ
  letI : IsProbabilityMeasure (R.sourceMarkedLaw μ) := hprob.1
  letI : IsProbabilityMeasure (R.targetMarkedLaw ν) := hprob.2.1
  obtain ⟨KG,KB,hKG,hKB,hEI,henergy,hDI,hdefect,hcores⟩ :=
    Cst.exists_original_good_bad_expected_core_packet η hη good bad hsplit hq hn hd hπ
      a a ha ha cell hcell hdisj K (fun t c ↦ (hK t c).measurableSet) hcarriers
      (hsep depth le_rfl)
  have hfamilies := Cst.original_truncated_forward_cell_core_packet χ ξ hπ a ha u horder
    hμreg hνreg hcal hgap hforward cell hcell hdisj G hG hcover K
    (fun t c ↦ (hK t c).measurableSet) hsplit n KG KB depth hcores
  let Ps := fun x ↦ x ∈ A ∧ ∀ c, a x ∈ cell c →
    D.corePoint (coreIndex c) (a x,u x) = x ∧ u x ∈ (Q c).cell (classify c (u x)) ∧
      ∃ k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) (classify c (u x)) k
  let Pt := fun y ↦ y ∈ B ∧ ∀ c, a y ∈ cell c →
    D.corePoint (coreIndex c) (a y,u y) = y ∧ u y ∈ (Q c).cell (classify c (u y)) ∧
      ∃ j, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j (classify c (u y))
  have hproper := Cst.rnCellRefinedTypes_iid_some η hη good bad hsplit hπ (I := Fin n) (J := Fin n)
  have hret := Cst.original_truncated_fine_retained_endpoint_properties χ ξ a ha hG
    good bad hsplit Ps Pt hsource htarget (I := Fin n) (J := Fin n)
  let energy := fun (sample : (Fin n → M × Option (CellRefinedType Cell T)) ×
      (Fin n → M × Option (CellRefinedType Cell T))) ↦ fineGoodHierarchyEnergy Cst.sourceCoordinate Cst.targetCoordinate cost KG sample +
    fineBadHierarchyEnergy Cst.sourceCoordinate Cst.targetCoordinate cost KB sample
  let defect := fun (sample : (Fin n → M × Option (CellRefinedType Cell T)) ×
      (Fin n → M × Option (CellRefinedType Cell T))) ↦ fineGoodDiscrepancy Cst.sourceCoordinate Cst.targetCoordinate depth sample +
    fineBadDiscrepancy Cst.sourceCoordinate Cst.targetCoordinate sample
  let scale : ℝ := (n : ℝ) ^ (2 / (q : ℝ))
  let price : ℝ := ∑ c, (2 * ((Q c).count + 1 : ℝ) + 1) * (scale * edgeBound c + |tilt| * ‖f‖)
  have hprice : 0 ≤ price := Finset.sum_nonneg fun c _ ↦
    mul_nonneg (by positivity) (add_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hB c))
      (mul_nonneg (abs_nonneg _) (norm_nonneg _)))
  let fineValue := fun (sample : (Fin n → M × Option (CellRefinedType Cell T)) ×
      (Fin n → M × Option (CellRefinedType Cell T))) ↦ ∑ c, PartialMatching.legalMaximumValue
    (Finset.univ.filter (fun e : Fin n × Fin n ↦
      fineOriginalRetainedCellTag a cell (sample.1 e.1) = some c ∧
      fineOriginalRetainedCellTag a cell (sample.2 e.2) = some c ∧
      D.originalClockClassAllowed (coreIndex c) (Q c) (classify c) (sample.1 e.1).1 (sample.2 e.2).1))
    (fun j k ↦ scale * D.originalClockClassKinetic (coreIndex c) (Q c) (reference c) (classify c)
      (sample.1 j).1 (sample.2 k).1 +
      tilt * D.originalClockClassProbe (coreIndex c) (Q c) (reference c) (classify c) f
        (sample.1 j).1 (sample.2 k).1)
  have hpoint : ∀ᵐ sample ∂law, fineValue sample ≤
      scale * energy sample / (1 - (3 * ε + 2 * ε ^ 2)) + (n : ℝ) * (|tilt| * ‖f‖) + price * defect sample := by
    filter_upwards [hfamilies,hret,hproper] with sample hf hr hp
    obtain ⟨family,he,hcost,hdef⟩ := hf
    let activeS := fun c j ↦ fineOriginalRetainedCellTag a cell (sample.1 j) = some c
    let activeT := fun c k ↦ fineOriginalRetainedCellTag a cell (sample.2 k) = some c
    have hs c j (hj : activeS c j) := (fineOriginalRetainedCellTag_eq_some_iff_flag a cell hdisj _ c (hp.1 j)).mp hj
    have ht c k (hk : activeT c k) := (fineOriginalRetainedCellTag_eq_some_iff_flag a cell hdisj _ c (hp.2 k)).mp hk
    have hsource' c j (hj : activeS c j) :
        a (sample.1 j).1 ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c ∧
        u (sample.1 j).1 ∈ (Q c).cell (classify c (u (sample.1 j).1)) ∧
        (∃ k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c)
          (classify c (u (sample.1 j).1)) k) ∧
        D.corePoint (coreIndex c) (a (sample.1 j).1,u (sample.1 j).1) = (sample.1 j).1 ∧
        (sample.1 j).1 ∈ A := by
      obtain ⟨hA,hprops⟩ := hr.1 j (hs c j hj).1
      obtain ⟨hrestore,hbin,hactive⟩ := hprops c (hs c j hj).2
      exact ⟨hsub c (hs c j hj).2,hbin,hactive,hrestore,hA⟩
    have htarget' c k (hk : activeT c k) :
        a (sample.2 k).1 ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c ∧
        u (sample.2 k).1 ∈ (Q c).cell (classify c (u (sample.2 k).1)) ∧
        (∃ j, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c)
          j (classify c (u (sample.2 k).1))) ∧
        D.corePoint (coreIndex c) (a (sample.2 k).1,u (sample.2 k).1) = (sample.2 k).1 ∧
        (sample.2 k).1 ∈ B := by
      obtain ⟨hB,hprops⟩ := hr.2 k (ht c k hk).1
      obtain ⟨hrestore,hbin,hactive⟩ := hprops c (ht c k hk).2
      exact ⟨hsub c (ht c k hk).2,hbin,hactive,hrestore,hB⟩
    have he' c e (hem : e ∈ (family c).edges) : activeS c e.1 ∧ activeT c e.2 ∧
        u (sample.1 e.1).1 < u (sample.2 e.2).1 := by
      obtain ⟨hsf,htf,hsc,htc,hf⟩ := he c e hem
      exact ⟨(fineOriginalRetainedCellTag_eq_some_iff_flag a cell hdisj _ c (hp.1 e.1)).mpr ⟨hsf,hsc⟩,
        (fineOriginalRetainedCellTag_eq_some_iff_flag a cell hdisj _ c (hp.2 e.2)).mpr ⟨htf,htc⟩,hf⟩
    have hb := (hfamily n n (fun j ↦ (sample.1 j).1) (fun k ↦ (sample.2 k).1)
      activeS activeT hsource' htarget' family he' scale (Real.rpow_nonneg (Nat.cast_nonneg _) _) tilt).2
    have hc := sum_card_le_of_original_source_tags (fun j ↦ fineOriginalRetainedCellTag a cell (sample.1 j))
      family (fun c e he ↦ (he' c e he).1)
    have heScale : (∑ c, (family c).cost (fun j k ↦ scale * cost (sample.1 j).1 (sample.2 k).1)) ≤
        scale * energy sample := by
      rw [show (∑ c, (family c).cost (fun j k ↦ scale * cost (sample.1 j).1 (sample.2 k).1)) =
          scale * ∑ c, (family c).cost (fun j k ↦ cost (sample.1 j).1 (sample.2 k).1) by
        simp only [OTSelector.PartialMatching.cost, Finset.mul_sum]]
      exact mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hdef' : (∑ c, (((@Finset.filter (Fin n) (activeS c)
        (fun j ↦ Classical.propDecidable (activeS c j)) Finset.univ).card : ℝ) - ((family c).card : ℝ))) ≤ defect sample := by
      convert hdef using 1
      apply Finset.sum_congr rfl
      intro c _
      rw [OTSelector.partitionCount_eq_card_filter]
      congr 2
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, activeS]
    have hden : 0 ≤ 1 - (3 * ε + 2 * ε ^ 2) := (sub_pos.mpr hsmall).le
    have hfinal := hb.trans (add_le_add (add_le_add (div_le_div_of_nonneg_right heScale hden)
      (mul_le_mul_of_nonneg_right hc (mul_nonneg (abs_nonneg _) (norm_nonneg _))))
      (mul_le_mul_of_nonneg_left hdef' hprice))
    simpa only [fineValue, activeS, activeT, price] using hfinal
  have hmodel := D.original_dependent_clockClass_model_mean hF hcomplete hu ha hinj
    coreIndex reference Q cell hcell hdisj (fun c z hz ↦ (hsub c hz).1)
    classify hclassify f hπ Cst η hη good bad hsplit n tilt
  have hraw := integral_normalized_value_le_of_energy_defect law hn fineValue energy defect
    hmodel.2.1 hEI hDI hsmall hprice hpoint henergy hdefect
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
  have hqpos : (0 : ℝ) < q := by positivity
  have hexp : 0 ≤ 1 - 2 / (q : ℝ) := by linarith [(div_le_one hqpos).mpr hqR]
  have hmass : (∑ p : Cell × T, bad p.1 p.2 Set.univ).toReal ^ (1 - 2 / (q : ℝ)) ≤
      θ ^ (1 - 2 / (q : ℝ)) := Real.rpow_le_rpow ENNReal.toReal_nonneg hbad.le hexp
  have henergy' : Cst.quadraticConstant * dyadicMatchingConstant q *
      (Fintype.card (Cell × T) : ℝ) ^ (2 / (q : ℝ)) *
        (∑ p : Cell × T, bad p.1 p.2 Set.univ).toReal ^ (1 - 2 / (q : ℝ)) ≤
      Cst.quadraticConstant * dyadicMatchingConstant q *
      (Fintype.card (Cell × T) : ℝ) ^ (2 / (q : ℝ)) * θ ^ (1 - 2 / (q : ℝ)) :=
    mul_le_mul_of_nonneg_left hmass
      (mul_nonneg (mul_nonneg Cst.quadratic_nonneg (dyadicMatchingConstant_pos hq).le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  refine ⟨hmodel.1,?_⟩
  change (∫ sample, originalClockClassOldModelValue D (q := q) (n := n)
      coreIndex Q reference classify cell f tilt sample ∂(Cst.refineSubplan η hη).markedLaw n) / n ≤ _
  have heq : (∫ sample, fineValue sample ∂law) = ∫ sample,
      originalClockClassOldModelValue D (q := q) (n := n) coreIndex Q reference classify cell f tilt
        sample ∂(Cst.refineSubplan η hη).markedLaw n := hmodel.2.2
  rw [← heq]
  exact hraw.trans (add_le_add (add_le_add
    (div_le_div_of_nonneg_right (by linarith only [henergy']) (sub_pos.mpr hsmall).le) (le_refl _)) (le_refl _))

end OTSelector.Reconstruction.PopulationLocalPressureCore
