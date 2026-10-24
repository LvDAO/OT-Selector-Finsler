import OTSelector.Reconstruction.FinslerConcreteUpperOriginalScoreComparison
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalIntegrability
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalCardSum
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineCanonicalIntegral
import OTSelector.Reconstruction.FinslerRelativeLawOriginalClockClassMembership
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalEndpointAllowed

/-! One global original RN canonical family satisfies the physical-to-model expected upper bound. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The SAME per-cell class geometry bounds the original physical canonical
mean by its original model mean. All endpoint recovery, class membership,
measurability, integrability and the single N-row error budget are internal. -/
theorem PopulationLocalPressureCore.original_dependent_canonical_physical_model_expectation
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    {C T : Type*} [Fintype C] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    (hI : MeasurableSet I) {globalGap ρ probeError : ℝ} (hρ : 0 ≤ ρ) (hprobe : 0 ≤ probeError)
    (coreIndex : C → Fin D.haar.continuous.count)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (Q : C → FiniteScalarBins I globalGap) (U : C → Set (ℚ → M))
    (f : M × M →ᵇ ℝ) {A B : Set M}
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (hgeometry : ∀ c,
      ∀ z ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ z' ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ j k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j k →
      ∀ s ∈ (Q c).cell j, ∀ t ∈ (Q c).cell k,
      D.corePoint (coreIndex c) (z,s) ∈ A → D.corePoint (coreIndex c) (z',t) ∈ B →
      let C₀ := D.haar.continuous.coefficient (coreIndex c)
      let S := (P C₀.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      (s,t) ∈ C₀.window.region ∧
      |populationSeedPairDeficit S (s,t) (R z,R z') -
        C₀.clockClassKinetic (Q c) (reference c).val j k
          ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z))| ≤
        ρ * C₀.clockClassKinetic (Q c) (reference c).val j k
          ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z)) ∧
      |f (D.corePoint (coreIndex c) (z,s),D.corePoint (coreIndex c) (z',t)) -
        C₀.clockClassProbe (Q c) (reference c).val (reference c).property f j k| ≤ 2 * probeError)
    (cell : C → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c)
    (classify : ∀ c, ℝ → Fin (Q c).count)
    (hmclass : ∀ c, Measurable (classify c))
    (hclass : ∀ c j s, s ∈ (Q c).cell j → classify c s = j)
    {π : Measure (M × M)} [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π μ ν)
    {q : ℕ} (Cst : PopulationTypedCostData π μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
    (η : Measure (M × M)) (hη : η ≤ π) (n : ℕ) (tilt : ℝ) :
    let Refined := Cst.refineSubplan η hη
    let legal := fun c ↦ D.originalClockClassAllowed (coreIndex c) (Q c) (classify c)
    let model := fun c (sample : (Fin n → M × Option (Bool × T)) ×
        (Fin n → M × Option (Bool × T))) j k ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      D.originalClockClassKinetic (coreIndex c) (Q c) (reference c) (classify c)
        (sample.1 j).1 (sample.2 k).1 +
      tilt * D.originalClockClassProbe (coreIndex c) (Q c) (reference c) (classify c) f
        (sample.1 j).1 (sample.2 k).1
    let canonical := fun sample c ↦ originalRetainedCellOptimizer a cell
      (originalSubplanPhysicalGraph legal) model c sample
    let physical := fun sample ↦ ∑ c, (canonical sample c).cost (fun j k ↦
      (n : ℝ) ^ (2 / (q : ℝ)) * ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal -
        u (sample.2 k).1 + u (sample.1 j).1) + tilt * f ((sample.1 j).1,(sample.2 k).1))
    let frozen := fun sample ↦ ∑ c, (canonical sample c).cost (model c sample)
    Integrable physical (Refined.markedLaw n) ∧ Integrable frozen (Refined.markedLaw n) ∧
      (∫ sample, physical sample ∂Refined.markedLaw n) ≤
        (1+ρ) * (∫ sample, frozen sample ∂Refined.markedLaw n) +
          (n : ℝ) * (|tilt| * (2 * probeError) + ρ * (|tilt| * ‖f‖)) := by
  classical
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let Refined := Cst.refineSubplan η hη
  let law := Refined.markedLaw n
  letI : IsProbabilityMeasure law := (Refined.iid_facts hπ n).1
  let legal := fun c ↦ D.originalClockClassAllowed (coreIndex c) (Q c) (classify c)
  let model := fun c (sample : (Fin n → M × Option (Bool × T)) ×
      (Fin n → M × Option (Bool × T))) j k ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
    D.originalClockClassKinetic (coreIndex c) (Q c) (reference c) (classify c)
      (sample.1 j).1 (sample.2 k).1 +
    tilt * D.originalClockClassProbe (coreIndex c) (Q c) (reference c) (classify c) f
      (sample.1 j).1 (sample.2 k).1
  let canonical := fun sample c ↦ originalRetainedCellOptimizer a cell
    (originalSubplanPhysicalGraph legal) model c sample
  let edge := fun (sample : (Fin n → M × Option (Bool × T)) ×
      (Fin n → M × Option (Bool × T))) j k ↦
    (n : ℝ) ^ (2 / (q : ℝ)) * ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal -
      u (sample.2 k).1 + u (sample.1 j).1) + tilt * f ((sample.1 j).1,(sample.2 k).1)
  let physical := fun sample ↦ ∑ c, (canonical sample c).cost (edge sample)
  let frozen := fun sample ↦ ∑ c, (canonical sample c).cost (model c sample)
  let correction := |tilt| * (2 * probeError) + ρ * (|tilt| * ‖f‖)
  have hcorrection : 0 ≤ correction := by positivity
  have hm c := D.measurable_originalClockClass_model hF hcomplete hu ha hinj
    (coreIndex c) (Q c) (reference c) (classify c) (hmclass c) f
  have hmodel c j k : Measurable (fun sample ↦ model c sample j k) := by
    simpa only [model, Function.comp_def] using
      (((hm c).2.2.2 ((n : ℝ) ^ (2 / (q : ℝ))) tilt).comp (show Measurable (fun sample :
      (Fin n → M × Option (Bool × T)) × (Fin n → M × Option (Bool × T)) ↦
        ((sample.1 j).1,(sample.2 k).1)) by fun_prop))
  have hσ c := measurableSet_mem_originalRetainedCellOptimizer a ha cell hcell
    (originalSubplanPhysicalGraph legal)
    (fun c S ↦ measurableSet_originalSubplanPhysicalGraph_eq legal (fun c ↦ (hm c).1) c S)
    model hmodel c
  have hedge := Cst.original_marked_tilted_edge_integrable hπ η hη n
    (fun x y ↦ f (x,y)) f.continuous.measurable
    (Filter.Eventually.of_forall fun p ↦ by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm p) tilt
  have Iphysical c : Integrable (fun sample ↦ (canonical sample c).cost (edge sample)) law :=
    OTSelector.PartialMatching.integrable_sample_cost_of_edge_events law
      (fun sample ↦ canonical sample c) (hσ c) edge hedge
  have Ifrozen c : Integrable (fun sample ↦ (canonical sample c).cost (model c sample)) law := by
    obtain ⟨B,hB,hbound⟩ := D.exists_originalClockClass_physical_edge_bound
      (coreIndex c) (Q c) (reference c) (classify c) f
    apply integrable_matching_cost_of_used_edge_bound law (fun sample ↦ canonical sample c)
      (hσ c) (fun sample ↦ model c sample) (hmodel c)
      ((n : ℝ) ^ (2 / (q : ℝ)) * B + |tilt| * ‖f‖) (by positivity)
    apply Filter.Eventually.of_forall
    intro sample e he
    have hs := originalRetainedCellOptimizer_support a cell (originalSubplanPhysicalGraph legal)
      model c sample e he
    exact hbound _ _ (hsub c hs.2.2.2.1).1 (hsub c hs.2.2.2.2).1
      _ (Real.rpow_nonneg (Nat.cast_nonneg n) _) tilt
  have hum : Measurable u := hu.continuous.measurable
  have hrestore c := D.original_cell_corePoint_ae hF hcomplete hu ha hinj horder hb hμreg hνreg
    hμinv hνinv hlabel0 hlabel1 (coreIndex c) (hcell c) (fun _ hz ↦ (hsub c hz).1)
  have hrange c := D.original_clock_range_on_core_ae γ originalGap I hI hcomplete ha hum
    hlabel0 hlabel1 (coreIndex c)
  let Ps := fun x ↦ x ∈ A ∧ ∀ c, a x ∈ cell c →
    D.corePoint (coreIndex c) (a x,u x) = x ∧ u x ∈ (Q c).cell (classify c (u x))
  let Pt := fun y ↦ y ∈ B ∧ ∀ c, a y ∈ cell c →
    D.corePoint (coreIndex c) (a y,u y) = y ∧ u y ∈ (Q c).cell (classify c (u y))
  have hs : ∀ᵐ x ∂μ, Ps x := by
    filter_upwards [hμA, ae_all_iff.mpr (fun c ↦ (hrestore c).1),
      ae_all_iff.mpr (fun c ↦ (hrange c).1)] with x hA hrest hran
    exact ⟨hA, fun c hc ↦ ⟨hrest c hc, (Q c).mem_classified_cell
      (classify c) (hclass c) (hran c (hsub c hc).1)⟩⟩
  have ht : ∀ᵐ y ∂ν, Pt y := by
    filter_upwards [hνB, ae_all_iff.mpr (fun c ↦ (hrestore c).2),
      ae_all_iff.mpr (fun c ↦ (hrange c).2)] with y hB hrest hran
    exact ⟨hB, fun c hc ↦ ⟨hrest c hc, (Q c).mem_classified_cell
      (classify c) (hclass c) (hran c (hsub c hc).1)⟩⟩
  have hsArray : ∀ᵐ xs ∂Measure.pi (fun _ : Fin n ↦ μ), ∀ j, Ps (xs j) :=
    ae_all_iff.mpr fun j ↦ (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ μ) j).ae hs
  have htArray : ∀ᵐ ys ∂Measure.pi (fun _ : Fin n ↦ ν), ∀ k, Pt (ys k) :=
    ae_all_iff.mpr fun k ↦ (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ ν) k).ae ht
  have hraw : ∀ᵐ sample ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
      (Measure.pi (fun _ : Fin n ↦ ν)), (∀ j, Ps (sample.1 j)) ∧ ∀ k, Pt (sample.2 k) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsArray,
      Measure.quasiMeasurePreserving_snd.ae htArray] with sample hs ht
    exact ⟨hs,ht⟩
  have hobserved := Refined.types.iid_original_physical_property hπ _ hraw
  have hpoint : ∀ᵐ sample ∂law, physical sample ≤ (1+ρ) * frozen sample + (n : ℝ) * correction := by
    filter_upwards [hobserved] with sample hp
    have hc c : (canonical sample c).cost (edge sample) ≤
        (1+ρ) * (canonical sample c).cost (model c sample) +
          ((canonical sample c).card : ℝ) * correction := by
      calc
        _ ≤ ∑ e ∈ (canonical sample c).edges,
            ((1+ρ) * model c sample e.1 e.2 + correction) := by
          apply Finset.sum_le_sum
          intro e he
          have hsupport := originalRetainedCellOptimizer_support a cell
            (originalSubplanPhysicalGraph legal) model c sample e he
          have hxs := (hp.1 e.1).2 c hsupport.2.2.2.1
          have hys := (hp.2 e.2).2 c hsupport.2.2.2.2
          have hlegal : D.originalClockClassAllowed (coreIndex c) (Q c) (classify c)
              (sample.1 e.1).1 (sample.2 e.2).1 :=
            (Finset.mem_filter.mp hsupport.1).2
          exact D.originalClockClass_score_le_of_geometry (coreIndex c) (Q c) (reference c) (U c) f hρ
            (hgeometry c) (classify c) _ _ (hsub c hsupport.2.2.2.1) (hsub c hsupport.2.2.2.2)
            hxs.2 hys.2 hlegal hxs.1 hys.1 (hp.1 e.1).1 (hp.2 e.2).1
            (scale := (n : ℝ) ^ (2 / (q : ℝ)))
            (Real.rpow_nonneg (Nat.cast_nonneg n) _) tilt
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
            OTSelector.PartialMatching.cost, OTSelector.PartialMatching.card]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ hc c)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hsum
    have hcard : (∑ c, ((canonical sample c).card : ℝ)) ≤ (n : ℝ) := by
      exact_mod_cast sum_card_originalRetainedCellOptimizer_le a cell hdisj
        (originalSubplanPhysicalGraph legal) model sample
    exact hsum.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard hcorrection))
  have IphysicalSum := integrable_finsetSum Finset.univ (fun c _ ↦ Iphysical c)
  have IfrozenSum := integrable_finsetSum Finset.univ (fun c _ ↦ Ifrozen c)
  have Iright := (IfrozenSum.const_mul (1+ρ)).add (integrable_const ((n : ℝ) * correction))
  have hle := integral_mono_ae IphysicalSum Iright hpoint
  dsimp only
  refine ⟨IphysicalSum, IfrozenSum, ?_⟩
  simp only [Pi.add_apply] at hle
  rw [integral_add (IfrozenSum.const_mul (1+ρ)) (integrable_const ((n : ℝ) * correction)),
    integral_const_mul, integral_const] at hle
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hle

end OTSelector.Reconstruction
