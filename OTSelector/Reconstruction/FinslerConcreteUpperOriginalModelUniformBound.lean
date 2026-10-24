import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelEnergyExpectation
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelCountError

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

/-- The original atlas controls the frozen model mean independently of the
fine reference cells and class count, after its genuine count errors vanish. -/
theorem original_model_expectation_eventually_le
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
    ∀ (G : ℕ → Set (ℚ → M)) (hG : ∀ n, MeasurableSet (G n)) (tilt : ℝ),
    let value := fun n ↦ D.originalClockClassOldModelValue (q := q) (n := n)
      coreIndex Q reference classify cell f tilt (T := T)
    (∀ n, 0 < n → Integrable (value n)
      ((Cst.refineSubplan (restrictOriginalRetainedResidual χ ξ a (G n))
        (restrictOriginalRetainedResidual_le χ ξ a ha (hG n))).markedLaw n)) ∧
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ n in Filter.atTop,
      (∫ sample, value n sample ∂(Cst.refineSubplan (restrictOriginalRetainedResidual χ ξ a (G n))
        (restrictOriginalRetainedResidual_le χ ξ a ha (hG n))).markedLaw n) / n ≤
      Cst.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) /
        (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * ‖f‖ + tolerance := by
  classical
  obtain ⟨edgeBound,hB,hupper⟩ := D.exists_original_model_energy_expectation_bound
    coreIndex f Q U reference hsmall houter hregion hkin classify hclassify hF hcomplete hu ha hinj
    horder hμreg hνreg χ ξ hπ Cst hq hcal hgap hforward cell hcell hdisj hsub hcover hsource htarget
  intro G hG tilt
  dsimp only
  constructor
  · intro n hn
    obtain ⟨depth,hd,hbound⟩ := hupper 1 zero_lt_one
    exact (hbound (G n) (hG n) n hn tilt).1
  let value : ℕ → ℝ := fun n ↦
    (∫ sample, D.originalClockClassOldModelValue (q := q) (n := n)
      coreIndex Q reference classify cell f tilt (T := T) sample
      ∂(Cst.refineSubplan (restrictOriginalRetainedResidual χ ξ a (G n))
        (restrictOriginalRetainedResidual_le χ ξ a ha (hG n))).markedLaw n) / n
  let leading : ℝ := Cst.quadraticConstant * dyadicMatchingConstant q *
    (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) / (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * ‖f‖
  let discarded : ℝ := Cst.quadraticConstant * dyadicMatchingConstant q *
    (Fintype.card (Cell × T) : ℝ) ^ (2 / (q : ℝ)) / (1 - (3 * ε + 2 * ε ^ 2))
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have htwo : (2 : ℝ) < q := by exact_mod_cast (by omega : 2 < q)
  have hexponent : 0 < 1 - 2 / (q : ℝ) := sub_pos.mpr ((div_lt_one hqpos).mpr htwo)
  apply eventually_le_of_all_small_compact_errors value leading discarded hexponent
  intro θ hθ
  obtain ⟨depth,hd,hbound⟩ := hupper θ hθ
  let error : ℕ → ℝ := fun n ↦
    (Cst.globalBound * (Real.sqrt (2 * Fintype.card T) + Real.sqrt (2 * Fintype.card (Cell × T))) *
      (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2)) / (1 - (3 * ε + 2 * ε ^ 2)) +
    (∑ c, (2 * ((Q c).count + 1 : ℝ) + 1) *
      ((n : ℝ) ^ (2 / (q : ℝ)) * edgeBound c + |tilt| * ‖f‖)) *
      ((Fintype.card T : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ depth + 1) ^ q) +
        (Fintype.card (Cell × T) : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q)) / n
  have he := (tendsto_original_model_energy_count_zero hq
    (Cst.globalBound * (Real.sqrt (2 * Fintype.card T) + Real.sqrt (2 * Fintype.card (Cell × T))))).div_const
      (1 - (3 * ε + 2 * ε ^ 2))
  have hd := tendsto_original_model_good_bad_count_error_zero hq
    (fun c ↦ (2 * ((Q c).count + 1 : ℝ) + 1)) edgeBound ‖f‖ tilt
    (Fintype.card T) (Fintype.card (Cell × T)) depth
  have herr : Filter.Tendsto error Filter.atTop (𝓝 0) := by
    simpa only [zero_div, zero_add] using he.add hd
  refine ⟨error,herr,?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have h := (hbound (G n) (hG n) n hnpos tilt).2
  change value n ≤ _ at h
  exact h.trans_eq (by dsimp only [leading,discarded,error]; ring)

end OTSelector.Reconstruction.PopulationLocalPressureCore
