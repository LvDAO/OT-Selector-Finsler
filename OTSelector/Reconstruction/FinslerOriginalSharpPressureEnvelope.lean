import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentWeightSharpUpper

/-! The true original full assignment inherits the limiting model upper while
all deterministic microscopic cutoff losses are sent to zero. -/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The literal original iid full assignment keeps only the base residual
energy after microscopic cutoff losses are removed. Its geometry error is
unchanged, and every actual cutoff/model experiment remains the one used by
the original sharp expected comparison. -/
theorem PopulationLocalPressureCore.original_sharp_assignment_upper_of_model_pressure
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    {Cells T : Type*} [Fintype Cells] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    {I : Set ℝ} {gap : ℝ} (coreIndex : Cells → Fin D.haar.continuous.count)
    (Q : Cells → FiniteScalarBins I gap)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (classify : ∀ c, ℝ → Fin (Q c).count) (cell : Cells → Set (ℚ → M))
    (hcell : ∀ c, MeasurableSet (cell c)) (f : M × M →ᵇ ℝ) (ε probeError : ℝ)
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ] {q : ℕ}
    (Cst : PopulationTypedCostData (χ + ξ) μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x)) (ha : Measurable a)
    (hq : 4 < q)
    (hsharp : D.originalWeightSharpExpectedBound coreIndex Q reference classify cell hcell f ε probeError χ ξ Cst ha)
    (p : ℝ → ℝ)
    (hmodel : ∀ (tilt budget tolerance : ℝ), 0 < budget → 0 < tolerance →
      ∃ (cutoff : ℕ → Cells → Set (ℚ → M))
        (hcutoff : ∀ n c, MeasurableSet (cutoff n c)),
      (∀ n, (∑ c, (μ.map a).real (cell c \ cutoff n c)) ≤ budget) ∧
      let G := fun n ↦ ⋃ c, cell c ∩ cutoff n c
      let hG := fun n ↦ MeasurableSet.iUnion fun c ↦ (hcell c).inter (hcutoff n c)
      let law := fun n ↦ (Cst.refineSubplan (restrictOriginalRetainedResidual χ ξ a (G n))
        (restrictOriginalRetainedResidual_le χ ξ a ha (hG n))).markedLaw n
      let model := fun n ↦ D.originalClockClassOldModelValue (q := q) (n := n)
        coreIndex Q reference classify cell f tilt (T := T)
      ∀ᶠ n in atTop, (∫ sample, model n sample ∂law n) / n ≤ p tilt + tolerance) :
    ∀ tilt : ℝ,
      let iid := fun n ↦ (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
      let assignment := fun n (sample : (Fin n → M) × (Fin n → M)) ↦ perturbedAssignmentValue
        (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
          ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
          tilt * f (sample.1 i,sample.2 j)) 0 0
      let A := Cst.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ))
      let geometry := (3 * ε + 2 * ε ^ 2) * (A / (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * ‖f‖ + 1) +
        (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖))
      (∀ n, 0 < n → Integrable (assignment n) (iid n)) ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop,
        (∫ sample, assignment n sample ∂iid n) / n ≤
          p tilt + geometry +
            (A * (ξ univ).toReal ^ (1 - 2 / (q : ℝ)) + 2 * |tilt| * ‖f‖ * (ξ univ).toReal) + ζ := by
  classical
  intro tilt
  let A := Cst.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ))
  let exponent := 1 - 2 / (q : ℝ)
  let base := (ξ univ).toReal
  let B := 2 * |tilt| * ‖f‖
  let repair := fun β : ℝ ↦ A * β ^ exponent + B * β
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg Cst.quadratic_nonneg (dyadicMatchingConstant_pos hq).le)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hexponent : 0 ≤ exponent := by
    dsimp only [exponent]
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    exact sub_nonneg.mpr ((div_le_one hqpos).mpr hqR)
  have hrepair : ContinuousAt repair base :=
    ((Real.continuousAt_rpow_const base exponent (Or.inr hexponent)).const_mul A).add
      (continuousAt_id.const_mul B)
  obtain ⟨cutoff,hcutoff,_,_⟩ := hmodel tilt 1 1 (by norm_num) (by norm_num)
  refine ⟨fun n hn ↦ ((hsharp cutoff hcutoff tilt).1 n hn).1,?_⟩
  intro ζ hζ
  have hthird : (0 : ℝ) < ζ / 3 := by positivity
  obtain ⟨d,hd,hnear⟩ := Metric.continuousAt_iff.mp hrepair (ζ / 3) hthird
  let budget := d / 2
  have hbudget : 0 < budget := half_pos hd
  have hdist : dist (base + budget) base < d := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hbudget]
    dsimp only [budget]
    linarith
  have hsmall : repair (base + budget) ≤ repair base + ζ / 3 := by
    have hh := hnear hdist
    rw [Real.dist_eq] at hh
    have := le_abs_self (repair (base + budget) - repair base)
    linarith
  obtain ⟨cutoff,hcutoff,hloss,hmodelUpper⟩ := hmodel tilt budget (ζ / 3) hbudget hthird
  have hfull := (hsharp cutoff hcutoff tilt).2 (ζ / 3) hthird
  filter_upwards [hmodelUpper,hfull] with n hmodelN hfullN
  let β := (ξ univ).toReal + ∑ c, (μ.map a).real (cell c \ cutoff n c)
  have hβ : 0 ≤ β := add_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg (fun _ _ ↦ measureReal_nonneg))
  have hβle : β ≤ base + budget := add_le_add (le_refl _) (hloss n)
  have hrepairLe : repair β ≤ repair base + ζ / 3 := by
    apply le_trans _ hsmall
    exact add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hβ hβle hexponent) hA)
      (mul_le_mul_of_nonneg_left hβle hB)
  dsimp only [repair,base,A,exponent,B,β] at hrepairLe
  linarith only [hmodelN,hfullN,hrepairLe]

end OTSelector.Reconstruction
