import OTSelector.Reconstruction.OriginalIIDFullSeedLocalLaplace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Order.LiminfLimsup

open Set Function Filter MeasureTheory ProbabilityTheory Metric Module Manifold OTSelector.Geometry
open scoped Topology ENNReal NNReal ContDiff BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The actual first moment of a finite iid sum is its sample size times the
original single-point integral. -/
theorem integral_iid_sum_eq_mul {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] {f : Ω → ℝ}
    (hf : Integrable f η) (N : ℕ) :
    (∫ sample : Fin N → Ω, ∑ i : Fin N, f (sample i)
      ∂Measure.pi (fun _ : Fin N ↦ η)) = (N : ℝ) * ∫ x, f x ∂η := by
  rw [integral_finsetSum _ (fun i _ ↦ integrable_comp_eval (i := i) hf)]
  simp_rw [integral_comp_eval (μ := fun _ : Fin N ↦ η) hf.aestronglyMeasurable]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The actual integer number of original observations in a measurable set has
expectation N times that set's original probability. -/
theorem integral_iid_card_filter_eq {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] {A : Set Ω}
    (hA : MeasurableSet A) (N : ℕ) :
    (∫ sample : Fin N → Ω,
      ((Finset.univ.filter (fun i : Fin N ↦ sample i ∈ A)).card : ℝ)
      ∂Measure.pi (fun _ : Fin N ↦ η)) = (N : ℝ) * η.real A := by
  have heq (sample : Fin N → Ω) :
      ((Finset.univ.filter (fun i : Fin N ↦ sample i ∈ A)).card : ℝ) =
        ∑ i : Fin N, A.indicator (fun _ ↦ (1 : ℝ)) (sample i) := by
    simp only [Finset.natCast_card_filter, Set.indicator]
  simp_rw [heq]
  rw [integral_iid_sum_eq_mul η ((integrable_const (1 : ℝ)).indicator hA),
    integral_indicator hA, integral_const]
  simp

/-- The ENNReal expectation of the unchanged iid endpoint count, with its
literal finite sum of unit indicators. -/
theorem lintegral_iid_indicatorCount_eq {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] {A : Set Ω}
    (hA : MeasurableSet A) (N : ℕ) :
    (∫⁻ sample : Fin N → Ω, ∑ i : Fin N,
      A.indicator (fun _ ↦ (1 : ℝ≥0∞)) (sample i)
      ∂Measure.pi (fun _ : Fin N ↦ η)) = (N : ℝ≥0∞) * η A := by
  rw [lintegral_finsetSum (f := fun (i : Fin N) (sample : Fin N → Ω) ↦
      A.indicator (fun _ ↦ (1 : ℝ≥0∞)) (sample i)) _ (fun i _ ↦
    ((measurable_const.indicator hA).comp (measurable_pi_apply i)))]
  have hcoord (i : Fin N) :
      (∫⁻ sample : Fin N → Ω, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) (sample i)
        ∂Measure.pi (fun _ : Fin N ↦ η)) = η A := by
    rw [← lintegral_map (measurable_const.indicator hA) (measurable_pi_apply i),
      (measurePreserving_eval (fun _ : Fin N ↦ η) i).map_eq]
    simpa using (lintegral_indicator_fun_one (μ := η) hA)
  simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Testing the Laplace defect with the indicator of one yields a fixed
nonzero scalar times the original set mass. -/
theorem integral_laplaceDefect_indicator_one_eq
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) {A : Set Ω}
    (hA : MeasurableSet A) :
    (∫ x, 1 - Real.exp (-A.indicator (fun _ ↦ (1 : ℝ)) x) ∂η) =
      (1 - Real.exp (-1)) * η.real A := by
  rw [OTSelector.Probability.integral_laplaceDefect_indicator_eq_restrict η hA,
    integral_const]
  simp [smul_eq_mul, mul_comm]

/-- Counting all marks in one spatial window integrates against its exact
original probability clock to the spatial volume alone. -/
theorem integral_spatial_indicator_laplaceDefect_eq {q : ℕ}
    (α : Measure ℝ) [IsProbabilityMeasure α] {W : Set (Fin q → ℝ)}
    (hW : MeasurableSet W) :
    (∫ p : (Fin q → ℝ) × ℝ,
      1 - Real.exp (-(W ×ˢ (univ : Set ℝ)).indicator (fun _ ↦ (1 : ℝ)) p)
      ∂(volume : Measure (Fin q → ℝ)).prod α) =
        (1 - Real.exp (-1)) * (volume : Measure (Fin q → ℝ)).real W := by
  rw [integral_laplaceDefect_indicator_one_eq _ (hW.prod MeasurableSet.univ)]
  congr 1
  simp only [measureReal_def, Measure.prod_prod, measure_univ, mul_one]


section ActualCore
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- Full-seed local spatial masses have their actual first-order intensity limit
at one common full-measure coordinate root set, for every positive radius and
both original colors. No mass-density or convergence callback is assumed. -/
theorem PopulationLocalPressureCore.original_ae_full_seed_spatial_mass_tendsto
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    (hnormalization : ∀ n,
      s n ^ finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker =
        ((n + 1 : ℕ) : ℝ)) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let full := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
    ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ B : ℝ, 0 < B → ∀ color : Fin 2,
        let η := if color = 0 then η₀ else η₁
        let θ := originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c)
        Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ) *
          η.real (full ∩ {x | s n • (e (R (a x)) - c) ∈ closedBall 0 B})) atTop
          (𝓝 (θ * (volume : Measure (Fin q → ℝ)).real (closedBall 0 B))) := by
  dsimp only
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let q := finrank ℝ S.covector.ker
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let full := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have hpos : Measurable (fun x ↦ e (R (a x))) := e.continuous.measurable.comp (hR.comp ha)
  filter_upwards [D.original_ae_full_seed_scaled_laplace_tendsto hF hcomplete hu ha hinj i
    s hs hlarge] with c hc
  intro B hB color
  let H : (Fin q → ℝ) × ℝ → ℝ :=
    (closedBall 0 B ×ˢ (univ : Set ℝ)).indicator (fun _ ↦ 1)
  have hH : Measurable H := measurable_const.indicator
    (isClosed_closedBall.measurableSet.prod MeasurableSet.univ)
  have hH0 : ∀ p, 0 ≤ H p := Set.indicator_nonneg (fun _ _ ↦ by norm_num)
  have hsupport : ∀ p, p.1 ∉ closedBall 0 B → H p = 0 := by
    intro p hp
    exact Set.indicator_of_notMem (fun h ↦ hp h.1) (fun _ ↦ (1 : ℝ))
  let η : Measure M := if color = 0 then η₀ else η₁
  have : IsFiniteMeasure η := by dsimp only [η]; split_ifs <;> infer_instance
  let α := populationTwoColorClockKernel u a η₀ η₁ color
    (a (S.curve (e.symm c) 0))
  have : IsProbabilityMeasure α := inferInstance
  let d := 1 - Real.exp (-1)
  have hd : d ≠ 0 := ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
  have hdef n :
      (∫ x in full, 1 - Real.exp (-H (s n • (e (R (a x)) - c), u x)) ∂η) =
        d * η.real (full ∩ {x | s n • (e (R (a x)) - c) ∈ closedBall 0 B}) := by
    have hA : MeasurableSet {x | s n • (e (R (a x)) - c) ∈ closedBall 0 B} :=
      isClosed_closedBall.measurableSet.preimage ((hpos.sub_const c).const_smul (s n))
    have heq : (fun x ↦ H (s n • (e (R (a x)) - c), u x)) =
        {x | s n • (e (R (a x)) - c) ∈ closedBall 0 B}.indicator (fun _ ↦ (1 : ℝ)) := by
      funext x
      simp only [H, Set.indicator, mem_prod, mem_univ, and_true, mem_ofPred_eq]
    simp_rw [show ∀ x, H (s n • (e (R (a x)) - c), u x) =
        {x | s n • (e (R (a x)) - c) ∈ closedBall 0 B}.indicator (fun _ ↦ (1 : ℝ)) x
      from fun x ↦ congrFun heq x]
    rw [integral_laplaceDefect_indicator_one_eq _ hA, measureReal_restrict_apply hA,
      inter_comm]
  have hclock : (∫ p, 1 - Real.exp (-H p)
      ∂(volume : Measure (Fin q → ℝ)).prod α) =
      d * (volume : Measure (Fin q → ℝ)).real (closedBall 0 B) :=
    integral_spatial_indicator_laplaceDefect_eq α isClosed_closedBall.measurableSet
  have ht := hc H hH hH0 ⟨B, hB, hsupport⟩ color
  change Tendsto (fun n ↦ s n ^ q *
      (∫ x in full, 1 - Real.exp (-H (s n • (e (R (a x)) - c), u x)) ∂η)) _
      (𝓝 (_ * ∫ p, 1 - Real.exp (-H p)
        ∂(volume : Measure (Fin q → ℝ)).prod α)) at ht
  simp_rw [hdef] at ht
  rw [hclock] at ht
  have hnorm n : s n ^ q = ((n + 1 : ℕ) : ℝ) := hnormalization n
  simp_rw [hnorm] at ht
  convert ht.div_const d using 1
  · funext n
    field_simp [hd]
    rfl
  · field_simp [hd]

end ActualCore
end OTSelector.Reconstruction
