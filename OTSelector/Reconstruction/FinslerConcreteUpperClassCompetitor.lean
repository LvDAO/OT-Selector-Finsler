import OTSelector.Reconstruction.FinslerConcreteUpperClassGeometry
import OTSelector.Reconstruction.MarkedStationaryValueLegalRegularity
import OTSelector.Finite.MeasurableLegalOptimizer

/-!
Legal reference optima are actual partial competitors for the unchanged physical
cloud. Relative comparison uses the true legal matching cardinality, with no
complete-bipartite assumption and no uniform bound on the scaled kinetic cost.
-/
open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ}

/-- Every legal model optimizer obeys the actual relative physical cost
bound. In particular this applies to the measurable fixed tie selector. -/
theorem IsLegalOptimal.relative_physical_cost_le
    (allowed : Finset (Fin m × Fin n))
    (physical frozen probe modelProbe : Fin m → Fin n → ℝ)
    {ρ B G : ℝ} (hρ : 0 ≤ ρ)
    (hkin : ∀ i j, (i, j) ∈ allowed → |physical i j - frozen i j| ≤ ρ * frozen i j)
    (hprobe : ∀ i j, (i, j) ∈ allowed → |probe i j - modelProbe i j| ≤ B)
    (hmodel : ∀ i j, (i, j) ∈ allowed → |modelProbe i j| ≤ G) (tilt : ℝ)
    (σ : OTSelector.PartialMatching m n)
    (hopt : IsLegalOptimal allowed (fun i j ↦ frozen i j + tilt * modelProbe i j) σ) :
    σ.cost (fun i j ↦ physical i j + tilt * probe i j) ≤
      (1 + ρ) * legalMaximumValue allowed (fun i j ↦ frozen i j + tilt * modelProbe i j) +
      (legalMaximumCard allowed : ℝ) * (|tilt| * B + ρ * (|tilt| * G)) := by
  obtain ⟨hlegal, hcard, hcost⟩ := hopt
  have hedge (i j) (hij : (i, j) ∈ allowed) :
      physical i j + tilt * probe i j ≤
        (1 + ρ) * (frozen i j + tilt * modelProbe i j) +
          (|tilt| * B + ρ * (|tilt| * G)) := by
    have hk := (abs_le.mp (hkin i j hij)).2
    have hp : tilt * (probe i j - modelProbe i j) ≤ |tilt| * B := by
      calc tilt * (probe i j - modelProbe i j) ≤ |tilt * (probe i j - modelProbe i j)| := le_abs_self _
        _ = |tilt| * |probe i j - modelProbe i j| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hprobe i j hij) (abs_nonneg _)
    have hm : -tilt * modelProbe i j ≤ |tilt| * G := by
      calc -tilt * modelProbe i j ≤ |-tilt * modelProbe i j| := le_abs_self _
        _ = |tilt| * |modelProbe i j| := by rw [abs_mul, abs_neg]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmodel i j hij) (abs_nonneg _)
    have hscaled := mul_le_mul_of_nonneg_left hm hρ
    nlinarith only [hk, hp, hscaled]
  calc σ.cost (fun i j ↦ physical i j + tilt * probe i j)
      ≤ ∑ e ∈ σ.edges, ((1 + ρ) * (frozen e.1 e.2 + tilt * modelProbe e.1 e.2) +
          (|tilt| * B + ρ * (|tilt| * G))) :=
        Finset.sum_le_sum fun e he ↦ hedge e.1 e.2 (hlegal he)
    _ = (1 + ρ) * σ.cost (fun i j ↦ frozen i j + tilt * modelProbe i j) +
        (σ.card : ℝ) * (|tilt| * B + ρ * (|tilt| * G)) := by
      unfold OTSelector.PartialMatching.cost OTSelector.PartialMatching.card
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [hcard, hcost]

/-- The existing measurable first legal optimum is an actual relative
physical competitor; tie selection changes none of its cost control. -/
theorem firstLegalOptimalMatching_physical_cost_le
    (allowed : Finset (Fin m × Fin n))
    (physical frozen probe modelProbe : Fin m → Fin n → ℝ)
    {ρ B G : ℝ} (hρ : 0 ≤ ρ)
    (hkin : ∀ i j, (i, j) ∈ allowed → |physical i j - frozen i j| ≤ ρ * frozen i j)
    (hprobe : ∀ i j, (i, j) ∈ allowed → |probe i j - modelProbe i j| ≤ B)
    (hmodel : ∀ i j, (i, j) ∈ allowed → |modelProbe i j| ≤ G) (tilt : ℝ) :
    (firstLegalOptimalMatching allowed (fun i j ↦ frozen i j + tilt * modelProbe i j)).cost
      (fun i j ↦ physical i j + tilt * probe i j) ≤
      (1 + ρ) * legalMaximumValue allowed (fun i j ↦ frozen i j + tilt * modelProbe i j) +
      (legalMaximumCard allowed : ℝ) * (|tilt| * B + ρ * (|tilt| * G)) :=
  IsLegalOptimal.relative_physical_cost_le allowed physical frozen probe modelProbe
    hρ hkin hprobe hmodel tilt _ (firstLegalOptimalMatching_isLegalOptimal _ _)

/-- A legal model optimizer remains an actual physical partial matching and its
cost has the relative bound, with the actual legal maximum cardinality. -/
theorem exists_legal_model_optimizer_relative_competitor
    (allowed : Finset (Fin m × Fin n))
    (physical frozen probe modelProbe : Fin m → Fin n → ℝ)
    {ρ B G : ℝ} (hρ : 0 ≤ ρ)
    (hkin : ∀ i j, (i, j) ∈ allowed → |physical i j - frozen i j| ≤ ρ * frozen i j)
    (hprobe : ∀ i j, (i, j) ∈ allowed → |probe i j - modelProbe i j| ≤ B)
    (hmodel : ∀ i j, (i, j) ∈ allowed → |modelProbe i j| ≤ G) (tilt : ℝ) :
    ∃ σ : OTSelector.PartialMatching m n,
      IsLegal allowed σ ∧ σ.card = legalMaximumCard allowed ∧
      σ.cost (fun i j ↦ frozen i j + tilt * modelProbe i j) =
        legalMaximumValue allowed (fun i j ↦ frozen i j + tilt * modelProbe i j) ∧
      σ.cost (fun i j ↦ physical i j + tilt * probe i j) ≤
        (1 + ρ) * legalMaximumValue allowed (fun i j ↦ frozen i j + tilt * modelProbe i j) +
        (legalMaximumCard allowed : ℝ) * (|tilt| * B + ρ * (|tilt| * G)) := by
  obtain ⟨σ, hlegal, hcard, hcost⟩ := exists_cost_eq_legalMaximumValue allowed
    (fun i j ↦ frozen i j + tilt * modelProbe i j)
  refine ⟨σ, hlegal, hcard, hcost, ?_⟩
  have hedge (i j) (hij : (i, j) ∈ allowed) :
      physical i j + tilt * probe i j ≤
        (1 + ρ) * (frozen i j + tilt * modelProbe i j) +
          (|tilt| * B + ρ * (|tilt| * G)) := by
    have hk := (abs_le.mp (hkin i j hij)).2
    have hp : tilt * (probe i j - modelProbe i j) ≤ |tilt| * B := by
      calc tilt * (probe i j - modelProbe i j) ≤ |tilt * (probe i j - modelProbe i j)| := le_abs_self _
        _ = |tilt| * |probe i j - modelProbe i j| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hprobe i j hij) (abs_nonneg _)
    have hm : -tilt * modelProbe i j ≤ |tilt| * G := by
      calc -tilt * modelProbe i j ≤ |-tilt * modelProbe i j| := le_abs_self _
        _ = |tilt| * |modelProbe i j| := by rw [abs_mul, abs_neg]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmodel i j hij) (abs_nonneg _)
    have hscaled := mul_le_mul_of_nonneg_left hm hρ
    nlinarith only [hk, hp, hscaled]
  calc σ.cost (fun i j ↦ physical i j + tilt * probe i j)
      ≤ ∑ e ∈ σ.edges, ((1 + ρ) * (frozen e.1 e.2 + tilt * modelProbe e.1 e.2) +
          (|tilt| * B + ρ * (|tilt| * G))) :=
        Finset.sum_le_sum fun e he ↦ hedge e.1 e.2 (hlegal he)
    _ = (1 + ρ) * σ.cost (fun i j ↦ frozen i j + tilt * modelProbe i j) +
        (σ.card : ℝ) * (|tilt| * B + ρ * (|tilt| * G)) := by
      unfold OTSelector.PartialMatching.cost OTSelector.PartialMatching.card
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [hcard, hcost]

/-- The true physical legal minimum obeys the same relative bound. -/
theorem legalMaximumValue_le_relative_of_allowed
    (allowed : Finset (Fin m × Fin n))
    (physical frozen probe modelProbe : Fin m → Fin n → ℝ)
    {ρ B G : ℝ} (hρ : 0 ≤ ρ)
    (hkin : ∀ i j, (i, j) ∈ allowed → |physical i j - frozen i j| ≤ ρ * frozen i j)
    (hprobe : ∀ i j, (i, j) ∈ allowed → |probe i j - modelProbe i j| ≤ B)
    (hmodel : ∀ i j, (i, j) ∈ allowed → |modelProbe i j| ≤ G) (tilt : ℝ) :
    legalMaximumValue allowed (fun i j ↦ physical i j + tilt * probe i j) ≤
      (1 + ρ) * legalMaximumValue allowed (fun i j ↦ frozen i j + tilt * modelProbe i j) +
      (legalMaximumCard allowed : ℝ) * (|tilt| * B + ρ * (|tilt| * G)) := by
  obtain ⟨σ, hlegal, hcard, _, hb⟩ := exists_legal_model_optimizer_relative_competitor
    allowed physical frozen probe modelProbe hρ hkin hprobe hmodel tilt
  exact (legalMaximumValue_le _ hlegal hcard).trans hb

end OTSelector.Reconstruction.PartialMatching

namespace OTSelector.Reconstruction.PopulationLocalPressureCore
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Original geometric data produce literal finite legal optimizers whose
unchanged physical endpoint costs satisfy a quantitative bound. The bins and
self-neighborhoods precede every finite reference/Hall cover. -/
theorem exists_original_clockClass_partial_competitors (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) (f : M × M →ᵇ ℝ)
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hscreen : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    {I : Set ℝ} (hI : IsCompact I) {globalGap : ℝ} (hglobalGap : 0 < globalGap)
    {ε probeError : ℝ} (hε : 0 < ε) (hprobeError : 0 < probeError) :
    let C := D.haar.continuous.coefficient i
    ∃ (Q : C.roots → FiniteScalarBins I globalGap) (U : C.roots → Set (ℚ → M)),
      (∀ z₀, IsOpen (U z₀) ∧ z₀.val ∈ U z₀) ∧
      ∀ z₀, ∀ (m n : ℕ) (zs : Fin m → (ℚ → M)) (zt : Fin n → (ℚ → M))
      (cs : Fin m → Fin (Q z₀).count) (ct : Fin n → Fin (Q z₀).count)
      (ts : Fin m → ℝ) (tt : Fin n → ℝ),
      (∀ j, zs j ∈ C.roots ∩ U z₀) → (∀ k, zt k ∈ C.roots ∩ U z₀) →
      (∀ j, ts j ∈ (Q z₀).cell (cs j)) → (∀ k, tt k ∈ (Q z₀).cell (ct k)) →
      (∀ j, D.corePoint i (zs j, ts j) ∈ A) → (∀ k, D.corePoint i (zt k, tt k) ∈ B) →
      ∀ scale : ℝ, 0 ≤ scale → ∀ tilt : ℝ,
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let d := fun j k ↦ (Module.finBasis ℝ S.covector.ker).equivFun (R (zt k) - R (zs j))
      let allowed := Finset.univ.filter (fun e : Fin m × Fin n ↦
        C.clockClassAllowed (Q z₀) (cs e.1) (ct e.2))
      let frozen := fun j k ↦ scale * C.clockClassKinetic (Q z₀) z₀.val (cs j) (ct k) (d j k)
      let modelProbe := fun j k ↦ C.clockClassProbe (Q z₀) z₀.val z₀.property f (cs j) (ct k)
      ∃ σ : OTSelector.PartialMatching m n,
        PartialMatching.IsLegal allowed σ ∧ σ.card = PartialMatching.legalMaximumCard allowed ∧
        σ.cost (fun j k ↦ frozen j k + tilt * modelProbe j k) =
          PartialMatching.legalMaximumValue allowed (fun j k ↦ frozen j k + tilt * modelProbe j k) ∧
        σ.cost (fun j k ↦ scale * populationSeedPairDeficit S (ts j, tt k) (R (zs j), R (zt k)) +
          tilt * f (D.corePoint i (zs j, ts j), D.corePoint i (zt k, tt k))) ≤
          (1 + (3 * ε + 2 * ε ^ 2)) *
            PartialMatching.legalMaximumValue allowed (fun j k ↦ frozen j k + tilt * modelProbe j k) +
          (PartialMatching.legalMaximumCard allowed : ℝ) *
            (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)) := by
  classical
  obtain ⟨Q, U, hU, hgeometry⟩ := D.exists_full_original_clockClass_geometry hF hcomplete hu ha hinj
    i f f.continuous hgap hsep hscreen hI hglobalGap hε hprobeError
  refine ⟨Q, U, hU, ?_⟩
  intro z₀ m n zs zt cs ct ts tt hzs hzt hts htt hAs hBt scale hscale tilt
  let C := D.haar.continuous.coefficient i
  dsimp only
  apply PartialMatching.exists_legal_model_optimizer_relative_competitor
  · positivity
  · intro j k hjk
    have hallowed : C.clockClassAllowed (Q z₀) (cs j) (ct k) := (Finset.mem_filter.mp hjk).2
    have hcost := (hgeometry z₀ (zs j) (hzs j) (zt k) (hzt k) (cs j) (ct k) hallowed
      (ts j) (hts j) (tt k) (htt k) (hAs j) (hBt k)).2.1
    have h := mul_le_mul_of_nonneg_left hcost hscale
    simpa only [← mul_sub, abs_mul, abs_of_nonneg hscale, mul_assoc, mul_left_comm] using h
  · intro j k hjk
    exact (hgeometry z₀ (zs j) (hzs j) (zt k) (hzt k) (cs j) (ct k)
      (Finset.mem_filter.mp hjk).2 (ts j) (hts j) (tt k) (htt k) (hAs j) (hBt k)).2.2
  · intro j k _
    exact C.clockClassProbe_abs_le (Q z₀) z₀.val z₀.property f (cs j) (ct k)

end OTSelector.Reconstruction.PopulationLocalPressureCore
