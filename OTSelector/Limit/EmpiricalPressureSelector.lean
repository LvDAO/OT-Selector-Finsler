import OTSelector.Transport.Coupling.EmpiricalFace
import OTSelector.Finite.EmpiricalSlack
import OTSelector.MeasureTheory.DerivativeDeterminedFaceLimit
import OTSelector.Probability.EmpiricalWeak
import OTSelector.Probability.RowScaling
import OTSelector.Transport.Coupling.OptimalityFromCalibrationSlack

/-!
Conditions: Two actual finite point lists and the indicated cost/coupling conventions.

Objects: The set of probability couplings optimal for their empirical laws.

Proof detail: Unpack the empirical laws and define the whole optimal coupling face using the actual cost optimum.

Sources: Gabriel Peyré, Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf).
Relation: Only the empiricalOptimalFace definition is extracted. Pressure and asymptotic selector assertions from the same file are excluded.
-/

/-!
# Actual empirical distance selectors from probe pressures

The face consists of every optimal coupling of the original empirical probability marginals,
including samples with repeated points. The pressure is the attained finite assignment value
for scaled distance slack plus an actual paired bounded continuous probe, divided by sample size.
Finite optimality supplies nonemptiness and every affine comparison used in reconstruction.
The compact space may be the union of supports with the restricted ambient distance; neither
compactness of the ambient manifold nor intrinsic path distance on that union is required.

Differentiability and the stated stochastic or filter pressure limits remain analytic premises.
This interface does not prove the geometric pressure theorem for a Finsler model.
-/

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction ENNReal

namespace OTSelector.Pressure

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]



/-- The actual attained assignment pressure, normalized as a probability readout. -/
noncomputable def empiricalDistancePressure {n : ℕ} (X Y : Fin n → M)
    (φ : M → ℝ) (k : ℝ) (f : (M × M) →ᵇ ℝ) (t : ℝ) : ℝ :=
  perturbedAssignmentValue (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
    (fun i j ↦ f (X i, Y j)) t / (n : ℝ)

/-- Finite assignment existence gives a member of the entire empirical optimal face. -/
theorem empiricalOptimalFace_nonempty {n : ℕ} [NeZero n] (X Y : Fin n → M) :
    (empiricalOptimalFace X Y).Nonempty := by
  obtain ⟨P, hP⟩ := exists_optimalFractionalAssignment (fun i j ↦ dist (X i) (Y j))
  refine ⟨fractionalEmpiricalCoupling X Y P hP.1, ?_⟩
  have hdist : (edist : M → M → ℝ≥0∞) = fun x y ↦ ENNReal.ofReal (dist x y) :=
    funext fun x ↦ funext fun y ↦ edist_dist x y
  change IsOptimalCoupling edist _ _ _
  rw [hdist]
  exact (optimalFractionalAssignment_iff_isOptimalCoupling X Y P hP.1 dist
    (fun _ _ ↦ dist_nonneg)).mp hP

/-- Every original empirical optimum supplies the pressure comparison for every paired probe. -/
theorem empiricalDistancePressure_le_of_mem {n : ℕ} [NeZero n]
    (X Y : Fin n → M) (φ : M → ℝ) (k : ℝ) (hk : 0 < k)
    (f : (M × M) →ᵇ ℝ) (t : ℝ) (γ : ProbabilityMeasure (M × M))
    (hγ : γ ∈ empiricalOptimalFace X Y) :
    empiricalDistancePressure X Y φ k f t ≤ empiricalDistancePressure X Y φ k f 0 +
      t * ∫ z, f z ∂(γ : Measure (M × M)) :=
  perturbedDistanceSlackValue_div_le_of_empirical_optimal X Y φ f k hk t γ hγ

variable [CompactSpace M]

/-- Probe-pressure limits construct a unique measure and control all actual empirical optima.
The source filter is arbitrary and nontrivial; positive sample sizes are expressed by `NeZero`. -/
theorem existsUnique_empirical_selector_of_pressure
    {ι : Type*} {l : Filter ι} [NeBot l]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (X Y : ∀ i, Fin (n i) → M)
    (φ : M → ℝ) (k : ι → ℝ) (hk : ∀ i, 0 < k i)
    (pressure : ((M × M) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((M × M) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0)
    (hzero : ∀ f, Tendsto (fun i ↦ empiricalDistancePressure (X i) (Y i) φ (k i) f 0)
      l (𝓝 (pressure f 0)))
    (hlower : ∀ f t, |t| < radius f → Tendsto
      (fun i ↦ max (pressure f t - empiricalDistancePressure (X i) (Y i) φ (k i) f t) 0)
      l (𝓝 0)) :
    ∃! π : ProbabilityMeasure (M × M),
      (∀ f : (M × M) →ᵇ ℝ, ∫ z, f z ∂(π : Measure (M × M)) = derivative f) ∧
        Tendsto (fun i ↦ empiricalOptimalFace (X i) (Y i)) l (𝓝 π).smallSets := by
  apply existsUnique_probabilityMeasure_of_pressure
    (fun i ↦ empiricalOptimalFace (X i) (Y i))
    (fun f i t ↦ empiricalDistancePressure (X i) (Y i) φ (k i) f t)
    pressure radius derivative
    (Eventually.of_forall fun i ↦ empiricalOptimalFace_nonempty (X i) (Y i))
    hradius hderiv hzero hlower
  intro f t _
  exact Eventually.of_forall fun i γ hγ ↦
    empiricalDistancePressure_le_of_mem (X i) (Y i) φ (k i) (hk i) f t γ hγ

/-- Whole-face convergence, marginal convergence, and a finite central pressure recover an
actual population distance optimum. Vanishing calibration slack is derived by dividing the
central pressure by its diverging scale. -/
theorem isOptimalCoupling_of_empirical_pressure_limit
    {ι : Type*} {l : Filter ι} [NeBot l]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (X Y : ∀ i, Fin (n i) → M)
    (φ : M → ℝ) (hφ : LipschitzWith 1 φ) (k : ι → ℝ) (hk : ∀ i, 0 < k i)
    (hscale : Tendsto k l atTop) (f : (M × M) →ᵇ ℝ) {p : ℝ}
    (hzero : Tendsto (fun i ↦ empiricalDistancePressure (X i) (Y i) φ (k i) f 0)
      l (𝓝 p))
    (π : ProbabilityMeasure (M × M)) (μ ν : ProbabilityMeasure M)
    (hface : Tendsto (fun i ↦ empiricalOptimalFace (X i) (Y i)) l (𝓝 π).smallSets)
    (hsource : Tendsto (fun i ↦ empiricalProbabilityMeasure (X i)) l (𝓝 μ))
    (htarget : Tendsto (fun i ↦ empiricalProbabilityMeasure (Y i)) l (𝓝 ν)) :
    IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  classical
  choose plans hplans using fun i ↦ empiricalOptimalFace_nonempty (X i) (Y i)
  have hlimit : Tendsto plans l (𝓝 π) :=
    hface.of_smallSets (Eventually.of_forall hplans)
  have hslack := tendsto_integral_distanceSlack_of_pressure n X Y φ f k hk
    (fun i ↦ (plans i : Measure (M × M))) hplans hzero hscale
  let cost : (M × M) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun z ↦ dist z.1 z.2, continuous_fst.dist continuous_snd⟩
  let potential : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨φ, hφ.continuous⟩
  have hdual (x y : M) : (-potential) x + potential y ≤ cost (x, y) := by
    change -φ x + φ y ≤ dist x y
    have h := hφ.le_add_mul y x
    simp only [NNReal.coe_one, one_mul, dist_comm] at h
    linarith
  have hslack' : Tendsto
      (fun i ↦ ∫ z, (cost z - (-potential) z.1 - potential z.2)
        ∂(plans i : Measure (M × M))) l (𝓝 0) := by
    convert hslack using 1
    funext i
    congr 1
    funext z
    change dist z.1 z.2 - -φ z.1 - φ z.2 = dist z.1 z.2 - φ z.2 + φ z.1
    ring
  have hpop := Reconstruction.population_optimality_of_weak_limits cost (-potential) potential
    (fun _ ↦ dist_nonneg) hdual plans (fun i ↦ empiricalProbabilityMeasure (X i))
    (fun i ↦ empiricalProbabilityMeasure (Y i)) π μ ν hlimit hsource htarget
    (Eventually.of_forall fun i ↦ (hplans i).1) hslack'
  have hdist : (edist : M → M → ℝ≥0∞) = fun x y ↦ ENNReal.ofReal (dist x y) :=
    funext fun x ↦ funext fun y ↦ edist_dist x y
  rw [hdist]
  exact hpop.2

/-- The actual empirical pressure selects a unique deterministic probability plan. Every
empirical distance optimizer converges to it, and converging empirical marginals make it a
population distance optimizer. The geometric pressure limits are the explicit remaining input. -/
theorem existsUnique_empirical_optimal_selector_of_pressure
    {ι : Type*} {l : Filter ι} [NeBot l]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (X Y : ∀ i, Fin (n i) → M)
    (φ : M → ℝ) (hφ : LipschitzWith 1 φ) (k : ι → ℝ) (hk : ∀ i, 0 < k i)
    (hscale : Tendsto k l atTop)
    (pressure : ((M × M) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((M × M) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0)
    (hzero : ∀ f, Tendsto (fun i ↦ empiricalDistancePressure (X i) (Y i) φ (k i) f 0)
      l (𝓝 (pressure f 0)))
    (hlower : ∀ f t, |t| < radius f → Tendsto
      (fun i ↦ max (pressure f t - empiricalDistancePressure (X i) (Y i) φ (k i) f t) 0)
      l (𝓝 0))
    (μ ν : ProbabilityMeasure M)
    (hsource : Tendsto (fun i ↦ empiricalProbabilityMeasure (X i)) l (𝓝 μ))
    (htarget : Tendsto (fun i ↦ empiricalProbabilityMeasure (Y i)) l (𝓝 ν)) :
    ∃! π : ProbabilityMeasure (M × M),
      (∀ f : (M × M) →ᵇ ℝ, ∫ z, f z ∂(π : Measure (M × M)) = derivative f) ∧
        Tendsto (fun i ↦ empiricalOptimalFace (X i) (Y i)) l (𝓝 π).smallSets ∧
        IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  obtain ⟨π, hπ, huniq⟩ := existsUnique_empirical_selector_of_pressure n X Y φ k hk
    pressure radius derivative hradius hderiv hzero hlower
  refine ⟨π, ⟨hπ.1, hπ.2, ?_⟩, fun γ hγ ↦ huniq γ ⟨hγ.1, hγ.2.1⟩⟩
  exact isOptimalCoupling_of_empirical_pressure_limit n X Y φ hφ k hk hscale 0 (hzero 0)
    π μ ν hπ.2 hsource htarget

/-- Under the original row probability laws, the same actual empirical construction gives one
population optimizer and vanishing outer failure probabilities for the entire empirical face.
No measurable optimizer choice, cross-row coupling, or distinct-sample premise is required. -/
theorem existsUnique_empirical_optimal_selector_row_of_pressure
    {Ω : ℕ → Type*} [∀ r, MeasurableSpace (Ω r)]
    (P : ∀ r, Measure (Ω r)) [∀ r, IsProbabilityMeasure (P r)]
    (sampleSize : ℕ → ℕ) [∀ r, NeZero (sampleSize r)]
    (X Y : ∀ z : Σ r, Ω r, Fin (sampleSize z.1) → M)
    (φ : M → ℝ) (hφ : LipschitzWith 1 φ)
    (k : (Σ r, Ω r) → ℝ) (hk : ∀ z, 0 < k z)
    (hscale : ∀ R : ℝ, Tendsto (fun r ↦ (P r).real {ω | k ⟨r, ω⟩ < R}) atTop (𝓝 0))
    (pressure : ((M × M) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((M × M) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0)
    (hzero : ∀ f ε, 0 < ε → Tendsto
      (fun r ↦ (P r).real {ω | ε ≤
        |empiricalDistancePressure (X ⟨r, ω⟩) (Y ⟨r, ω⟩) φ (k ⟨r, ω⟩) f 0 - pressure f 0|})
      atTop (𝓝 0))
    (hlower : ∀ f t, |t| < radius f → ∀ ε, 0 < ε → Tendsto
      (fun r ↦ (P r).real {ω | ε ≤ max (pressure f t -
        empiricalDistancePressure (X ⟨r, ω⟩) (Y ⟨r, ω⟩) φ (k ⟨r, ω⟩) f t) 0})
      atTop (𝓝 0))
    (μ ν : ProbabilityMeasure M)
    (hsource : ∀ U ∈ 𝓝 μ, Tendsto
      (fun r ↦ (P r).real {ω | empiricalProbabilityMeasure (X ⟨r, ω⟩) ∉ U}) atTop (𝓝 0))
    (htarget : ∀ U ∈ 𝓝 ν, Tendsto
      (fun r ↦ (P r).real {ω | empiricalProbabilityMeasure (Y ⟨r, ω⟩) ∉ U}) atTop (𝓝 0)) :
    ∃! π : ProbabilityMeasure (M × M),
      (∀ f : (M × M) →ᵇ ℝ, ∫ z, f z ∂(π : Measure (M × M)) = derivative f) ∧
        (∀ U ∈ 𝓝 π, Tendsto (fun r ↦ (P r).real
          {ω | ∃ γ ∈ empiricalOptimalFace (X ⟨r, ω⟩) (Y ⟨r, ω⟩), γ ∉ U}) atTop (𝓝 0)) ∧
        IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  have hscale' : Tendsto k (Probability.rowProbabilityFilter P) atTop := by
    rw [Filter.tendsto_atTop]
    simpa only [Probability.eventually_rowProbabilityFilter_iff, not_le] using hscale
  have hzero' (f : (M × M) →ᵇ ℝ) :
      Tendsto (fun z ↦ empiricalDistancePressure (X z) (Y z) φ (k z) f 0)
        (Probability.rowProbabilityFilter P) (𝓝 (pressure f 0)) :=
    (Probability.tendsto_rowProbabilityFilter_real_iff P _ _).mpr (hzero f)
  have hlower' (f : (M × M) →ᵇ ℝ) (t : ℝ) (ht : |t| < radius f) :
      Tendsto (fun z ↦ max (pressure f t - empiricalDistancePressure (X z) (Y z) φ (k z) f t) 0)
        (Probability.rowProbabilityFilter P) (𝓝 0) := by
    apply (Probability.tendsto_rowProbabilityFilter_real_iff P _ _).mpr
    simpa only [sub_zero, abs_of_nonneg (le_max_right (_ : ℝ) 0)] using hlower f t ht
  have hsource' : Tendsto (fun z ↦ empiricalProbabilityMeasure (X z))
      (Probability.rowProbabilityFilter P) (𝓝 μ) := by
    rw [Filter.tendsto_def]
    exact hsource
  have htarget' : Tendsto (fun z ↦ empiricalProbabilityMeasure (Y z))
      (Probability.rowProbabilityFilter P) (𝓝 ν) := by
    rw [Filter.tendsto_def]
    exact htarget
  have hface_iff (π : ProbabilityMeasure (M × M)) :
      Tendsto (fun z ↦ empiricalOptimalFace (X z) (Y z))
          (Probability.rowProbabilityFilter P) (𝓝 π).smallSets ↔
        ∀ U ∈ 𝓝 π, Tendsto (fun r ↦ (P r).real
          {ω | ∃ γ ∈ empiricalOptimalFace (X ⟨r, ω⟩) (Y ⟨r, ω⟩), γ ∉ U}) atTop (𝓝 0) := by
    rw [Filter.tendsto_smallSets_iff]
    simp only [Probability.eventually_rowProbabilityFilter_iff,
      Set.subset_def, not_forall, exists_prop]
  obtain ⟨π, hπ, huniq⟩ := existsUnique_empirical_optimal_selector_of_pressure
    (fun z : Σ r, Ω r ↦ sampleSize z.1) X Y φ hφ k hk hscale' pressure radius derivative
    hradius hderiv hzero' hlower' μ ν hsource' htarget'
  exact ⟨π, ⟨hπ.1, (hface_iff π).mp hπ.2.1, hπ.2.2⟩,
    fun γ hγ ↦ huniq γ ⟨hγ.1, (hface_iff γ).mpr hγ.2.1, hγ.2.2⟩⟩

/-- Source and target samples are each iid under the same original joint row law. The paper
scale `(n + 1)^(2/q)` automatically diverges, and both empirical marginals converge by their
common laws. The actual central and tilted pressure limits and their differentiability remain
as analytic convergence premises. -/
theorem existsUnique_empirical_optimal_selector_of_iid_pressure
    {Ω : ℕ → Type*} [∀ r, MeasurableSpace (Ω r)]
    (P : ∀ r, Measure (Ω r)) [∀ r, IsProbabilityMeasure (P r)]
    (X Y : ∀ r, Fin (r + 1) → Ω r → M) (μ ν : ProbabilityMeasure M)
    (hX : ∀ r i, Measurable (X r i)) (hY : ∀ r i, Measurable (Y r i))
    (hindepX : ∀ r, ProbabilityTheory.iIndepFun (X r) (P r))
    (hindepY : ∀ r, ProbabilityTheory.iIndepFun (Y r) (P r))
    (hlawX : ∀ r i, (P r).map (X r i) = (μ : Measure M))
    (hlawY : ∀ r i, (P r).map (Y r i) = (ν : Measure M))
    (φ : M → ℝ) (hφ : LipschitzWith 1 φ) (q : ℝ) (hq : 0 < q)
    (pressure : ((M × M) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((M × M) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0)
    (hzero : ∀ f ε, 0 < ε → Tendsto
      (fun r ↦ (P r).real {ω | ε ≤ |empiricalDistancePressure
        (fun i ↦ X r i ω) (fun i ↦ Y r i ω) φ (((r + 1 : ℕ) : ℝ) ^ (2 / q)) f 0 -
          pressure f 0|}) atTop (𝓝 0))
    (hlower : ∀ f t, |t| < radius f → ∀ ε, 0 < ε → Tendsto
      (fun r ↦ (P r).real {ω | ε ≤ max (pressure f t - empiricalDistancePressure
        (fun i ↦ X r i ω) (fun i ↦ Y r i ω) φ (((r + 1 : ℕ) : ℝ) ^ (2 / q)) f t) 0})
      atTop (𝓝 0)) :
    ∃! π : ProbabilityMeasure (M × M),
      (∀ f : (M × M) →ᵇ ℝ, ∫ z, f z ∂(π : Measure (M × M)) = derivative f) ∧
        (∀ U ∈ 𝓝 π, Tendsto (fun r ↦ (P r).real
          {ω | ∃ γ ∈ empiricalOptimalFace (fun i ↦ X r i ω) (fun i ↦ Y r i ω), γ ∉ U})
          atTop (𝓝 0)) ∧
        IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  have hscale : ∀ R : ℝ, Tendsto
      (fun r ↦ (P r).real {ω | (((r + 1 : ℕ) : ℝ) ^ (2 / q)) < R}) atTop (𝓝 0) := by
    simpa only [Probability.eventually_rowProbabilityFilter_iff, not_le] using
      (Filter.tendsto_atTop.mp (Probability.tendsto_distancePressureScale_row P q hq))
  exact existsUnique_empirical_optimal_selector_row_of_pressure P (fun r ↦ r + 1)
    (fun z i ↦ X z.1 i z.2) (fun z i ↦ Y z.1 i z.2) φ hφ
    (fun z ↦ ((z.1 + 1 : ℕ) : ℝ) ^ (2 / q))
    (fun z ↦ Real.rpow_pos_of_pos (by positivity) _)
    hscale pressure radius derivative hradius hderiv hzero hlower μ ν
    (Probability.tendsto_measureReal_empirical_notMem_of_row_iid P X μ hX hindepX hlawX)
    (Probability.tendsto_measureReal_empirical_notMem_of_row_iid P Y ν hY hindepY hlawY)

end OTSelector.Pressure
