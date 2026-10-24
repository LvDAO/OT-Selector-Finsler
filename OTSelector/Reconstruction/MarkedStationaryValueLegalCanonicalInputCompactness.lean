import OTSelector.Reconstruction.MarkedStationaryValueLegalCanonicalFirstInputScene
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryOriginalInputIntensity

/-!
# Compactness of canonical actual matching/input laws

Uniform local first moments come from the unchanged physical input intensity.
The first matching is dominated by its own original source input. The unused
second edge slot is filled by that same first matching before Prokhorov is
applied. Weak limits retain stationarity and the exact original compact input
Laplace field; fullness of nonproper marginals is not asserted here.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Metric
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
local instance canonicalStationaryInputCompactnessInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance canonicalStationaryInputCompactnessPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace
local instance canonicalStationaryInputCompactnessInputNonempty (q : ℕ) : Nonempty
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := ⟨⟨0, inferInstance⟩⟩
local instance canonicalStationaryInputCompactnessPlanNonempty (q : ℕ) : Nonempty
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := ⟨⟨0, inferInstance⟩⟩

/-- The actual first-plan laws are uniformly tight over any family of genuine
matchings with fixed original clocks, without a kinetic or second moment bound. -/
theorem isTightMeasureSet_genuineStationary_firstPlan
    {I : Type*} {q : ℕ} {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : I → LegalWeightedStationaryPoissonMatching q α β kin g) :
    IsTightMeasureSet (range (fun i ↦
      (M i).law.toMeasure.map (fun s ↦ s.1.1))) := by
  let K := CompactExhaustion.choice (LegalMarkedPhysicalEdge q)
  have hb (n : ℕ) : ∃ R > 0, ∀ e ∈ K n, ‖e.1.1‖ < R := by
    obtain ⟨R, hR, hbound⟩ := ((K.isCompact n).image
      (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
    exact ⟨R, hR, fun x hx ↦ hbound _ ⟨x, hx, rfl⟩⟩
  choose R hR hKR using hb
  refine LocalFiniteMeasure.isTightMeasureSet_map_of_lintegral_localMass_le
    (fun i ↦ ((M i).law : Measure (LegalMarkedOptimalInputScene q)))
    (fun _ s ↦ s.1.1) (fun _ ↦ measurable_fst.fst)
    (fun n ↦ interior (K n)) (fun _ ↦ isOpen_interior) ?_
    (fun n ↦ volume (ball (0 : Fin q → ℝ) (R n)))
    (fun _ ↦ measure_ball_lt_top.ne) ?_
  · intro A hA
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hA
    exact ⟨n + 1, hn.trans (K.subset_interior_succ n)⟩
  · intro i n
    let B : Set (LegalMarkedPhysicalPoint q) := ball (0 : Fin q → ℝ) (R n) ×ˢ univ
    have hB : MeasurableSet B := measurableSet_ball.prod MeasurableSet.univ
    have hdom : ∀ᵐ s ∂((M i).law : Measure (LegalMarkedOptimalInputScene q)),
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (interior (K n)) ≤
          legalInputColorMeasure q s.2 0 B := by
      filter_upwards [(M i).full_matching] with s hs
      calc
        _ ≤ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Prod.fst ⁻¹' B) := by
          apply measure_mono
          intro e he
          exact ⟨by simpa only [mem_ball, dist_zero_right] using
            (hKR n e (interior_subset he)), mem_univ _⟩
        _ = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst B :=
          (Measure.map_apply measurable_fst hB).symm
        _ = _ := congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ μ B) hs.source_marginal
    apply (lintegral_mono_ae hdom).trans
    rw [lintegral_legalInputColorMeasure_eq_intensity q _ 0 hB,
      (M i).inputColorIntensities_eq_volume_prod.1, Measure.prod_prod, measure_univ, mul_one]

/-- Complete original colored input laws have the same uniform local first
moment bound. No law is assigned to selected or unmatched endpoints. -/
theorem isTightMeasureSet_genuineStationary_coloredInput
    {I : Type*} {q : ℕ} {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : I → LegalWeightedStationaryPoissonMatching q α β kin g) :
    IsTightMeasureSet (range (fun i ↦ (M i).law.toMeasure.map Prod.snd)) := by
  let K := CompactExhaustion.choice (LegalColoredInputPoint q)
  have hb (n : ℕ) : ∃ R > 0, ∀ e ∈ K n, ‖e.1.1‖ < R := by
    obtain ⟨R, hR, hbound⟩ := ((K.isCompact n).image
      (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
    exact ⟨R, hR, fun x hx ↦ hbound _ ⟨x, hx, rfl⟩⟩
  choose R hR hKR using hb
  refine LocalFiniteMeasure.isTightMeasureSet_map_of_lintegral_localMass_le
    (fun i ↦ ((M i).law : Measure (LegalMarkedOptimalInputScene q)))
    (fun _ s ↦ s.2) (fun _ ↦ measurable_snd)
    (fun n ↦ interior (K n)) (fun _ ↦ isOpen_interior) ?_
    (fun n ↦ volume (ball (0 : Fin q → ℝ) (R n)) +
      volume (ball (0 : Fin q → ℝ) (R n)))
    (fun _ ↦ ENNReal.add_ne_top.mpr ⟨measure_ball_lt_top.ne, measure_ball_lt_top.ne⟩) ?_
  · intro A hA
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hA
    exact ⟨n + 1, hn.trans (K.subset_interior_succ n)⟩
  · intro i n
    let B : Set (LegalMarkedPhysicalPoint q) := ball (0 : Fin q → ℝ) (R n) ×ˢ univ
    have hB : MeasurableSet B := measurableSet_ball.prod MeasurableSet.univ
    have hc (c : Fin 2) : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
        legalInputColorMeasure q s.2 c B) := by
      convert (Kernel.measurable_coe (legalMarkedInputColorKernel q c) hB) using 1
      funext s
      rw [legalMarkedInputColorKernel_apply]
    calc
      _ ≤ ∫⁻ s, legalInputColorMeasure q s.2 0 B + legalInputColorMeasure q s.2 1 B
          ∂((M i).law : Measure (LegalMarkedOptimalInputScene q)) := by
        apply lintegral_mono
        intro s
        refine (measure_mono ?_).trans (legalInput_mass_le_sum_colorMass q s.2 hB)
        intro e he
        exact ⟨⟨by simpa only [mem_ball, dist_zero_right] using
          (hKR n e (interior_subset he)), mem_univ _⟩, mem_univ _⟩
      _ = _ := by
        rw [lintegral_add_left (hc 0), lintegral_legalInputColorMeasure_eq_intensity q _ 0 hB,
          lintegral_legalInputColorMeasure_eq_intensity q _ 1 hB,
          (M i).inputColorIntensities_eq_volume_prod.1,
          (M i).inputColorIntensities_eq_volume_prod.2,
          Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one]

/-- The unchanged first matching and complete original input retain their
actual joint law. Filling the unused slot by that same plan gives tight laws. -/
theorem isTightMeasureSet_genuineStationary_canonicalFirstInputLaw
    {I : Type*} {q : ℕ} {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : I → LegalWeightedStationaryPoissonMatching q α β kin g) :
    IsTightMeasureSet (range (fun i ↦
      (legalMarkedCanonicalFirstInputLaw q (M i).law : Measure (LegalMarkedOptimalInputScene q)))) := by
  let P i := ((M i).law : Measure (LegalMarkedOptimalInputScene q))
  have hp := isTightMeasureSet_genuineStationary_firstPlan M
  have hi := isTightMeasureSet_genuineStationary_coloredInput M
  have hpair := isTightMeasureSet_original_joint_of_marginals P
    (fun _ s ↦ s.1.1) (fun _ s ↦ s.1.1)
    (fun _ ↦ measurable_fst.fst) (fun _ ↦ measurable_fst.fst) hp hp
  exact isTightMeasureSet_original_joint_of_marginals P
    (fun _ s ↦ (s.1.1, s.1.1)) (fun _ s ↦ s.2)
    (fun _ ↦ measurable_fst.fst.prodMk measurable_fst.fst) (fun _ ↦ measurable_snd) hpair hi

/-- Genuine stationary joint laws stay stationary under an actual weak
limit. This assertion alone makes no compactness or full-marginal claim. -/
theorem measurePreserving_reroot_of_genuineStationary_tendsto
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hw : Tendsto (fun n ↦ (M n).law) atTop (𝓝 Q)) (v : Fin q → ℝ) :
    MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q))
      (Q : Measure (LegalMarkedOptimalInputScene q)) := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ Q hw
    (continuous_legalMarkedInputSceneReroot q v)
  have he (n : ℕ) : (M n).law.map
      (continuous_legalMarkedInputSceneReroot q v).measurable.aemeasurable = (M n).law := by
    apply ProbabilityMeasure.toMeasure_injective
    exact ((M n).stationary v).map_eq
  simp only [he] at hmap
  have heq := tendsto_nhds_unique hmap hw
  exact ⟨(continuous_legalMarkedInputSceneReroot q v).measurable,
    congrArg (fun P : ProbabilityMeasure (LegalMarkedOptimalInputScene q) ↦ (P : Measure (LegalMarkedOptimalInputScene q))) heq⟩

/-- Every actual weak limit keeps the same prescribed original compact
Poisson input field, regardless of any escape through endpoint projections. -/
theorem input_laplace_of_genuineStationary_tendsto
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hw : Tendsto (fun n ↦ (M n).law) atTop (𝓝 Q))
    (S : ℝ) (hS : 0 < S) (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x)
    (hz : ∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
      x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
        ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β := by
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw
    (legalMarkedInputSceneLaplace q F hF)
  have he (n : ℕ) := (M n).input_laplace S hS F hF hz
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (.of_forall fun n ↦ (he n).symm))

/-- Every sequence of genuine original matchings has a common stationary
weak limit after filling only the unused second edge slot canonically. All
actual first matching/input correlations, true Palms and values are retained;
fullness of the limiting nonproper endpoint marginals is a subsequent result. -/
theorem exists_stationary_originalInput_subseq_canonicalFirstInputLaw
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∃ Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n ↦ legalMarkedCanonicalFirstInputLaw q (M (φ n)).law) atTop (𝓝 Q) ∧
      (∀ v, MeasurePreserving (legalMarkedInputSceneReroot q v)
        (Q : Measure (LegalMarkedOptimalInputScene q))
      (Q : Measure (LegalMarkedOptimalInputScene q))) ∧
      (∀ S : ℝ, 0 < S →
        ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
        (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
          x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
        (∫ s, legalMarkedInputSceneLaplace q F hF s
          ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
          ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
            ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) := by
  obtain ⟨Q, φ, hφ, hw⟩ := exists_tendsto_subseq_probabilityMeasure_of_isTight
    (fun n ↦ legalMarkedCanonicalFirstInputLaw q (M n).law)
    (isTightMeasureSet_genuineStationary_canonicalFirstInputLaw M)
  refine ⟨Q, φ, hφ, hw, ?_, ?_⟩
  · exact measurePreserving_reroot_of_genuineStationary_tendsto
      (fun n ↦ (M (φ n)).canonicalFirstInput) hw
  · exact input_laplace_of_genuineStationary_tendsto
      (fun n ↦ (M (φ n)).canonicalFirstInput) hw

end OTSelector.Reconstruction
