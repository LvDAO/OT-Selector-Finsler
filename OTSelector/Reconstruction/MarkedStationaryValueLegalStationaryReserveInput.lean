import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryDilationPoisson

/-!
# Independent original dilated inputs produce the actual unit-intensity reserve

The retained matching and reserve are sampled from two independent original
joint laws. Their literal colored input measures are added, while the retained
matching remains the first original plan. Exact Laplace calculations identify
the combined Poisson input law without assigning a law to selected orphans.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local instance markedStationaryValueLegalStationaryReserveInputInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryReserveInputPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Add the two actual locally finite measures, preserving their multiplicities. -/
def legalLocalFiniteMeasureSum {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (p : LocalFiniteMeasure X × LocalFiniteMeasure X) : LocalFiniteMeasure X :=
  ⟨(p.1 : Measure X) + (p.2 : Measure X), by
    constructor
    intro K hK
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩

section Sum
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- Actual measure superposition is measurable in the original vague carrier. -/
theorem measurable_legalLocalFiniteMeasureSum : Measurable (legalLocalFiniteMeasureSum (X := X)) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  exact (measurable_localFiniteMeasure_coe.comp measurable_fst).add
    (measurable_localFiniteMeasure_coe.comp measurable_snd)

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
theorem testIntegral_legalLocalFiniteMeasureSum
    (p : LocalFiniteMeasure X × LocalFiniteMeasure X) (F : C_c(X, ℝ)) :
    LocalFiniteMeasure.testIntegral (legalLocalFiniteMeasureSum p) F =
      LocalFiniteMeasure.testIntegral p.1 F + LocalFiniteMeasure.testIntegral p.2 F := by
  exact integral_add_measure F.integrable F.integrable
end Sum

/-- Retain the entire first original matching and add only the second
original input as unused reserve. All original input coordinates are retained. -/
def legalMarkedReserveInputScene (q : ℕ)
    (p : LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) :
    LegalMarkedOptimalInputScene q := (p.1.1, legalLocalFiniteMeasureSum (p.1.2, p.2.2))

theorem measurable_legalMarkedReserveInputScene (q : ℕ) :
    Measurable (legalMarkedReserveInputScene q) :=
  measurable_fst.fst.prodMk (measurable_legalLocalFiniteMeasureSum.comp
    (measurable_fst.snd.prodMk measurable_snd.snd))

/-- Independent copies are taken before any retained points are selected. -/
def legalMarkedReserveInputLaw (q : ℕ)
    (Q R : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    ProbabilityMeasure (LegalMarkedOptimalInputScene q) :=
  ⟨((Q : Measure _).prod (R : Measure _)).map (legalMarkedReserveInputScene q),
    Measure.isProbabilityMeasure_map (measurable_legalMarkedReserveInputScene q).aemeasurable⟩

/-- The actual input superposition has exactly the product of its original
compact Laplace readouts. -/
theorem legalMarkedReserveInputScene_laplace (q : ℕ)
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x)
    (p : LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) :
    legalMarkedInputSceneLaplace q F hF (legalMarkedReserveInputScene q p) =
      legalMarkedInputSceneLaplace q F hF p.1 * legalMarkedInputSceneLaplace q F hF p.2 := by
  change Real.exp (-LocalFiniteMeasure.testIntegral (legalLocalFiniteMeasureSum (p.1.2, p.2.2)) F) = _
  rw [testIntegral_legalLocalFiniteMeasureSum, neg_add, Real.exp_add]
  rfl

/-- Exact independence belongs to the two original copies, not to any
adaptive port or leftover process. -/
theorem integral_laplace_legalMarkedReserveInputLaw (q : ℕ)
    (Q R : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s
      ∂(legalMarkedReserveInputLaw q Q R : Measure (LegalMarkedOptimalInputScene q))) =
      (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(Q : Measure (LegalMarkedOptimalInputScene q))) *
        ∫ s, legalMarkedInputSceneLaplace q F hF s ∂(R : Measure (LegalMarkedOptimalInputScene q)) := by
  change (∫ s, legalMarkedInputSceneLaplace q F hF s
    ∂((Q : Measure _).prod (R : Measure _)).map (legalMarkedReserveInputScene q)) = _
  rw [integral_map (measurable_legalMarkedReserveInputScene q).aemeasurable
    (legalMarkedInputSceneLaplace q F hF).continuous.aestronglyMeasurable]
  simp_rw [legalMarkedReserveInputScene_laplace]
  exact integral_prod_mul _ _

/-- Two independently dilated genuine original input laws superpose with the
sum of their actual physical intensities and the unchanged original colors. -/
theorem integral_laplace_original_dilated_reserve
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(legalMarkedReserveInputLaw q
      (legalMarkedInputDilationLaw q c hc M.law) (legalMarkedInputDilationLaw q d hd N.law) :
        Measure (LegalMarkedOptimalInputScene q))) =
      Real.exp ((|(c ^ q)⁻¹| + |(d ^ q)⁻¹|) *
        ((∫ x, (Real.exp (-F (x, 0)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod α) +
          ∫ y, (Real.exp (-F (y, 1)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod β)) := by
  rw [integral_laplace_legalMarkedReserveInputLaw,
    M.dilation_input_laplace_eq_global_exp c hc F hF,
    N.dilation_input_laplace_eq_global_exp d hd F hF, ← Real.exp_add, add_mul]

/-- Adding an independent input reserve leaves the entire retained original
matching pair law exactly unchanged, including its full displacement Palm. -/
theorem legalMarkedInputPairLaw_reserveInputLaw (q : ℕ)
    (Q R : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    legalMarkedInputPairLaw q (legalMarkedReserveInputLaw q Q R) = legalMarkedInputPairLaw q Q := by
  apply ProbabilityMeasure.toMeasure_injective
  change (((Q : Measure (LegalMarkedOptimalInputScene q)).prod
    (R : Measure (LegalMarkedOptimalInputScene q))).map (legalMarkedReserveInputScene q)).map Prod.fst =
      (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst
  rw [Measure.map_map measurable_fst (measurable_legalMarkedReserveInputScene q)]
  have hcomp : Prod.fst ∘ legalMarkedReserveInputScene q = Prod.fst ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map measurable_fst measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- When the two actual Haar intensities add to one, the independent original
reserve produces exactly the original prescribed compact Poisson input field. -/
theorem original_dilated_reserve_input_laplace
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hunit : |(c ^ q)⁻¹| + |(d ^ q)⁻¹| = 1)
    (S : ℝ) (hS : 0 < S) (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x)
    (hz : ∀ (x : LegalMarkedPhysicalPoint q) (k : Fin 2),
      x.1 ∉ haarRootCube (Fin q) S → F (x, k) = 0) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(legalMarkedReserveInputLaw q
      (legalMarkedInputDilationLaw q c hc M.law) (legalMarkedInputDilationLaw q d hd N.law) :
        Measure (LegalMarkedOptimalInputScene q))) =
      ∫ z, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) z
        ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β := by
  rw [integral_laplace_original_dilated_reserve M N c d hc hd F hF, hunit, one_mul]
  rw [← M.input_laplace_eq_global_exp F hF]
  exact M.input_laplace S hS F hF hz

/-- The actual original reserve superposition commutes with the common
physical root translation, including both immutable input colors. -/
theorem legalMarkedReserveInputScene_commute_reroot (q : ℕ) (v : Fin q → ℝ)
    (p : LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) :
    legalMarkedInputSceneReroot q v (legalMarkedReserveInputScene q p) =
      legalMarkedReserveInputScene q
        (legalMarkedInputSceneReroot q v p.1, legalMarkedInputSceneReroot q v p.2) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (((p.1.2 : Measure (LegalColoredInputPoint q)) + p.2.2).map
      (legalColoredInputPointReroot q v)) = _
    exact Measure.map_add _ _ (legalColoredInputPointReroot q v).continuous.measurable

/-- Independence is taken at the original stationary scene laws. Their
actual retained-plan/reserve-input superposition is stationary. -/
theorem measurePreserving_legalMarkedReserveInputLaw (q : ℕ)
    (Q R : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hQ : ∀ v, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) Q)
    (hR : ∀ v, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (R : Measure (LegalMarkedOptimalInputScene q)) R) (v : Fin q → ℝ) :
    MeasurePreserving (legalMarkedInputSceneReroot q v)
      (legalMarkedReserveInputLaw q Q R : Measure (LegalMarkedOptimalInputScene q))
      (legalMarkedReserveInputLaw q Q R : Measure (LegalMarkedOptimalInputScene q)) := by
  refine ⟨(continuous_legalMarkedInputSceneReroot q v).measurable, ?_⟩
  change (((Q : Measure (LegalMarkedOptimalInputScene q)).prod
    (R : Measure (LegalMarkedOptimalInputScene q))).map (legalMarkedReserveInputScene q)).map
      (legalMarkedInputSceneReroot q v) = _
  rw [Measure.map_map (continuous_legalMarkedInputSceneReroot q v).measurable
    (measurable_legalMarkedReserveInputScene q)]
  have hcomp : legalMarkedInputSceneReroot q v ∘ legalMarkedReserveInputScene q =
      legalMarkedReserveInputScene q ∘ Prod.map (legalMarkedInputSceneReroot q v)
        (legalMarkedInputSceneReroot q v) := by
    funext p
    exact legalMarkedReserveInputScene_commute_reroot q v p
  rw [hcomp, ← Measure.map_map (measurable_legalMarkedReserveInputScene q)
    ((hQ v).measurable.prodMap (hR v).measurable), ((hQ v).prod (hR v)).map_eq]
  rfl

end OTSelector.Reconstruction
