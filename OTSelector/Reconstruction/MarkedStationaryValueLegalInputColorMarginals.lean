import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointDomination
import OTSelector.MeasureTheory.CompactProductMarginalDomination

/-!
# Whole endpoint marginals are dominated by their own immutable input color

Each input color is recovered from the literal joint point measure by restriction
and projection. Finite colors make this projection proper on compact source
windows, while no properness is imposed on the matching's endpoint projections.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance markedStationaryValueLegalInputColorMarginalsInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputColorMarginalsPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The unchanged original physical input of one immutable color. -/
def legalInputColorMeasure (q : ℕ) (μ : LocalFiniteMeasure (LegalColoredInputPoint q))
    (c : Fin 2) : Measure (LegalMarkedPhysicalPoint q) :=
  ((μ : Measure (LegalColoredInputPoint q)).restrict {x | x.2 = c}).map Prod.fst

instance legalInputColorMeasureFiniteOnCompacts (q : ℕ)
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) (c : Fin 2) :
    IsFiniteMeasureOnCompacts (legalInputColorMeasure q μ c) := by
  constructor
  intro K hK
  rw [legalInputColorMeasure, Measure.map_apply measurable_fst hK.measurableSet,
    Measure.restrict_apply (hK.measurableSet.preimage measurable_fst)]
  have he : Prod.fst ⁻¹' K ∩ {x : LegalColoredInputPoint q | x.2 = c} = K ×ˢ {c} := by
    ext x
    simp
  rw [he]
  exact (hK.prod isCompact_singleton).measure_lt_top

/-- Reading a color after restriction and projection is exactly its original
colored compact test. -/
theorem integral_legalInputColorMeasure (q : ℕ)
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) (c : Fin 2)
    (f : C_c(LegalMarkedPhysicalPoint q, ℝ)) :
    (∫ x, f x ∂legalInputColorMeasure q μ c) =
      LocalFiniteMeasure.testIntegral μ (cavityProductTest f (legalInputColorTest c)) := by
  rw [legalInputColorMeasure, integral_map (f := fun x ↦ f x)
    measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
  have hc : MeasurableSet {x : LegalColoredInputPoint q | x.2 = c} :=
    measurable_snd (measurableSet_singleton c)
  rw [← integral_indicator hc]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    by_cases hx : x.2 = c <;> simp [cavityProductTest, legalInputColorTest, hx]

/-- Both whole matching marginals are dominated by the corresponding unchanged
original input in the same joint scene. No endpoint projection finiteness is
assumed; it follows from the input domination. -/
theorem legalMarkedInput_marginals_le_of_testDomination
    (q : ℕ) (s : LegalMarkedOptimalInputScene q) (h : legalMarkedInputTestDomination q s) :
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst ≤ legalInputColorMeasure q s.2 0 ∧
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd ≤ legalInputColorMeasure q s.2 1 := by
  constructor
  · apply fst_le_of_compact_product_tests
    intro f hf g hg
    rw [integral_legalInputColorMeasure]
    exact (h f hf g hg).1
  · apply snd_le_of_compact_product_tests
    intro f hf g hg
    rw [integral_legalInputColorMeasure]
    exact (h f hf g hg).2

/-- One common AE event carries complete source and target marginal domination
for every actual joint weak limit, without any global separation of clock laws. -/
theorem ae_legalMarkedInput_marginals_le_of_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst ≤ legalInputColorMeasure q s.2 0 ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd ≤ legalInputColorMeasure q s.2 1 := by
  filter_upwards [ae_legalMarkedInputTestDomination_of_tendsto q α β kin hk g hg t L hL hweak]
    with s hs
  exact legalMarkedInput_marginals_le_of_testDomination q s hs

end OTSelector.Reconstruction
