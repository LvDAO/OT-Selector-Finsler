import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate

/-!
# Dilation of the same original stationary matching and colored inputs

Only the transverse physical coordinate is dilated. The original clocks,
immutable colors and matching-input correlations are retained. Rerooting
conjugates by the inverse physical dilation, so every actual stationary joint
law remains stationary at its new physical intensity.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalStationaryDilationInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryDilationPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Spatial dilation preserves the literal original scalar clock. -/
def legalMarkedPointDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0) :
    LegalMarkedPhysicalPoint q ≃ₜ LegalMarkedPhysicalPoint q where
  toFun p := (c • p.1, p.2)
  invFun p := (c⁻¹ • p.1, p.2)
  left_inv p := by simp only [smul_smul, inv_mul_cancel₀ hc, one_smul]
  right_inv p := by simp only [smul_smul, mul_inv_cancel₀ hc, one_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Both original endpoints are dilated by the same physical factor. -/
def legalMarkedEdgeDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0) :
    LegalMarkedPhysicalEdge q ≃ₜ LegalMarkedPhysicalEdge q :=
  (legalMarkedPointDilation q c hc).prodCongr (legalMarkedPointDilation q c hc)

/-- Dilation fixes the immutable original source/target tag. -/
def legalColoredInputDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0) :
    LegalColoredInputPoint q ≃ₜ LegalColoredInputPoint q :=
  (legalMarkedPointDilation q c hc).prodCongr (Homeomorph.refl (Fin 2))

/-- The same full original joint scene after deterministic physical dilation. -/
def legalMarkedInputSceneDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (s : LegalMarkedOptimalInputScene q) : LegalMarkedOptimalInputScene q :=
  ((localFiniteMapHomeomorph (legalMarkedEdgeDilation q c hc) s.1.1,
    localFiniteMapHomeomorph (legalMarkedEdgeDilation q c hc) s.1.2),
    localFiniteMapHomeomorph (legalColoredInputDilation q c hc) s.2)

theorem continuous_legalMarkedInputSceneDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0) :
    Continuous (legalMarkedInputSceneDilation q c hc) :=
  (((continuous_localFiniteMapHomeomorph _).comp continuous_fst.fst).prodMk
    ((continuous_localFiniteMapHomeomorph _).comp continuous_fst.snd)).prodMk
      ((continuous_localFiniteMapHomeomorph _).comp continuous_snd)

private theorem localFiniteMapHomeomorph_comp_congr
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
    [LocallyCompactSpace X] [BorelSpace X]
    (a b c d : X ≃ₜ X) (h : a ∘ b = c ∘ d) (μ : LocalFiniteMeasure X) :
    localFiniteMapHomeomorph a (localFiniteMapHomeomorph b μ) =
      localFiniteMapHomeomorph c (localFiniteMapHomeomorph d μ) := by
  apply Subtype.ext
  change ((μ : Measure X).map b).map a = ((μ : Measure X).map d).map c
  rw [Measure.map_map a.continuous.measurable b.continuous.measurable,
    Measure.map_map c.continuous.measurable d.continuous.measurable, h]

/-- Every literal original reroot is conjugated by inverse spatial dilation. -/
theorem legalMarkedInputSceneReroot_dilation (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (v : Fin q → ℝ) (s : LegalMarkedOptimalInputScene q) :
    legalMarkedInputSceneReroot q v (legalMarkedInputSceneDilation q c hc s) =
      legalMarkedInputSceneDilation q c hc (legalMarkedInputSceneReroot q (c⁻¹ • v) s) := by
  have hp : physicalScenePointReroot v ∘ legalMarkedPointDilation q c hc =
      legalMarkedPointDilation q c hc ∘ physicalScenePointReroot (c⁻¹ • v) := by
    funext p
    apply Prod.ext
    · change c • p.1 - v = c • (p.1 - c⁻¹ • v)
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul]
    · rfl
  have he : physicalSceneEdgeReroot v ∘ legalMarkedEdgeDilation q c hc =
      legalMarkedEdgeDilation q c hc ∘ physicalSceneEdgeReroot (c⁻¹ • v) := by
    funext p
    exact Prod.ext (congrFun hp p.1) (congrFun hp p.2)
  have hi : legalColoredInputPointReroot q v ∘ legalColoredInputDilation q c hc =
      legalColoredInputDilation q c hc ∘ legalColoredInputPointReroot q (c⁻¹ • v) := by
    funext p
    exact Prod.ext (congrFun hp p.1) rfl
  apply Prod.ext
  · apply Prod.ext
    · exact localFiniteMapHomeomorph_comp_congr _ _ _ _ he s.1.1
    · exact localFiniteMapHomeomorph_comp_congr _ _ _ _ he s.1.2
  · exact localFiniteMapHomeomorph_comp_congr _ _ _ _ hi s.2

/-- Dilation of the unchanged original joint scene law preserves stationarity;
its new physical intensity is not silently normalized back to one. -/
theorem measurePreserving_dilated_legalMarkedInputSceneLaw (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) (c : ℝ) (hc : c ≠ 0)
    (hQ : ∀ v, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) Q) (v : Fin q → ℝ) :
    MeasurePreserving (legalMarkedInputSceneReroot q v)
      ((Q : Measure (LegalMarkedOptimalInputScene q)).map (legalMarkedInputSceneDilation q c hc))
      ((Q : Measure (LegalMarkedOptimalInputScene q)).map (legalMarkedInputSceneDilation q c hc)) := by
  refine ⟨(continuous_legalMarkedInputSceneReroot q v).measurable, ?_⟩
  rw [Measure.map_map (continuous_legalMarkedInputSceneReroot q v).measurable
    (continuous_legalMarkedInputSceneDilation q c hc).measurable]
  have hcomp : legalMarkedInputSceneReroot q v ∘ legalMarkedInputSceneDilation q c hc =
      legalMarkedInputSceneDilation q c hc ∘ legalMarkedInputSceneReroot q (c⁻¹ • v) := by
    funext s
    exact legalMarkedInputSceneReroot_dilation q c hc v s
  rw [hcomp, ← Measure.map_map (continuous_legalMarkedInputSceneDilation q c hc).measurable
    (continuous_legalMarkedInputSceneReroot q (c⁻¹ • v)).measurable, (hQ _).map_eq]

end OTSelector.Reconstruction
