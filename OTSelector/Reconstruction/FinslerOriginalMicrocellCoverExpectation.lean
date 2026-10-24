import OTSelector.Reconstruction.FinslerOriginalMacroToMicrocellExpectation
import OTSelector.Reconstruction.FinslerOriginalMacroFittingTwoMassControls

/-! An actual original measurable cell produces its own deterministic fitting
microboxes and the legal macro-to-micro expectation bound on those boxes. -/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}


/-- The original Haar mass-loss and hole limits, exact macro fit and actual
original expectation bound are produced together. The macrobox is fixed before
the microscopic grid and accuracy; no shape or sample-law oracle is required. -/
theorem PopulationLocalPressureCore.exists_original_microcell_cover_expectation_bound
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    [(κ (D.haar.continuous.coefficient i).seedIndex).IsAddHaarMeasure]
    {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (classify : ℝ → Fin Q.count) (hm : Measurable classify)
    (hclass : ∀ j x, x ∈ Q.cell j → classify x = j)
    (fallbackS fallbackT : Fin Q.count → ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ) (hP₀ : ∀ j k, 0 ≤ P₀ j k)
    (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (Pf residual : (ℚ → M) → Fin Q.count → Fin Q.count → ℝ)
    (hmPf : ∀ j k, Measurable (fun z ↦ Pf z j k))
    (hPf : ∀ z ∈ L, ∀ j k, Pf z j k = P₀ j k / D.rootIntensity i z)
    (hresidual : ∀ᵐ z ∂lambda.restrict L, ∀ j k, 0 ≤ residual z j k)
    (hrow : ∀ᵐ z ∂lambda.restrict L, ∀ j, ∑ k, (Pf z j k + residual z j k) =
      (condDistrib u a η₀ z).real (Q.cell j))
    (hcol : ∀ᵐ z ∂lambda.restrict L, ∀ k, ∑ j, (Pf z j k + residual z j k) =
      (condDistrib u a η₁ z).real (Q.cell k))
    {Cells : Type*} [Fintype Cells]
    (cell : Cells → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (K : Cells → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (c : Cells) (hc : L ⊆ cell c)
    (hKc : K c = finiteClassPopulationKernel Pf
      (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Q.cell j) (Q.measurable_cell j) (fallbackS j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Q.cell k) (Q.measurable_cell k) (fallbackT k)))
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z) (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    (hb : Measurable b)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x, u x) = x) (hη₁inv : ∀ᵐ y ∂η₁, b (a y, u y) = y)
    (hlabel0 : η₀.map a = lambda) (hlabel1 : η₁.map a = lambda)
    (πWhole ξ : Measure (M × M)) [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
    (hsplit : πWhole = (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b)) + ξ)
    {T : Type*} [Fintype T] {qAtlas : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData πWhole η₀ η₁ T qAtlas cost)
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    (ref : (D.haar.continuous.coefficient i).roots) (f : M × M →ᵇ ℝ)
    (hzero : ∀ j k, ¬(D.haar.continuous.coefficient i).clockClassAllowed Q j k → P₀ j k = 0)
    (hq : 4 < Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let root := populationSeedRootLabelValue Seed a
    let basis := Module.finBasis ℝ Seed.covector.ker
    let coord := atlasSeedCoord Seed basis.equivFunL a
    let q := Module.finrank ℝ Seed.covector.ker
    ∃ (R : ℕ) (B : ℝ), 0 < R ∧ 0 ≤ B ∧
    ∀ (ε : ℝ≥0∞), 0 < ε →
    ∀ (order : ℕ → ℕ) [∀ N, NeZero (order N)], Tendsto order atTop atTop →
    ∃ indices : ℕ → Finset (Fin q → ℤ),
      (∀ N, Set.PairwiseDisjoint (↑(indices N) : Set (Fin q → ℤ))
        (fun ν ↦ (BoxIntegral.unitPartition.box (order N) ν : Set (Fin q → ℝ)))) ∧
      (∀ N, lambda (L \ coord ⁻¹' (⋃ ν ∈ indices N,
        (BoxIntegral.unitPartition.box (order N) ν : Set (Fin q → ℝ)))) < ε) ∧
      (∀ N, volume ((coord '' L) \ (⋃ ν ∈ indices N,
        (BoxIntegral.unitPartition.box (order N) ν : Set (Fin q → ℝ)))) < ε) ∧
      Tendsto (fun N ↦ volume ((⋃ ν ∈ indices N,
        (BoxIntegral.unitPartition.box (order N) ν : Set (Fin q → ℝ))) \ (coord '' L))) atTop (𝓝 0) ∧
    ∀ (N : ℕ), 0 < N → ∀ (G : Set (ℚ → M)) (hG : MeasurableSet G) (tilt : ℝ),
      L ∩ G = L ∩ coord ⁻¹' (⋃ ν ∈ indices N,
        (BoxIntegral.unitPartition.box (order N) ν : Set (Fin q → ℝ))) →
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    let original := originalRetainedSeedClassCost a L (fun x ↦ root (a x)) basis.equivFunL.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
      ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic Q ref.val)
      (C.clockClassProbe Q ref.val ref.property f) tilt
    let micro := fun ν : Fin q → ℤ ↦ originalRetainedSeedClassCost a
      (L ∩ (basis.equivFunL ∘ root) ⁻¹' (BoxIntegral.unitPartition.box (order N) ν : Set (Fin q → ℝ)))
      (fun x ↦ root (a x)) basis.equivFunL.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
      ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic Q ref.val)
      (C.clockClassProbe Q ref.val ref.property f) tilt
    Integrable original (Refined.markedLaw N) ∧
    (∀ ν ∈ (indices N), Integrable (micro ν) (Refined.markedLaw N)) ∧
    (∫ sample, original sample ∂Refined.markedLaw N) / N ≤
      (∑ ν ∈ (indices N), ∫ sample, micro ν sample ∂Refined.markedLaw N) / N +
      activeGridRepairError q (legalGridRepairConstant q (Q.count + 1) (Q.count * Q.count))
        B ‖f‖ tilt 1 ((N : ℝ) / ((2 * R * (order N) : ℕ) : ℝ) ^ q) := by
  classical
  obtain ⟨R,B,hR,hB,hroot,hbound⟩ := D.exists_original_macro_to_microcell_expectation_bound
    hF hcomplete hu ha hinj i hL hsub Q classify hm hclass fallbackS fallbackT P₀ hP₀ hmass
    Pf residual hmPf hPf hresidual hrow hcol cell hcell hdisj K c hc hKc Qglobal hwhole
    hb hη₀inv hη₁inv hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst ref f hzero
  dsimp only
  refine ⟨R,B,hR,hB,?_⟩
  intro ε hε order _ horder
  obtain ⟨indices,hdisjoint,hloss,hmissing,hfill,hfit⟩ :=
    D.exists_cell_macro_fitting_microscopic_cubes_with_two_mass_controls hF hcomplete hu ha hinj i hL hsub
      (Module.finBasis ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) hR
      (fun z hz ↦ hroot z (hsub hz)) hε order horder
  refine ⟨indices,hdisjoint,hloss,hmissing,hfill,?_⟩
  intro N hN G hG tilt htrace
  have hcover : ∀ z ∈ L ∩ G,
      atlasSeedCoord (P (D.haar.continuous.coefficient i).seedIndex).seed
        (Module.finBasis ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFunL a z ∈
        ⋃ ν ∈ indices N, (BoxIntegral.unitPartition.box (order N) ν : Set _) := by
    intro z hz
    rw [htrace] at hz
    exact hz.2
  exact hbound G hG (order N) N (order N).pos_of_neZero hq hN tilt (indices N) (hfit N) hcover

end OTSelector.Reconstruction
