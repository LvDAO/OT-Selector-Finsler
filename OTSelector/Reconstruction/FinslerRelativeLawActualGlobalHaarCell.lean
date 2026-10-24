import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery
import OTSelector.Reconstruction.FinslerRelativeLawActualHaarCoordinates
import OTSelector.Reconstruction.FinslerRelativeLawGlobalRetainedCell

/-!
The retained original physical pair population equals its literal fixed
pair-class population on the original Haar cell under the actual seed physical
map. Both original endpoint recovery and original density normalization are
discharged from the unchanged original population and pressure-core data.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

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

/-- Reading the original label and original clock from the given physical
retained population recovers the literal raw Haar-cell pair law. The same
original almost-everywhere inverse is used throughout. -/
theorem PopulationLocalPressureCore.actual_global_retained_cell_pair_coordinates_eq_haar
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hb : Measurable b)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x, u x) = x)
    (hη₁inv : ∀ᵐ y ∂η₁, b (a y, u y) = y)
    (hlabel0 : η₀.map a = lambda) (hlabel1 : η₁.map a = lambda)
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {I J : Type*} [Fintype I] [Fintype J]
    (Sbin : I → Set ℝ) (Tbin : J → Set ℝ)
    (hSbin : ∀ j, MeasurableSet (Sbin j)) (hTbin : ∀ k, MeasurableSet (Tbin k))
    (fallbackS : I → ℝ) (fallbackT : J → ℝ)
    (P₀ : I → J → ℝ) (Pf : (ℚ → M) → I → J → ℝ)
    (hmPf : ∀ j k, Measurable (fun z ↦ Pf z j k))
    (hPf : ∀ z ∈ L, ∀ j k, Pf z j k = P₀ j k / D.rootIntensity i z)
    {Cells : Type*} [Fintype Cells]
    (cell : Cells → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (K : Cells → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (c : Cells) (hc : cell c = L)
    (hKc : K c = finiteClassPopulationKernel Pf
      (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Sbin j) (hSbin j) (fallbackS j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Tbin k) (hTbin k) (fallbackT k)))
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z) (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    (side : Bool) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue Seed a
    let read := fun x ↦ (R (a x), u x)
    let αc := fun j ↦ normalizedActualBinKernel
      (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₀)) (Sbin j) (hSbin j) (fallbackS j)
    let βc := fun k ↦ normalizedActualBinKernel
      (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₁)) (Tbin k) (hTbin k) (fallbackT k)
    (((((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map
      (Prod.map b b)).restrict {p | a (if side then p.2 else p.1) ∈ L}).map (Prod.map read read)) =
      (((κ C.seedIndex).restrict (R '' L) ⊗ₘ finiteClassPopulationKernel (fun _ j k ↦ P₀ j k) αc βc).map
        sameLabelPopulationPair) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue Seed a
  let Kg := finiteCellPairKernel cell hcell K
  have hdom : ∀ᵐ z ∂lambda,
      (Kg z).map Prod.fst ≤ condDistrib u a η₀ z ∧ (Kg z).map Prod.snd ≤ condDistrib u a η₁ z :=
    hwhole.mono fun z hz ↦ clockPair_marginals_le_of_original_split _ _ _ _ hz
  have hR : Measurable R := measurable_populationSeedRootLabelValue Seed hF hcomplete hu ha hinj
  have hread := original_retained_pair_restrict_read_coordinates η₀ η₁ lambda a u ha
    hu.continuous.measurable b hb hη₀inv hη₁inv hlabel0 hlabel1 Kg hdom hL R hR side
  have hlocal := compProd_finiteCellPairKernel_restrict lambda cell hcell hdisj K c
  rw [hc, hKc] at hlocal
  have hhaar := D.actual_retained_cell_pair_law_eq_haar hF hcomplete hu ha hinj i hL hsub
    Sbin Tbin hSbin hTbin fallbackS fallbackT P₀ Pf hmPf hPf
  dsimp only at hread hhaar ⊢
  exact hread.trans ((congrArg
    (fun μ ↦ (μ.map (Prod.map R id)).map sameLabelPopulationPair) hlocal).trans
      (congrArg (fun μ ↦ μ.map sameLabelPopulationPair) hhaar))

end OTSelector.Reconstruction
