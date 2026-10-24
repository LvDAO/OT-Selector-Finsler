import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery

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

/-- The actual retained ORIGINAL physical pair population is exactly the
fixed pair-class law on the original Haar cell, pushed through the actual seed
physical field. The residual completing the original conditional marginals
supplies the required domination automatically. -/
theorem PopulationLocalPressureCore.actual_original_retained_physical_pair_law_eq_haar
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ y ∂η₁, y ∈ F.potentialRegularDomain u)
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
    (Q : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Q]
    (hwhole :
      let α := fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Sbin j) (hSbin j) (fallbackS j)
      let β := fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Tbin k) (hTbin k) (fallbackT k)
      ∀ᵐ z ∂lambda.restrict L, Vlasov.IsCoupling
        (finiteClassPopulationKernel Pf α β z + Q z) (condDistrib u a η₀ z) (condDistrib u a η₁ z)) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue Seed a
    let α := fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Sbin j) (hSbin j) (fallbackS j)
    let β := fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Tbin k) (hTbin k) (fallbackT k)
    let αc := fun j ↦ normalizedActualBinKernel
      (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₀)) (Sbin j) (hSbin j) (fallbackS j)
    let βc := fun k ↦ normalizedActualBinKernel
      (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₁)) (Tbin k) (hTbin k) (fallbackT k)
    ((((lambda.restrict L) ⊗ₘ finiteClassPopulationKernel Pf α β).map sameLabelPopulationPair).map
      (Prod.map b b)) =
      ((κ C.seedIndex).restrict (R '' L) ⊗ₘ finiteClassPopulationKernel (fun _ j k ↦ P₀ j k) αc βc).map
        (labelClockPairPhysicalMap (populationSeedPhysicalMap Seed)) := by
  classical
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue Seed a
  let α := fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Sbin j) (hSbin j) (fallbackS j)
  let β := fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Tbin k) (hTbin k) (fallbackT k)
  let KP := finiteClassPopulationKernel Pf α β
  have hmarginals : ∀ᵐ z ∂lambda.restrict L,
      (KP z).map Prod.fst ≤ condDistrib u a η₀ z ∧ (KP z).map Prod.snd ≤ condDistrib u a η₁ z :=
    hwhole.mono fun z hz ↦ clockPair_marginals_le_of_original_split _ _ _ _ hz
  have hphysical := D.haar.original_retained_pair_physical_law_eq_seed hF hcomplete hu ha hinj horder hb
    hη₀reg hη₁reg hη₀inv hη₁inv hlabel0 hlabel1 i hL hsub KP hmarginals
  have hhaar := D.actual_retained_cell_pair_law_eq_haar hF hcomplete hu ha hinj i hL hsub
    Sbin Tbin hSbin hTbin fallbackS fallbackT P₀ Pf hmPf hPf
  dsimp only
  rw [sameLabelPair_physical_map_eq _ _ b hb]
  exact hphysical.trans (congrArg (fun μ ↦ μ.map (labelClockPairPhysicalMap (populationSeedPhysicalMap Seed))) hhaar)

end OTSelector.Reconstruction
