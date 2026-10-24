import OTSelector.Reconstruction.FinslerRelativeLawActualPhysicalHaarLaw
import OTSelector.Reconstruction.FinslerRelativeLawRetainedFlagSampling

/-!
The literal Haar-cell retained law is realized in the SAME original RN-marked
iid experiment as the uniform rebuilt residual repair. Only geometric atlas
marks are forgotten; all retained/residual flags and original positions remain.
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

/-- The same original marked samples carrying the quantitative residual
repair have an exact independent mixture of the literal Haar retained endpoint
laws and the unchanged original residual endpoint laws. No retained-sample
distribution premise is supplied. -/
theorem PopulationLocalPressureCore.actual_original_retained_iid_flag_law_eq_haar
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
        (finiteClassPopulationKernel Pf α β z + Q z) (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    (πWhole ξ : Measure (M × M)) [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
    (hsplit : πWhole =
      ((((lambda.restrict L) ⊗ₘ finiteClassPopulationKernel Pf
        (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Sbin j) (hSbin j) (fallbackS j))
        (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Tbin k) (hTbin k) (fallbackT k))).map
          sameLabelPopulationPair).map (Prod.map b b)) + ξ)
    {T : Type*} [Fintype T] {q : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData πWhole η₀ η₁ T q cost)
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {NS NT : Type*} [Fintype NS] [Fintype NT] :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue Seed a
    let αc := fun j ↦ normalizedActualBinKernel
      (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₀)) (Sbin j) (hSbin j) (fallbackS j)
    let βc := fun k ↦ normalizedActualBinKernel
      (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₁)) (Tbin k) (hTbin k) (fallbackT k)
    let H := ((κ C.seedIndex).restrict (R '' L) ⊗ₘ
      finiteClassPopulationKernel (fun _ j k ↦ P₀ j k) αc βc).map
        (labelClockPairPhysicalMap (populationSeedPhysicalMap Seed))
    let hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
    let Refined := Cst.refineSubplan ξ hξ
    ((Measure.pi (fun _ : NS ↦ Refined.types.sourceMarkedLaw η₀)).prod
      (Measure.pi (fun _ : NT ↦ Refined.types.targetMarkedLaw η₁))).map
        (Prod.map (fun x i ↦ ((x i).1, subplanRetentionFlag (x i).2))
          (fun y j ↦ ((y j).1, subplanRetentionFlag (y j).2))) =
      (Measure.pi (fun _ : NS ↦
        (H.map Prod.fst).map (fun x ↦ (x, false)) +
          (ξ.map Prod.fst).map (fun x ↦ (x, true)))).prod
      (Measure.pi (fun _ : NT ↦
        (H.map Prod.snd).map (fun y ↦ (y, false)) +
          (ξ.map Prod.snd).map (fun y ↦ (y, true)))) := by
  have hphysical := D.actual_original_retained_physical_pair_law_eq_haar hF hcomplete hu ha
    hinj horder hb hη₀reg hη₁reg hη₀inv hη₁inv hlabel0 hlabel1 i hL hsub
    Sbin Tbin hSbin hTbin fallbackS fallbackT P₀ Pf hmPf hPf Q hwhole
  dsimp only at hphysical ⊢
  have hsample := Cst.refineSubplan_flagged_iid_law (I := NS) (J := NT) hπWhole ξ
    (show ξ ≤ πWhole from by rw [hsplit]; exact Measure.le_add_left le_rfl)
  dsimp only at hsample
  have hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
  let _instξ : IsFiniteMeasure ξ := isFiniteMeasure_of_le πWhole hξ
  let χ := ((((lambda.restrict L) ⊗ₘ finiteClassPopulationKernel Pf
    (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Sbin j) (hSbin j) (fallbackS j))
    (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Tbin k) (hTbin k) (fallbackT k))).map
      sameLabelPopulationPair).map (Prod.map b b))
  have hcancel : πWhole - ξ = χ := by rw [hsplit, Measure.add_sub_cancel]
  have hdiff := hcancel.trans hphysical
  simp_rw [hdiff] at hsample
  exact hsample

end OTSelector.Reconstruction
