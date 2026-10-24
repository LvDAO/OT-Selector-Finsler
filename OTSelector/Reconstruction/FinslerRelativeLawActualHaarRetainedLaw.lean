import OTSelector.Probability.KernelDensityCoordinateCancellation
import OTSelector.Transport.Coupling.WindowPairFlow
import OTSelector.Probability.FiniteClassThinning
import OTSelector.Reconstruction.FinslerPopulationHaarCellLaws
import OTSelector.Reconstruction.FinslerCoefficientCoreOscillation

/-!
The actual original pressure core identifies retained normalized reference
pair laws with fixed pair-class laws over the original Haar cell. Original
coordinate pushforward, finite positive density and normalized within-bin clock
identities are all derived from the stored original core data.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Normalized original bin laws depend only on their literal conditional measure. -/
theorem normalizedActualBinKernel_apply_congr
    {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W] [MeasurableSpace X]
    (κ : Kernel Z X) (η : Kernel W X) (B : Set X) (hB : MeasurableSet B)
    (fallback : X) (z : Z) (w : W) (h : κ z = η w) :
    normalizedActualBinKernel κ B hB fallback z = normalizedActualBinKernel η B hB fallback w := by
  change (if κ z B = 0 then Measure.dirac fallback else (κ z B)⁻¹ • (κ z).restrict B) =
    (if η w B = 0 then Measure.dirac fallback else (η w B)⁻¹ • (η w).restrict B)
  rw [h]

/-- The literal window-mask formula has the fixed numerator required by
original Haar-cell density cancellation. -/
theorem maskedClockFlow_normalized_reference
    {I J : Type*} (keep : I → J → Prop) (A : I → J → ℝ)
    (θ d₀ d : ℝ) (i : I) (j : J) :
    maskedClockFlow keep (fun i j ↦ θ * (d₀ * A i j) / d) i j =
      (θ * d₀ * maskedClockFlow keep A i j) / d := by
  classical
  by_cases h : keep i j
  · simp only [maskedClockFlow, ite_eq_left h]
    ring
  · simp only [maskedClockFlow, ite_eq_right h, mul_zero, zero_div]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual original normalized reference flow becomes the literal fixed
pair-class flow over the original Haar cell, retaining its original in-bin
clock kernels. All coordinate, density and positivity identities are discharged
from the original pressure core. -/
theorem PopulationLocalPressureCore.actual_retained_cell_pair_law_eq_haar
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {I J : Type*} [Fintype I] [Fintype J]
    (Sbin : I → Set ℝ) (Tbin : J → Set ℝ)
    (hSbin : ∀ j, MeasurableSet (Sbin j)) (hTbin : ∀ k, MeasurableSet (Tbin k))
    (fallbackS : I → ℝ) (fallbackT : J → ℝ)
    (P₀ : I → J → ℝ) (Pf : (ℚ → M) → I → J → ℝ)
    (hmPf : ∀ j k, Measurable (fun z ↦ Pf z j k))
    (hPf : ∀ z ∈ L, ∀ j k, Pf z j k = P₀ j k / D.rootIntensity i z) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue Seed a
    let α := fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Sbin j) (hSbin j) (fallbackS j)
    let β := fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Tbin k) (hTbin k) (fallbackT k)
    let αc := fun j ↦ normalizedActualBinKernel
      (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₀)) (Sbin j) (hSbin j) (fallbackS j)
    let βc := fun k ↦ normalizedActualBinKernel
      (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₁)) (Tbin k) (hTbin k) (fallbackT k)
    (((lambda.restrict L) ⊗ₘ finiteClassPopulationKernel Pf α β).map (Prod.map R id)) =
      (κ C.seedIndex).restrict (R '' L) ⊗ₘ finiteClassPopulationKernel (fun _ j k ↦ P₀ j k) αc βc := by
  classical
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue Seed a
  let f := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  let d := fun w ↦ (f w).toReal
  let m := (κ C.seedIndex).restrict (R '' L)
  let α := fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Sbin j) (hSbin j) (fallbackS j)
  let β := fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Tbin k) (hTbin k) (fallbackT k)
  let αc := fun j ↦ normalizedActualBinKernel
    (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₀)) (Sbin j) (hSbin j) (fallbackS j)
  let βc := fun k ↦ normalizedActualBinKernel
    (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₁)) (Tbin k) (hTbin k) (fallbackT k)
  have hR : Measurable R := measurable_populationSeedRootLabelValue Seed hF hcomplete hu ha hinj
  have hd : Measurable d :=
    (measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj C.seedIndex).ennreal_toReal
  have hsub' : L ⊆ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
  have himage : MeasurableSet (R '' L) := D.haar.measurable_cell_label_image hcomplete i hL hsub
  have hfinite (w) (hw : w ∈ R '' L) : f w ≠ (∞ : ℝ≥0∞) := by
    obtain ⟨z, hz, rfl⟩ := hw
    rw [show f (R z) = populationSeedPieceRootDensity P a κ lambda C.seedIndex z from
      populationSeedPieceHaarDensity_at_root P a κ lambda hF hcomplete hu ha hinj
        C.seedIndex (C.roots_subset_piece (hsub hz))]
    exact ((D.haar.intensity i).finite_density z (hsub' hz)).ne
  have hbase : (lambda.restrict L).map R = m.withDensity (fun w ↦ ENNReal.ofReal (d w)) := by
    rw [map_populationSeedCore_eq_withDensity P a κ lambda hF hcomplete hu ha hinj
      C.seedIndex hL (hsub.trans C.roots_subset_piece)]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem himage] with w hw
    exact (ENNReal.ofReal_toReal (hfinite w hw)).symm
  have hpos : ∀ᵐ w ∂m, 0 < d w := by
    filter_upwards [ae_restrict_mem himage] with w hw
    exact (D.haar.intensity i).lower_pos.trans_le
      (((D.haar.intensity i).bounds w (image_mono hsub' hw)).1)
  apply compProd_original_coordinate_density_cancel_classFlow
    (lambda.restrict L) m R hR d hd hpos hbase P₀ αc βc
    (finiteClassPopulationKernel Pf α β)
  filter_upwards [ae_restrict_mem hL] with z hz
  have hzI : z ∈ (D.haar.intensity i).roots := hsub' hz
  let w : Seed.labels := ⟨R z, (D.haar.intensity i).labels_subset (mem_image_of_mem R hzI)⟩
  have hroot : a (Seed.curve w 0) = z := (D.haar.intensity i).root_identity z hzI
  have hκ₀ : populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₀) (R z) =
      condDistrib u a η₀ z := by
    rw [show R z = (w : Seed.covector.ker) from rfl, populationSeedCoordinateClockKernel_at_label, hroot]
  have hκ₁ : populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₁) (R z) =
      condDistrib u a η₁ z := by
    rw [show R z = (w : Seed.covector.ker) from rfl, populationSeedCoordinateClockKernel_at_label, hroot]
  have hα (j) : αc j (R z) = α j z := normalizedActualBinKernel_apply_congr _ _ _ _ _ _ _ hκ₀
  have hβ (k) : βc k (R z) = β k z := normalizedActualBinKernel_apply_congr _ _ _ _ _ _ _ hκ₁
  have hm (j k) : Measurable (fun w ↦ P₀ j k / d w) :=
    measurable_div.comp (measurable_const.prodMk hd)
  rw [finiteClassPopulationKernel_apply Pf hmPf α β z,
    finiteClassPopulationKernel_apply _ hm αc βc (R z)]
  have hαfun : (fun j ↦ αc j (R z)) = (fun j ↦ α j z) := funext hα
  have hβfun : (fun k ↦ βc k (R z)) = (fun k ↦ β k z) := funext hβ
  rw [hαfun, hβfun]
  apply congrArg (fun p ↦ finiteClassPopulationCoupling p (fun j ↦ α j z) (fun k ↦ β k z))
  funext j k
  exact hPf z hz j k

end OTSelector.Reconstruction
