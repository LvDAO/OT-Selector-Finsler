import OTSelector.Reconstruction.FinslerOriginalPhysicalUnitDensityPressureUpper
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSupportedProbeExtension
import OTSelector.Reconstruction.FinslerOriginalIIDPressureUpperLocalization
import OTSelector.Limit.FinslerMeanTiltSupergradient

/-!
# The original unit-density pressure upper for supported probes and actual iid arrays

The compact-carrier probe is extended with its exact norm, and the unchanged
original full assignment upper is transferred to arbitrary iid sample spaces.
The original frozen cells, their Haar density powers, their unit-density legal
pressures, and every geometry and discarded-mass error remain explicit.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
universe u₁ u₂ u₃
namespace OTSelector.Reconstruction
open OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {E : Type u₁} {M : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- An ambient probe agreeing on the carrier gives the exact same expected
empirical pressure under the original iid law, with the physical mean scale. -/
theorem integral_finslerSupportedPressure_eq_original_assignment
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {Ω : Type u₃} [MeasurableSpace Ω] (R : Measure Ω) [IsProbabilityMeasure R]
    {n : ℕ} (X Y : Fin (n + 1) → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : iIndepFun X R) (hYi : iIndepFun Y R)
    (hXlaw : ∀ i, R.map (X i) = (μ : Measure M))
    (hYlaw : ∀ j, R.map (Y j) = (ν : Measure M))
    (hXY : IndepFun (fun ξ i ↦ X i ξ) (fun ξ j ↦ Y j ξ) R)
    (u : M → ℝ) (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (f : (K × K) →ᵇ ℝ) (g : (M × M) →ᵇ ℝ)
    (hg : ∀ x ∈ K, ∀ y ∈ K, g (x,y) =
      f (supportProjection μ K hK.measurableSet hμ x,
        supportProjection ν K hK.measurableSet hν y)) (tilt : ℝ) :
    (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
      (fun i ↦ X i ξ) (fun j ↦ Y j ξ) u (finslerMeanScale E n) f tilt ∂R) =
    (∫ sample : (Fin (n + 1) → M) × (Fin (n + 1) → M),
      perturbedAssignmentValue (fun i j ↦ finslerMeanScale E n *
        ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal -
          u (sample.2 j) + u (sample.1 i)) + tilt * g (sample.1 i,sample.2 j)) 0 0
      ∂canonicalLaw μ ν n) / (n + 1 : ℕ) := by
  letI : MetricSpace M := F.metricSpace
  rw [integral_finslerSupportedPressure_eq_canonicalLaw hcomplete μ ν K
    hK.measurableSet hμ hν R X Y hX hY hXi hYi hXlaw hYlaw hXY u hu]
  rw [← integral_div]
  apply integral_congr_ae
  have hx : ∀ᵐ sample ∂canonicalLaw μ ν n, ∀ i, canonicalX n i sample ∈ K := by
    apply ae_all_iff.mpr
    intro i
    have hm : ∀ᵐ x ∂(canonicalLaw μ ν n).map (canonicalX n i), x ∈ K := by
      rw [canonicalLaw_map_canonicalX]
      exact hμ
    exact ae_of_ae_map (measurable_canonicalX n i).aemeasurable hm
  have hy : ∀ᵐ sample ∂canonicalLaw μ ν n, ∀ j, canonicalY n j sample ∈ K := by
    apply ae_all_iff.mpr
    intro j
    have hm : ∀ᵐ y ∂(canonicalLaw μ ν n).map (canonicalY n j), y ∈ K := by
      rw [canonicalLaw_map_canonicalY]
      exact hν
    exact ae_of_ae_map (measurable_canonicalY n j).aemeasurable hm
  filter_upwards [hx,hy] with sample hx hy
  have heq : perturbedEdgeCost
      (fun i j ↦ finslerMeanScale E n *
        ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal -
          u (sample.2 j) + u (sample.1 i)))
      (fun i j ↦ f (supportProjection μ K hK.measurableSet hμ (sample.1 i),
        supportProjection ν K hK.measurableSet hν (sample.2 j))) tilt =
      (fun i j ↦ finslerMeanScale E n *
        ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal -
          u (sample.2 j) + u (sample.1 i)) + tilt * g (sample.1 i,sample.2 j)) := by
    funext i j
    exact congrArg (fun z ↦ finslerMeanScale E n *
      ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal -
        u (sample.2 j) + u (sample.1 i)) + tilt * z)
      (hg _ (hx i) _ (hy j)).symm
  simp only [finslerSupportedPressure, Pressure.supportedDistancePressure,
    distanceSlackEdgeCost, perturbedAssignmentValue, perturbedEdgeCost_zero]
  exact congrArg (fun cost : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ↦
    assignmentCost cost (optimalAssignment cost) / ((n + 1 : ℕ) : ℝ)) heq

variable {u : M → ℝ} {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : ProbabilityMeasure M} {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ}
  {b : (ℚ → M) × ℝ → M} {r : ℝ} {δ loss : ℝ≥0∞}
  {Ω : ℕ → Type u₃} [∀ n, MeasurableSpace (Ω n)]

/-- The original frozen-cell pressure upper for the supported original iid
experiment. The ambient extension appears only in the literal local class
probe; every physical error uses the exact supported-probe norm. -/
def PopulationLocalPressureCore.originalSupportedWeightUnitDensityPressureData
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ ((μ : Measure M).map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (f : (K × K) →ᵇ ℝ) (g : (M × M) →ᵇ ℝ) (ε probeError : ℝ)
    (R : ∀ n, Measure (Ω n)) (X Y : ∀ n, Fin (n + 1) → Ω n → M) : Prop :=
    ∃ (N : Fin D.haar.continuous.count → ℕ)
      (refs : ∀ i, Fin (N i) → (D.haar.continuous.coefficient i).roots)
      (cells : ∀ i, Fin (N i) → Set (ℚ → M))
      (_hcells : ∀ i c, MeasurableSet (cells i c)),
      (∀ i c, cells i c ⊆ (D.haar.continuous.coefficient i).roots ∩ U i (refs i c)) ∧
      let Cell := Sigma (fun i ↦ Fin (N i))
      let coreIndex := fun c : Cell ↦ c.1
      let reference := fun c : Cell ↦ refs c.1 c.2
      let cell := fun c : Cell ↦ cells c.1 c.2
      let Qlocal := fun c : Cell ↦ Q c.1 (reference c)
      let P₀ := fun c : Cell ↦ D.originalWindowReferenceWeights γ originalGap I c.1 (reference c) (Qlocal c) retentionError
      let Seed := fun c : Cell ↦ (P (D.haar.continuous.coefficient c.1).seedIndex).seed
      let q := fun c ↦ Module.finrank ℝ (Seed c).covector.ker
      let coord := fun c ↦ atlasSeedCoord (Seed c) (Module.finBasis ℝ (Seed c).covector.ker).equivFunL a
      ∃ (hP₀ : ∀ c j k, 0 ≤ P₀ c j k) (hmass : ∀ c, 0 < ∑ j, ∑ k, P₀ c j k),
      ∃ (A : ℝ), 0 ≤ A ∧ ∃ cHaar : Cell → ℝ≥0, (∀ c, 0 < cHaar c) ∧
      (∀ c, (κ (D.haar.continuous.coefficient c.1).seedIndex).map
        (Module.finBasis ℝ (Seed c).covector.ker).equivFunL =
        (cHaar c : ℝ≥0∞) • (volume : Measure (Fin (q c) → ℝ))) ∧
      ∃ unitPressure : Cell → ℝ → ℝ,
        (∀ c,
          let C := D.haar.continuous.coefficient (coreIndex c)
          let _instClass := normalizedClockClassPairMeasure_probability (P₀ c) (hP₀ c) (hmass c)
          let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
          let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
          let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
          let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
          ∀ tilt, Tendsto (fun L : ℝ ↦ finiteClassLegalScalePressure (q c)
            (C.clockClassAllowed (Qlocal c)) α β
            (C.clockClassKinetic (Qlocal c) (reference c).val)
            (C.clockClassProbe (Qlocal c) (reference c).val (reference c).property g) L tilt)
            atTop (𝓝 (unitPressure c tilt))) ∧
        ∀ tilt : ℝ,
          let geometry := (3 * ε + 2 * ε ^ 2) *
              (A / (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * ‖f‖ + 1) +
            (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖))
          let residual := (ENNReal.ofReal (retentionError + splitError + δ.toReal) +
            ((μ : Measure M).map a) D.haar.continuous.population.rootsᶜ).toReal
          ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop,
            (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
              (fun i ↦ X n i ξ) (fun j ↦ Y n j ξ) u (finslerMeanScale E n) f tilt ∂R n) ≤
              (∑ c,
                let density : ℝ≥0 := cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
                volume.real ((coord c) '' cell c) * (density : ℝ) ^ (1 - 2 / (q c : ℝ)) *
                  unitPressure c (tilt * (density : ℝ) ^ (2 / (q c : ℝ)))) + geometry +
                (A * residual ^ (1 - 2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) +
                  2 * |tilt| * ‖f‖ * residual) + ζ

/-- The actual original iid supported expectation inherits the complete
unit-density cell upper, with the same local pressures and explicit errors. -/
theorem PopulationLocalPressureCore.originalWeightUnitDensityPressureData_supported_iid
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ ((μ : Measure M).map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (f : (K × K) →ᵇ ℝ) (g : (M × M) →ᵇ ℝ) (ε probeError : ℝ)
    (R : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (R n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (R n)) (hYi : ∀ n, iIndepFun (Y n) (R n))
    (hXlaw : ∀ n i, (R n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n j, (R n).map (Y n j) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun ξ i ↦ X n i ξ) (fun ξ j ↦ Y n j ξ) (R n))
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hgnorm : ‖g‖ = ‖f‖)
    (hg : ∀ x ∈ K, ∀ y ∈ K, g (x,y) =
      f (supportProjection μ K hK.measurableSet hμ x,
        supportProjection ν K hK.measurableSet hν y))
    (hdata : D.originalWeightUnitDensityPressureData γ originalGap Q U
      retentionError splitError g ε probeError) :
    D.originalSupportedWeightUnitDensityPressureData γ originalGap Q U
      retentionError splitError K hK hμ hν f g ε probeError R X Y := by
  classical
  rcases hdata with ⟨N,refs,cells,hcells,hsub,hP₀,hmass,A,hA,cHaar,hcHaar,hmap,
    unitPressure,hunit,hupper⟩
  refine ⟨N,refs,cells,hcells,hsub,hP₀,hmass,A,hA,cHaar,hcHaar,hmap,
    unitPressure,hunit,?_⟩
  intro tilt
  dsimp only
  intro ζ hζ
  have hup := (tendsto_add_atTop_nat 1).eventually ((hupper tilt).2 ζ hζ)
  filter_upwards [hup] with n hn
  rw [integral_finslerSupportedPressure_eq_original_assignment hcomplete μ ν K hK
    hμ hν (R n) (X n) (Y n) (hX n) (hY n) (hXi n) (hYi n)
    (hXlaw n) (hYlaw n) (hXY n) u hu f g hg tilt]
  simpa only [finslerMeanScale, canonicalLaw, twoColourLaw, hgnorm] using hn

/-- Actual calibrated original physical data yield the supported empirical
expected upper on the paper's arbitrary genuine iid sample spaces. This keeps
all geometric and residual errors explicit and asserts no exact final-pressure
identification. -/
theorem exists_original_physical_unit_density_supported_upper
    (hcore : PopulationHaarPressureCoreLaw P a κ ((μ : Measure M).map a) μ ν ρ₀ ρ₁ v b r)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂(μ : Measure M), x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂(ν : Measure M), y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂(μ : Measure M), b (a x,u x) = x) (hνinv : ∀ᵐ y ∂(ν : Measure M), b (a y,u y) = y)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    (πOriginal : Measure (M × M)) (hπOriginal : Vlasov.IsCoupling πOriginal μ ν)
    (hcalOriginal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂πOriginal, u p.2 - u p.1 = dist p.1 p.2)
    (hδne : δ ≠ 0) (hlossne : loss ≠ 0) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (retentionError splitError : ℝ) (hretention : 0 < retentionError)
    (hretention1 : retentionError < 1) (hsplitError : 0 < splitError)
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (f : (K × K) →ᵇ ℝ)
    (R : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (R n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (R n)) (hYi : ∀ n, iIndepFun (Y n) (R n))
    (hXlaw : ∀ n i, (R n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n j, (R n).map (Y n j) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun ξ i ↦ X n i ξ) (fun ξ j ↦ Y n j ξ) (R n))
    {ε probeError : ℝ} (hε : 0 < ε) (hprobe : 0 < probeError)
    (hsmall : 3 * ε + 2 * ε ^ 2 < 1) (hq : 4 < Module.finrank ℝ E - 1) :
    ∃ g : (M × M) →ᵇ ℝ, ‖g‖ = ‖f‖ ∧
    (∀ x ∈ K, ∀ y ∈ K, g (x,y) =
      f (supportProjection μ K hK.measurableSet hμK x,
        supportProjection ν K hK.measurableSet hνK y)) ∧
    ∃ (I : Set ℝ), IsCompact I ∧ ∃ originalGap : ℝ, 0 < originalGap ∧
    ∃ γ : Kernel (ℚ → M) (ℝ × ℝ), IsMarkovKernel γ ∧
    ∃ D : PopulationLocalPressureCore P a κ ((μ : Measure M).map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss,
    ∃ (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
      (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M)),
      D.originalSupportedWeightUnitDensityPressureData γ originalGap Q U
        retentionError splitError K hK hμK hνK f g ε probeError R X Y := by
  letI : MetricSpace M := F.metricSpace
  obtain ⟨g,hgnorm,hg,_⟩ :=
    exists_original_supported_probe_ambient_extension μ ν K hK hμK hνK f
  obtain ⟨I,hI,originalGap,hgap,γ,hγ,D,Q,U,hdata⟩ :=
    exists_original_physical_unit_density_pressure_upper hcore hκ hF hcomplete hu ha hinj
      horder hb hμreg hνreg hμinv hνinv hA hB hAB hμA hνB
      πOriginal hπOriginal hcalOriginal hδne hlossne hδ hδ1
      retentionError splitError hretention hretention1 hsplitError g hε hprobe hsmall hq
  refine ⟨g,hgnorm,hg,I,hI,originalGap,hgap,γ,hγ,D,Q,U,?_⟩
  exact D.originalWeightUnitDensityPressureData_supported_iid hcomplete γ originalGap Q U
    retentionError splitError K hK hμK hνK f g ε probeError R X Y
    hX hY hXi hYi hXlaw hYlaw hXY hu hgnorm hg hdata

end OTSelector.Reconstruction
