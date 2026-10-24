import OTSelector.Reconstruction.FinslerOriginalSharpFamilyAssignmentPressureUpper
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedPopulation

/-! The original physical sharp population factory also supplies its actual
limiting finite-family full-assignment pressure upper. -/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
universe u₁ u₂
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {E : Type u₁} {M : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The pressure conclusion of one actual original weighted population:
literal finite-class pressure limits and the original full iid assignment
upper, with its explicit physical geometry and once-counted residual errors. -/
def PopulationLocalPressureCore.originalWeightLimitingPressureData
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ) (f : M × M →ᵇ ℝ) (ε probeError : ℝ) : Prop :=
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
      ∃ limit : Cell → ℝ → ℝ,
        (∀ c,
          let C := D.haar.continuous.coefficient (coreIndex c)
          let _instClass := normalizedClockClassPairMeasure_probability (P₀ c) (hP₀ c) (hmass c)
          let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
          let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
          let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
          let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
          let density := cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
          ∀ tilt, Tendsto (fun L : ℝ ↦ finiteClassLegalPressure (q c) (C.clockClassAllowed (Qlocal c)) α β
            (density * Real.toNNReal (L ^ (q c))) (C.densityClockClassKinetic (Qlocal c) (reference c).val density)
            (C.clockClassProbe (Qlocal c) (reference c).val (reference c).property f) tilt / L ^ (q c))
            atTop (𝓝 (limit c tilt))) ∧
        ∀ tilt : ℝ,
          let iid := fun n ↦ (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
          let assignment := fun n (sample : (Fin n → M) × (Fin n → M)) ↦ perturbedAssignmentValue
            (fun i j ↦ (n : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
              tilt * f (sample.1 i,sample.2 j)) 0 0
          let geometry := (3 * ε + 2 * ε ^ 2) *
              (A / (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * ‖f‖ + 1) +
            (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖))
          let residual := (ENNReal.ofReal (retentionError + splitError + δ.toReal) +
            (μ.map a) D.haar.continuous.population.rootsᶜ).toReal
          (∀ n, 0 < n → Integrable (assignment n) (iid n)) ∧
          ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop,
            (∫ sample, assignment n sample ∂iid n) / n ≤
              (∑ c, volume.real ((coord c) '' cell c) * limit c tilt) + geometry +
                (A * residual ^ (1 - 2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) +
                  2 * |tilt| * ‖f‖ * residual) + ζ

/-- The existing actual original sharp population data discharge every
finite-family pressure input, including the same global population, atlas,
classifier, actual class weights and sharp empirical comparison. The full
original iid assignment is bounded by its literal limiting class pressures,
the existing geometry error and one explicitly bounded original residual. -/
theorem PopulationLocalPressureCore.originalWeightSharpPairedPopulationData_pressure_upper
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ) (f : M × M →ᵇ ℝ) (ε probeError : ℝ)
    (ha : Measurable a) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    (hbalance : ν.map a = μ.map a)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hdim : 6 ≤ Module.finrank ℝ E)
    (hdata : D.originalWeightSharpPairedPopulationData γ originalGap Q U retentionError splitError f ε probeError ha) :
    D.originalWeightLimitingPressureData γ originalGap Q U retentionError splitError f ε probeError := by
  classical
  rcases hdata with ⟨T,hT,quadC,Bnd,forwardGap,hquad,hB,hfg,N,refs,cells,Pf,Qf,hcells,
    hsub,hPfM,hQfM,hfields,hweights,hdensity,hdisj,hcover,Qglobal,hQglobal,hwhole,
    ξ,hχfinite,hξfinite,hπ,hcal,hξmass,Cst,hquadEq,hBEq,hfgood,classify,hclassM,hclass,hsharp,hpaired⟩
  letI : Fintype T := hT
  let Cell := Sigma (fun i ↦ Fin (N i))
  let coreIndex := fun c : Cell ↦ c.1
  let reference := fun c : Cell ↦ refs c.1 c.2
  let cell := fun c : Cell ↦ cells c.1 c.2
  let hcell := fun c : Cell ↦ hcells c.1 c.2
  let Qlocal := fun c : Cell ↦ Q c.1 (reference c)
  let P₀ := fun c : Cell ↦ D.originalWindowReferenceWeights γ originalGap I c.1 (reference c) (Qlocal c) retentionError
  letI : MeasurableSpace (Option (Bool × T)) := ⊤
  letI : MeasurableSingletonClass (Option (Bool × T)) := ⟨fun _ ↦ trivial⟩
  let α := fun (c : Cell) j ↦ normalizedActualBinKernel (condDistrib u a μ)
    ((Qlocal c).cell j) ((Qlocal c).measurable_cell j) 0
  let β := fun (c : Cell) k ↦ normalizedActualBinKernel (condDistrib u a ν)
    ((Qlocal c).cell k) ((Qlocal c).measurable_cell k) 0
  let KP := fun c : Cell ↦ finiteClassPopulationKernel (Pf c.1 c.2) (α c) (β c)
  let χ := (((μ.map a) ⊗ₘ finiteCellPairKernel cell hcell KP).map
    sameLabelPopulationPair).map (Prod.map b b)
  letI : IsFiniteMeasure χ := hχfinite
  letI : IsFiniteMeasure ξ := hξfinite
  letI : IsSFiniteKernel Qglobal := hQglobal
  letI (c : Cell) : (κ (D.haar.continuous.coefficient (coreIndex c)).seedIndex).IsAddHaarMeasure := hκ _
  have hP₀ : ∀ c j k, 0 ≤ P₀ c j k := fun c ↦ (hweights c.1 c.2).1
  have hmass : ∀ c, 0 < ∑ j, ∑ k, P₀ c j k := fun c ↦ (hweights c.1 c.2).2.2.2
  have hres (c : Cell) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ j k, 0 ≤ Qf c.1 c.2 z j k := by
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.1
  have hrow (c : Cell) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ j,
      (∑ k, (Pf c.1 c.2 z j k + Qf c.1 c.2 z j k)) = (condDistrib u a μ z).real ((Qlocal c).cell j) := by
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.2.1
  have hcol (c : Cell) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ k,
      (∑ j, (Pf c.1 c.2 z j k + Qf c.1 c.2 z j k)) = (condDistrib u a ν z).real ((Qlocal c).cell k) := by
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.2.2.1
  obtain ⟨cHaar,hcHaar,hmap,limit,hlimit,hupper⟩ := D.exists_original_sharp_family_assignment_pressure_upper
    hF hcomplete hu ha hinj coreIndex cell hcell (fun c z hz ↦ (hsub c.1 c.2 hz).1)
    hdisj Qlocal reference classify hclassM hclass (fun _ _ ↦ 0) (fun _ _ ↦ 0)
    P₀ hP₀ hmass (fun c ↦ (hweights c.1 c.2).2.1)
    (fun c ↦ Pf c.1 c.2) (fun c ↦ Qf c.1 c.2) (fun c ↦ hPfM c.1 c.2)
    (fun c ↦ hdensity c.1 c.2) hres hrow hcol KP (fun _ ↦ rfl) Qglobal hwhole
    hb hμinv hνinv hbalance χ ξ rfl hπ Cst f hdim ε probeError hsharp
  let q := Module.finrank ℝ E - 1
  let A := Cst.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ))
  have hq : 4 < q := by dsimp only [q]; omega
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg Cst.quadratic_nonneg (dyadicMatchingConstant_pos hq).le)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨N,refs,cells,hcells,hsub,hP₀,hmass,A,hA,cHaar,hcHaar,hmap,limit,hlimit,?_⟩
  intro tilt
  refine ⟨(hupper tilt).1,?_⟩
  intro ζ hζ
  filter_upwards [(hupper tilt).2 ζ hζ] with n hn
  let residual := (ENNReal.ofReal (retentionError + splitError + δ.toReal) +
    (μ.map a) D.haar.continuous.population.rootsᶜ).toReal
  have hξreal : (ξ univ).toReal ≤ residual := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,measure_ne_top _ _⟩) hξmass
  have hexp : 0 ≤ 1 - 2 / (q : ℝ) := by
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    exact sub_nonneg.mpr ((div_le_one hqpos).mpr hqR)
  have hrepair : A * (ξ univ).toReal ^ (1 - 2 / (q : ℝ)) + 2 * |tilt| * ‖f‖ * (ξ univ).toReal ≤
      A * residual ^ (1 - 2 / (q : ℝ)) + 2 * |tilt| * ‖f‖ * residual :=
    add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ENNReal.toReal_nonneg hξreal hexp) hA)
      (mul_le_mul_of_nonneg_left hξreal (by positivity))
  exact hn.trans (add_le_add (add_le_add (le_refl _) hrepair) (le_refl ζ))

end OTSelector.Reconstruction
