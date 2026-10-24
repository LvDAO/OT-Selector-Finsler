import OTSelector.MeasureTheory.LabelClockWindowDensities
import OTSelector.Reconstruction.FinslerMeasuredAtlas
import OTSelector.Probability.LabelClockConditionalDensity
import OTSelector.Transport.Coupling.LabelClockCoordinates

/-!
# Original conditional laws from actual calibrated window densities

One measured Finsler atlas supplies both original laws with the same potential,
labels, window enumeration and measurable inverse. The explicit window mass
Radon–Nikodym sums have normalized sections equal to the existing scalar
conditionals, while the whole optimal face and geometric pullback formulas persist.
-/

open Set MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace OTSelector.Reconstruction

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : Geometry.ContinuousFinslerNorm E M}

/-- One original measured atlas supplies the same labels and clock for both laws.
The actual countable window mass densities on their common label reference have
normalized sections equal to the existing scalar conditionals. A single measurable
inverse reconstructs all original nonnegative observables. The full earlier
optimal-face, scalar-volume and per-window geometric density outputs are retained. -/
theorem exists_finsler_conditional_window_atlas (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instMeasuredAtlasMetric : MetricSpace M := F.metricSpace
    let _instMeasuredAtlasProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instMeasuredAtlasBorel : StandardBorelSpace M := inferInstance
    let _instMeasuredAtlasNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
    ∃ (u : M → ℝ) (a : M → (ℚ → M)), LipschitzWith 1 u ∧
      MeasurableSet (F.potentialRegularDomain u) ∧
      (∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u) ∧
      (∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u) ∧ Measurable a ∧
      Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)) ∧
      (∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) ∧
      μ.map a = ν.map a ∧
      (∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ κ : Kernel (ℚ → M) (M × M), IsMarkovKernel κ ∧ κ ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂κ z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2) ∧
      (∀ᵐ x ∂μ, x ∈ calibratedInterior u) ∧
      (∀ᵐ y ∂ν, y ∈ calibratedInterior u) ∧
      μ.map (fun x ↦ (a x, u x)) ≪ (μ.map a).prod volume ∧
      ν.map (fun x ↦ (a x, u x)) ≪ (ν.map a).prod volume ∧
      (∀ᵐ z ∂μ.map a,
        condDistrib u a μ z ≪ volume ∧ condDistrib u a ν z ≪ volume ∧
        (condDistrib id a μ z).map u ≪ volume ∧
        (condDistrib id a ν z).map u ≪ volume) ∧
      ∃ ι : Type (max u v), Countable ι ∧
        ∃ P : ι → F.CalibratedSeedWindow u,
          (⋃ i, (P i).toManifold '' (P i).domain) = calibratedInterior u ∧
          (∀ᵐ x ∂μ, x ∈ ⋃ i, (P i).toManifold '' (P i).domain) ∧
          (∀ᵐ y ∂ν, y ∈ ⋃ i, (P i).toManifold '' (P i).domain) ∧
          (∀ i,
            (∀ z ∈ (P i).domain,
              a ((P i).toManifold z) = a ((P i).seed.curve z.2 0)) ∧
            MeasurableEmbedding (fun w : (P i).labels ↦ a ((P i).seed.curve w 0)) ∧
            ∀ η : Measure M, η = μ ∨ η = ν →
              let χ := extChartAt 𝓘(ℝ, E) ((P i).toManifold (P i).center)
              let ρ := ((η.restrict χ.source).map χ).rnDeriv m
              let μpar := tubeParameterMeasure (P i).seed.normalization m
              η.comap (fun z : (P i).domain ↦ (P i).toManifold z) =
                (μpar.comap ((↑) : (P i).domain → ℝ × (P i).seed.covector.ker)).withDensity
                  (fun z ↦ ENNReal.ofReal
                    (parameterizedJacobian (P i).readout (P i).seed.normalization z) *
                    ρ ((P i).readout z))) ∧
          ∃ (r : ℕ → ι) (b : (ℚ → M) × ℝ → M),
            Function.Surjective r ∧ Measurable b ∧
            (∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x) ∧
            let O : ℕ → Set M := fun j ↦
              (P (r j)).toManifold '' (P (r j)).domain
            let C := disjointed O
            let lambda := μ.map a
            let R := lambda.prod (volume : Measure ℝ)
            ∀ (η : Measure M) [IsFiniteMeasure η], η = μ ∨ η = ν →
              let p := fun j ↦
                ((η.restrict (C j)).map (fun x ↦ (a x, u x))).rnDeriv R
              let h := fun y ↦ ∑' j, p j y
              Measurable h ∧
                R.withDensity h = η.map (fun x ↦ (a x, u x)) ∧
                (∀ᵐ z ∂lambda, ∫⁻ s, h (z, s) ∂volume = 1) ∧
                (∀ᵐ z ∂lambda,
                  (volume : Measure ℝ).withDensity (fun s ↦ h (z, s)) =
                    condDistrib u a η z) ∧
                ∀ g : M → ℝ≥0∞, Measurable g →
                  (∫⁻ x, g x ∂η) =
                    ∫⁻ z, ∫⁻ s, h (z, s) * g (b (z, s)) ∂volume ∂lambda
 := by
  classical
  let _instMeasuredAtlasMetric : MetricSpace M := F.metricSpace
  let _instMeasuredAtlasProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instMeasuredAtlasBorel : StandardBorelSpace M := inferInstance
  let _instMeasuredAtlasNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface,
      hμI, hνI, hμjoint, hνjoint, hcond, ι, hι, P, hcover, hμcover, hνcover, hwindow⟩ :=
    exists_finsler_measured_calibrated_atlas hF hcomplete m μ ν
      hμchart hνchart hA hB hAB hμ hν
  let _instWindowAtlasCountable : Countable ι := hι
  have huMeas : Measurable u := hu.continuous.measurable
  obtain ⟨b, hb, hbinv, _⟩ := exists_measurable_labelClock_inverse hN ha huMeas hinj
  obtain ⟨x, hx⟩ := hμcover.exists
  obtain ⟨i, _⟩ := mem_iUnion.mp hx
  let _instWindowAtlasNonempty : Nonempty ι := ⟨i⟩
  obtain ⟨r, hr⟩ := exists_surjective_nat ι
  let O : ℕ → Set M := fun j ↦ (P (r j)).toManifold '' (P (r j)).domain
  have hO (j : ℕ) : MeasurableSet (O j) :=
    (P (r j)).measurableSet_image hF hcomplete hu
  have hcoverNat (η : Measure M)
      (hη : ∀ᵐ x ∂η, x ∈ ⋃ i, (P i).toManifold '' (P i).domain) :
      ∀ᵐ x ∂η, x ∈ ⋃ j, O j := by
    filter_upwards [hη] with x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, rfl⟩ := hr i
    exact mem_iUnion.mpr ⟨j, hi⟩
  refine ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface,
    hμI, hνI, hμjoint, hνjoint, hcond, ι, hι, P, hcover, hμcover, hνcover, hwindow,
    r, b, hr, hb, hbinv, ?_⟩
  dsimp only
  intro η _ hη
  have hdata : η.map a = μ.map a ∧
      (∀ᵐ x ∂η, x ∈ F.potentialRegularDomain u) ∧
      η.map (fun x ↦ (a x, u x)) ≪ (η.map a).prod volume ∧
      (∀ᵐ x ∂η, x ∈ ⋃ j, O j) := by
    rcases hη with hη | hη
    · subst η
      exact ⟨rfl, hμN, hμjoint, hcoverNat μ hμcover⟩
    · subst η
      exact ⟨hbalance.symm, hνN, hνjoint, hcoverNat ν hνcover⟩
  obtain ⟨hηmap, hηN, hηjoint, hηcover⟩ := hdata
  obtain ⟨hh, hden, hnorm, hint⟩ :=
    labelClock_window_density_reconstruction η ha huMeas O hO hηcover hηjoint b hb
      (hηN.mono fun x hx ↦ hbinv x hx)
  have hconditional := ae_withDensity_clock_eq_condDistrib η huMeas hh hden
  rw [hηmap] at hh hden hnorm hint hconditional
  exact ⟨hh, hden, hnorm, hconditional, hint⟩

end OTSelector.Reconstruction
