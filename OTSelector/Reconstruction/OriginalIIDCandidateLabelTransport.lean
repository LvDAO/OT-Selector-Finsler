import OTSelector.Reconstruction.OriginalIIDFixedCandidateRootRecovery
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Exact original candidate readout transport to original labels

The original label pushforward is the actual standard-coordinate volume law
with its exact Haar intensity. Weighted signed readouts transport without a
positive density bound. Quotient readouts require the true zero-density
condition on the coordinate function; zero-density coordinates have zero
original label mass automatically.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000

section GenericDensityTransport
variable {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]

/-- A true density pushforward gives zero original label mass to zero-density
coordinates. This is a measure consequence, not a density lower bound. -/
theorem ae_label_intensity_pos_of_map_eq_withDensity
    (lambda : Measure Z) (mu : Measure V) (label : Z → V)
    (hlabel : Measurable label) (theta : V → ℝ) (htheta : Measurable theta)
    (hlaw : lambda.map label = mu.withDensity (fun c ↦ ENNReal.ofReal (theta c))) :
    ∀ᵐ z ∂lambda, 0 < theta (label z) := by
  apply ae_of_ae_map (μ := lambda) (p := fun c ↦ 0 < theta c) hlabel.aemeasurable
  rw [hlaw,ae_withDensity_iff htheta.ennreal_ofReal]
  exact Eventually.of_forall (fun c hc ↦
    lt_of_not_ge (fun h ↦ hc (ENNReal.ofReal_eq_zero.mpr h)))

/-- Weighted signed label readouts have exactly the integrability and integral
of theta times the same coordinate function. Zero density is allowed. -/
theorem density_label_weighted_transport
    (lambda : Measure Z) (mu : Measure V) (label : Z → V)
    (hlabel : Measurable label) (theta : V → ℝ) (htheta : Measurable theta)
    (hnonneg : ∀ c, 0 ≤ theta c)
    (hlaw : lambda.map label = mu.withDensity (fun c ↦ ENNReal.ofReal (theta c)))
    (g : V → ℝ)
    (hg : AEStronglyMeasurable g (mu.withDensity (fun c ↦ ENNReal.ofReal (theta c)))) :
    (Integrable (fun z ↦ g (label z)) lambda ↔ Integrable (fun c ↦ theta c*g c) mu) ∧
      (∫ z, g (label z) ∂lambda) = ∫ c, theta c*g c ∂mu := by
  have hreal (c : V) : (ENNReal.ofReal (theta c)).toReal = theta c :=
    ENNReal.toReal_ofReal (hnonneg c)
  have hgmap : AEStronglyMeasurable g (lambda.map label) := by rwa [hlaw]
  have hmap := integrable_map_measure (f := label) (g := g) hgmap hlabel.aemeasurable
  rw [hlaw] at hmap
  have hwith := integrable_withDensity_iff_integrable_smul' (μ := mu) (g := g)
    htheta.ennreal_ofReal (Eventually.of_forall (fun c ↦ ENNReal.ofReal_lt_top))
  refine ⟨hmap.symm.trans (by simpa only [hreal,smul_eq_mul] using hwith),?_⟩
  calc
    _ = ∫ c, g c ∂lambda.map label := (integral_map hlabel.aemeasurable hgmap).symm
    _ = _ := by
      rw [hlaw]
      simpa only [hreal,smul_eq_mul] using integral_withDensity_eq_integral_toReal_smul
        htheta.ennreal_ofReal (Eventually.of_forall (fun c ↦ ENNReal.ofReal_lt_top)) g

/-- Dividing a genuine coordinate readout by theta transports its signed
integral exactly, provided the coordinate function actually vanishes at zero
density. AE measurability suffices and no inverse-density bound is needed. -/
theorem density_label_quotient_transport
    (lambda : Measure Z) (mu : Measure V) (label : Z → V)
    (hlabel : Measurable label) (theta : V → ℝ) (htheta : Measurable theta)
    (hnonneg : ∀ c, 0 ≤ theta c)
    (hlaw : lambda.map label = mu.withDensity (fun c ↦ ENNReal.ofReal (theta c)))
    (f : V → ℝ) (hf : AEStronglyMeasurable f mu)
    (hzero : ∀ᵐ c ∂mu, theta c = 0 → f c = 0) :
    (Integrable (fun z ↦ f (label z)/theta (label z)) lambda ↔ Integrable f mu) ∧
      (∫ c, f c ∂mu) = ∫ z, f (label z)/theta (label z) ∂lambda := by
  let g := fun c ↦ f c/theta c
  have hg : AEStronglyMeasurable g (mu.withDensity (fun c ↦ ENNReal.ofReal (theta c))) :=
    ((hf.aemeasurable.div htheta.aemeasurable).aestronglyMeasurable).mono_ac
      (withDensity_absolutelyContinuous mu _)
  have hproduct : (fun c ↦ theta c*g c) =ᵐ[mu] f := by
    filter_upwards [hzero] with c hc
    by_cases hz : theta c = 0
    · simp only [hz,g,hc hz,zero_div,zero_mul]
    · dsimp only [g]
      field_simp
  have hw := density_label_weighted_transport lambda mu label hlabel theta htheta hnonneg hlaw g hg
  refine ⟨hw.1.trans (integrable_congr hproduct),?_⟩
  exact (integral_congr_ae hproduct).symm.trans hw.2.symm

end GenericDensityTransport

section OriginalCandidate
open Manifold OTSelector.Geometry
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual old Haar core transports signed candidate readouts through its
proved original label law and its exact standard-coordinate Haar intensity.
Weighted and quotient formulations retain their genuine zero-density domains. -/
theorem PopulationHaarPressureCore.candidate_label_transport
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := Module.finrank ℝ S.covector.ker
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    let label := fun z ↦ e (R z)
    let K := e '' (R '' C.roots)
    let density := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    let theta := fun c : Fin q → ℝ ↦
      (originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) * (density (e.symm c)).toReal
    (∀ᵐ z ∂lambda.restrict C.roots, 0 < theta (label z)) ∧
      (∀ (g : (Fin q → ℝ) → ℝ),
        AEStronglyMeasurable g (((volume : Measure (Fin q → ℝ)).restrict K).withDensity
          (fun c ↦ ENNReal.ofReal (theta c))) →
        (Integrable (fun z ↦ g (label z)) (lambda.restrict C.roots) ↔
          Integrable (fun c ↦ theta c*g c) ((volume : Measure (Fin q → ℝ)).restrict K)) ∧
        (∫ z in C.roots, g (label z) ∂lambda) = ∫ c in K, theta c*g c ∂volume) ∧
      ∀ (f : (Fin q → ℝ) → ℝ),
        AEStronglyMeasurable f ((volume : Measure (Fin q → ℝ)).restrict K) →
        (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K, theta c = 0 → f c = 0) →
        (Integrable (fun z ↦ f (label z)/theta (label z)) (lambda.restrict C.roots) ↔
          Integrable f ((volume : Measure (Fin q → ℝ)).restrict K)) ∧
        (∫ c in K, f c ∂volume) = ∫ z in C.roots, f (label z)/theta (label z) ∂lambda := by
  intro C S q e R label K density theta
  let _labelTransportMetric : MetricSpace M := F.metricSpace
  let _labelTransportProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _labelTransportPolish : PolishSpace M := inferInstance
  let _labelTransportBorel : BorelSpace (ℚ → M) := inferInstance
  have hlabel : Measurable label := e.continuous.measurable.comp
    (measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj)
  have htheta : Measurable theta := measurable_const.mul
    (((measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj C.seedIndex).comp
      e.symm.continuous.measurable).ennreal_toReal)
  have hnonneg (c : Fin q → ℝ) : 0 ≤ theta c :=
    mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg
  have hlaw := D.map_original_label_eq_coordinate_intensity hF hcomplete hu ha hinj i
  change (lambda.restrict C.roots).map label =
    ((volume : Measure (Fin q → ℝ)).restrict K).withDensity
      (fun c ↦ ENNReal.ofReal (theta c)) at hlaw
  refine ⟨ae_label_intensity_pos_of_map_eq_withDensity (lambda.restrict C.roots)
    (volume.restrict K) label hlabel theta htheta hlaw,?_,?_⟩
  · intro g hg
    exact density_label_weighted_transport (lambda.restrict C.roots) (volume.restrict K)
      label hlabel theta htheta hnonneg hlaw g hg
  · intro f hf hzero
    exact density_label_quotient_transport (lambda.restrict C.roots) (volume.restrict K)
      label hlabel theta htheta hnonneg hlaw f hf hzero

end OriginalCandidate
end OTSelector.Reconstruction
