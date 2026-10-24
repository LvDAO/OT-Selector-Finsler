import OTSelector.Reconstruction.FinslerPopulationWindowClock
import OTSelector.Geometry.CalibratedSeedWindowComparisonJacobian

/-!
# Original conditional densities in the actual comparison Jacobi frame

The comparison has the original central curve and joint phase derivative. Its actual
graph position matrix therefore computes the original physical window Jacobian. The
conditional measure keeps one fixed potential clock across all comparison windows.
-/

open Set MeasureTheory ProbabilityTheory Manifold Metric Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M V ι Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual graph clock of the original curve in the window's fixed manifold chart. -/
def populationWindowGraphClock (P : F.CalibratedSeedWindow u) (A : E ≃L[ℝ] (ℝ × V))
    (w : P.seed.covector.ker) (t : ℝ) : ℝ :=
  (A (P.readout (t, w))).1

/-- The original time velocity in the same graph coordinate. -/
def populationWindowGraphSpeed (P : F.CalibratedSeedWindow u) (A : E ≃L[ℝ] (ℝ × V))
    (w : P.seed.covector.ker) (t : ℝ) : ℝ :=
  (fderiv ℝ (A ∘ P.comparisonReadout P.seed.curve) (w, t) (0, 1)).1

/-- The actual graph phase's position derivative matrix in the fixed label basis. -/
def populationWindowGraphPositionMatrix (P : F.CalibratedSeedWindow u)
    (bW : Basis ι ℝ P.seed.covector.ker) (bV : Basis ι ℝ V)
    (A : E ≃L[ℝ] (ℝ × V)) (Γ : P.seed.covector.ker → ℝ → M)
    (e : OpenPartialHomeomorph (P.seed.covector.ker × ℝ) (P.seed.covector.ker × ℝ))
    (w : P.seed.covector.ker) (s : ℝ) : Matrix ι ι ℝ :=
  vectorFamilyMatrix bV (fun j ↦
    (fderiv ℝ (fun z ↦ F.adaptedGraphPhase (P.toManifold P.center) A
      (A ∘ P.comparisonReadout Γ) e (z, s)) w (bW j)).1)

/-- The fixed change of parameter-volume normalization for this frame. -/
def populationWindowGraphNormalization (P : F.CalibratedSeedWindow u)
    (bW : Basis ι ℝ P.seed.covector.ker) (bV : Basis ι ℝ V)
    (A : E ≃L[ℝ] (ℝ × V)) : ℝ :=
  |(LinearMap.toMatrix (timeLabelBasis bV) (timeLabelBasis bW)
    (P.seed.normalization.trans A).symm.toLinearEquiv.toLinearMap).det|

omit [BorelSpace E] in
/-- Matching actual joint phase jets give the full original physical density in
the same Jacobi frame, retaining graph speed and fixed parameter normalization. -/
theorem populationWindowPhysicalDensity_eq_comparisonGraphPhase
    (P : ℕ → F.CalibratedSeedWindow u) (ρ : M → ℝ) (v : ℕ → E → ℝ) (j : ℕ)
    (bW : Basis ι ℝ (P j).seed.covector.ker) (bV : Basis ι ℝ V)
    (A : E ≃L[ℝ] (ℝ × V)) {Γ : (P j).seed.covector.ker → ℝ → M}
    {w : (P j).seed.covector.ker} {t : ℝ} (hcurve : (P j).seed.curve w = Γ w)
    {D : ((P j).seed.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily ((P j).toManifold (P j).center)
      (P j).seed.curve) D (w, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily ((P j).toManifold (P j).center) Γ) D (w, t))
    {e : OpenPartialHomeomorph ((P j).seed.covector.ker × ℝ)
      ((P j).seed.covector.ker × ℝ)}
    (he : (e : (P j).seed.covector.ker × ℝ → (P j).seed.covector.ker × ℝ) =
      curveGraphCoordinateMap (A ∘ (P j).comparisonReadout Γ))
    (hz : (w, t) ∈ e.source)
    (hv : (fderiv ℝ (A ∘ (P j).comparisonReadout Γ) (w, t) (0, 1)).1 ≠ 0)
    (hP : DifferentiableAt ℝ
      (fun z ↦ F.adaptedGraphPhase ((P j).toManifold (P j).center) A
        (A ∘ (P j).comparisonReadout Γ) e
          (z, (A ((P j).comparisonReadout Γ (w, t))).1)) w) :
    populationWindowPhysicalDensity P ρ v j w t =
      (ρ ((P j).seed.curve w t) * v j ((P j).readout (t, w))) *
        (|populationWindowGraphSpeed (P j) A w t| *
          |(populationWindowGraphPositionMatrix (P j) bW bV A Γ e w
            (populationWindowGraphClock (P j) A w t)).det| *
          populationWindowGraphNormalization (P j) bW bV A) := by
  have hJac := ((P j).parameterizedJacobian_comparisonGraphPhase_data
    bW bV A hcurve h₁ h₂ he hz hv hP).2
  change parameterizedJacobian (P j).readout (P j).seed.normalization (t, w) = _ at hJac
  unfold populationWindowPhysicalDensity
  rw [hJac]
  exact mul_comm _ _

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M]
  [MeasurableSpace Z]

omit [BorelSpace E] in
/-- The original conditional law, in a fixed common clock, has the exact actual
Jacobi density on every comparison subwindow. Its label factor is finite and
constant along the curve. All Jacobian data come from matching actual phase jets. -/
theorem PopulationFullWindowRestrictionLaw.clockShift_restrict_eq_comparisonGraphPhase
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    {b : Z × ℝ → M} (hlaw : PopulationFullWindowRestrictionLaw P a κ lambda η ρ v b)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instJacobiLawMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instJacobiLawOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x) (u₀ : ℝ) :
    ∀ᵐ z ∂lambda, ∀ j, (populationWindowLabelReference P a κ j).rnDeriv lambda z <
        (∞ : ℝ≥0∞) ∧
      ∀ w ∈ (P j).labels ∩ ball (P j).center.2 ((P j).seed.radius (P j).center),
        a ((P j).seed.curve w 0) = z →
        ∀ (K : Set ℝ), MeasurableSet K →
          (∀ q ∈ K, q + u₀ - (P j).seed.level ∈ populationWindowTimeInterval P j) →
          ∀ (bW : Basis ι ℝ (P j).seed.covector.ker) (bV : Basis ι ℝ V)
            (A : E ≃L[ℝ] (ℝ × V)) (Γ : (P j).seed.covector.ker → ℝ → M),
            (P j).seed.curve w = Γ w →
            ∀ (e : OpenPartialHomeomorph ((P j).seed.covector.ker × ℝ)
                ((P j).seed.covector.ker × ℝ)),
              (e : (P j).seed.covector.ker × ℝ → (P j).seed.covector.ker × ℝ) =
                curveGraphCoordinateMap (A ∘ (P j).comparisonReadout Γ) →
              (∀ q ∈ K, ∃ D : ((P j).seed.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ),
                HasFDerivAt (F.chartMomentumFamily ((P j).toManifold (P j).center)
                  (P j).seed.curve) D (w, q + u₀ - (P j).seed.level) ∧
                HasFDerivAt (F.chartMomentumFamily ((P j).toManifold (P j).center) Γ)
                  D (w, q + u₀ - (P j).seed.level)) →
              (∀ q ∈ K, (w, q + u₀ - (P j).seed.level) ∈ e.source) →
              (∀ q ∈ K, (fderiv ℝ (A ∘ (P j).comparisonReadout Γ)
                (w, q + u₀ - (P j).seed.level) (0, 1)).1 ≠ 0) →
              (∀ q ∈ K, DifferentiableAt ℝ
                (fun y ↦ F.adaptedGraphPhase ((P j).toManifold (P j).center) A
                  (A ∘ (P j).comparisonReadout Γ) e
                    (y, (A ((P j).comparisonReadout Γ
                      (w, q + u₀ - (P j).seed.level))).1)) w) →
              ((condDistrib u a η z).map (fun s : ℝ ↦ s - u₀)).restrict K =
                (volume.restrict K).withDensity (fun q ↦
                  let t := q + u₀ - (P j).seed.level
                  ENNReal.ofReal
                    ((ρ ((P j).seed.curve w t) *
                        (((populationWindowLabelReference P a κ j).rnDeriv lambda z).toReal *
                          v j ((P j).readout (t, w)))) *
                      (|populationWindowGraphSpeed (P j) A w t| *
                        |(populationWindowGraphPositionMatrix (P j) bW bV A Γ e w
                          (populationWindowGraphClock (P j) A w t)).det| *
                        populationWindowGraphNormalization (P j) bW bV A))) := by
  filter_upwards [hlaw.clockShift_restrict_eq_ofReal hF hcomplete hu hinj horder hinv u₀]
    with z hz
  intro j
  refine ⟨(hz j).1, ?_⟩
  intro w hw hwz K hK hKI bW bV A Γ hcurve e he hjets hsource hspeed hphase
  rw [(hz j).2 w hw hwz K hK hKI]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hK] with q hq
  obtain ⟨D, h₁, h₂⟩ := hjets q hq
  dsimp only
  rw [populationWindowPhysicalDensity_eq_comparisonGraphPhase P ρ v j bW bV A
    hcurve h₁ h₂ he (hsource q hq) (hspeed q hq) (hphase q hq)]
  congr 1
  ring

end OTSelector.Reconstruction
