import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationCoordinates
import OTSelector.Transport.Neumann.FiniteMassGridPlan
import OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiCellLaw
import OTSelector.MeasureTheory.CompactCarrierGridGeometry
import OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiGridPrecision
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Original finite density endpoints admit genuine quadratic epsilon couplings
from their actual Neumann gradient discrepancy. -/
open MeasureTheory Set TopologicalSpace
open scoped Distributions BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual Neumann gradient discrepancy controls a genuine coupling of the
original equal finite density laws, in the literal Euclidean half-quadratic cost. -/
theorem exists_originalDensity_quadratic_epsilon_coupling
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    {K₀ : Set (ι → ℝ)} (hK₀ : IsCompact K₀) (hK₀K : K₀ ⊆ interior (K : Set (ι → ℝ)))
    (hμ : ∀ᵐ z ∂μ, z ∈ K₀) (f g : (ι → ℝ) → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hfl : ∀ᵐ z ∂μ, ρ ≤ f z) (hgl : ∀ᵐ z ∂μ, ρ ≤ g z)
    (hmass : (∫ z, f z ∂μ) = ∫ z, g z ∂μ)
    (hbound : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ z, φ z * f z ∂μ) - (∫ z, φ z * g z ∂μ)‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μ φ‖) :
    ∀ ε : ℝ, 0 < ε → ∃ π : Measure ((ι → ℝ) × (ι → ℝ)),
      Vlasov.IsCoupling π (μ.withDensity (fun z ↦ ENNReal.ofReal (f z)))
        (μ.withDensity (fun z ↦ ENNReal.ofReal (g z))) ∧
      Integrable (fun z ↦ ‖(EuclideanSpace.equiv ι ℝ).symm z.2 -
        (EuclideanSpace.equiv ι ℝ).symm z.1‖ ^ 2 / 2) π ∧
      (∫ z, ‖(EuclideanSpace.equiv ι ℝ).symm z.2 -
        (EuclideanSpace.equiv ι ℝ).symm z.1‖ ^ 2 / 2 ∂π) ≤ ρ⁻¹ * C ^ 2 / 2 + ε := by
  classical
  intro ε hε
  have hf0 : ∀ᵐ z ∂μ, 0 ≤ f z := hfl.mono fun _ hz ↦ hρ.le.trans hz
  have hg0 : ∀ᵐ z ∂μ, 0 ≤ g z := hgl.mono fun _ hz ↦ hρ.le.trans hz
  let σf := μ.withDensity (fun z ↦ ENNReal.ofReal (f z))
  let σg := μ.withDensity (fun z ↦ ENNReal.ofReal (g z))
  have : IsFiniteMeasure σf := originalDensityWithDensity_isFiniteMeasure μ f hf hf0
  have : IsFiniteMeasure σg := originalDensityWithDensity_isFiniteMeasure μ g hg hg0
  by_cases hm : 0 < ∫ z, f z ∂μ
  · let e : (ι → ℝ) ≃ᵐ EuclideanSpace ℝ ι :=
      (EuclideanSpace.equiv ι ℝ).symm.toHomeomorph.toMeasurableEquiv
    have hKimage : IsCompact (e '' K₀) :=
      hK₀.image (EuclideanSpace.equiv ι ℝ).symm.continuous
    obtain ⟨R, hR, hRbound⟩ := hKimage.isBounded.exists_pos_norm_le
    let Ω : Set (EuclideanSpace ℝ ι) := Metric.closedBall 0 R
    have hΩc : IsCompact Ω := isCompact_closedBall _ _
    have hΩconv : Convex ℝ Ω := convex_closedBall _ _
    have hΩne : Ω.Nonempty := ⟨0, by simp [Ω, hR.le]⟩
    have hKΩ : ∀ z ∈ K₀, e z ∈ Ω := by
      intro z hz
      simpa only [Ω, Metric.mem_closedBall, dist_zero_right] using
        hRbound (e z) (mem_image_of_mem e hz)
    let D := Metric.diam Ω
    let M := D ^ 2 / 2
    have hD : 0 ≤ D := Metric.diam_nonneg
    obtain ⟨δ, hδ, h, hh, hprecision⟩ := exists_neumannQuadratic_grid_precision
      (∫ z, f z ∂μ) D M D hε
    obtain ⟨s, hsne, hsΩ, T, hT, hnear⟩ :=
      exists_compact_measurable_finiteIndex_grid hΩc hΩne hh
    let _ : Fintype s := inferInstance
    have : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
    let Tp : (ι → ℝ) → s := T ∘ e
    let x : s → (ι → ℝ) := fun i ↦ e.symm i
    have hTp : Measurable Tp := hT.comp e.measurable
    have hgeometry := compact_grid_quadratic_geometry hΩc
      (fun i : s ↦ (i : EuclideanSpace ℝ ι)) (fun i ↦ hsΩ i.property)
    have hnode : ∀ z ∈ Ω, ∀ i : s, ‖z - (EuclideanSpace.equiv ι ℝ).symm (x i)‖ ≤ D := by
      intro z hz i
      change ‖z - e (x i)‖ ≤ D
      simpa only [x, e.apply_symm_apply] using hgeometry.1 z hz i
    have hdisp : ∀ z, e z ∈ Ω → ‖e (x (Tp z)) - e z‖ ≤ h := by
      intro z hz
      simpa only [x, Tp, Function.comp_apply, e.apply_symm_apply] using hnear (e z) hz
    have hmem : ∀ᵐ z ∂μ, (EuclideanSpace.equiv ι ℝ).symm z ∈ Ω ∧
        (EuclideanSpace.equiv ι ℝ).symm (x (Tp z)) ∈ Ω ∧
        (EuclideanSpace.equiv ι ℝ).symm (x (Tp z)) ∈ Ω := by
      change ∀ᵐ z ∂μ, e z ∈ Ω ∧ e (x (Tp z)) ∈ Ω ∧ e (x (Tp z)) ∈ Ω
      filter_upwards [hμ] with z hz
      exact ⟨hKΩ z hz, by simpa only [x, Tp, Function.comp_apply, e.apply_symm_apply] using hsΩ (T (e z)).property,
        by simpa only [x, Tp, Function.comp_apply, e.apply_symm_apply] using hsΩ (T (e z)).property⟩
    have hdispμ : ∀ᵐ z ∂μ, ‖(EuclideanSpace.equiv ι ℝ).symm (x (Tp z)) -
        (EuclideanSpace.equiv ι ℝ).symm z‖ ≤ h := by
      exact hμ.mono fun z hz ↦ hdisp z (hKΩ z hz)
    have hcost : ∀ i j : s, ‖(EuclideanSpace.equiv ι ℝ).symm (x j) -
        (EuclideanSpace.equiv ι ℝ).symm (x i)‖ ^ 2 / 2 ≤ M := by
      intro i j
      change ‖e (x j) - e (x i)‖ ^ 2 / 2 ≤ M
      simpa only [x, e.apply_symm_apply] using hgeometry.2 i j
    obtain ⟨P, hP, hrow, hcol, hPcost⟩ :=
      exists_originalDensity_quadratic_finiteMass_grid_plan K μ hK₀ hK₀K hμ f g hf hg
        hρ hC hfl hgl hm rfl hmass.symm hbound Tp Tp hTp hTp x x hD hh.le hδ
        hΩconv hnode hmem hdispμ hdispμ hcost
    have hsuppf : ∀ᵐ z ∂σf, z ∈ e ⁻¹' Ω :=
      Measure.AbsolutelyContinuous.ae_le
        (MeasureTheory.withDensity_absolutelyContinuous μ _)
        (hμ.mono fun z hz ↦ hKΩ z hz)
    have hsuppg : ∀ᵐ z ∂σg, z ∈ e ⁻¹' Ω :=
      Measure.AbsolutelyContinuous.ae_le
        (MeasureTheory.withDensity_absolutelyContinuous μ _)
        (hμ.mono fun z hz ↦ hKΩ z hz)
    have himage : e '' (e ⁻¹' Ω) = Ω := image_preimage_eq _ e.surjective
    obtain ⟨π, hπ, _, hπI, hπcost⟩ :=
      exists_finiteIndex_coordinate_quadratic_coupling_lift_finite_mass e σf σg
        (by rwa [himage]) hsuppf hsuppg hTp hTp
        (originalDensityCellWeight μ f Tp) (originalDensityCellWeight μ g Tp)
        (originalDensityCellWeight_map_withDensity μ f hf hf0 Tp hTp)
        (originalDensityCellWeight_map_withDensity μ g hg hg0 Tp hTp)
        P hP hrow hcol x x hh.le (fun z hz ↦ hdisp z hz) (fun z hz ↦ hdisp z hz)
    refine ⟨π, hπ, hπI, ?_⟩
    rw [himage, originalDensityWithDensity_univ μ f hf hf0, ENNReal.toReal_ofReal
      (integral_nonneg_of_ae hf0)] at hπcost
    change (∑ i : s, ∑ j : s, (‖e (x j) - e (x i)‖ ^ 2 / 2) * P i j) ≤ _ at hPcost
    have hmatrix : (∑ i : s, ∑ j : s, P i j * (‖e (x j) - e (x i)‖ ^ 2 / 2)) ≤
        ρ⁻¹ * C ^ 2 / 2 + (∫ z, f z ∂μ) * (D / (1 + δ) * h + D / δ * h + M * δ) := by
      simpa only [mul_comm] using hPcost
    have hprecision' : (∫ z, f z ∂μ) *
        (D / (1 + δ) * h + D / δ * h + M * δ + 2 * D * h) < ε := by
      convert hprecision using 1
      ring
    change (∫ z, ‖e z.2 - e z.1‖ ^ 2 / 2 ∂π) ≤ _
    dsimp [D] at hprecision' hmatrix hπcost
    linarith
  · have hfzero : (∫ z, f z ∂μ) = 0 := le_antisymm (le_of_not_gt hm) (integral_nonneg_of_ae hf0)
    have hgzero : (∫ z, g z ∂μ) = 0 := hmass.symm.trans hfzero
    have hσf : σf = 0 := Measure.measure_univ_eq_zero.mp (by
      rw [originalDensityWithDensity_univ μ f hf hf0, hfzero, ENNReal.ofReal_zero])
    have hσg : σg = 0 := Measure.measure_univ_eq_zero.mp (by
      rw [originalDensityWithDensity_univ μ g hg hg0, hgzero, ENNReal.ofReal_zero])
    refine ⟨0, ?_, integrable_zero_measure, ?_⟩
    · constructor
      · simpa only [Measure.map_zero] using hσf.symm
      · simpa only [Measure.map_zero] using hσg.symm
    · simp only [integral_zero_measure]
      positivity

end OTSelector.Reconstruction
