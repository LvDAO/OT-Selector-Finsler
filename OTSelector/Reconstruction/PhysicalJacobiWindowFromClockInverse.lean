import OTSelector.Reconstruction.PhysicalJacobiMomentWindow

/-!
# Building moment windows from physical-time densities

The actual physical density is read at the original time. A graph inverse supplies
its graph-time form and the continuous volume factor automatically. The inverse is
used only on its genuine closed interval, and a measurable extension handles the
unconstrained values elsewhere without altering the physical density.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A physical-time conditional density and its actual inverse clock construct the
moment-window data. Graph-time density bounds and their matching to the physical law
are derived, rather than supplied separately. -/
def physicalJacobiMomentWindow_of_clockInverse
    {K J P A B C : ℝ → Matrix n n ℝ} {μ : Measure ℝ}
    {l h a b θ κ R : ℝ} (hlh : l < h)
    (H : ClosedHamiltonianJacobiSystem J P A B C a b)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0)
    {s v τ : ℝ → ℝ}
    (hs : ∀ t ∈ Ioo l h, HasDerivAt s (v t) t)
    (hinj : InjOn s (Ioo l h)) (himage : s '' Ioo l h = Ioo a b)
    (hv : ContinuousOn v (Ioo l h))
    (hτ : ContinuousOn τ (Icc a b)) (hτimage : MapsTo τ (Icc a b) (Icc l h))
    (hτs : ∀ t ∈ Ioo l h, τ (s t) = t)
    (hkernel : ∀ t ∈ Ioo l h,
      K t = v t • ((J (s t))⁻¹ * C (s t) * (J (s t))⁻¹ᵀ))
    {ρ w : ℝ → ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc l h))
    (hρ0 : ∀ t ∈ Ioo l h, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo l h, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo l h, 0 ≤ w t) (hθ : 0 < θ) (hκ : 0 ≤ κ)
    (hμ : μ.restrict (Ioo l h) = (volume.restrict (Ioo l h)).withDensity (fun t ↦
      ENNReal.ofReal ((ρ t * w t / θ) * (|v t| * |(J (s t)).det| * κ)))) :
    PhysicalJacobiMomentWindow K μ l h := by
  classical
  let τm : ℝ → ℝ := (Icc a b).piecewise τ (fun _ ↦ 0)
  have hτm : Measurable τm :=
    hτ.measurable_piecewise continuous_zero.continuousOn measurableSet_Icc
  have hτm_eq : ∀ t ∈ Icc a b, τm t = τ t :=
    fun t ht ↦ by simp [τm, ht]
  have hmaps : MapsTo s (Ioo l h) (Ioo a b) := by
    intro t ht
    rw [← himage]
    exact mem_image_of_mem _ ht
  have hτopen : MapsTo τ (Ioo a b) (Ioo l h) := by
    intro t ht
    rw [← himage] at ht
    obtain ⟨q, hq, rfl⟩ := ht
    rwa [hτs q hq]
  refine {
    left_lt_right := hlh
    a := a
    b := b
    θ := θ
    κ := κ
    R := R
    J := J
    P := P
    A := A
    B := B
    C := C
    s := s
    v := v
    ρ := ρ ∘ τm
    w := w ∘ τ
    system := H
    interior_det := hd
    clock_derivative := hs
    clock_injective := hinj
    clock_image := himage
    speed_continuous := hv
    kernel_eq := hkernel
    density_measurable := hρ.comp hτm
    weight_continuous := hw.comp hτ hτimage
    density_nonneg := ?_
    density_bounded := ?_
    weight_nonneg := fun t ht ↦ hw0 _ (hτopen ht)
    normalizer_pos := hθ
    normalization_nonneg := hκ
    conditional_density := ?_ }
  · intro t ht
    simpa only [Function.comp_def, hτm_eq t (Ioo_subset_Icc_self ht)] using hρ0 _ (hτopen ht)
  · intro t ht
    simpa only [Function.comp_def, hτm_eq t (Ioo_subset_Icc_self ht)] using hρR _ (hτopen ht)
  · rw [hμ]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [Function.comp_def, hτm_eq _ (Ioo_subset_Icc_self (hmaps ht)), hτs t ht]

end OTSelector.Reconstruction
