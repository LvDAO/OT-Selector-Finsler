import OTSelector.MeasureTheory.EndpointDensityShellBand
import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficDeterminant

/-! Integrating the old-leg determinant against the original physical density.
Only a pointwise density law is needed; a measurable density representative is
chosen below the literal chart density without changing the original measure. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- A bound on the product of a literal physical density and an observable
bounds the observable's original integral. Density measurability is unnecessary. -/
theorem lintegral_restrict_le_of_density_product_bound
    {μ : Measure ℝ} {f d : ℝ→ℝ} {I B : Set ℝ} {K : ℝ}
    (hμ : μ.restrict I = (volume.restrict I).withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hB : MeasurableSet B) (hsub : B⊆I) (hd : Measurable d)
    (hf0 : ∀x∈B,0≤f x) (hbound : ∀x∈B,f x*d x≤K) :
    (∫⁻x in B,ENNReal.ofReal (d x)∂μ) ≤ ENNReal.ofReal K * volume B := by
  have hrestrict : μ.restrict B =
      (volume.restrict B).withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
    rw [← Measure.restrict_restrict_of_subset hsub,hμ,
      restrict_withDensity hB,Measure.restrict_restrict_of_subset hsub]
  obtain ⟨g,hgm,hgf,hg⟩:=exists_measurable_le_withDensity_eq
    (volume.restrict B) (fun x ↦ ENNReal.ofReal (f x))
  calc
    _ = ∫⁻x,ENNReal.ofReal (d x)∂(volume.restrict B).withDensity g := by
      rw [hrestrict,hg]
    _ = ∫⁻x,g x*ENNReal.ofReal (d x)∂volume.restrict B :=
      lintegral_withDensity_eq_lintegral_mul _ hgm hd.ennreal_ofReal
    _ ≤ ∫⁻_x,ENNReal.ofReal K∂volume.restrict B := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with x hx
      calc
        _ ≤ ENNReal.ofReal (f x)*ENNReal.ofReal (d x) := by gcongr; exact hgf x
        _ = ENNReal.ofReal (f x*d x) := (ENNReal.ofReal_mul (hf0 x hx)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hbound x hx)
    _ = _ := by simp

/-- The original `a^k` density cancels the full old-leg `(2t/a)^k`
determinant singularity before integration at the endpoint. -/
theorem lintegral_left_oldFocal_det_le_of_density_rank_bound
    {μ : Measure ℝ} {f d : ℝ→ℝ} {l h t K D : ℝ} {k : ℕ}
    (hμ : μ.restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (ht : 0<t) (hth : l+2*t≤h) (hK : 0≤K) (hD : 0≤D)
    (hd : Measurable d) (hd0 : ∀x∈Ioo l (l+2*t),0≤d x)
    (hf : ∀a∈Ioo 0 (2*t),0≤f (l+a) ∧ f (l+a)≤K*a^k)
    (hdet : ∀a∈Ioo 0 (2*t),d (l+a)≤D*(2*t/a)^k) :
    (∫⁻x in Ioo l (l+2*t),ENNReal.ofReal (d x)∂μ) ≤
      ENNReal.ofReal (K*D*(2*t)^(k+1)) := by
  have hprod (x : ℝ) (hx : x∈Ioo l (l+2*t)) : f x*d x≤K*D*(2*t)^k := by
    let a:=x-l
    have ha:a∈Ioo 0 (2*t):=⟨by dsimp [a];linarith [hx.1],by dsimp [a];linarith [hx.2]⟩
    have hf':=hf a ha
    have hd':=hdet a ha
    rw [add_sub_cancel] at hf' hd'
    calc
      _ ≤ (K*a^k)*(D*(2*t/a)^k) :=
        mul_le_mul hf'.2 hd' (hd0 x hx) (mul_nonneg hK (pow_nonneg ha.1.le _))
      _ = K*D*(2*t)^k := by
        rw [div_pow]
        field_simp [ha.1.ne']
  have h := lintegral_restrict_le_of_density_product_bound hμ measurableSet_Ioo
    (fun x hx ↦ ⟨hx.1,hx.2.trans_le hth⟩) hd
    (fun x hx ↦ by simpa [add_sub_cancel] using (hf (x-l)
      ⟨by linarith [hx.1],by linarith [hx.2]⟩).1) hprod
  calc
    _ ≤ ENNReal.ofReal (K*D*(2*t)^k)*volume (Ioo l (l+2*t)) := h
    _ = _ := by
      rw [Real.volume_Ioo,←ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [pow_succ]
      ring

end OTSelector.Reconstruction
