import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficDensity

/-! The true reflected endpoint density cancels the right old-leg
singularity pointwise before integration. No uniform rectangle bound or
replacement density is used. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Under the original density law, the reflected a^k density cancels the
full old-leg (2t/a)^k growth at the right endpoint, including arbitrarily
small inward distances a=h-x. -/
theorem lintegral_right_oldFocal_det_le_of_density_rank_bound
    {μ : Measure ℝ} {f d : ℝ→ℝ} {l h t K D : ℝ} {k : ℕ}
    (hμ : μ.restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (ht : 0<t) (hth : l≤h-2*t) (hK : 0≤K) (hD : 0≤D)
    (hd : Measurable d) (hd0 : ∀x∈Ioo (h-2*t) h,0≤d x)
    (hf : ∀a∈Ioo 0 (2*t),0≤f (h-a) ∧ f (h-a)≤K*a^k)
    (hdet : ∀a∈Ioo 0 (2*t),d (h-a)≤D*(2*t/a)^k) :
    (∫⁻x in Ioo (h-2*t) h,ENNReal.ofReal (d x)∂μ) ≤
      ENNReal.ofReal (K*D*(2*t)^(k+1)) := by
  have hprod (x : ℝ) (hx : x∈Ioo (h-2*t) h) : f x*d x≤K*D*(2*t)^k := by
    let a:=h-x
    have ha:a∈Ioo 0 (2*t):=⟨by dsimp [a];linarith [hx.2],by dsimp [a];linarith [hx.1]⟩
    have heq:h-a=x:=by dsimp [a];ring
    have hf':=hf a ha
    have hd':=hdet a ha
    rw [heq] at hf' hd'
    calc
      _ ≤ (K*a^k)*(D*(2*t/a)^k) :=
        mul_le_mul hf'.2 hd' (hd0 x hx) (mul_nonneg hK (pow_nonneg ha.1.le _))
      _ = K*D*(2*t)^k := by
        rw [div_pow]
        field_simp [ha.1.ne']
  have hmeasure := lintegral_restrict_le_of_density_product_bound hμ measurableSet_Ioo
    (fun x hx ↦ ⟨hth.trans_lt hx.1,hx.2⟩) hd
    (fun x hx ↦ by simpa only [sub_sub_cancel] using (hf (h-x)
      ⟨by linarith [hx.2],by linarith [hx.1]⟩).1) hprod
  calc
    _ ≤ ENNReal.ofReal (K*D*(2*t)^k)*volume (Ioo (h-2*t) h) := hmeasure
    _ = _ := by
      rw [Real.volume_Ioo,←ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [pow_succ]
      ring

end OTSelector.Reconstruction
