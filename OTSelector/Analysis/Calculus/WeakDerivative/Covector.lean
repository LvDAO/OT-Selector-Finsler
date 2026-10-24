import OTSelector.Analysis.WeakDerivativePrimitive
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CovectorWeakDerivative.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CovectorWeakDerivative`; the selected original proof blocks follow. -/
section

/-!
Conditions: Finite-dimensional covector-valued integrable p,q satisfy the actual fixed-endpoint C1 test-function weak derivative identity.

Objects: An almost-everywhere primitive identity, continuous representative and almost-everywhere derivative q.

Proof detail: Evaluate in a basis, apply the scalar weak-primitive/du Bois–Reymond argument and FTC, then reconstruct the covector-valued primitive.

Sources: D. H. Fremlin, Section 225E (absolutely continuous functions as indefinite integrals), 225F (integration by parts) (https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29); Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); J. M. Ball, Section 3, proof of Lemma 3.1, equation (3.5), p. 512 (du Bois–Reymond constant principle) (https://people.maths.ox.ac.uk/~ball/Papers/BallAndCrooks2011.pdf#page=12).
Relation: Finite-dimensional vector/covector extension of the classical weak-primitive argument; equality is almost everywhere until the continuous representative is constructed.
-/

/-!
# Continuous representatives of covector weak derivatives

Finite-dimensional covector-valued weak derivatives are reconstructed by scalar
fixed-endpoint tests along a basis. The original momentum need only be integrable;
its representative is a constant covector plus the actual vector-valued primitive.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A covector weak derivative identity produces a continuous primitive representative
and its almost everywhere actual derivative, without continuity of the given momentum. -/
theorem exists_ae_eq_const_add_integral_of_covector_weak_derivative
    {p q : ℝ → E →L[ℝ] ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : IntervalIntegrable p volume a b) (hq : IntervalIntegrable q volume a b)
    (hweak : ∀ η : ℝ → E, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
      (∫ t in a..b, q t (η t) + p t (deriv η t)) = 0) :
    ∃ C : E →L[ℝ] ℝ,
      (p =ᵐ[volume.restrict (Ioo a b)] (fun t ↦ C + ∫ s in a..t, q s)) ∧
      ContinuousOn (fun t ↦ C + ∫ s in a..t, q s) (Icc a b) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b),
        HasDerivAt (fun u ↦ C + ∫ s in a..u, q s) (q t) t) := by
  let e := Module.finBasis ℝ E
  have hi (i : Fin (Module.finrank ℝ E)) : ∃ C : ℝ,
      (fun t ↦ p t (e i)) =ᵐ[volume.restrict (Ioo a b)]
        (fun t ↦ C + ∫ s in a..t, q s (e i)) := by
    have hpi : IntervalIntegrable (fun t ↦ p t (e i)) volume a b :=
      ⟨hp.1.apply_continuousLinearMap (e i), hp.2.apply_continuousLinearMap (e i)⟩
    have hqi : IntervalIntegrable (fun t ↦ q t (e i)) volume a b :=
      ⟨hq.1.apply_continuousLinearMap (e i), hq.2.apply_continuousLinearMap (e i)⟩
    obtain ⟨C, hC, _⟩ := exists_ae_eq_const_add_integral_of_weak_derivative hab hpi hqi
      (by
        intro φ hφ hφa hφb
        have hw := hweak (fun t ↦ φ t • e i) (hφ.smul contDiff_const)
          (by simp [hφa]) (by simp [hφb])
        have hd : deriv (fun t ↦ φ t • e i) = fun t ↦ deriv φ t • e i := by
          funext t
          exact ((hφ.differentiable one_ne_zero t).hasDerivAt.smul_const (e i)).deriv
        simpa only [hd, map_smul, smul_eq_mul, mul_comm] using hw)
    exact ⟨C, hC⟩
  choose Cs hCs using hi
  let C : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (e.constr ℝ Cs)
  have hC (i) : C (e i) = Cs i := by
    simp [C]
  refine ⟨C, ?_, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr hCs, ae_restrict_mem measurableSet_Ioo] with t ht htin
    have hqat : IntervalIntegrable q volume a t := hq.mono_set (by
      rw [uIcc_of_le htin.1.le, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl htin.2.le)
    apply ContinuousLinearMap.coe_injective
    apply e.ext
    intro i
    change p t (e i) = C (e i) + (∫ s in a..t, q s) (e i)
    rw [hC, ContinuousLinearMap.intervalIntegral_apply hqat]
    exact ht i
  · have hQ := intervalIntegral.continuousOn_primitive_interval' hq left_mem_uIcc
    rw [uIcc_of_le hab] at hQ
    intro t ht
    exact continuousWithinAt_const.add (hQ t ht)
  · filter_upwards [ae_restrict_of_ae hq.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Ioo] with t ht htin
    have htin' : t ∈ uIcc a b := by
      rw [uIcc_of_le hab]
      exact ⟨htin.1.le, htin.2.le⟩
    exact (ht htin' a left_mem_uIcc).const_add C

end OTSelector.Geometry

end
end
