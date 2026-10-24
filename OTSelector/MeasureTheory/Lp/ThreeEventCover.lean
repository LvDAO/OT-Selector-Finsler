import OTSelector.MeasureTheory.Lp.FiniteBandEnergySum
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalMinimizerRightRegularNormAssembly.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalMinimizerRightRegularNormAssembly`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Lp.ThreeEventCover

## Lemma skeleton

* **Conditions:** Nonnegative traffic covered by three arbitrary events, L2 bounds for each event indicator, and the displayed nonnegative constants for the square-root helper.
* **Objects:** L2 of the whole traffic with the sum of the three norm bounds, and explicit split of a quadratic-plus-exponential square root.
* **Proof detail:** Bound the nonnegative traffic by the sum of its covering indicators and use L2 monotonicity/Minkowski. For the helper apply sqrt(a+b)<=sqrt(a)+sqrt(b) and exponential square-root algebra.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=214): Section 7A, Theorem 7.14, p. 199 (Minkowski).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=211): Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp).
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): Three-event domination works for overlapping events; no measurable partition or independence is inferred.
-/

/-! Shared regular source/target norm algebra and the three-event assembly. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- A quadratic physical-window rate and original count tail give their
explicit square-root rate at the same band energy. -/
theorem regularBirth_sqrt_square_tail
    {C K s V R K₀ : ℝ} (hC : 0≤C) (hK : 0≤K) (hs : 0<s)
    (hV : 0≤V) (hR : 0≤R) :
    Real.sqrt (C*K*s^2*V+R*Real.exp (-(K-K₀)/2))≤
      Real.sqrt C*Real.sqrt K*s*Real.sqrt V+
        Real.sqrt R*Real.exp (K₀/4)*Real.exp (-K/4) := by
  have hexp : Real.sqrt (Real.exp (-(K-K₀)/2))=
      Real.exp (K₀/4)*Real.exp (-K/4) := by
    rw [Real.sqrt_eq_rpow,←Real.exp_mul,←Real.exp_add]
    congr 1
    ring
  apply (sqrt_add_energy_le_sqrt_terms (by positivity) (by positivity)).trans_eq
  rw [Real.sqrt_mul (by positivity : 0≤C*K*s^2),Real.sqrt_mul (by positivity : 0≤C*K),
    Real.sqrt_mul hC,Real.sqrt_sq_eq_abs,abs_of_pos hs,Real.sqrt_mul hR,hexp]
  ring

/-- Three genuine event estimates cover a nonnegative traffic and give its
whole L2 norm. The same proof applies to both original endpoint colors. -/
theorem nonnegative_traffic_memLp_two_of_three_event_cover
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : Ω→ℝ} (hT : AEStronglyMeasurable T P) (hT0 : ∀ω,0≤T ω)
    (A B C : Set Ω) (hcover : ∀ω,ω∈A∨ω∈B∨ω∈C)
    (hA : MemLp (A.indicator T) 2 P) (hB : MemLp (B.indicator T) 2 P)
    (hC : MemLp (C.indicator T) 2 P)
    {rA rB rC : ℝ} (hrA : 0≤rA) (hrB : 0≤rB) (hrC : 0≤rC)
    (hnA : eLpNorm (A.indicator T) 2 P≤ENNReal.ofReal rA)
    (hnB : eLpNorm (B.indicator T) 2 P≤ENNReal.ofReal rB)
    (hnC : eLpNorm (C.indicator T) 2 P≤ENNReal.ofReal rC) :
    MemLp T 2 P ∧ eLpNorm T 2 P≤ENNReal.ofReal (rA+rB+rC) := by
  have hdom : ∀ᵐω∂P,‖T ω‖≤A.indicator T ω+B.indicator T ω+C.indicator T ω := by
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs,abs_of_nonneg (hT0 ω)]
    have hAn := indicator_nonneg (s:=A) (f:=T) (fun x _↦hT0 x) ω
    have hBn := indicator_nonneg (s:=B) (f:=T) (fun x _↦hT0 x) ω
    have hCn := indicator_nonneg (s:=C) (f:=T) (fun x _↦hT0 x) ω
    rcases hcover ω with ha|hb|hc
    · rw [indicator_of_mem ha];linarith
    · rw [indicator_of_mem hb];linarith
    · rw [indicator_of_mem hc];linarith
  refine ⟨((hA.add hB).add hC).mono' hT hdom,?_⟩
  calc
    _≤eLpNorm (fun ω↦A.indicator T ω+B.indicator T ω+C.indicator T ω) 2 P :=
      eLpNorm_mono_ae_real hdom
    _≤(eLpNorm (A.indicator T) 2 P+eLpNorm (B.indicator T) 2 P)+eLpNorm (C.indicator T) 2 P :=
      (eLpNorm_add_le (hA.add hB).aestronglyMeasurable hC.aestronglyMeasurable (by norm_num)).trans
        (add_le_add (eLpNorm_add_le hA.aestronglyMeasurable hB.aestronglyMeasurable (by norm_num)) le_rfl)
    _≤(ENNReal.ofReal rA+ENNReal.ofReal rB)+ENNReal.ofReal rC := add_le_add (add_le_add hnA hnB) hnC
    _=_ := by rw [←ENNReal.ofReal_add hrA hrB,←ENNReal.ofReal_add (add_nonneg hrA hrB) hrC]

end OTSelector.Probability

end
end
