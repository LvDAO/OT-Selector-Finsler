import OTSelector.Geometry.Finsler.CovectorNormalization
import OTSelector.Analysis.Calculus.UniformSeedNormalization
import OTSelector.Analysis.Calculus.UniformAmbientSecondJet
import OTSelector.Analysis.Calculus.ParameterizedSecondJetLevel

/-!
# Uniform actual inverse-state approximation by normalized polynomial seeds

A large compact subcore is selected using the actual ambient second jets. The
explicit same-branch Finsler normalization transports their uniform covector
remainder. On the unchanged allowed core, the actual inverse state already has
the prescribed energy and is fixed by normalization. Thus the resulting estimate
compares genuine original inverse states with the selected polynomial seeds.
The uniform scalar potential remainder is retained on this very same core.
-/

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- Original constant-energy inverse states and the actual normalized second-jet
polynomials have a uniform first-order-small discrepancy on a large compact
subcore. Neither a uniform discrepancy nor an abstract normalization is assumed. -/
theorem exists_compact_uniform_normalized_polynomial_seed
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {c : ℝ} (hc : 0 < c)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hLip : LipschitzWith L (fderiv ℝ G))
    {C H : Set E} (hHC : H ⊆ C)
    {ν : Measure E} (hH : IsCompact H) (hνH : ν H ≠ ⊤)
    (hsecond : ∀ x ∈ H, DifferentiableAt ℝ (fderiv ℝ G) x)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) H)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    (henergy : ∀ y ∈ C, F.chartEnergy old (eL.symm (y, fderiv ℝ G y)) = c)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      (∀ η : ℝ, 0 < η → ∃ r > 0,
        ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
          ‖G (x + h) - scalarSecondJetPolynomial
            (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) (x + h)‖ ≤ η * ‖h‖ ^ 2) ∧
      ∀ η : ℝ, 0 < η → ∃ r > 0,
        ∀ x ∈ K, ∀ h : E, ‖h‖ < r → x + h ∈ C →
          let P := scalarSecondJetPolynomial
            (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
          (x + h, fderiv ℝ P (x + h)) ∈ eL.target ∧
            F.covectorNormalization old eL c (x + h, fderiv ℝ P (x + h)) ∈
              chartEnergyDomain old ∧
          ‖eL.symm (x + h, fderiv ℝ G (x + h)) -
            F.covectorNormalization old eL c (x + h, fderiv ℝ P (x + h))‖ ≤
              η * ‖h‖ := by
  obtain ⟨K, hKH, hK, hloss, hHK, hrem⟩ :=
    exists_compact_uniform_ambient_secondJet hH hνH hG hsecond hHess hε
  obtain ⟨_, hN, hspec⟩ := hF.covectorNormalization_spec old heL hsource hInv hc
  have hscalar : ∀ η : ℝ, 0 < η → ∃ r > 0,
      ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
        ‖G (x + h) - scalarSecondJetPolynomial
          (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) (x + h)‖ ≤ η * ‖h‖ ^ 2 := by
    intro η hη
    obtain ⟨r, hr, hb⟩ := hrem η hη
    refine ⟨r, hr, ?_⟩
    intro x hx h hh
    have hid : G (x + h) - scalarSecondJetPolynomial
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) (x + h) =
        G (x + h) - G x - fderiv ℝ G x h -
          (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ G) x h h := by
      dsimp only [scalarSecondJetPolynomial, secondJetPolynomial]
      simp only [add_sub_cancel_left]
      ring
    rw [hid]
    exact (hb x hx h hh).2
  have hfirstRem : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
      ‖fderiv ℝ G (x + h) - fderiv ℝ G x -
        fderiv ℝ (fderiv ℝ G) x h‖ ≤ η * ‖h‖ := by
    intro η hη
    obtain ⟨r, hr, hb⟩ := hrem η hη
    exact ⟨r, hr, fun x hx h hh ↦ (hb x hx h hh).1⟩
  refine ⟨K, hKH, hK, hloss, hHK, hscalar, ?_⟩
  intro η hη
  obtain ⟨r, hr, hb⟩ := uniform_original_seed_normalization hG hLip hK hHK hfirstRem
    eL.open_target (hN.of_le (by simp)) (fun x hx ↦ hlegal x (hHC (hKH hx))) hη
  refine ⟨r, hr, ?_⟩
  intro x hx h hh hy
  let B := fderiv ℝ (fderiv ℝ G) x
  let P := scalarSecondJetPolynomial (x, G x, fderiv ℝ G x, B)
  have hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt G (fderiv ℝ G y) y :=
    Filter.Eventually.of_forall fun y ↦ (hG.differentiable one_ne_zero y).hasFDerivAt
  have hsym : ∀ v w : E, B v w = B w v :=
    second_derivative_symmetric_of_eventually hfirst (hsecond x (hKH hx)).hasFDerivAt
  have hDP : fderiv ℝ P (x + h) = fderiv ℝ G x + B h := by
    simpa only [P, scalarSecondJetPolynomial, add_sub_cancel_left] using
      (hasFDerivAt_secondJetPolynomial x (G x) (fderiv ℝ G x) B hsym (x + h)).fderiv
  have hfixed := (hspec (x + h, fderiv ℝ G (x + h)) (hlegal (x + h) hy)).2.2.2.2
    (henergy (x + h) hy)
  obtain ⟨_, hmodel, hbound⟩ := hb x hx h hh
  have hpoly : (x + h, fderiv ℝ P (x + h)) ∈ eL.target := by
    rw [hDP]
    exact hmodel
  change (x + h, fderiv ℝ P (x + h)) ∈ eL.target ∧
    F.covectorNormalization old eL c (x + h, fderiv ℝ P (x + h)) ∈
      chartEnergyDomain old ∧
    ‖eL.symm (x + h, fderiv ℝ G (x + h)) -
      F.covectorNormalization old eL c (x + h, fderiv ℝ P (x + h))‖ ≤ η * ‖h‖
  refine ⟨hpoly, (hspec _ hpoly).2.1, ?_⟩
  rw [hfixed] at hbound
  rw [hDP]
  exact hbound

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
