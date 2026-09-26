import PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient
import PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
import PoincareConjecture.ParallelImplementation.BoundedInitialDataJetExtension
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.UniformStationaryFullJetDifference
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Uniform difference bounds for the SAME actual stationary initial lift in
full parabolic jet norm, not for an evolved solution. -/
theorem uniform_stationary_full_jet_differences
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 ≤ T → ∀ s : FullJet T,
      (∀ p : Slab T, s.1.1.1.1 p = u p.2 ∧
        s.1.1.1.2.1 p = fderiv ℝ u p.2 ∧
        s.1.1.1.2.2 p = fderiv ℝ (fderiv ℝ u) p.2 ∧ s.1.2 p = 0) →
      (∀ p : Pair T, s.1.1.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (s.1.1.1.2.2 p.1.1 - s.1.1.1.2.2 p.1.2)) →
      (∀ p : Pair T, s.2 p = 0) →
      ∀ (i : Fin 3) (h : ℝ), h ≠ 0 → ‖finiteSpatialDifferenceJet s i h‖ ≤ C :=
/- SWARM_PROOF_BEGIN -/
by
  letI : NormedAddCommGroup (E3 →L[ℝ] E3) := inferInstance
  letI : NormedSpace ℝ (E3 →L[ℝ] E3) := inferInstance
  letI : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
  letI : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
  letI : NormedAddCommGroup ((E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ ((E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedAddCommGroup
      ((E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ]
        (E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ
      ((E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ]
        (E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
  obtain ⟨C, hCpos, hUniform⟩ :=
    PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient.exists_uniform_initial_difference_jets
      u hu hc alpha ha ha1
  refine ⟨C, hCpos, ?_⟩
  intro T hT s hsData hsHessianInc hsTimeInc i h hh
  let spatialUnit :=
    PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.spatialUnit
  let shiftPoint {T : ℝ} (p : Slab T) (j : Fin 3) (r : ℝ) : Slab T :=
    PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint p j r
  let spatialShiftPairMap {T : ℝ} (j : Fin 3) (r : ℝ) : Pair T → Pair T :=
    PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialShiftPairMap j r
  let spatialShiftPair_rho {T : ℝ} (j : Fin 3) (r : ℝ) (p : Pair T) :=
    PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialShiftPair_rho j r p
  let e : E3 := spatialUnit i
  have he : ‖e‖ ≤ 1 := by
    simp [e, spatialUnit,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.spatialUnit]
  obtain ⟨u0, A0, H0, hvalues, hu0, hA0, hu0norm, hA0norm, hH0norm,
      hH0holder⟩ := hUniform h hh e he
  obtain ⟨q, hqSpace, hqTime, hqTimeInc, hqData, _, hqBound⟩ :=
    PoincareConjecture.ParallelImplementation.BoundedInitialDataJetExtension.exists_bounded_initial_jet_extension
      T alpha C hT ha (le_of_lt hCpos) u0 A0 H0 hu0 hA0 hH0holder

  let D1 : E3 → E3 →L[ℝ] E6 := fderiv ℝ u
  let D2 : E3 → E3 →L[ℝ] E3 →L[ℝ] E6 := fderiv ℝ D1
  let Q := fun {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E3 → F) (x : E3) => h⁻¹ • (f (x + h • e) - f x)
  let dq : E3 → E6 :=
    PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient.differenceQuotient
      u h e

  have quotient_fderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E3 → F) (hf : Differentiable ℝ f) :
      fderiv ℝ (Q f) = Q (fderiv ℝ f : E3 → E3 →L[ℝ] F) := by
    funext x
    change fderiv ℝ (fun y : E3 => h⁻¹ • (f (y + h • e) - f y)) x =
      h⁻¹ • (fderiv ℝ f (x + h • e) - fderiv ℝ f x)
    have hshift : Differentiable ℝ (fun y : E3 => f (y + h • e)) :=
      hf.comp (differentiable_id.add_const (h • e))
    have hdiff : DifferentiableAt ℝ (fun y : E3 => f (y + h • e) - f y) x :=
      (hshift x).sub (hf x)
    rw [fderiv_fun_const_smul hdiff (h⁻¹)]
    change h⁻¹ • fderiv ℝ ((fun y : E3 => f (y + h • e)) - f) x =
      h⁻¹ • (fderiv ℝ f (x + h • e) - fderiv ℝ f x)
    rw [fderiv_sub (hshift x) (hf x)]
    rw [fderiv_comp_add_right]

  have huDiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hD1cd : ContDiff ℝ 1 D1 := by
    simpa [D1] using hu.fderiv_right (m := 1)
      (show (2 : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hD1Diff : Differentiable ℝ D1 := hD1cd.differentiable (by norm_num)
  have hq1 : fderiv ℝ dq = Q D1 := by
    change fderiv ℝ (Q u) = Q D1
    simpa [dq, Q, D1,
      PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient.differenceQuotient] using quotient_fderiv u huDiff
  have hq2 : fderiv ℝ (fderiv ℝ dq) = Q D2 := by
    rw [hq1]
    simpa [Q, D2] using quotient_fderiv D1 hD1Diff
  have hq1eval (x : E3) : fderiv ℝ dq x =
      h⁻¹ • (fderiv ℝ u (x + h • e) - fderiv ℝ u x) := by
    simpa [Q, D1] using congrFun hq1 x
  have hq2eval (x : E3) : fderiv ℝ (fderiv ℝ dq) x =
      h⁻¹ • (fderiv ℝ (fderiv ℝ u) (x + h • e) -
        fderiv ℝ (fderiv ℝ u) x) := by
    simpa [Q, D1, D2] using congrFun hq2 x

  have hsU (p : Slab T) : s.1.1.1.1 p = u p.2 := (hsData p).1
  have hsD1 (p : Slab T) : s.1.1.1.2.1 p = fderiv ℝ u p.2 :=
    (hsData p).2.1
  have hsD2 (p : Slab T) : s.1.1.1.2.2 p = fderiv ℝ (fderiv ℝ u) p.2 :=
    (hsData p).2.2.1
  have hsTime (p : Slab T) : s.1.2 p = 0 := (hsData p).2.2.2
  let r : FullJet T := finiteSpatialDifferenceJet s i h
  have hshiftCoord (p : Slab T) : (shiftPoint p i h).2 = p.2 + h • e := by
    rfl

  have hrU (p : Slab T) : r.1.1.1.1 p = u0 p.2 := by
    change h⁻¹ • (s.1.1.1.1 (shiftPoint p i h) - s.1.1.1.1 p) = u0 p.2
    rw [hsU (shiftPoint p i h), hsU p, (hvalues p.2).1]
    rw [hshiftCoord p]
    simp [PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient.differenceQuotient]
  have hrD1 (p : Slab T) : r.1.1.1.2.1 p = A0 p.2 := by
    change h⁻¹ • (s.1.1.1.2.1 (shiftPoint p i h) - s.1.1.1.2.1 p) = A0 p.2
    rw [hsD1 (shiftPoint p i h), hsD1 p, (hvalues p.2).2.1]
    rw [hshiftCoord p]
    simpa [dq, PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient.differenceQuotient] using (hq1eval p.2).symm
  have hrD2 (p : Slab T) : r.1.1.1.2.2 p = H0 p.2 := by
    change h⁻¹ • (s.1.1.1.2.2 (shiftPoint p i h) - s.1.1.1.2.2 p) = H0 p.2
    rw [hsD2 (shiftPoint p i h), hsD2 p, (hvalues p.2).2.2]
    rw [hshiftCoord p]
    simpa [dq, PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient.differenceQuotient] using (hq2eval p.2).symm
  have hrHessEq (p : Slab T) : r.1.1.1.2.2 p = q.1.1.1.2.2 p := by
    calc
      r.1.1.1.2.2 p = H0 p.2 := hrD2 p
      _ = q.1.1.1.2.2 p := ((hqData p).2.2.1).symm

  have hrHessianIncFormula (p : Pair T) :
      r.1.1.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (r.1.1.1.2.2 p.1.1 - r.1.1.1.2.2 p.1.2) := by
    change h⁻¹ •
        (s.1.1.2 (spatialShiftPairMap i h p) - s.1.1.2 p) =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((h⁻¹ • (s.1.1.1.2.2 (shiftPoint p.1.1 i h) -
            s.1.1.1.2.2 p.1.1)) -
          (h⁻¹ • (s.1.1.1.2.2 (shiftPoint p.1.2 i h) -
            s.1.1.1.2.2 p.1.2)))
    have hsIncShift := hsHessianInc (spatialShiftPairMap i h p)
    have hpairFst : (spatialShiftPairMap i h p).1.1 = shiftPoint p.1.1 i h := by
      rfl
    have hpairSnd : (spatialShiftPairMap i h p).1.2 = shiftPoint p.1.2 i h := by
      rfl
    have hsIncShift' : s.1.1.2 (spatialShiftPairMap i h p) =
        (parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) ^ alpha)⁻¹ •
          (s.1.1.1.2.2 (shiftPoint p.1.1 i h) -
            s.1.1.1.2.2 (shiftPoint p.1.2 i h)) := by
      simpa only [hpairFst, hpairSnd] using hsIncShift
    have hsIncBase := hsHessianInc p
    have hrhoShift :
        parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) =
          parabolicRho p.1.1 p.1.2 := spatialShiftPair_rho i h p
    rw [hsIncShift', hsIncBase]
    have hrhoPow :
        (parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) ^ alpha)⁻¹ =
          (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ := by rw [hrhoShift]
    rw [hrhoPow]
    simp only [smul_sub, smul_smul]
    have hcoeff : h⁻¹ * (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ * h⁻¹ := mul_comm _ _
    rw [hcoeff]
    abel_nf

  have hrTime (p : Slab T) : r.1.2 p = q.1.2 p := by
    change h⁻¹ • (s.1.2 (shiftPoint p i h) - s.1.2 p) = q.1.2 p
    rw [hsTime (shiftPoint p i h), hsTime p, (hqData p).2.2.2]
    simp
  have hrTimeInc (p : Pair T) : r.2 p = q.2 p := by
    change h⁻¹ • (s.2 (spatialShiftPairMap i h p) - s.2 p) = q.2 p
    rw [hsTimeInc (spatialShiftPairMap i h p), hsTimeInc p, hqTimeInc p]
    simp

  have heq : r = q := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · apply BoundedContinuousFunction.ext
            intro p
            exact (hrU p).trans ((hqData p).1).symm
          · apply Prod.ext
            · apply BoundedContinuousFunction.ext
              intro p
              exact (hrD1 p).trans ((hqData p).2.1).symm
            · apply BoundedContinuousFunction.ext
              intro p
              exact (hrD2 p).trans ((hqData p).2.2.1).symm
        · apply BoundedContinuousFunction.ext
          intro p
          calc
            r.1.1.2 p =
                (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
                  (r.1.1.1.2.2 p.1.1 - r.1.1.1.2.2 p.1.2) := hrHessianIncFormula p
            _ = q.1.1.2 p := by
              rw [hrHessEq p.1.1, hrHessEq p.1.2, hqSpace.2 p]
      · apply BoundedContinuousFunction.ext
        intro p
        exact hrTime p
    · apply BoundedContinuousFunction.ext
      intro p
      exact hrTimeInc p

  have hqBoundC : ‖q‖ ≤ C :=
    hqBound.trans (max_le hu0norm (max_le hA0norm (max_le hH0norm le_rfl)))
  calc
    ‖finiteSpatialDifferenceJet s i h‖ = ‖q‖ := by
      change ‖r‖ = ‖q‖
      rw [heq]
    _ ≤ C := hqBoundC
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.UniformStationaryFullJetDifference
