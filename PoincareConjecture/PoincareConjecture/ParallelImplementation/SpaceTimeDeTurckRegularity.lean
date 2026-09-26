import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.SmoothOperatorInverse
import PoincareConjecture.ParallelImplementation.PositiveOperatorInvertible
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SpaceTimeDeTurckRegularity
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open scoped ContDiff BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem contDiff_spacetime_deturck
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (u : ℝ × E3 → E6) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ (t : ℝ) (x v : E3), v ≠ 0 →
      0 < inner ℝ (metricOp E (fun y => u (t,y)) x v) v) :
    ∀ k : Fin 3, ContDiff ℝ ∞
      (fun q : ℝ × E3 => deturckField E (fun y => u (q.1,y)) q.2 k) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hfullDeriv : ContDiff ℝ ∞ (fderiv ℝ u) :=
    hu.fderiv_right (m := ∞) (by simp)
  have hsliceDeriv (q : ℝ × E3) :
      fderiv ℝ (fun y : E3 => u (q.1, y)) q.2 =
        (fderiv ℝ u q).comp (ContinuousLinearMap.inr ℝ ℝ E3) := by
    have huq : DifferentiableAt ℝ u q :=
      (hu.differentiable (by simp)).differentiableAt
    have hinc : fderiv ℝ (fun y : E3 => (q.1, y)) q.2 =
        ContinuousLinearMap.inr ℝ ℝ E3 :=
      (hasFDerivAt_prodMk_right q.1 q.2).fderiv
    simpa only [Function.comp_def, hinc] using
      (fderiv_comp (f := fun y : E3 => (q.1, y)) q.2 huq
        (hasFDerivAt_prodMk_right q.1 q.2).differentiableAt)
  have hspatial : ∀ a : Idx, ContDiff ℝ ∞
      (fun q : ℝ × E3 =>
        fderiv ℝ (fun y : E3 => u (q.1, y)) q.2 (EuclideanSpace.single a 1)) := by
    intro a
    have happly : ContDiff ℝ ∞ (fun q : ℝ × E3 =>
        (fderiv ℝ u q) (ContinuousLinearMap.inr ℝ ℝ E3
          (EuclideanSpace.single a 1))) :=
      hfullDeriv.clm_apply contDiff_const
    have heq : (fun q : ℝ × E3 =>
        fderiv ℝ (fun y : E3 => u (q.1, y)) q.2 (EuclideanSpace.single a 1)) =
      (fun q : ℝ × E3 => (fderiv ℝ u q) (ContinuousLinearMap.inr ℝ ℝ E3
          (EuclideanSpace.single a 1))) := by
      funext q
      rw [hsliceDeriv q]
      rfl
    rw [heq]
    exact happly
  have hmetric : ContDiff ℝ ∞
      (fun q : ℝ × E3 => metricOp E (fun y => u (q.1, y)) q.2) := by
    change ContDiff ℝ ∞ (fun q : ℝ × E3 =>
      (1 : E3 →L[ℝ] E3) + E (u q))
    exact contDiff_const.add (E.contDiff.comp hu)
  have hunit : ∀ q : ℝ × E3,
      IsUnit (metricOp E (fun y => u (q.1, y)) q.2) := by
    intro q
    apply PositiveOperatorInvertible.positive_operator_isUnit
    intro v hv
    exact hpos q.1 q.2 v hv
  have hinv : ContDiff ℝ ∞ (fun q : ℝ × E3 =>
      Ring.inverse (metricOp E (fun y => u (q.1, y)) q.2)) := by
    rw [contDiff_iff_contDiffAt]
    intro q
    obtain ⟨A, hA⟩ := hunit q
    have hInv := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) A
    rw [hA] at hInv
    exact hInv.comp q hmetric.contDiffAt
  have hinvCoeff : ∀ i j : Idx, ContDiff ℝ ∞
      (fun q : ℝ × E3 => inverseCoefficients E (fun y => u (q.1, y)) q.2 i j) := by
    intro i j
    have hv : ContDiff ℝ ∞ (fun q : ℝ × E3 =>
        Ring.inverse (metricOp E (fun y => u (q.1, y)) q.2)
          (EuclideanSpace.single j 1)) :=
      hinv.clm_apply contDiff_const
    change ContDiff ℝ ∞ (fun q : ℝ × E3 =>
      (Ring.inverse (metricOp E (fun y => u (q.1, y)) q.2)
        (EuclideanSpace.single j 1)) i)
    exact (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := i)).comp hv
  have hfirst : ∀ a i j : Idx, ContDiff ℝ ∞
      (fun q : ℝ × E3 =>
        firstCoefficients (fun y => u (q.1, y)) q.2 a i j) := by
    intro a i j
    have hv : ContDiff ℝ ∞ (fun q : ℝ × E3 =>
        fderiv ℝ (fun y : E3 => u (q.1, y)) q.2
          (EuclideanSpace.single a 1)) := hspatial a
    fin_cases i <;> fin_cases j <;>
      simp [firstCoefficients, MorganTianLib.MetricCoefficient.symmetricSixMatrix] <;>
      exact (contDiff_piLp_apply (𝕜 := ℝ) (p := 2)).comp hv
  have hlower : ∀ l i j : Idx, ContDiff ℝ ∞
      (fun q : ℝ × E3 =>
        lowerChristoffel (firstCoefficients (fun y => u (q.1, y)) q.2) l i j) := by
    intro l i j
    simp only [lowerChristoffel]
    exact contDiff_const.mul
      (((hfirst i j l).add (hfirst j i l)).sub (hfirst l i j))
  have hchrist : ∀ k i j : Idx, ContDiff ℝ ∞
      (fun q : ℝ × E3 =>
        christoffelField E (fun y => u (q.1, y)) q.2 k i j) := by
    intro k i j
    change ContDiff ℝ ∞ (fun q : ℝ × E3 =>
      ∑ l : Idx,
        inverseCoefficients E (fun y => u (q.1, y)) q.2 k l *
          lowerChristoffel (firstCoefficients (fun y => u (q.1, y)) q.2) l i j)
    apply ContDiff.sum
    intro l hl
    exact (hinvCoeff k l).mul (hlower l i j)
  intro k
  change ContDiff ℝ ∞ (fun q : ℝ × E3 =>
    ∑ a : Idx, ∑ b : Idx,
      inverseCoefficients E (fun y => u (q.1, y)) q.2 a b *
        christoffelField E (fun y => u (q.1, y)) q.2 k a b)
  apply ContDiff.sum
  intro a ha
  apply ContDiff.sum
  intro b hb
  exact (hinvCoeff a b).mul (hchrist k a b)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SpaceTimeDeTurckRegularity
