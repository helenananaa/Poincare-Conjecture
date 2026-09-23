import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoefficientConnectionBilin
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffelSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** coefficient connection differentiable. -/
theorem coefficient_connection_differentiable (G : E3 → (E3 →L[ℝ] E3)) (x : E3) (hG : ContDiffAt ℝ 2 G x)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) :
    DifferentiableAt ℝ (fun y : E3 => coefficientConnectionBilin (G y)
      (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1))) x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hGdiff : DifferentiableAt ℝ G x := hG.differentiableAt (by norm_num)
  have hDf : DifferentiableAt ℝ (fderiv ℝ G) x := by
    have hDf' : ContDiffAt ℝ 1 (fderiv ℝ G) x :=
      hG.fderiv_right (by norm_num)
    exact hDf'.differentiableAt (by norm_num)
  have hJets : DifferentiableAt ℝ
      (fun y : E3 => fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) x := by
    apply differentiableAt_pi.mpr
    intro r
    exact hDf.clm_apply (differentiableAt_const (EuclideanSpace.single r (1 : ℝ)))
  have hInput : DifferentiableAt ℝ
      (fun y : E3 => (G y, fun r : Fin 3 =>
        fderiv ℝ G y (EuclideanSpace.single r 1))) x := hGdiff.prodMk hJets
  have hChristoffel : ∀ k i j : Fin 3,
      DifferentiableAt ℝ
        (fun y : E3 => coordinateChristoffel (G y)
          (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k i j) x := by
    intro k i j
    have hsmooth := coordinate_christoffel_smooth (G x) c hc hpos
      (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) k i j
    simpa [Function.comp_def] using
      DifferentiableAt.fun_comp'
        (f := fun y : E3 =>
          (G y, fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)))
        (g := fun q => coordinateChristoffel q.1 q.2 k i j)
        (hf := hInput) (hg := hsmooth.differentiableAt (by simp))
  have hterm : ∀ i j k : Fin 3,
      DifferentiableAt ℝ
        (fun y : E3 =>
          (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
            ((EuclideanSpace.proj (𝕜 := ℝ) j).smulRight
              (coordinateChristoffel (G y)
                (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k i j •
                EuclideanSpace.single k (1 : ℝ)))) x := by
    intro i j k
    have hχ := hChristoffel k i j
    let B := (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
      ((EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (EuclideanSpace.single k (1 : ℝ)))
    have hscalar : DifferentiableAt ℝ
        (fun y : E3 => coordinateChristoffel (G y)
          (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k i j • B) x :=
      hχ.smul_const B
    have heq : (fun y : E3 =>
        (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
          ((EuclideanSpace.proj (𝕜 := ℝ) j).smulRight
            (coordinateChristoffel (G y)
              (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k i j •
              EuclideanSpace.single k (1 : ℝ)))) =
        (fun y : E3 => coordinateChristoffel (G y)
          (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k i j • B) := by
      funext y
      ext v w
      simp [B, ContinuousLinearMap.smulRight_apply, smul_smul,
        mul_comm, mul_left_comm]
    rw [heq]
    exact hscalar
  have hsum : DifferentiableAt ℝ
      (fun y : E3 => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
          ((EuclideanSpace.proj (𝕜 := ℝ) j).smulRight
            (coordinateChristoffel (G y)
              (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k i j •
              EuclideanSpace.single k (1 : ℝ)))) x := by
    apply DifferentiableAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    intro i hi
    apply DifferentiableAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    intro j hj
    apply DifferentiableAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    intro k hk
    exact hterm i j k
  simpa only [coefficientConnectionBilin] using hsum
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
