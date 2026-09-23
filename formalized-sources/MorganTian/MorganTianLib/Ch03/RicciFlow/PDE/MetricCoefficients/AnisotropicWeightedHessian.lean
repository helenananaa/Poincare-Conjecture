import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianEstimate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** anisotropic weighted hessian. -/
theorem anisotropic_weighted_hessian 
    (B : E3 ≃L[ℝ] E3) (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ i j : Fin 3,
      let H := fun y : E3 => fderiv ℝ (fun z : E3 => fderiv ℝ (anisotropicHeatKernel B t) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1);
      Integrable (fun y : E3 => |H y| *‖y‖^alpha) volume ∧
        (∫ y : E3, |H y| *‖y‖^alpha) ≤ C*t^(alpha/2-1) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨Ciso, hCiso, hmoment⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_weighted_hessian_recursive
      alpha ha ha1
  let L : E3 →L[ℝ] E3 := B.toContinuousLinearMap
  let Ls : E3 →L[ℝ] E3 := B.symm.toContinuousLinearMap
  let A : ℝ := (1 + ‖Ls‖) ^ 2
  let Q : ℝ := (1 + ‖L‖) ^ alpha
  let C : ℝ := 9 * A * Q * Ciso
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro t ht i j
  let K : E3 → ℝ := MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t
  let H : E3 → ℝ := fun y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (anisotropicHeatKernel B t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
  let F : E3 → ℝ := fun y => |H y| * ‖y‖ ^ alpha
  let U : E3 := Ls (EuclideanSpace.single i 1)
  let V : E3 := Ls (EuclideanSpace.single j 1)
  let D : E3 → ℝ := fun y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ K z U) y V
  let I : Fin 3 → Fin 3 → E3 → ℝ := fun k l z =>
    fderiv ℝ (fun w : E3 => fderiv ℝ K w (EuclideanSpace.single k 1)) z
      (EuclideanSpace.single l 1)
  let S : E3 → ℝ := fun z => ∑ k : Fin 3, ∑ l : Fin 3,
    |I k l z| * ‖z‖ ^ alpha
  let G : E3 → ℝ := fun z => (A * Q) * S z
  change Integrable F volume ∧ (∫ y : E3, F y) ≤ C * t ^ (alpha / 2 - 1)

  have hKcont : ContDiff ℝ ∞ K := by
    simpa [K] using
      (MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_heat_equation ht).1
  have hKtwo : ContDiff ℝ 2 K := by
    apply contDiffOn_univ.mp
    intro x hx
    have hx2 : ContDiffAt ℝ 2 K x := by
      intro n hn
      exact hKcont.contDiffAt (x := x) n (by simp)
    exact hx2.contDiffWithinAt
  have hKfd : ContDiff ℝ 1 (fderiv ℝ K) := hKtwo.fderiv_right (by norm_num)
  have hfirst : ContDiff ℝ 1 (fun z : E3 => fderiv ℝ K z U) :=
    hKfd.clm_apply contDiff_const
  have hsecond : Continuous (fderiv ℝ (fun z : E3 => fderiv ℝ K z U)) :=
    hfirst.continuous_fderiv (by norm_num)
  have hDcont : Continuous D := hsecond.clm_apply continuous_const
  have hHcont : Continuous H := by
    have heq : H = fun y : E3 =>
        |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ * D (B.symm y) := by
      funext y
      simpa [H, D, U, V, K, Ls] using
        (anisotropic_hessian_formula B t ht y
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    rw [heq]
    exact continuous_const.mul (hDcont.comp B.symm.continuous)
  have hFcont : Continuous F := by
    dsimp [F]
    exact hHcont.abs.mul (continuous_norm.rpow_const (fun _ => Or.inr ha.le))
  have hFnonneg (y : E3) : 0 ≤ F y := by
    dsimp [F]
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hentry_diff (x : E3) (k : Fin 3) :
      DifferentiableAt ℝ (fun z : E3 => fderiv ℝ K z (EuclideanSpace.single k 1)) x := by
    have hK2 : ContDiffAt ℝ 2 K x := by
      intro n hn
      exact hKcont.contDiffAt (x := x) n (by simp)
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ K) x := hK2.fderiv_right (by norm_num)
    exact (hfd.clm_apply contDiffAt_const).differentiableAt (by norm_num)

  have hdecomp (v : E3) :
      v = ∑ k : Fin 3, v k • EuclideanSpace.single k 1 := by
    ext k
    simp [Pi.single_apply]
  have hUfun : (fun z : E3 => fderiv ℝ K z U) =
      (fun z => ∑ k : Fin 3, U k • fderiv ℝ K z (EuclideanSpace.single k 1)) := by
    funext z
    calc
      fderiv ℝ K z U = fderiv ℝ K z (∑ k : Fin 3, U k • EuclideanSpace.single k 1) := by
        exact congrArg (fun v : E3 => fderiv ℝ K z v) (hdecomp U)
      _ = ∑ k : Fin 3, U k • fderiv ℝ K z (EuclideanSpace.single k 1) := by
        simp only [map_sum, map_smul]
  have hderivU : fderiv ℝ (fun z : E3 => fderiv ℝ K z U) =
      (fun x : E3 => ∑ k : Fin 3,
        U k • fderiv ℝ (fun z : E3 => fderiv ℝ K z (EuclideanSpace.single k 1)) x) := by
    funext x
    have hsum : HasFDerivAt
        (fun z : E3 => ∑ k : Fin 3,
          U k • fderiv ℝ K z (EuclideanSpace.single k 1))
        (∑ k : Fin 3,
          U k • fderiv ℝ (fun z : E3 => fderiv ℝ K z (EuclideanSpace.single k 1)) x) x := by
      apply HasFDerivAt.fun_sum (u := Finset.univ)
      intro k hk
      exact (hentry_diff x k).hasFDerivAt.const_smul (U k)
    calc
      fderiv ℝ (fun z : E3 => fderiv ℝ K z U) x =
          fderiv ℝ (fun z : E3 => ∑ k : Fin 3,
            U k • fderiv ℝ K z (EuclideanSpace.single k 1)) x := by rw [hUfun]
      _ = ∑ k : Fin 3,
          U k • fderiv ℝ (fun z : E3 => fderiv ℝ K z (EuclideanSpace.single k 1)) x :=
            hsum.fderiv
  have hVcoord (z : E3) (k : Fin 3) :
      fderiv ℝ (fun w : E3 => fderiv ℝ K w (EuclideanSpace.single k 1)) z V =
        ∑ l : Fin 3, V l * I k l z := by
    calc
      fderiv ℝ (fun w : E3 => fderiv ℝ K w (EuclideanSpace.single k 1)) z V =
          fderiv ℝ (fun w : E3 => fderiv ℝ K w (EuclideanSpace.single k 1)) z
            (∑ l : Fin 3, V l • EuclideanSpace.single l 1) := by
              exact congrArg
                (fun v : E3 =>
                  fderiv ℝ (fun w : E3 => fderiv ℝ K w (EuclideanSpace.single k 1)) z v)
                (hdecomp V)
      _ = ∑ l : Fin 3, V l * I k l z := by
        simp only [map_sum, map_smul, smul_eq_mul, I]
  have hcoord (z : E3) :
      fderiv ℝ (fun w : E3 => fderiv ℝ K w U) z V =
        ∑ k : Fin 3, ∑ l : Fin 3, (U k * V l) * I k l z := by
    rw [hderivU]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    calc
      ∑ k : Fin 3, U k *
          (fderiv ℝ (fun w : E3 => fderiv ℝ K w (EuclideanSpace.single k 1)) z) V =
        ∑ k : Fin 3, U k * (∑ l : Fin 3, V l * I k l z) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hVcoord z k]
      _ = ∑ k : Fin 3, ∑ l : Fin 3, (U k * V l) * I k l z := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          ring

  have hdet : LinearMap.det B.toLinearEquiv.toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero
  have hdpos : 0 < |LinearMap.det B.toLinearEquiv.toLinearMap| := abs_pos.mpr hdet
  have hdetL : |L.det| = |LinearMap.det B.toLinearEquiv.toLinearMap| := by
    rw [ContinuousLinearMap.det]
    rfl
  have hdirection (z : E3) :
      H (L z) = |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ *
        fderiv ℝ (fun w : E3 => fderiv ℝ K w U) z V := by
    simpa [H, U, V, K, L, Ls] using
      (anisotropic_hessian_formula B t ht (L z)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
  have hcancel (z : E3) :
      |L.det| • F (L z) =
        |fderiv ℝ (fun w : E3 => fderiv ℝ K w U) z V| * ‖L z‖ ^ alpha := by
    change |L.det| * (|H (L z)| * ‖L z‖ ^ alpha) = _
    rw [hdetL, hdirection, abs_mul, abs_inv]
    simp only [abs_abs]
    field_simp [ne_of_gt hdpos]

  have hcoordnorm (k : Fin 3) : |U k| ≤ ‖Ls‖ := by
    have hk : |U k| ≤ ‖U‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le U k)
    have hUnorm : ‖U‖ ≤ ‖Ls‖ := by
      calc
        ‖U‖ = ‖Ls (EuclideanSpace.single i 1)‖ := rfl
        _ ≤ ‖Ls‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := Ls.le_opNorm _
        _ = ‖Ls‖ := by simp
    exact hk.trans hUnorm
  have hcoordnormV (l : Fin 3) : |V l| ≤ ‖Ls‖ := by
    have hl : |V l| ≤ ‖V‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le V l)
    have hVnorm : ‖V‖ ≤ ‖Ls‖ := by
      calc
        ‖V‖ = ‖Ls (EuclideanSpace.single j 1)‖ := rfl
        _ ≤ ‖Ls‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := Ls.le_opNorm _
        _ = ‖Ls‖ := by simp
    exact hl.trans hVnorm
  have hcoeff (k l : Fin 3) : |U k * V l| ≤ A := by
    rw [abs_mul]
    dsimp [A]
    calc
      |U k| * |V l| ≤ ‖Ls‖ * ‖Ls‖ :=
        mul_le_mul (hcoordnorm k) (hcoordnormV l) (abs_nonneg _) (norm_nonneg _)
      _ ≤ (1 + ‖Ls‖) * (1 + ‖Ls‖) := by
        exact mul_le_mul (by linarith [norm_nonneg Ls])
          (by linarith [norm_nonneg Ls]) (norm_nonneg Ls) (by positivity)
      _ = (1 + ‖Ls‖) ^ 2 := by ring
  have hweight (z : E3) : ‖L z‖ ^ alpha ≤ Q * ‖z‖ ^ alpha := by
    have hnorm : ‖L z‖ ≤ (1 + ‖L‖) * ‖z‖ := by
      calc
        ‖L z‖ ≤ ‖L‖ * ‖z‖ := L.le_opNorm z
        _ ≤ (1 + ‖L‖) * ‖z‖ := by
          exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg L]) (norm_nonneg z)
    calc
      ‖L z‖ ^ alpha ≤ ((1 + ‖L‖) * ‖z‖) ^ alpha :=
        Real.rpow_le_rpow (norm_nonneg _) hnorm ha.le
      _ = Q * ‖z‖ ^ alpha := by
        rw [Real.mul_rpow (by positivity) (norm_nonneg z)]
  have hsumcoeff (z : E3) :
      (∑ k : Fin 3, ∑ l : Fin 3, |U k * V l| * |I k l z|) ≤
        A * (∑ k : Fin 3, ∑ l : Fin 3, |I k l z|) := by
    calc
      (∑ k : Fin 3, ∑ l : Fin 3, |U k * V l| * |I k l z|) ≤
          ∑ k : Fin 3, ∑ l : Fin 3, A * |I k l z| := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro l hl
        exact mul_le_mul_of_nonneg_right (hcoeff k l) (abs_nonneg _)
      _ = A * (∑ k : Fin 3, ∑ l : Fin 3, |I k l z|) := by
        simp only [Finset.mul_sum]
  have hpoint (z : E3) :
      |L.det| • F (L z) ≤ G z := by
    rw [hcancel]
    have habs : |fderiv ℝ (fun w : E3 => fderiv ℝ K w U) z V| ≤
        ∑ k : Fin 3, ∑ l : Fin 3, |U k * V l| * |I k l z| := by
      rw [hcoord z]
      calc
        |∑ k : Fin 3, ∑ l : Fin 3, (U k * V l) * I k l z| ≤
            ∑ k : Fin 3, |∑ l : Fin 3, (U k * V l) * I k l z| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin 3, ∑ l : Fin 3, |U k * V l| * |I k l z| := by
          apply Finset.sum_le_sum
          intro k hk
          calc
            |∑ l : Fin 3, (U k * V l) * I k l z| ≤
                ∑ l : Fin 3, |(U k * V l) * I k l z| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ l : Fin 3, |U k * V l| * |I k l z| := by simp [abs_mul]
    have hnonnegS : 0 ≤ ∑ k : Fin 3, ∑ l : Fin 3, |I k l z| := by
      positivity
    have hTmul :
        (∑ k : Fin 3, ∑ l : Fin 3, |I k l z|) * ‖z‖ ^ alpha = S z := by
      dsimp [S]
      simp only [Finset.sum_mul]
    calc
      |fderiv ℝ (fun w : E3 => fderiv ℝ K w U) z V| * ‖L z‖ ^ alpha ≤
          (A * (∑ k : Fin 3, ∑ l : Fin 3, |I k l z|)) * ‖L z‖ ^ alpha :=
        mul_le_mul_of_nonneg_right (habs.trans (hsumcoeff z)) (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ (A * (∑ k : Fin 3, ∑ l : Fin 3, |I k l z|)) * (Q * ‖z‖ ^ alpha) :=
        mul_le_mul_of_nonneg_left (hweight z) (mul_nonneg (le_of_lt hApos) hnonnegS)
      _ = (A * Q) *
          ((∑ k : Fin 3, ∑ l : Fin 3, |I k l z|) * ‖z‖ ^ alpha) := by ring
      _ = G z := by
        rw [hTmul]

  have hsumInt : Integrable S volume := by
    dsimp [S]
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro l hl
    simpa [I, K] using (hmoment t ht k l).1
  have hGint : Integrable G volume := by
    dsimp [G]
    exact hsumInt.const_mul (A * Q)
  have hsumIntegral :
      (∫ z : E3, S z) = ∑ k : Fin 3, ∑ l : Fin 3,
        ∫ z : E3, |I k l z| * ‖z‖ ^ alpha := by
    dsimp [S]
    calc
      (∫ z : E3, ∑ k : Fin 3, ∑ l : Fin 3,
          |I k l z| * ‖z‖ ^ alpha) =
          ∑ k : Fin 3, ∫ z : E3, ∑ l : Fin 3,
            |I k l z| * ‖z‖ ^ alpha := by
              apply integral_finsetSum
              intro k hk
              apply integrable_finsetSum
              intro l hl
              simpa [I, K] using (hmoment t ht k l).1
      _ = ∑ k : Fin 3, ∑ l : Fin 3,
          ∫ z : E3, |I k l z| * ‖z‖ ^ alpha := by
            apply Finset.sum_congr rfl
            intro k hk
            apply integral_finsetSum
            intro l hl
            simpa [I, K] using (hmoment t ht k l).1
  have hsumBound :
      (∫ z : E3, S z) ≤ 9 * (Ciso * t ^ (alpha / 2 - 1)) := by
    rw [hsumIntegral]
    calc
      (∑ k : Fin 3, ∑ l : Fin 3,
          ∫ z : E3, |I k l z| * ‖z‖ ^ alpha) ≤
          ∑ k : Fin 3, ∑ l : Fin 3, Ciso * t ^ (alpha / 2 - 1) := by
            apply Finset.sum_le_sum
            intro k hk
            apply Finset.sum_le_sum
            intro l hl
            simpa [I, K] using (hmoment t ht k l).2
      _ = 9 * (Ciso * t ^ (alpha / 2 - 1)) := by
        simp [Finset.sum_const, Fintype.card_fin]
        ring
  have hGbound : (∫ z : E3, G z) ≤ C * t ^ (alpha / 2 - 1) := by
    rw [show (∫ z : E3, G z) = (A * Q) * (∫ z : E3, S z) by
      dsimp [G]
      rw [integral_const_mul]]
    dsimp [C]
    calc
      (A * Q) * (∫ z : E3, S z) ≤
          (A * Q) * (9 * (Ciso * t ^ (alpha / 2 - 1))) :=
        mul_le_mul_of_nonneg_left hsumBound (mul_nonneg (le_of_lt hApos) (le_of_lt hQpos))
      _ = 9 * A * Q * Ciso * t ^ (alpha / 2 - 1) := by ring

  let f : E3 → E3 := fun z => B z
  have hfSurj : Function.Surjective f := by
    intro y
    exact ⟨B.symm y, by simp [f]⟩
  have himage : f '' (Set.univ : Set E3) = Set.univ :=
    Set.image_univ_of_surjective hfSurj
  have htransCont : Continuous (fun z : E3 => |L.det| • F (L z)) := by
    change Continuous (fun z : E3 => |L.det| * F (L z))
    exact continuous_const.mul (hFcont.comp L.continuous)
  have hdenNonneg (z : E3) : 0 ≤ |L.det| • F (L z) := by
    change 0 ≤ |L.det| * (|H (L z)| * ‖L z‖ ^ alpha)
    positivity
  have hSnonneg (z : E3) : 0 ≤ S z := by
    dsimp [S]
    positivity
  have hGnonneg (z : E3) : 0 ≤ G z := by
    dsimp [G]
    exact mul_nonneg (mul_nonneg (le_of_lt hApos) (le_of_lt hQpos)) (hSnonneg z)
  have htransInt : Integrable (fun z : E3 => |L.det| • F (L z)) volume := by
    refine Integrable.mono' (f := fun z : E3 => |L.det| • F (L z)) (g := G)
      hGint htransCont.aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hdenNonneg z)]
    exact hpoint z
  have hf' : ∀ z ∈ (Set.univ : Set E3), HasFDerivWithinAt f L Set.univ z := by
    intro z hz
    simpa [f, L] using
      (ContinuousLinearMap.hasFDerivAt L (x := z)).hasFDerivWithinAt (s := Set.univ)
  have hfinj : Set.InjOn f (Set.univ : Set E3) := by
    intro x hx y hy hxy
    exact B.injective hxy
  have hchangeInt :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hfinj F
  have hFintOn : IntegrableOn F (f '' (Set.univ : Set E3)) volume :=
    hchangeInt.mpr (integrableOn_univ.mpr (by simpa [f, L] using htransInt))
  have hFint : Integrable F volume := by
    rw [himage] at hFintOn
    exact integrableOn_univ.mp hFintOn
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hfinj F
  have hchangeIntEq :
      (∫ y : E3, F y) = ∫ z : E3, |L.det| • F (f z) := by
    simpa [himage] using hchange
  refine ⟨hFint, ?_⟩
  calc
    (∫ y : E3, F y) = ∫ z : E3, |L.det| • F (f z) := hchangeIntEq
    _ ≤ ∫ z : E3, G z := by
      apply integral_mono htransInt hGint
      intro z
      simpa [f, L] using hpoint z
    _ ≤ C * t ^ (alpha / 2 - 1) := hGbound
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
