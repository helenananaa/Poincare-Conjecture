import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** diffusion cutoff commutator. -/
theorem diffusion_cutoff_commutator 
    (A : E3 →L[ℝ] E3) (f chi : E3 → ℝ) (x : E3)
    (hf : ContDiffAt ℝ 2 f x) (hchi : ContDiffAt ℝ 2 chi x) :
    let e := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ);
    let L := fun u : E3 → ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
      (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ u y (e j)) x (e i);
    L (fun y => chi y*f y) - chi x*L f = f x*L chi +
      ∑ i : Fin 3, ∑ j : Fin 3, (A (e j)) i *
        (fderiv ℝ chi x (e i)*fderiv ℝ f x (e j) +
          fderiv ℝ chi x (e j)*fderiv ℝ f x (e i)) :=
/- SWARM_PROOF_BEGIN -/
by
  let e := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)
  let L := fun u : E3 → ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
    (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ u y (e j)) x (e i)
  let p : E3 → ℝ := fun y => chi y * f y
  have hp : ContDiffAt ℝ 2 p x := hchi.mul hf
  have hsecond (i j : Fin 3) :
      fderiv ℝ (fun y : E3 => fderiv ℝ p y (e j)) x (e i) =
        chi x * fderiv ℝ (fun y : E3 => fderiv ℝ f y (e j)) x (e i) +
          f x * fderiv ℝ (fun y : E3 => fderiv ℝ chi y (e j)) x (e i) +
          (fderiv ℝ chi x (e i) * fderiv ℝ f x (e j) +
            fderiv ℝ chi x (e j) * fderiv ℝ f x (e i)) := by
    let dc : E3 → ℝ := fun y => fderiv ℝ chi y (e j)
    let dfj : E3 → ℝ := fun y => fderiv ℝ f y (e j)
    have hdcC : ContDiffAt ℝ 1 dc x := by
      exact (hchi.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    have hdfC : ContDiffAt ℝ 1 dfj x := by
      exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    have hpjC : ContDiffAt ℝ 1 (fun y : E3 => fderiv ℝ p y (e j)) x := by
      exact (hp.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    have hnear : ∀ᶠ y : E3 in 𝓝 x, ContDiffAt ℝ 2 chi y ∧ ContDiffAt ℝ 2 f y := by
      filter_upwards [hchi.eventually (by norm_num), hf.eventually (by norm_num)] with y hyc hyf
      exact ⟨hyc, hyf⟩
    have hlocal : (fun y : E3 => fderiv ℝ p y (e j)) =ᶠ[𝓝 x]
        (fun y => dc y * f y + chi y * dfj y) := by
      filter_upwards [hnear] with y hy
      have hm := fderiv_fun_mul
        (hy.1.differentiableAt (by norm_num)) (hy.2.differentiableAt (by norm_num))
      have hm' := congrArg (fun D : E3 →L[ℝ] ℝ => D (e j)) hm
      have hm'' : fderiv ℝ p y (e j) =
          chi y * fderiv ℝ f y (e j) + f y * fderiv ℝ chi y (e j) := by
        simpa [p, smul_eq_mul] using hm'
      calc
        fderiv ℝ p y (e j) =
            chi y * fderiv ℝ f y (e j) + f y * fderiv ℝ chi y (e j) := hm''
        _ = dc y * f y + chi y * dfj y := by
          dsimp [dc, dfj]
          ring
    have hdc : DifferentiableAt ℝ dc x := hdcC.differentiableAt (by norm_num)
    have hdfj : DifferentiableAt ℝ dfj x := hdfC.differentiableAt (by norm_num)
    have hpj : DifferentiableAt ℝ (fun y : E3 => fderiv ℝ p y (e j)) x :=
      hpjC.differentiableAt (by norm_num)
    have hchiD : DifferentiableAt ℝ chi x := hchi.differentiableAt (by norm_num)
    have hfD : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
    have hrD : DifferentiableAt ℝ (fun y : E3 => dc y * f y + chi y * dfj y) x := by
      exact (hdc.mul hfD).add (hchiD.mul hdfj)
    have hder := (hrD.hasFDerivAt.congr_of_eventuallyEq hlocal).fderiv
    rw [hder]
    have hsum := fderiv_fun_add
      (f := fun y : E3 => dc y * f y) (g := fun y => chi y * dfj y)
      (hdc.mul hfD) (hchiD.mul hdfj)
    rw [hsum]
    have hmul₁ := fderiv_fun_mul (c := dc) (d := f) hdc hfD
    have hmul₂ := fderiv_fun_mul (c := chi) (d := dfj) hchiD hdfj
    have hmul₁' := congrArg (fun D : E3 →L[ℝ] ℝ => D (e i)) hmul₁
    have hmul₂' := congrArg (fun D : E3 →L[ℝ] ℝ => D (e i)) hmul₂
    change
      fderiv ℝ (fun y : E3 => dc y * f y) x (e i) +
        fderiv ℝ (fun y : E3 => chi y * dfj y) x (e i) = _
    rw [hmul₁', hmul₂']
    simp only [add_apply, smul_apply, smul_eq_mul]
    dsimp [dc, dfj]
    ring
  change
    (∑ i : Fin 3, ∑ j : Fin 3,
      (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ p y (e j)) x (e i)) -
      chi x * (∑ i : Fin 3, ∑ j : Fin 3,
        (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ f y (e j)) x (e i)) =
      f x * (∑ i : Fin 3, ∑ j : Fin 3,
        (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ chi y (e j)) x (e i)) +
      ∑ i : Fin 3, ∑ j : Fin 3, (A (e j)) i *
        (fderiv ℝ chi x (e i) * fderiv ℝ f x (e j) +
          fderiv ℝ chi x (e j) * fderiv ℝ f x (e i))
  simp_rw [hsecond]
  simp only [Finset.sum_add_distrib, mul_add]
  have hChi :
      (∑ i : Fin 3, ∑ j : Fin 3, (A (e j)) i *
        (chi x * fderiv ℝ (fun y : E3 => fderiv ℝ f y (e j)) x (e i))) =
      chi x * ∑ i : Fin 3, ∑ j : Fin 3,
        (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ f y (e j)) x (e i) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, chi x *
          ((A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ f y (e j)) x (e i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i : Fin 3, chi x * ∑ j : Fin 3,
          (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ f y (e j)) x (e i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mul_sum Finset.univ
          (fun j : Fin 3 => (A (e j)) i *
            fderiv ℝ (fun y : E3 => fderiv ℝ f y (e j)) x (e i)) (chi x)).symm
      _ = _ := by
        exact (Finset.mul_sum Finset.univ
          (fun i : Fin 3 => ∑ j : Fin 3,
            (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ f y (e j)) x (e i))
          (chi x)).symm
  have hF :
      (∑ i : Fin 3, ∑ j : Fin 3, (A (e j)) i *
        (f x * fderiv ℝ (fun y : E3 => fderiv ℝ chi y (e j)) x (e i))) =
      f x * ∑ i : Fin 3, ∑ j : Fin 3,
        (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ chi y (e j)) x (e i) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, f x *
          ((A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ chi y (e j)) x (e i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i : Fin 3, f x * ∑ j : Fin 3,
          (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ chi y (e j)) x (e i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mul_sum Finset.univ
          (fun j : Fin 3 => (A (e j)) i *
            fderiv ℝ (fun y : E3 => fderiv ℝ chi y (e j)) x (e i)) (f x)).symm
      _ = _ := by
        exact (Finset.mul_sum Finset.univ
          (fun i : Fin 3 => ∑ j : Fin 3,
            (A (e j)) i * fderiv ℝ (fun y : E3 => fderiv ℝ chi y (e j)) x (e i))
          (f x)).symm
  rw [hChi, hF]
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
