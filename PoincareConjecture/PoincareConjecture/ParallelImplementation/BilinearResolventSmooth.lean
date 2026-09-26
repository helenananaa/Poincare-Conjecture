import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BilinearResolventSmooth
open scoped ContDiff Topology
/-- Construct the actual solution of a parameterized linear fixed-point
identity and prove its smoothness. No smooth or continuous solution branch
is supplied; no artificial submultiplicative norm on a forcing graph is used. -/
theorem exists_smooth_bilinear_resolvent
    {A X : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (m : A →L[ℝ] X →L[ℝ] X) (c : X) :
    ∃ w : A → X,
      ContDiffOn ℝ ∞ w {a : A | ‖m a‖ < 1} ∧
      ∀ a : A, ‖m a‖ < 1 →
        w a = c + m a (w a) ∧
        (∀ x : X, x = c + m a x → x = w a) ∧
        ‖w a‖ ≤ ‖c‖ / (1 - ‖m a‖) :=
/- SWARM_PROOF_BEGIN -/
by
  let B := X →L[ℝ] X
  let g : A → B := fun a => 1 - m a
  let w : A → X := fun a => Ring.inverse (g a) c
  refine ⟨w, ?_, ?_⟩
  · change ContDiffOn ℝ ∞ (fun x : A => (Ring.inverse (g x)) c)
      {x : A | ‖m x‖ < 1}
    intro a ha
    have hg : ContDiffAt ℝ ∞ g a := by
      dsimp [g]
      fun_prop
    have hu : IsUnit (g a) := by
      exact isUnit_one_sub_of_norm_lt_one (by simpa [g] using ha)
    have hi : ContDiffAt ℝ ∞ (fun x => Ring.inverse (g x)) a := by
      exact (contDiffAt_ringInverse ℝ hu.unit).comp a hg
    exact (hi.clm_apply contDiffAt_const).contDiffWithinAt
  · intro a ha
    have hu : IsUnit (g a) := by
      exact isUnit_one_sub_of_norm_lt_one (by simpa [g] using ha)
    have hcancel : (g a) * Ring.inverse (g a) = 1 :=
      Ring.mul_inverse_cancel (g a) hu
    have hrel : (g a) (w a) = c := by
      have h := congrArg (fun T : B => T c) hcancel
      simpa [w, mul_apply_eq_comp] using h
    have heq : w a = c + m a (w a) := by
      have hrel' : w a - m a (w a) = c := by
        change ((1 - m a) (w a)) = c at hrel
        simpa using hrel
      calc
        w a = (w a - m a (w a)) + m a (w a) := by abel
        _ = c + m a (w a) := by rw [hrel']
    have hnorm : ‖w a‖ ≤ ‖c‖ + ‖m a‖ * ‖w a‖ := by
      calc
        ‖w a‖ = ‖c + m a (w a)‖ := congrArg norm heq
        _ ≤ ‖c‖ + ‖m a (w a)‖ := norm_add_le _ _
        _ ≤ ‖c‖ + ‖m a‖ * ‖w a‖ := by
          gcongr
          exact (m a).le_opNorm (w a)
    have hden : 0 < 1 - ‖m a‖ := sub_pos.mpr ha
    refine ⟨heq, ?_, ?_⟩
    · intro x hx
      have hxrel : (g a) x = c := by
        change x - m a x = c
        calc
          x - m a x = (c + m a x) - m a x := congrArg (fun y : X => y - m a x) hx
          _ = c := by abel
      calc
        x = Ring.inverse (g a) ((g a) x) := by
          have hc := congrArg (fun T : B => T x) (Ring.inverse_mul_cancel (g a) hu)
          simpa [mul_apply_eq_comp] using hc.symm
        _ = w a := by simp [w, hxrel]
    · apply (le_div_iff₀ hden).2
      nlinarith [hnorm]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BilinearResolventSmooth
