import PoincareConjecture.ParallelMath.Variational.WidthContinuity
import PoincareConjecture.ParallelMath.Variational.AdmissibleTransfer
import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Uniform distortion only on a real time slab gives relative continuity of its least cost; no global-time extension is assumed. -/
theorem leastCost_continuousOn_time_interval {A : Type*} [Nonempty A]
    (F : ℝ → A → ℝ) (a b K : ℝ) (hab : a ≤ b) (hK : 0 ≤ K)
    (hn : ∀ t ∈ Icc a b, ∀ x, 0 ≤ F t x)
    (hd : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x,
      F t x ≤ Real.exp (K*|t-s|)*F s x) :
    ContinuousOn (fun t => Variational.leastCost (F t)) (Icc a b) :=
/- SWARM_PROOF_BEGIN -/
by
  -- Clamp time onto `[a, b]` (1-Lipschitz) so the already-proved global result applies,
  -- without asking anything of `F` outside the slab.
  let G : ℝ → A → ℝ := fun t x => F (projIcc a b hab t : ℝ) x
  have hGnn : ∀ t x, 0 ≤ G t x := fun t x =>
    hn (projIcc a b hab t : ℝ) (projIcc a b hab t).property x
  have hGctrl : ∀ s t x, G t x ≤ Real.exp (K * |t - s|) * G s x := fun s t x => by
    have hbase :=
      hd (projIcc a b hab s : ℝ) (projIcc a b hab s).property
        (projIcc a b hab t : ℝ) (projIcc a b hab t).property x
    have hlip : |(projIcc a b hab t : ℝ) - (projIcc a b hab s : ℝ)| ≤ |t - s| :=
      abs_projIcc_sub_projIcc hab
    have hexp :
        Real.exp (K * |(projIcc a b hab t : ℝ) - (projIcc a b hab s : ℝ)|) ≤
          Real.exp (K * |t - s|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlip hK)
    exact hbase.trans (mul_le_mul_of_nonneg_right hexp (hGnn s x))
  have hGcont : Continuous (fun t => Variational.leastCost (G t)) :=
    Variational.leastCost_continuous_of_exp_distortion G hGnn K hK hGctrl
  refine hGcont.continuousOn.congr ?_
  intro t ht
  have hclamp : (projIcc a b hab t : ℝ) = t :=
    congrArg Subtype.val (projIcc_of_mem hab ht)
  simp [G, hclamp]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
