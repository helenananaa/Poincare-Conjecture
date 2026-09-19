import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.ParallelMath.Transport.CostOpenDerivative
import PoincareConjecture.ParallelMath.Transport.WidthLocalContinuity
import PoincareConjecture.ParallelMath.Transport.PeakLocalControl

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Endpoint-safe per-competitor time estimates give continuity of an actual inf-sup on a regular slab. -/
theorem leastPeak_continuousOn_from_derivative_bounds {A B : Type*} [Nonempty A] [Nonempty B]
    (F F' : A → B → ℝ → ℝ) (a b K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ x y, ContinuousOn (F x y) (Icc a b))
    (hn : ∀ x y t, t ∈ Icc a b → 0 ≤ F x y t)
    (hd : ∀ x y t, t ∈ Ioo a b → HasDerivAt (F x y) (F' x y t) t)
    (hbnd : ∀ x y t, t ∈ Ioo a b → |F' x y t| ≤ K*F x y t)
    (hpeak : ∀ x t, t ∈ Icc a b → BddAbove (range (fun y => F x y t))) :
    ContinuousOn (fun t => PoincareConjecture.ParallelMath.Variational.leastPeak
      (fun x y => F x y t)) (Icc a b) :=
/- SWARM_PROOF_BEGIN -/
by
  -- Competitorwise exponential control on Icc a b. Derivatives are used only on
  -- interiors of subintervals, so the outer endpoints a, b need not be differentiable.
  have hcomp : ∀ x y, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F x y t ≤ Real.exp (K * |t - s|) * F x y s := by
    intro x y s hs t ht
    rcases le_total s t with hst | hts
    · -- s ≤ t: grow forward on [s, t]
      have hgr :=
        cost_growth_from_interior_derivatives (F x y) (F' x y) s t K hst hK
          ((hf x y).mono (Icc_subset_Icc hs.1 ht.2))
          (fun u hu => hn x y u (Icc_subset_Icc hs.1 ht.2 hu))
          (fun u hu => hd x y u (Ioo_subset_Ioo hs.1 ht.2 hu))
          (fun u hu => hbnd x y u (Ioo_subset_Ioo hs.1 ht.2 hu))
      rw [abs_of_nonneg (sub_nonneg.mpr hst)]
      exact hgr.2
    · -- t ≤ s: grow forward on [t, s], then invert the lower bound
      have hgr :=
        cost_growth_from_interior_derivatives (F x y) (F' x y) t s K hts hK
          ((hf x y).mono (Icc_subset_Icc ht.1 hs.2))
          (fun u hu => hn x y u (Icc_subset_Icc ht.1 hs.2 hu))
          (fun u hu => hd x y u (Ioo_subset_Ioo ht.1 hs.2 hu))
          (fun u hu => hbnd x y u (Ioo_subset_Ioo ht.1 hs.2 hu))
      have hle := hgr.1
      rw [neg_mul, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)] at hle
      rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub]
      exact hle
  -- Pass the comparison to each peak, then to the infimum of peaks.
  have hpeak_ctrl : ∀ x,
      (∀ t ∈ Icc a b, 0 ≤
          PoincareConjecture.ParallelMath.Variational.peakCost (fun y => F x y t)) ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        PoincareConjecture.ParallelMath.Variational.peakCost (fun y => F x y t) ≤
          Real.exp (K * |t - s|) *
            PoincareConjecture.ParallelMath.Variational.peakCost (fun y => F x y s) := by
    intro x
    exact peakCost_exp_control_on (fun t y => F x y t) (Icc a b) K
      (fun t ht y => hn x y t ht)
      (fun t ht => hpeak x t ht)
      (fun s hs t ht y => hcomp x y s hs t ht)
  exact leastCost_continuousOn_of_exp_distortion
    (fun t x => PoincareConjecture.ParallelMath.Variational.peakCost (fun y => F x y t))
    (Icc a b) K hK
    (fun t ht x => (hpeak_ctrl x).1 t ht)
    (fun s hs t ht x => (hpeak_ctrl x).2 s hs t ht)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
