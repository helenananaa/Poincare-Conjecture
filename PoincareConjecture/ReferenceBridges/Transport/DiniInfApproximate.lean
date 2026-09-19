import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import MorganTianLib.Ch02.ForwardDifference
import PoincareConjecture.ParallelMath.Variational.InfimumApproximation

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport.Reference
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Uniform short-time approximate competitors yield a Dini bound without an attained minimizer. -/
theorem leastCost_forwardDiff_of_approximate_competitors {A : Type*} [Nonempty A]
    (F : ℝ → A → ℝ) (s c : ℝ) (hn : ∀ t a, 0 ≤ F t a)
    (happrox : ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
      ∀ h : ℝ, 0 < h → h < delta → ∃ a : A,
        F s a ≤ PoincareConjecture.ParallelMath.Variational.leastCost (F s)+eta*h ∧
        F (s+h) a ≤ F s a+(c+eta)*h) :
    MorganTianLib.ForwardDiffQuotientLE
      (fun t => PoincareConjecture.ParallelMath.Variational.leastCost (F t)) s c :=
/- SWARM_PROOF_BEGIN -/
by
  intro r hr
  set u : ℝ → ℝ :=
    fun t => PoincareConjecture.ParallelMath.Variational.leastCost (F t)
  set eta : ℝ := (r - c) / 4 with heta_def
  have heta_pos : 0 < eta := by
    rw [heta_def]
    exact div_pos (sub_pos.mpr hr) (by norm_num)
  obtain ⟨delta, hdelta_pos, hdelta⟩ := happrox eta heta_pos
  filter_upwards [Ioo_mem_nhdsGT (lt_add_of_pos_right s hdelta_pos)] with t ht
  have ht_s : 0 < t - s := sub_pos.mpr ht.1
  have ht_delta : t - s < delta := sub_lt_iff_lt_add'.mpr ht.2
  obtain ⟨a, ha_s, ha_t⟩ := hdelta (t - s) ht_s ht_delta
  have hle : u t ≤ F t a :=
    (PoincareConjecture.ParallelMath.Variational.leastCost_nonneg_and_approx
      (F t) (fun a => hn t a)).2.1 a
  have hwidth : u t ≤ u s + (c + 2 * eta) * (t - s) := by
    have hrewrite : s + (t - s) = t := by ring
    calc u t
        ≤ F t a := hle
      _ = F (s + (t - s)) a := by rw [hrewrite]
      _ ≤ F s a + (c + eta) * (t - s) := ha_t
      _ ≤ u s + eta * (t - s) + (c + eta) * (t - s) := by linarith [ha_s]
      _ = u s + (c + 2 * eta) * (t - s) := by ring
  have hslope : slope u s t ≤ c + 2 * eta := by
    rw [slope_def_field]
    exact (div_le_iff₀ ht_s).mpr (by linarith [hwidth])
  have hstrict : c + 2 * eta < r := by
    linarith [heta_def]
  exact hslope.trans_lt hstrict
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport.Reference
