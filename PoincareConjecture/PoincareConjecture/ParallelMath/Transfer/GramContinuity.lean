import PoincareConjecture.ParallelMath.Transfer.Core

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath.Transfer
open Set Filter
open scoped Topology

/-- The Gram area of a fixed continuous bilinear form is jointly continuous
in the two vectors. `Real.sqrt` vanishes on the negative discriminant, so no
positive-semidefinite hypothesis is required. -/
theorem continuous_gramArea_pair {V : Type*}
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousSMul ℝ V]
    (G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hG : Continuous fun p : V × V => G p.1 p.2) :
    Continuous fun p : V × V => gramArea G p.1 p.2 :=
/- SWARM_PROOF_BEGIN -/
by
  have hvv : Continuous fun p : V × V => G p.1 p.1 :=
    hG.comp (continuous_fst.prodMk continuous_fst)
  have hww : Continuous fun p : V × V => G p.2 p.2 :=
    hG.comp (continuous_snd.prodMk continuous_snd)
  have hdet : Continuous fun p : V × V =>
      G p.1 p.1 * G p.2 p.2 - (G p.1 p.2) ^ 2 :=
    (hvv.mul hww).sub (hG.pow 2)
  unfold gramArea
  exact hdet.sqrt
/- SWARM_PROOF_END -/

/-- Gram area depends continuously on the three independent Gram entries. -/
theorem continuous_sqrt_gram_det :
    Continuous fun p : ℝ × ℝ × ℝ => Real.sqrt (p.1 * p.2.1 - p.2.2 ^ 2) :=
/- SWARM_PROOF_BEGIN -/
by
  have hpoly : Continuous fun p : ℝ × ℝ × ℝ => p.1 * p.2.1 - p.2.2 ^ 2 := by
    fun_prop
  exact hpoly.sqrt
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath.Transfer
