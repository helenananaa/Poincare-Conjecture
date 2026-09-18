import PoincareConjecture.Topology.FiberSaturation.SmoothChartAdjustment

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Bundle Manifold Filter
open scoped Manifold ContDiff Topology
variable {V W H G M N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G}

/-- Local smooth pasting on the actual piecewise domain. Equality on a whole
collar, not just equality at one level, supplies all orders of compatibility. -/
theorem contMDiffOn_ite_le {f g : M → N} {S T : Set M}
    (hS : IsOpen S) (hT : IsOpen T)
    (hf : ContMDiffOn I J ∞ f S) (hg : ContMDiffOn I J ∞ g T)
    {θ : M → ℝ} (hθ : Continuous θ) {c d : ℝ} (hd : 0 < d)
    (heq : EqOn f g (θ ⁻¹' Ioo (c-d) (c+d))) :
    ContMDiffOn I J ∞ (fun x => if θ x ≤ c then f x else g x)
      ((θ ⁻¹' Iic c).ite S T) := by
  classical
  intro x hx
  by_cases hxc : θ x ≤ c
  · have hxS : x ∈ S := by simpa [Set.ite, hxc] using hx
    have hfx := (hf x hxS).contMDiffAt (hS.mem_nhds hxS)
    apply ContMDiffAt.contMDiffWithinAt
    apply hfx.congr_of_eventuallyEq
    by_cases hlt : θ x < c
    · filter_upwards [(isOpen_Iio.preimage hθ).mem_nhds hlt] with y hy
      change θ y < c at hy
      simp only [if_pos (le_of_lt hy)]
    · have hxc' : θ x = c := le_antisymm hxc (le_of_not_gt hlt)
      have hxb : θ x ∈ Ioo (c-d) (c+d) := by rw [hxc']; constructor <;> linarith
      filter_upwards [(isOpen_Ioo.preimage hθ).mem_nhds hxb] with y hy
      split_ifs
      · rfl
      · exact (heq hy).symm
  · have hxT : x ∈ T := by simpa [Set.ite, hxc] using hx
    have hgx := (hg x hxT).contMDiffAt (hT.mem_nhds hxT)
    apply ContMDiffAt.contMDiffWithinAt
    apply hgx.congr_of_eventuallyEq
    filter_upwards [(isOpen_Ioi.preimage hθ).mem_nhds (lt_of_not_ge hxc)] with y hy
    change c < θ y at hy
    simp only [if_neg (not_le.mpr hy)]

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
