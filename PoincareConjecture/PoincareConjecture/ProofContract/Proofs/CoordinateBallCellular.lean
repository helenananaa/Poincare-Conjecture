import PoincareConjecture.ProofContract.Proofs.SqueezableCompactCollapse
import PoincareConjecture.ProofContract.Proofs.NestedCellSqueeze
import PoincareConjecture.ProofContract.Proofs.CollapseComplementHomeomorph
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import Mathlib.Geometry.Manifold.Instances.Sphere
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology Manifold ContDiff
/-- A buffered closed coordinate ball is an intersection of strictly nested buffered coordinate cells. -/
theorem coordinate_closed_ball_cellular {M : ClosedThreeManifold.{u}} (a : CoordinateBall M) :
    ∃ b : ℕ → CoordinateBall M,
      (∀ n, (b (n+1)).parametrization '' Metric.closedBall (0:Euclidean3) 1 ⊆ (b n).removed) ∧
      (⋂ n, (b n).parametrization '' Metric.closedBall (0:Euclidean3) 1) =
        a.parametrization '' Metric.closedBall (0:Euclidean3) 1 :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : Set Euclidean3 := Metric.closedBall 0 2
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_closedBall (0 : Euclidean3) 2
  have hKsource : K ⊆ a.parametrization.source := by
    simpa [K] using a.contains_two
  obtain ⟨δ, hδ, hδsource⟩ :=
    hKcompact.exists_cthickening_subset_open a.parametrization.open_source hKsource
  let r : ℕ → ℝ := fun n => 1 + δ / (4 * ((n : ℝ) + 1))
  have hrpos : ∀ n, 0 < r n := by
    intro n
    dsimp [r]
    have : 0 < δ / (4 * ((n : ℝ) + 1)) := by positivity
    linarith
  have hr1 : ∀ n, 1 < r n := by
    intro n
    dsimp [r]
    have : 0 < δ / (4 * ((n : ℝ) + 1)) := by positivity
    linarith
  have hrdec : ∀ n, r (n + 1) < r n := by
    intro n
    dsimp [r]
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hn' : 0 < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
    have hden : 4 * ((n : ℝ) + 1) < 4 * (((n + 1 : ℕ) : ℝ) + 1) := by
      norm_num
    simpa [add_comm] using add_lt_add_left
      (div_lt_div_of_pos_left hδ (by positivity) hden) 1
  have hr_tendsto : Tendsto r atTop (𝓝 1) := by
    have hden : Tendsto (fun n : ℕ => (4 : ℝ) * ((n : ℝ) + 1)) atTop atTop := by
      exact (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    have hquot : Tendsto (fun n : ℕ => δ / (4 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    simpa [r] using tendsto_const_nhds.add hquot
  have hscaled : ∀ n, (fun x : Euclidean3 => r n • x) '' K ⊆
      a.parametrization.source := by
    intro n x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy' : ‖y‖ ≤ 2 := by
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hy
    apply hδsource
    apply Metric.mem_cthickening_of_dist_le (r n • y) y δ K hy
    rw [dist_eq_norm, show r n • y - y = (r n - 1) • y by module]
    rw [norm_smul, Real.norm_of_nonneg (by linarith [hr1 n])]
    calc
      (r n - 1) * ‖y‖ ≤ (r n - 1) * 2 :=
        mul_le_mul_of_nonneg_left hy' (by linarith [hr1 n])
      _ = δ / (2 * ((n : ℝ) + 1)) := by
        dsimp [r]
        field_simp <;> ring
      _ ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hδ]
  let h : ∀ n, Euclidean3 ≃ₜ Euclidean3 := fun n =>
    Homeomorph.smulOfNeZero (r n) (ne_of_gt (hrpos n))
  let p : ∀ n, OpenPartialHomeomorph Euclidean3 M := fun n =>
    (h n).toOpenPartialHomeomorph.trans a.parametrization
  have hsource : ∀ n, Metric.closedBall (0 : Euclidean3) 2 ⊆ (p n).source := by
    intro n z hz
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨by simp, ?_⟩
    change h n z ∈ a.parametrization.source
    exact hscaled n ⟨z, hz, rfl⟩
  let b : ℕ → CoordinateBall M := fun n => ⟨p n, hsource n⟩
  have hb_apply (n : ℕ) (z : Euclidean3) :
      (b n).parametrization z = a.parametrization (r n • z) := by
    simp [b, p, h]
  refine ⟨b, ?_, ?_⟩
  · intro n
    rintro x ⟨z, hz, rfl⟩
    have hz' : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    let y : Euclidean3 := (r (n + 1) / r n) • z
    have hy : y ∈ Metric.ball (0 : Euclidean3) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [y]
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have hquot : r (n + 1) / r n < 1 :=
        (div_lt_iff₀ (hrpos n)).2 (by simpa using hrdec n)
      calc
        (r (n + 1) / r n) * ‖z‖ ≤ (r (n + 1) / r n) * 1 :=
          mul_le_mul_of_nonneg_left hz' (by positivity)
        _ < 1 := by linarith
    refine ⟨y, hy, ?_⟩
    rw [hb_apply, hb_apply]
    dsimp [y]
    rw [smul_smul]
    rw [show r n * (r (n + 1) / r n) = r (n + 1) by
      field_simp [ne_of_gt (hrpos n)]]
  · apply Set.Subset.antisymm
    · intro x hx
      have hx0 := mem_iInter.1 hx 0
      rcases hx0 with ⟨z, hz, hzx⟩
      have hz' : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
      have hz2 : z ∈ Metric.closedBall (0 : Euclidean3) 2 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using (show ‖z‖ ≤ 2 by linarith)
      have hxsource : r 0 • z ∈ a.parametrization.source :=
        (hsource 0 hz2).2
      have hxtarget : x ∈ a.parametrization.target := by
        rw [← hzx, hb_apply]
        exact a.parametrization.map_source hxsource
      let v : Euclidean3 := a.parametrization.symm x
      have hxrepr : a.parametrization v = x := by
        dsimp [v]
        exact a.parametrization.right_inv hxtarget
      have hvbound : ‖v‖ ≤ 1 := by
        by_contra hv
        have hvgt : 1 < ‖v‖ := lt_of_not_ge hv
        have hbound : ∀ n, ‖v‖ ≤ r n := by
          intro n
          rcases mem_iInter.1 hx n with ⟨w, hw, hxw⟩
          have hw' : ‖w‖ ≤ 1 := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hw
          have hw2 : w ∈ Metric.closedBall (0 : Euclidean3) 2 := by
            simpa [Metric.mem_closedBall, dist_zero_right] using (show ‖w‖ ≤ 2 by linarith)
          have hwsource : r n • w ∈ a.parametrization.source :=
            (hsource n hw2).2
          have hvw : v = r n • w := by
            dsimp [v]
            calc
              a.parametrization.symm x =
                  a.parametrization.symm ((b n).parametrization w) := by rw [hxw]
              _ = a.parametrization.symm (a.parametrization (r n • w)) := by
                rw [hb_apply]
              _ = r n • w := a.parametrization.left_inv hwsource
          rw [hvw, norm_smul, Real.norm_of_nonneg (hrpos n).le]
          calc
            r n * ‖w‖ ≤ r n * 1 := mul_le_mul_of_nonneg_left hw' (hrpos n).le
            _ = r n := by ring
        obtain ⟨N, hN⟩ := eventually_atTop.1
          ((tendsto_order.1 hr_tendsto).2 ‖v‖ hvgt)
        exact (not_lt_of_ge (hbound N)) (hN N le_rfl)
      refine ⟨v, ?_, hxrepr⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using hvbound
    · rintro x ⟨z, hz, rfl⟩
      refine mem_iInter.2 (fun n => ?_)
      refine ⟨(1 / r n) • z, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (by positivity)]
        have hz' : ‖z‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hz
        calc
          (1 / r n) * ‖z‖ ≤ (1 / r n) * 1 :=
            mul_le_mul_of_nonneg_left hz' (by positivity)
          _ ≤ 1 := by
            simpa only [mul_one] using
              ((div_le_iff₀ (hrpos n)).2 (by linarith [hr1 n]) :
                1 / r n ≤ (1 : ℝ))
      · rw [hb_apply, smul_smul]
        rw [show r n * (1 / r n) = (1 : ℝ) by
          field_simp [ne_of_gt (hrpos n)], one_smul]
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
