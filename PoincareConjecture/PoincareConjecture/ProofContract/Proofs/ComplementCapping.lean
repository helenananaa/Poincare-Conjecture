import PoincareConjecture.ProofContract.Proofs.RadialCapping
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Extend a prescribed boundary sphere map across the actual punctured complement into a ball. -/
theorem coordinate_complement_capping {M : ClosedThreeManifold.{u}}
    (b : CoordinateBall M) (h : Sphere2 ≃ₜ Sphere2) :
    ∃ F : C(b.Complement, DoubleBall.Ball),
      ∀ s : Sphere2, F (b.boundary s) = DoubleBall.boundary (h s) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨G, hGboundary, hGzero⟩ := radial_capping_extension h
  let D := {x : Euclidean3 // 1 ≤ ‖x‖}
  let X := b.Complement
  let collar : Set X :=
    (fun x : X => (x : M)) ⁻¹' (b.parametrization '' Metric.ball 0 2)
  have hsource2 : Metric.closedBall (0 : Euclidean3) 2 ⊆
      b.parametrization.source := by
    exact b.contains_two
  have hsource_ball : Metric.ball (0 : Euclidean3) 2 ⊆
      b.parametrization.source :=
    Metric.ball_subset_closedBall.trans hsource2
  have hcollar_open : IsOpen collar := by
    apply IsOpen.preimage continuous_subtype_val
    exact b.parametrization.isOpen_image_of_subset_source Metric.isOpen_ball hsource_ball
  have hcont2 : ContinuousOn b.parametrization (Metric.closedBall 0 2) :=
    b.parametrization.continuousOn.mono hsource2
  have hcompact2 : IsCompact (b.parametrization '' Metric.closedBall 0 2) :=
    (isCompact_closedBall (0 : Euclidean3) 2).image_of_continuousOn hcont2
  have hclosed2 : IsClosed (b.parametrization '' Metric.closedBall 0 2) :=
    hcompact2.isClosed
  let K : Set X :=
    (fun x : X => (x : M)) ⁻¹' (b.parametrization '' Metric.closedBall 0 2)
  have hKclosed : IsClosed K := by
    exact hclosed2.preimage continuous_subtype_val
  have hcollar_K : collar ⊆ K := by
    intro x hx
    rcases hx with ⟨z, hz, hzx⟩
    exact ⟨z, Metric.ball_subset_closedBall hz, hzx⟩
  have hclosure_K : closure collar ⊆ K :=
    closure_minimal hcollar_K hKclosed
  have hclosure_coord (x : X) (hx : x ∈ closure collar) :
      ∃ z : Euclidean3, z ∈ Metric.closedBall 0 2 ∧
        b.parametrization z = (x : M) ∧ 1 ≤ ‖z‖ := by
    rcases hclosure_K hx with ⟨z, hz, hzx⟩
    have hzsource : z ∈ b.parametrization.source := hsource2 hz
    have hnormlower : 1 ≤ ‖z‖ := by
      by_contra hn
      have hzlt : ‖z‖ < 1 := lt_of_not_ge hn
      exact x.property ⟨z, (by simpa using hzlt), hzx⟩
    exact ⟨z, hz, hzx, hnormlower⟩
  have hsymm_on : ContinuousOn
      (fun x : X => b.parametrization.symm (x : M)) (closure collar) := by
    rw [continuousOn_iff_continuous_restrict]
    let g : closure collar → M := fun x => (x : X)
    have hg : Continuous g := by
      exact continuous_subtype_val.comp continuous_subtype_val
    have hc : Continuous (fun x : closure collar =>
        b.parametrization.symm (g x)) := by
      apply b.parametrization.continuousOn_symm.comp_continuous hg
      intro x
      rcases hclosure_coord x.1 x.2 with ⟨z, hz, hzx, _⟩
      simpa [g, hzx] using b.parametrization.map_source (hsource2 hz)
    change Continuous (fun x : closure collar =>
      b.parametrization.symm ((x : X) : M))
    exact hc
  obtain ⟨s0, hs0⟩ : (Metric.sphere (0 : Euclidean3) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let d0 : D := ⟨s0, by simpa [Metric.mem_sphere, dist_zero_right] using hs0.ge⟩
  let q : X → D := fun x =>
    if hx : 1 ≤ ‖b.parametrization.symm (x : M)‖ then
      ⟨b.parametrization.symm (x : M), hx⟩
    else d0
  have hqnorm : ∀ x : X, x ∈ closure collar →
      1 ≤ ‖b.parametrization.symm (x : M)‖ := by
    intro x hx
    rcases hclosure_coord x hx with ⟨z, hz, hzx, hzlower⟩
    have hzsource : z ∈ b.parametrization.source := hsource2 hz
    have hinv : b.parametrization.symm (x : M) = z := by
      rw [← hzx]
      exact b.parametrization.left_inv hzsource
    simpa [hinv] using hzlower
  have hq_cont : ContinuousOn q (closure collar) := by
    rw [continuousOn_iff_continuous_restrict]
    let q' : closure collar → D := fun x =>
      ⟨b.parametrization.symm (x : M), hqnorm x x.property⟩
    have hsymm' : Continuous (fun x : closure collar =>
        b.parametrization.symm (x : M)) := by
      exact continuousOn_iff_continuous_restrict.mp hsymm_on
    have hq' : Continuous q' := by
      exact hsymm'.subtype_mk (fun x => hqnorm x x.property)
    have heq : (closure collar).restrict q = q' := by
      funext x
      apply Subtype.ext
      simp [q, q', hqnorm x x.property]
    rw [heq]
    exact hq'
  let f₀ : X → DoubleBall.Ball := fun x => G (q x)
  have hf₀ : ContinuousOn f₀ (closure collar) := by
    exact G.continuous.comp_continuousOn hq_cont
  let zero : DoubleBall.Ball := ⟨0, by simp [Metric.mem_closedBall]
    ⟩
  let f : X → DoubleBall.Ball :=
    Set.piecewise collar f₀ (fun _ => zero)
  have hfrontier_zero : ∀ x ∈ frontier collar, f₀ x = zero := by
    intro x hx
    rcases hclosure_coord x (frontier_subset_closure hx) with ⟨z, hz, hzx, hzlower⟩
    have hzsource : z ∈ b.parametrization.source := hsource2 hz
    have hinv : b.parametrization.symm (x : M) = z := by
      rw [← hzx]
      exact b.parametrization.left_inv hzsource
    have hnormle : ‖z‖ ≤ 2 := by
      simpa [Metric.mem_closedBall] using hz
    have hxnot : x ∉ collar := by
      intro hxin
      exact (disjoint_frontier_iff_isOpen.mpr hcollar_open).le_bot ⟨hx, hxin⟩
    have hnormge : 2 ≤ ‖z‖ := by
      by_contra hn
      have hzlt : ‖z‖ < 2 := lt_of_not_ge hn
      apply hxnot
      exact ⟨z, (by simpa using hzlt), hzx⟩
    have hnormeq : ‖z‖ = 2 := le_antisymm hnormle hnormge
    have hqz : q x = ⟨z, hzlower⟩ := by
      apply Subtype.ext
      simp [q, hinv, hzlower]
    apply Subtype.ext
    change (G (q x) : Euclidean3) = (zero : Euclidean3)
    rw [hqz]
    simpa [zero] using hGzero ⟨z, hzlower⟩ hnormge
  have hf : Continuous f := by
    change Continuous (Set.piecewise collar f₀ (fun _ => zero))
    exact continuous_piecewise hfrontier_zero hf₀ continuous_const.continuousOn
  refine ⟨⟨f, hf⟩, ?_⟩
  intro s
  have hs_norm : ‖(s : Euclidean3)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using s.property
  have hs_source : (s : Euclidean3) ∈ b.parametrization.source := by
    exact b.contains_two (by simp [Metric.mem_closedBall, hs_norm])
  have hs_collar : b.boundary s ∈ collar := by
    change b.parametrization (s : Euclidean3) ∈
      b.parametrization '' Metric.ball 0 2
    refine ⟨s, ?_, rfl⟩
    simpa [Metric.mem_ball, dist_zero_right, hs_norm]
  have hs_inv : b.parametrization.symm ((b.boundary s : b.Complement) : M) =
      (s : Euclidean3) := by
    change b.parametrization.symm (b.parametrization (s : Euclidean3)) = _
    exact b.parametrization.left_inv hs_source
  have hDs : 1 ≤ ‖(s : Euclidean3)‖ := by simpa [hs_norm]
  have hq_s : q (b.boundary s) = ⟨(s : Euclidean3), hDs⟩ := by
    apply Subtype.ext
    simp [q, hs_inv, hDs]
  change Set.piecewise collar f₀ (fun _ => zero) (b.boundary s) = _
  rw [Set.piecewise_eq_of_mem collar f₀ (fun _ : X => zero) hs_collar]
  change G (q (b.boundary s)) = _
  rw [hq_s]
  apply Subtype.ext
  simpa [DoubleBall.boundary] using hGboundary s
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
