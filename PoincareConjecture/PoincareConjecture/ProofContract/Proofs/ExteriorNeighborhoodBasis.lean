import PoincareConjecture.ProofContract.Proofs.CoordinateOpenExterior
import PoincareConjecture.ProofContract.Proofs.ShrunkCoordinateComplement
import PoincareConjecture.ProofContract.Proofs.CompactChartSqueeze
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.RelativeCompactCollapse
import PoincareConjecture.ProofContract.Proofs.MarkedCollapseRecognition
import PoincareConjecture.ProofContract.Proofs.ConnectedSumSphereReduction
import Mathlib
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology Manifold ContDiff
/-- Open exteriors of smaller coordinate balls form neighborhoods of the larger closed exterior. -/
theorem exterior_neighborhood_basis (M : ClosedThreeManifold.{u}) (a : CoordinateBall M)
    (U : Set M) (hU : IsOpen U)
    (hKU : {x : M | x ∉ a.parametrization '' Metric.ball (0:Euclidean3) (3/4)} ⊆ U) :
    ∃ r : ℝ, (1/2:ℝ)<r ∧ r<(3/4:ℝ) ∧
      {x : M | x ∉ a.parametrization '' Metric.ball (0:Euclidean3) (3/4)} ⊆
        {x : M | x ∉ a.parametrization '' Metric.closedBall (0:Euclidean3) r} ∧
      {x : M | x ∉ a.parametrization '' Metric.closedBall (0:Euclidean3) r} ⊆ U :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let L : Set M := Uᶜ
  have hLcompact : IsCompact L := by
    dsimp [L]
    exact isCompact_univ.of_isClosed_subset hU.isClosed_compl (subset_univ _)
  have hLimage : L ⊆ a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4) := by
    intro x hx
    by_contra hxi
    exact hx (hKU hxi)
  have hLtarget : L ⊆ a.parametrization.target := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hLimage hx
    apply a.parametrization.map_source
    apply a.contains_two
    have hz' : ‖z‖ < (3 / 4 : ℝ) := by
      simpa [Metric.mem_ball] using hz
    simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ 2 by linarith)
  let S : Set Euclidean3 := a.parametrization.symm '' L
  have hScompact : IsCompact S := by
    dsimp [S]
    exact hLcompact.image_of_continuousOn
      (a.parametrization.symm.continuousOn.mono hLtarget)
  have hSsubset : S ⊆ Metric.ball (0 : Euclidean3) (3 / 4) := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hLimage hx
    rw [a.parametrization.left_inv]
    · exact hw
    · apply a.contains_two
      have hw' : ‖w‖ < (3 / 4 : ℝ) := by
        simpa [Metric.mem_ball] using hw
      simpa [Metric.mem_closedBall] using (show ‖w‖ ≤ 2 by linarith)
  have hfirst : ∀ r : ℝ, r < (3 / 4 : ℝ) →
      {x : M | x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)} ⊆
        {x : M | x ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) r} := by
    intro r hr x hx hxr
    obtain ⟨z, hz, rfl⟩ := hxr
    apply hx
    refine ⟨z, ?_, rfl⟩
    have hz' : ‖z‖ ≤ r := by
      simpa [Metric.mem_closedBall] using hz
    simpa [Metric.mem_ball] using hz'.trans_lt hr
  by_cases hSempty : S.Nonempty
  · obtain ⟨z, hzS, hzmax⟩ :=
      hScompact.exists_isMaxOn hSempty continuous_norm.continuousOn
    let R : ℝ := ‖z‖
    have hR0 : 0 ≤ R := by
      dsimp [R]
      exact norm_nonneg _
    have hR3 : R < (3 / 4 : ℝ) := by
      simpa [R, Metric.mem_ball] using hSsubset hzS
    let B : ℝ := max (1 / 2 : ℝ) R
    have hB3 : B < (3 / 4 : ℝ) := by
      dsimp [B]
      exact max_lt (by norm_num) hR3
    let r : ℝ := (B + 3 / 4) / 2
    have hrhalf : (1 / 2 : ℝ) < r := by
      dsimp [r]
      have hBhalf : (1 / 2 : ℝ) ≤ B := by
        dsimp [B]
        exact le_max_left _ _
      linarith
    have hr3 : r < (3 / 4 : ℝ) := by
      dsimp [r]
      linarith
    have hRr : R < r := by
      have hBR : R ≤ B := by
        dsimp [B]
        exact le_max_right _ _
      dsimp [r]
      linarith
    refine ⟨r, hrhalf, hr3, hfirst r hr3, ?_⟩
    intro x hx
    by_contra hxu
    have hxL : x ∈ L := hxu
    let w : Euclidean3 := a.parametrization.symm x
    have hwsrc : w ∈ a.parametrization.source :=
      a.parametrization.symm.map_source (hLtarget hxL)
    have hxw : a.parametrization w = x :=
      a.parametrization.right_inv (hLtarget hxL)
    have hwS : w ∈ S := by
      refine ⟨x, hxL, rfl⟩
    apply hx
    refine ⟨w, ?_, hxw⟩
    have hwmax : ‖w‖ ≤ R := hzmax hwS
    have hwr : ‖w‖ ≤ r := hwmax.trans (le_of_lt hRr)
    simpa [Metric.mem_closedBall] using hwr
  · have hLempty : L = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hSempty ⟨a.parametrization.symm x, ⟨x, hx, rfl⟩⟩
    let r : ℝ := 5 / 8
    have hrhalf : (1 / 2 : ℝ) < r := by
      dsimp [r]
      norm_num
    have hr3 : r < (3 / 4 : ℝ) := by
      dsimp [r]
      norm_num
    refine ⟨r, hrhalf, hr3, hfirst r hr3, ?_⟩
    intro x hx
    by_contra hxu
    have : x ∈ L := hxu
    rw [hLempty] at this
    exact this
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
