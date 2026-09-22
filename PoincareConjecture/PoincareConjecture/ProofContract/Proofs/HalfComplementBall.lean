import PoincareConjecture.ProofContract.Proofs.ExteriorLocalShrinkability
import PoincareConjecture.ProofContract.Proofs.AnnularCappingMap
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
/-- Closed complement of the half-radius coordinate ball, with its exact boundary parametrization. -/
theorem half_coordinate_complement_ball (M : ClosedThreeManifold.{u})
    (e : M ≃ₜ Sphere3) (a : CoordinateBall M) :
    let C := {x : M // x ∉ a.parametrization '' Metric.ball (0:Euclidean3) (1/2)}
    ∃ q : C ≃ₜ DoubleBall.Ball, ∀ (s : Sphere2) (x : C),
      (x:M)=a.parametrization ((1/2:ℝ) • (s:Euclidean3)) →
        (q x:Euclidean3)=(s:Euclidean3) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let C : Type u :=
    {x : M // x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2)}
  let K : Set C := {x | (x : M) ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)}
  change ∃ q : C ≃ₜ DoubleBall.Ball, ∀ (s : Sphere2) (x : C),
    (x : M) = a.parametrization ((1 / 2 : ℝ) • (s : Euclidean3)) →
      (q x : Euclidean3) = (s : Euclidean3)
  letI : TopologicalSpace.MetrizableSpace M :=
    e.isEmbedding.metrizableSpace
  letI : TopologicalSpace.MetrizableSpace C :=
    IsEmbedding.subtypeVal.metrizableSpace
  letI : MetricSpace C := TopologicalSpace.metrizableSpaceMetric C
  have hopen_half : IsOpen
      (a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2)) := by
    apply a.parametrization.isOpen_image_of_subset_source Metric.isOpen_ball
    intro z hz
    apply a.contains_two
    have hz' : ‖z‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    simpa [Metric.mem_closedBall, dist_zero_right] using (show ‖z‖ ≤ 2 by linarith)
  have hopen_three : IsOpen
      (a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)) := by
    apply a.parametrization.isOpen_image_of_subset_source Metric.isOpen_ball
    intro z hz
    apply a.contains_two
    have hz' : ‖z‖ < (3 / 4 : ℝ) := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    simpa [Metric.mem_closedBall, dist_zero_right] using (show ‖z‖ ≤ 2 by linarith)
  have hclosed_half : IsClosed
      {x : M | x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2)} :=
    isClosed_compl_iff.mpr hopen_half
  have hCcompact : IsCompact (Set.univ : Set C) := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    have himage : (fun x : C => (x : M)) '' (Set.univ : Set C) =
        {x : M | x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2)} := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    rw [himage]
    exact hclosed_half.isCompact
  letI : CompactSpace C := isCompact_univ_iff.mp hCcompact
  have hKclosed : IsClosed K := by
    change IsClosed ((fun x : C => (x : M)) ⁻¹'
      {x : M | x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)})
    exact (isClosed_compl_iff.mpr hopen_three).preimage continuous_subtype_val
  have hKcompact : IsCompact K := hKclosed.isCompact
  have hhalf_three :
      a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2) ⊆
        a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4) := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    have hz' : ‖z‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hz'' : ‖z‖ < (3 / 4 : ℝ) := by linarith
    simpa [Metric.mem_ball, dist_zero_right] using hz''
  have hKU : K ⊆
      {x : C | (x : M) ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2)} := by
    intro x hx
    change (x : M) ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4) at hx
    change (x : M) ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2)
    intro hx'
    exact hx (hhalf_three hx')
  let U : Set C := {x : C |
    (x : M) ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2)}
  have hUopen : IsOpen U := by
    change IsOpen ((fun x : C => (x : M)) ⁻¹'
      {x : M | x ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2)})
    have hcompact_half : IsCompact
        (a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2)) := by
      apply (isCompact_closedBall (0 : Euclidean3) (1 / 2)).image_of_continuousOn
      apply a.parametrization.continuousOn.mono
      intro z hz
      apply a.contains_two
      have hz' : ‖z‖ ≤ (1 / 2 : ℝ) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
      simpa [Metric.mem_closedBall, dist_zero_right] using (show ‖z‖ ≤ 2 by linarith)
    exact (isOpen_compl_iff.mpr hcompact_half.isClosed).preimage continuous_subtype_val
  have hKn : K.Nonempty := by
    obtain ⟨s, hs⟩ : (Metric.sphere (0 : Euclidean3) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    let s0 : Sphere2 := ⟨s, hs⟩
    let x : C := ⟨a.parametrization (s : Euclidean3), by
      intro hx
      rcases hx with ⟨z, hz, hzx⟩
      apply (a.boundary s0).property
      refine ⟨z, ?_, hzx⟩
      exact Metric.ball_subset_ball (by norm_num) hz⟩
    refine ⟨x, ?_⟩
    change a.parametrization (s : Euclidean3) ∉
      a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)
    intro hx
    rcases hx with ⟨z, hz, hzx⟩
    apply (a.boundary s0).property
    refine ⟨z, ?_, hzx⟩
    exact Metric.ball_subset_ball (by norm_num) hz
  have hshrink : ∀ W : Set C, IsOpen W → K ⊆ W → ∀ eps : ℝ, 0 < eps →
      ∃ h : C ≃ₜ C, (∀ x, x ∉ W → h x = x) ∧
        ∀ x ∈ K, ∀ y ∈ K, dist (h x) (h y) < eps := by
    intro W hW hKW eps heps
    simpa [C, K] using
      (exterior_core_locally_shrinkable M e a (Y := C) (f := id)
        continuous_id W hW hKW eps heps)
  obtain ⟨g, hg, hgs, hgfix, hgk⟩ :=
    squeezable_compact_relative_collapse K hKcompact hKn hshrink U hUopen hKU
  obtain ⟨f, hf, hfs, hfk, hfb⟩ :=
    (show ∃ f : C → DoubleBall.Ball, Continuous f ∧ Surjective f ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ K ∧ y ∈ K)) ∧
      ∀ (s : Sphere2) (x : C), (x : M) =
        a.parametrization ((1 / 2 : ℝ) • (s : Euclidean3)) →
          (f x : Euclidean3) = (s : Euclidean3) from
      by simpa [C, K] using annular_capping_single_fiber M a)
  let S : Set C := {x | ∃ s : Sphere2,
    (x : M) = a.parametrization ((1 / 2 : ℝ) • (s : Euclidean3))}
  have hfix : ∀ x ∈ S, g x = x := by
    intro x hx
    obtain ⟨s, hs⟩ := hx
    apply hgfix x
    intro hxU
    change (x : M) ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2) at hxU
    apply hxU
    refine ⟨(1 / 2 : ℝ) • (s : Euclidean3), ?_, hs.symm⟩
    have hsphere : ‖(s : Euclidean3)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using s.property
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (by norm_num), hsphere]
    norm_num
  obtain ⟨q, hqg, hqS⟩ :=
    recognition_from_equal_collapse_fibers K S f g hf hfs hg hgs hfk hgk hfix
  refine ⟨q, ?_⟩
  intro s x hs
  calc
    (q x : Euclidean3) = (f x : Euclidean3) := congrArg (fun z : DoubleBall.Ball => (z : Euclidean3)) (hqS x ⟨s, hs⟩)
    _ = (s : Euclidean3) := hfb s x hs
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
