import PoincareConjecture.ProofContract.Proofs.CompactEuclideanEnclosure
import PoincareConjecture.ProofContract.Proofs.ExteriorNeighborhoodBasis
import PoincareConjecture.ProofContract.Proofs.ScaledOpenExterior
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
/-- The outer closed exterior is locally squeezable inside the half-radius complement. -/
theorem exterior_core_locally_shrinkable (M : ClosedThreeManifold.{u}) (e : M ≃ₜ Sphere3)
    (a : CoordinateBall M) :
    let C := {x : M // x ∉ a.parametrization '' Metric.ball (0:Euclidean3) (1/2)}
    let K : Set C := {x | (x:M) ∉ a.parametrization '' Metric.ball (0:Euclidean3) (3/4)}
    ∀ (Y : Type v) [MetricSpace Y] (f : C → Y), Continuous f →
      ∀ W : Set C, IsOpen W → K ⊆ W → ∀ eps : ℝ, 0<eps →
        ∃ h : C ≃ₜ C, (∀ x, x∉W → h x=x) ∧
          ∀ x∈K, ∀ y∈K, dist (f (h x)) (f (h y))<eps :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let C : Type u :=
    {x : M // x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2)}
  let K : Set C := {x | (x : M) ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)}
  change ∀ (Y : Type v) [MetricSpace Y] (f : C → Y), Continuous f →
      ∀ W : Set C, IsOpen W → K ⊆ W → ∀ eps : ℝ, 0 < eps →
        ∃ h : C ≃ₜ C, (∀ x, x ∉ W → h x = x) ∧
          ∀ x ∈ K, ∀ y ∈ K, dist (f (h x)) (f (h y)) < eps
  intro Y _ f hf W hW hKW eps heps
  let Cset : Set M :=
    {x : M | x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2)}
  let K₀ : Set M :=
    {x : M | x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)}
  have hsource_half : Metric.closedBall (0 : Euclidean3) (1 / 2) ⊆
      a.parametrization.source := by
    intro z hz
    apply a.contains_two
    have hz' : ‖z‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ 2 by linarith)
  have hsource_three : Metric.closedBall (0 : Euclidean3) (3 / 4) ⊆
      a.parametrization.source := by
    intro z hz
    apply a.contains_two
    have hz' : ‖z‖ ≤ (3 / 4 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ 2 by linarith)
  have hopen_three : IsOpen
      (a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)) := by
    exact a.parametrization.isOpen_image_of_subset_source Metric.isOpen_ball
      (fun z hz => by
        apply a.contains_two
        have hz' : ‖z‖ < (3 / 4 : ℝ) := by
          simpa [Metric.mem_ball, dist_zero_right] using hz
        simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ 2 by linarith)
        )
  have hK₀compact : IsCompact K₀ := by
    apply isCompact_univ.of_isClosed_subset
      (isClosed_compl_iff.mpr hopen_three)
    exact subset_univ _
  have hKcompact : IsCompact K := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    have himage : (fun x : C => (x : M)) '' K = K₀ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        have hxC : x ∈ Cset := by
          intro hxm
          obtain ⟨z, hz, hzx⟩ := hxm
          apply hx
          refine ⟨z, ?_, hzx⟩
          have hz' : ‖z‖ < (1 / 2 : ℝ) := by
            simpa [Metric.mem_ball, dist_zero_right] using hz
          have hz'' : ‖z‖ < (3 / 4 : ℝ) := by linarith
          simpa [Metric.mem_ball, dist_zero_right] using hz''
        exact ⟨⟨x, hxC⟩, hx, rfl⟩
    rw [himage]
    exact hK₀compact
  obtain ⟨U₀, hU₀, hWU₀⟩ := hW.image_val
  have hK₀U₀ : K₀ ⊆ U₀ := by
    intro x hx
    have hxC : x ∈ Cset := by
      intro hxm
      obtain ⟨z, hz, hzx⟩ := hxm
      apply hx
      refine ⟨z, ?_, hzx⟩
      have hz' : ‖z‖ < (1 / 2 : ℝ) := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      have hz'' : ‖z‖ < (3 / 4 : ℝ) := by linarith
      simpa [Metric.mem_ball, dist_zero_right] using hz''
    have hxK : (⟨x, hxC⟩ : C) ∈ K := by exact hx
    have hxW : (⟨x, hxC⟩ : C) ∈ W := hKW hxK
    have hximage : x ∈ (fun y : C => (y : M)) '' W :=
      ⟨⟨x, hxC⟩, hxW, rfl⟩
    change x ∈ Subtype.val '' W at hximage
    have hximage' : x ∈ U₀ ∩ Cset := hWU₀ ▸ hximage
    exact hximage'.1
  have hcompact_half : IsCompact
      (a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2)) := by
    exact (isCompact_closedBall (0 : Euclidean3) (1 / 2)).image_of_continuousOn
      (a.parametrization.continuousOn.mono hsource_half)
  have hopen_ext_half : IsOpen
      {x : M | x ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2)} := by
    exact isOpen_compl_iff.mpr hcompact_half.isClosed
  let U : Set M := U₀ ∩
      {x : M | x ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2)}
  have hU : IsOpen U := hU₀.inter hopen_ext_half
  have hK₀U : K₀ ⊆ U := by
    intro x hx
    refine ⟨hK₀U₀ hx, ?_⟩
    intro hxm
    obtain ⟨z, hz, hzx⟩ := hxm
    apply hx
    refine ⟨z, ?_, hzx⟩
    have hz' : ‖z‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hz'' : ‖z‖ < (3 / 4 : ℝ) := by linarith
    simpa [Metric.mem_ball, dist_zero_right] using hz''
  obtain ⟨r, hrhalf, hrthree, hbase, hOsubU⟩ :=
    exterior_neighborhood_basis M a U hU hK₀U
  have hrpos : 0 < r := by linarith
  have hrone : r < 1 := by linarith
  have hsource_r : Metric.closedBall (0 : Euclidean3) r ⊆
      a.parametrization.source := by
    intro z hz
    apply a.contains_two
    have hz' : ‖z‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ 2 by linarith)
  have hcompact_r : IsCompact
      (a.parametrization '' Metric.closedBall (0 : Euclidean3) r) := by
    exact (isCompact_closedBall (0 : Euclidean3) r).image_of_continuousOn
      (a.parametrization.continuousOn.mono hsource_r)
  let O : Set M := {x : M |
    x ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) r}
  have hOopen : IsOpen O := by
    exact isOpen_compl_iff.mpr hcompact_r.isClosed
  obtain ⟨eO⟩ := scaled_coordinate_open_exterior M e a r hrpos hrone
  let Uopen : TopologicalSpace.Opens M := ⟨O, hOopen⟩
  have hK₀O : K₀ ⊆ O := hbase
  obtain ⟨b, hKb, hbU⟩ :=
    compact_euclidean_chart_enclosure M Uopen eO K₀ hK₀compact hK₀O
  have hbremovedU : b.removed ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    apply hOsubU
    apply hbU
    refine ⟨z, ?_, rfl⟩
    have hz' : ‖z‖ < (1 : ℝ) := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    simpa [Metric.mem_closedBall, dist_zero_right] using (show ‖z‖ ≤ 2 by linarith)
  have hcU : b.parametrization 0 ∈ U := by
    exact hOsubU (hbU ⟨0, by simp [Metric.mem_closedBall], rfl⟩)
  have hcC : b.parametrization 0 ∈ Cset := by
    intro hxm
    obtain ⟨z, hz, hzx⟩ := hxm
    have : b.parametrization 0 ∈
        {x : M | x ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2)} :=
      hcU.2
    apply this
    exact ⟨z, Metric.ball_subset_closedBall hz, hzx⟩
  let c : C := ⟨b.parametrization 0, hcC⟩
  let P : Set C := f ⁻¹' Metric.ball (f c) (eps / 2)
  have hPopen : IsOpen P := hf.isOpen_preimage _ Metric.isOpen_ball
  have hcP : c ∈ P := by
    exact Metric.mem_ball_self (by positivity)
  obtain ⟨V₀, hV₀, hPV₀⟩ := hPopen.image_val
  let V : Set M := V₀ ∩ U
  have hV : IsOpen V := hV₀.inter hU
  have hcV₀ : (b.parametrization 0 : M) ∈ V₀ := by
    have hcmem : (b.parametrization 0 : M) ∈
        (fun x : C => (x : M)) '' P := ⟨c, hcP, rfl⟩
    change (b.parametrization 0 : M) ∈ Subtype.val '' P at hcmem
    have hcmem' : (b.parametrization 0 : M) ∈ V₀ ∩ Cset := hPV₀ ▸ hcmem
    exact hcmem'.1
  have hcV : b.parametrization 0 ∈ V := ⟨hcV₀, hcU⟩
  obtain ⟨H, hHimage, hHfix⟩ :=
    compact_subset_coordinate_squeeze b K₀ hK₀compact hKb V hV hcV
  have hAhalf_H : ∀ x : M,
      x ∈ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2) → H x = x := by
    intro x hx
    apply hHfix
    intro hxb
    have hxu : x ∈ U := hbremovedU hxb
    obtain ⟨z, hz, hzx⟩ := hx
    exact hxu.2 ⟨z, Metric.ball_subset_closedBall hz, hzx⟩
  have hpres : ∀ x : M,
      x ∈ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2) ↔
        H x ∈ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2) := by
    intro x
    constructor
    · intro hx
      rw [hAhalf_H x hx]
      exact hx
    · intro hx
      have hfix := hAhalf_H (H x) hx
      have hxeq : H x = x := H.injective hfix
      exact hxeq ▸ hx
  have hCiff : ∀ x : M, x ∈ Cset ↔ H x ∈ Cset := by
    intro x
    exact not_congr (hpres x)
  let h : C ≃ₜ C := H.subtype (fun x => hCiff x)
  refine ⟨h, ?_, ?_⟩
  · intro x hxW
    apply Subtype.ext
    change H (x : M) = (x : M)
    apply hHfix
    intro hxb
    apply hxW
    have hxu : (x : M) ∈ U := hbremovedU hxb
    have hximage : (x : M) ∈ (fun y : C => (y : M)) '' W := by
      change (x : M) ∈ Subtype.val '' W
      exact hWU₀.symm ▸ ⟨hxu.1, x.property⟩
    obtain ⟨y, hy, hxy⟩ := hximage
    have hsub : y = x := Subtype.ext hxy
    exact hsub ▸ hy
  · intro x hx y hy
    have hxV : (H (x : M)) ∈ V := by
      have hmem : (H (x : M)) ∈ H '' K₀ := ⟨(x : M), hx, rfl⟩
      exact hHimage hmem
    have hyV : (H (y : M)) ∈ V := by
      have hmem : (H (y : M)) ∈ H '' K₀ := ⟨(y : M), hy, rfl⟩
      exact hHimage hmem
    have hxsmall : dist (f (h x)) (f c) < eps / 2 := by
      have hxP : (⟨H (x : M), (h x).property⟩ : C) ∈ P := by
        have hximage : H (x : M) ∈
            (fun z : C => (z : M)) '' P := by
          change H (x : M) ∈ Subtype.val '' P
          exact hPV₀.symm ▸ ⟨hxV.1, (h x).property⟩
        obtain ⟨z, hz, hzx⟩ := hximage
        have hzeq : z = (⟨H (x : M), (h x).property⟩ : C) := Subtype.ext hzx
        exact hzeq ▸ hz
      exact Metric.mem_ball.mp hxP
    have hysmall : dist (f (h y)) (f c) < eps / 2 := by
      have hyP : (⟨H (y : M), (h y).property⟩ : C) ∈ P := by
        have hyimage : H (y : M) ∈
            (fun z : C => (z : M)) '' P := by
          change H (y : M) ∈ Subtype.val '' P
          exact hPV₀.symm ▸ ⟨hyV.1, (h y).property⟩
        obtain ⟨z, hz, hzy⟩ := hyimage
        have hzeq : z = (⟨H (y : M), (h y).property⟩ : C) := Subtype.ext hzy
        exact hzeq ▸ hz
      exact Metric.mem_ball.mp hyP
    calc
      dist (f (h x)) (f (h y)) ≤ dist (f (h x)) (f c) + dist (f c) (f (h y)) :=
        dist_triangle _ _ _
      _ < eps / 2 + eps / 2 := by
        exact add_lt_add hxsmall (by simpa [dist_comm] using hysmall)
      _ = eps := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
