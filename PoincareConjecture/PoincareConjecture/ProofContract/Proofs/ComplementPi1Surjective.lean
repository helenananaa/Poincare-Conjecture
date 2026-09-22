import PoincareConjecture.ProofContract.Proofs.ExteriorCoverConnected
import PoincareConjecture.ProofContract.Proofs.ComplementPi1Reduction
import HatcherLib.Ch1.SimplyConnectedPieceSurjection
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Actual complement pi1 surjectivity, with no outstanding theorem premise. -/
theorem coordinate_complement_pi1_surjective : CoordinateComplementPi1SurjectiveStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro M b
  rcases exterior_cover_sets b with ⟨hopenU, hcover, hUcomp, -⟩
  rcases puncture_cover_sets b with ⟨-, hopenV, -, -, -⟩
  rcases exterior_cover_connectivity b with ⟨hU_path, hV_simple, hUV_path⟩
  obtain ⟨x, hx⟩ := hUV_path.nonempty
  have hxU : x ∈ exteriorU b := hx.1
  have hxV : x ∈ punctureV b := hx.2
  let u : exteriorU b := ⟨x, hxU⟩
  let r : C(exteriorU b, b.Complement) :=
    ⟨fun y => ⟨(y : M), hUcomp y⟩,
      Continuous.subtype_mk continuous_subtype_val (fun y => hUcomp y)⟩
  let c : b.Complement := r u
  let j : C(b.Complement, M) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let iU : C(exteriorU b, M) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hsurj : Surjective (FundamentalGroup.map iU u) := by
    simpa [iU, u] using
      (HatcherLib.pi1_surjective_of_simply_connected_open_piece
        (exteriorU b) (punctureV b) hopenU hopenV hcover hU_path hV_simple hUV_path
        x hxU hxV)
  have hcomp : j.comp r = iU := by
    ext y
    rfl
  have hmap (d : FundamentalGroup (exteriorU b) u) :
      FundamentalGroup.map j (r u) (FundamentalGroup.map r u d) =
        FundamentalGroup.map (j.comp r) u d := by
    change ((FundamentalGroup.toPath d).map r).map j = _
    rw [← Path.Homotopic.Quotient.map_comp]
    rfl
  have hcomp_map :
      (FundamentalGroup.map j c) ∘ (FundamentalGroup.map r u) =
        FundamentalGroup.map iU u := by
    funext d
    change FundamentalGroup.map j (r u) (FundamentalGroup.map r u d) =
      FundamentalGroup.map iU u d
    rw [hmap]
    rfl
  refine ⟨c, ?_⟩
  exact Function.Surjective.of_comp (by rw [hcomp_map]; exact hsurj)
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
