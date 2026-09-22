import HatcherLib.Ch1.VanKampen
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
set_option autoImplicit false
noncomputable section
namespace HatcherLib
open Set Function
open scoped Topology
/-- A simply connected second open piece contributes no generators to pi1. -/
theorem pi1_surjective_of_simply_connected_open_piece
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hUpath : IsPathConnected U) (hVsimple : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hxU⟩) :=
/- SWARM_PROOF_BEGIN -/
by
  have hVpath : IsPathConnected V := hVsimple.isPathConnected
  let cover : PathConnectedOpenCover x Bool :=
    { carrier := fun b => if b then V else U
      isOpen := by
        intro b
        cases b
        · simpa using hU
        · simpa using hV
      cover := by
        intro y hy
        rcases (Set.mem_union y U V).1 (hcover ▸ Set.mem_univ y) with hyU | hyV
        · exact Set.mem_iUnion.2 ⟨false, by simpa using hyU⟩
        · exact Set.mem_iUnion.2 ⟨true, by simpa using hyV⟩
      base_mem := by
        intro b
        cases b
        · simpa using hxU
        · simpa using hxV
      pathConnected := by
        intro b
        cases b
        · simpa using hUpath
        · simpa using hVpath
      interPathConnected := by
        intro b c
        cases b <;> cases c
        · simpa using hUpath
        · simpa using hUV
        · simpa [inter_comm] using hUV
        · simpa using hVpath }
  letI : SimplyConnectedSpace V := hVsimple.simplyConnectedSpace
  have hword : ∀ w : FreeProduct (fun i => CoverFundamentalGroup cover i),
      ∃ a : FundamentalGroup U ⟨x, hxU⟩,
        FundamentalGroup.map
            (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hxU⟩ a =
          vanKampenMap cover w := by
    intro w
    induction w using Monoid.CoprodI.induction_on with
    | one =>
        exact ⟨1, by simp only [map_one]⟩
    | of i a =>
        cases i with
        | false =>
            dsimp [cover] at a
            change FundamentalGroup U ⟨x, hxU⟩ at a
            refine ⟨a, ?_⟩
            rw [vanKampenMap, freeProductLift, Monoid.CoprodI.lift_of]
            congr 1
        | true =>
            refine ⟨1, ?_⟩
            letI : SimplyConnectedSpace (cover.carrier true) := by
              change SimplyConnectedSpace V
              exact hVsimple.simplyConnectedSpace
            have ha : a = 1 := Subsingleton.elim _ _
            rw [ha]
            rw [vanKampenMap, freeProductLift, Monoid.CoprodI.lift_of]
            change (1 : FundamentalGroup X x) = 1
            rfl
    | mul y z hy hz =>
        obtain ⟨a, ha⟩ := hy
        obtain ⟨b, hb⟩ := hz
        refine ⟨a * b, ?_⟩
        rw [map_mul, ha, hb]
        exact (vanKampenMap cover).map_mul y z |>.symm
  intro g
  obtain ⟨w, hw⟩ := vanKampenMap_surjective cover g
  obtain ⟨a, ha⟩ := hword w
  exact ⟨a, ha.trans hw⟩
/- SWARM_PROOF_END -/
end HatcherLib
