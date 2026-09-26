import PoincareConjecture.ParallelImplementation.ClosedSphereCutData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ClosedSideHalfCollar
open Set PoincareConjecture.ProofContract.V1
open PoincareConjecture.ParallelImplementation.ClosedSphereCutData
open scoped Topology
/-- Construct the one-sided collar in the ACTUAL positive closed cut piece.
This supplies the concrete input for the ball-cap seam construction. -/
theorem exists_actual_closed_side_half_collar
    {M : ClosedThreeManifold} (hsc : SimplyConnectedSpace M)
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (hf : Topology.IsEmbedding f)
    (p : Sphere2) :
    let U := connectedComponentIn (embeddedSphereCutSlice f)ᶜ
      (embeddedSphereCutPositiveSeed f p)
    ∃ b : Sphere2 → closure U, ∃ k : Sphere2 × Ico (0 : ℝ) 1 → closure U,
      Topology.IsEmbedding b ∧ Topology.IsOpenEmbedding k ∧
      (∀ s : Sphere2, (b s).1 = f (s, ⟨0, by norm_num⟩)) ∧
      (∀ (s : Sphere2) (t : Ico (0 : ℝ) 1),
        (k (s,t)).1 = f (s, ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1,t.2.2]⟩)) ∧
      (∀ s : Sphere2, k (s, ⟨0, by norm_num⟩) = b s) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp only
  let U : Set M := connectedComponentIn (embeddedSphereCutSlice f)ᶜ
    (embeddedSphereCutPositiveSeed f p)
  have hcut := closed_embedded_sphere_cut_sides hsc f hf p
  dsimp only [U] at hcut
  rcases hcut with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hclosure⟩
  let C : Set M := closure U
  let g : Sphere2 × Ioo (-2 : ℝ) 2 → M := fun q =>
    f (q.1, ⟨(q.2 : ℝ) / 2, by
      constructor <;> linarith [q.2.2.1, q.2.2.2]⟩)
  have hg : Topology.IsOpenEmbedding g := by
    simpa only [g] using
      ClosedSphereCollarOpen.closed_sphere_collar_interior_isOpenEmbedding f hf
  let j : Sphere2 × Ico (0 : ℝ) 1 → Sphere2 × Ioo (-2 : ℝ) 2 := fun q =>
    (q.1, ⟨(q.2 : ℝ), by constructor <;> linarith [q.2.2.1, q.2.2.2]⟩)
  have hj : Topology.IsEmbedding j := by
    change Topology.IsEmbedding (fun q : Sphere2 × Ico (0 : ℝ) 1 =>
      (q.1, (⟨(q.2 : ℝ), by constructor <;> linarith [q.2.2.1, q.2.2.2]⟩ : Ioo (-2 : ℝ) 2)))
    exact Topology.IsEmbedding.id.prodMap
      (Topology.IsEmbedding.inclusion (by
        intro t ht
        constructor <;> linarith [ht.1, ht.2]))
  let k0 : Sphere2 × Ico (0 : ℝ) 1 → M := g ∘ j
  have hk0 : Topology.IsEmbedding k0 := by
    exact hg.isEmbedding.comp hj
  have hkclosure : ∀ q : Sphere2 × Ico (0 : ℝ) 1, k0 q ∈ C := by
    intro q
    change f (q.1, ⟨(q.2 : ℝ) / 2, _⟩) ∈ closure U
    exact (hclosure q.1 ((q.2 : ℝ) / 2)
      (by nlinarith [q.2.2.1])
      (by nlinarith [q.2.2.1, q.2.2.2])).2 (by nlinarith [q.2.2.1])
  let k : Sphere2 × Ico (0 : ℝ) 1 → C := fun q => ⟨k0 q, hkclosure q⟩
  have hkemb : Topology.IsEmbedding k := hk0.codRestrict C hkclosure
  let A : Set (Sphere2 × Ioo (-2 : ℝ) 2) :=
    Set.univ ×ˢ ((Subtype.val : Ioo (-2 : ℝ) 2 → ℝ) ⁻¹' Ioo (-1 : ℝ) 1)
  have hAopen : IsOpen A := by
    exact isOpen_univ.prod (isOpen_Ioo.preimage continuous_subtype_val)
  have hgAopen : IsOpen (g '' A) := hg.isOpenMap _ hAopen
  have hrange : Set.range k = (Subtype.val : C → M) ⁻¹' (g '' A) := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      change k0 q ∈ g '' A
      refine ⟨j q, ?_, rfl⟩
      simp only [A, Set.mem_prod, Set.mem_univ, true_and, Set.mem_preimage,
        Set.mem_Ioo]
      constructor <;> linarith [q.2.2.1, q.2.2.2]
    · intro hy
      rcases hy with ⟨q, hqA, hqy⟩
      rcases q with ⟨s, t⟩
      have ht : (-1 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1 := by
        simpa [A] using hqA
      have hy : g (s, t) ∈ closure U := by
        rw [hqy]
        simpa [C] using y.property
      have hloc := (hclosure s ((t : ℝ) / 2)
        (by nlinarith [ht.1, ht.2])
        (by nlinarith [ht.1, ht.2])).1 (by simpa [g] using hy)
      have htpos : 0 ≤ (t : ℝ) := by linarith
      let t' : Ico (0 : ℝ) 1 := ⟨(t : ℝ), ⟨htpos, by linarith [ht.2]⟩⟩
      refine ⟨(s, t'), ?_⟩
      apply Subtype.ext
      change g (s, t) = y.1
      simpa [g, k0, j] using hqy
  have hrangeOpen : IsOpen (Set.range k) := by
    rw [hrange]
    exact hgAopen.preimage continuous_subtype_val
  have hkopen : Topology.IsOpenEmbedding k := ⟨hkemb, hrangeOpen⟩
  let Z : Set (Sphere2 × Icc (-1 : ℝ) 1) :=
    {q | (q.2 : ℝ) = 0}
  let e : Sphere2 ≃ₜ Z :=
    { toEquiv :=
        { toFun := fun s => ⟨(s, ⟨0, by norm_num⟩), by simp [Z]⟩
          invFun := fun q => q.1.1
          left_inv := by intro s; rfl
          right_inv := by
            intro q
            apply Subtype.ext
            apply Prod.ext
            · rfl
            · apply Subtype.ext
              have hq' := q.property
              change (↑(q.1.2) : ℝ) = 0 at hq'
              exact hq'.symm }
      continuous_toFun := by fun_prop
      continuous_invFun := continuous_fst.comp continuous_subtype_val }
  let j0 : Sphere2 → Sphere2 × Icc (-1 : ℝ) 1 :=
    fun s => (s, ⟨0, by norm_num⟩)
  have hj0 : Topology.IsEmbedding j0 := by
    change Topology.IsEmbedding ((Subtype.val : Z → Sphere2 × Icc (-1 : ℝ) 1) ∘ e)
    exact Topology.IsEmbedding.subtypeVal.comp e.isEmbedding
  let b0 : Sphere2 → M := f ∘ j0
  have hb0 : Topology.IsEmbedding b0 := hf.comp hj0
  have hbclosure : ∀ s : Sphere2, b0 s ∈ C := by
    intro s
    change f (s, ⟨0, _⟩) ∈ closure U
    exact (hclosure s 0 (by norm_num) (by norm_num)).2 (by norm_num)
  let b : Sphere2 → C := fun s => ⟨b0 s, hbclosure s⟩
  have hb : Topology.IsEmbedding b := hb0.codRestrict C hbclosure
  refine ⟨b, k, hb, hkopen, ?_, ?_, ?_⟩
  · intro s
    rfl
  · intro s t
    rfl
  · intro s
    apply Subtype.ext
    change k0 (s, ⟨0, by norm_num⟩) = b0 s
    simp [k0, b0, g, j, j0]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ClosedSideHalfCollar
