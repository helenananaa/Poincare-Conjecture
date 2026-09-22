import PoincareConjecture.ProofContract.Proofs.PunctureCover
import PoincareConjecture.ProofContract.Proofs.RadialDeformation
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
def complementIntoPuncture {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) :
    C(b.Complement, punctureU b) :=
  ⟨fun x => ⟨(x:M), (puncture_cover_sets b).2.2.2.1 x⟩,
    continuous_subtype_val.subtype_mk _⟩
def punctureIntoManifold {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) :
    C(punctureU b, M) := ⟨Subtype.val, continuous_subtype_val⟩
def complementIntoManifold {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) :
    C(b.Complement, M) := ⟨Subtype.val, continuous_subtype_val⟩
/-- A relative homotopy, not merely a pointwise map of the punctured neighborhood. -/
theorem coordinate_puncture_deformation {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) :
    ∃ r : C(punctureU b, b.Complement), r.comp (complementIntoPuncture b) = ContinuousMap.id b.Complement ∧
      ∃ H : (punctureIntoManifold b).Homotopy ((complementIntoManifold b).comp r),
        ∀ (t : unitInterval) (c : b.Complement), H (t, complementIntoPuncture b c) = (c:M) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let X := punctureU b
  let A : Set X := {x | (x : M) ∈ b.parametrization '' Metric.closedBall 0 1}
  let B : Set X := {x | (x : M) ∉ b.removed}
  have hremoved : IsOpen b.removed :=
    (coordinate_removed_open_complement_compact b).1
  have hclosed1 : IsClosed (b.parametrization '' Metric.closedBall (0 : Euclidean3) 1) := by
    rw [← (coordinate_closure_frontier b).1]
    exact isClosed_closure
  have hAclosed : IsClosed A := by
    change IsClosed ((fun x : X => (x : M)) ⁻¹'
      (b.parametrization '' Metric.closedBall (0 : Euclidean3) 1))
    exact hclosed1.preimage continuous_subtype_val
  have hBclosed : IsClosed B := by
    change IsClosed ((fun x : X => (x : M)) ⁻¹' b.removedᶜ)
    exact hremoved.isClosed_compl.preimage continuous_subtype_val
  have hcover : A ∪ B = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : (x : M) ∈ b.parametrization '' Metric.closedBall (0 : Euclidean3) 1
    · exact Or.inl hx
    · right
      change (x : M) ∉ b.removed
      intro hx'
      apply hx
      exact image_mono Metric.ball_subset_closedBall hx'
  have hsource1 : Metric.closedBall (0 : Euclidean3) 1 ⊆
      b.parametrization.source := by
    intro y hy
    apply b.contains_two
    have hy' : ‖y‖ ≤ (1 : ℝ) := by
      simpa [Metric.mem_closedBall] using hy
    simpa [Metric.mem_closedBall] using (show ‖y‖ ≤ (2 : ℝ) by linarith)
  have hinj1 : Set.InjOn b.parametrization
      (Metric.closedBall (0 : Euclidean3) 1) := by
    intro x hx y hy hxy
    have h := congrArg b.parametrization.symm hxy
    simpa only [b.parametrization.left_inv (hsource1 hx),
      b.parametrization.left_inv (hsource1 hy)] using h
  obtain ⟨R, hRformula, hRzero, hRone, hRfixed, hRbounds⟩ :=
    radial_push_to_unit_complement
  let D := {y : Euclidean3 // (1 / 2 : ℝ) < ‖y‖}
  have hcoord : ∀ x : A,
      (1 / 2 : ℝ) < ‖(b.parametrization.symm (x : X) : Euclidean3)‖ := by
    intro x
    obtain ⟨y, hy, hxy⟩ := x.property
    have hysrc : y ∈ b.parametrization.source := hsource1 hy
    have hsymm : b.parametrization.symm (x : X) = y := by
      rw [← hxy]
      exact b.parametrization.left_inv hysrc
    rw [hsymm]
    by_contra hn
    have hy' : ‖y‖ ≤ (1 / 2 : ℝ) := le_of_not_gt hn
    have hxU : (x : M) ∉ b.parametrization ''
        Metric.closedBall (0 : Euclidean3) (1 / 2 : ℝ) := by
      change (x : M) ∉ b.parametrization ''
        Metric.closedBall (0 : Euclidean3) (1 / 2 : ℝ)
      exact x.1.property
    apply hxU
    exact ⟨y, by simpa [Metric.mem_closedBall] using hy', hxy⟩
  let coord : A → D := fun x =>
    ⟨b.parametrization.symm (x : X), hcoord x⟩
  have htargetA : ∀ x : A, (x : M) ∈ b.parametrization.target := by
    intro x
    rw [← b.parametrization.image_source_eq_target]
    obtain ⟨y, hy, hxy⟩ := x.property
    exact ⟨y, hsource1 hy, hxy⟩
  have hcoord_cont : Continuous coord := by
    apply Continuous.subtype_mk
    · exact b.parametrization.continuousOn_symm.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) htargetA
  have hcoord_le : ∀ x : A, ‖(coord x : Euclidean3)‖ ≤ (1 : ℝ) := by
    intro x
    obtain ⟨y, hy, hxy⟩ := x.property
    have hsymm : b.parametrization.symm (x : X) = y := by
      rw [← hxy]
      exact b.parametrization.left_inv (hsource1 hy)
    rw [show (coord x : Euclidean3) = b.parametrization.symm (x : X) by rfl,
      hsymm]
    simpa [Metric.mem_closedBall] using hy
  have hradial_complement : ∀ y : D, ‖(y : Euclidean3)‖ ≤ (1 : ℝ) →
      b.parametrization (R (1, y)) ∉ b.removed := by
    intro y hy
    have hlow : 1 ≤ ‖R (1, y)‖ := hRone y
    have hupp : ‖R (1, y)‖ ≤ (1 : ℝ) := by
      have h := (hRbounds (1 : unitInterval) y).2
      simpa [max_eq_left hy] using h
    change b.parametrization (R (1, y)) ∉ b.removed
    change b.parametrization (R (1, y)) ∉
      b.parametrization '' Metric.ball (0 : Euclidean3) 1
    intro hz
    obtain ⟨z, hzball, hzeq⟩ := hz
    have hzclosed : z ∈ Metric.closedBall (0 : Euclidean3) 1 :=
      Metric.ball_subset_closedBall hzball
    have houtclosed : R (1, y) ∈ Metric.closedBall (0 : Euclidean3) 1 := by
      simpa [Metric.mem_closedBall] using hupp
    have houtz : R (1, y) = z := hinj1 houtclosed hzclosed hzeq.symm
    have hznorm : ‖z‖ < (1 : ℝ) := by
      simpa [Metric.mem_ball] using hzball
    rw [← houtz] at hznorm
    linarith
  let localA : C(A, b.Complement) :=
    ⟨fun x => ⟨b.parametrization (R (1, coord x)),
        hradial_complement (coord x) (hcoord_le x)⟩,
      (b.parametrization.continuousOn.comp_continuous
        (R.continuous.comp (continuous_const.prodMk hcoord_cont)) (by
          intro x
          apply b.contains_two
          have h := (hRbounds (1 : unitInterval) (coord x)).2
          have hupp : ‖R (1, coord x)‖ ≤ (1 : ℝ) := by
            simpa [max_eq_left (hcoord_le x)] using h
          simpa [Metric.mem_closedBall] using (show ‖R (1, coord x)‖ ≤ (2 : ℝ) by linarith))).subtype_mk
        (fun x => hradial_complement (coord x) (hcoord_le x))⟩
  have hnotAcomp : ∀ x : X, x ∉ A → (x : M) ∉ b.removed := by
    intro x hx
    change (x : M) ∉ b.removed
    intro hx'
    apply hx
    exact image_mono Metric.ball_subset_closedBall hx'
  let f : X → b.Complement := fun x =>
    if hx : x ∈ A then localA ⟨x, hx⟩ else ⟨(x : M), hnotAcomp x hx⟩
  let g : X → b.Complement := fun x =>
    if hx : x ∈ B then ⟨(x : M), hx⟩ else f x
  have hfA : ContinuousOn f (closure A) := by
    rw [hAclosed.closure_eq, continuousOn_iff_continuous_restrict]
    convert localA.continuous using 1
    ext x
    simp [f]
  have hgB : ContinuousOn g B := by
    rw [continuousOn_iff_continuous_restrict]
    have hid : Continuous (fun x : B =>
        (⟨(x : X), x.property⟩ : b.Complement)) := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    convert hid using 1
    ext x
    simp [g]
  have hAcsubB : closure Aᶜ ⊆ B := by
    have hsub : Aᶜ ⊆ B := by
      intro x hx
      have hx' := (Set.mem_union x A B).1 (hcover ▸ Set.mem_univ x)
      exact hx'.resolve_left hx
    rw [← hBclosed.closure_eq]
    exact closure_mono hsub
  have hgAc : ContinuousOn g (closure Aᶜ) := hgB.mono hAcsubB
  let Rset : Set X := {x | (x : M) ∈ b.removed}
  have hRsetopen : IsOpen Rset := by
    change IsOpen ((fun x : X => (x : M)) ⁻¹' b.removed)
    exact hremoved.preimage continuous_subtype_val
  have hRsetsubA : Rset ⊆ A := by
    intro x hx
    change (x : M) ∈ b.parametrization '' Metric.closedBall (0 : Euclidean3) 1
    exact image_mono Metric.ball_subset_closedBall hx
  have hlocal_id : ∀ (x : X) (hxA : x ∈ A) (hxB : x ∈ B),
      localA ⟨x, hxA⟩ = ⟨(x : M), hxB⟩ := by
    intro x hxA hxB
    have hxA' := hxA
    obtain ⟨y, hy, hxy⟩ := hxA'
    have hsymm : b.parametrization.symm (x : X) = y := by
      rw [← hxy]
      exact b.parametrization.left_inv (hsource1 hy)
    have hy_le : ‖y‖ ≤ (1 : ℝ) := by simpa [Metric.mem_closedBall] using hy
    have hy_notlt : ¬ ‖y‖ < (1 : ℝ) := by
      intro hylt
      apply hxB
      change (x : M) ∉ b.removed at hxB
      exact ⟨y, by simpa [Metric.mem_ball] using hylt, hxy⟩
    have hy_eq : ‖y‖ = (1 : ℝ) := le_antisymm hy_le (le_of_not_gt hy_notlt)
    have hfix : R (1, coord ⟨x, hxA⟩) = coord ⟨x, hxA⟩ := by
      apply hRfixed
      rw [show (coord ⟨x, hxA⟩ : Euclidean3) = y by simp [coord, hsymm], hy_eq]
    have hparam : b.parametrization (b.parametrization.symm (x : X)) = (x : M) :=
      b.parametrization.right_inv (htargetA ⟨x, hxA⟩)
    apply Subtype.ext
    dsimp [localA]
    rw [hfix]
    change b.parametrization (b.parametrization.symm (x : X)) = (x : M)
    exact hparam
  have hfront : ∀ x ∈ frontier A, f x = g x := by
    intro x hx
    have hxA : x ∈ A := by
      rw [← hAclosed.closure_eq]
      exact hx.1
    have hxB : x ∈ B := by
      by_contra hn
      have hxR : x ∈ Rset := by
        change (x : M) ∈ b.removed
        change ¬ ((x : M) ∉ b.removed) at hn
        exact not_not.mp hn
      have hnhds : A ∈ 𝓝 x :=
        Filter.mem_of_superset (hRsetopen.mem_nhds hxR) hRsetsubA
      exact hx.2 (mem_interior_iff_mem_nhds.mpr hnhds)
    rw [show f x = localA ⟨x, hxA⟩ by simp [f, hxA],
      show g x = ⟨(x : M), hxB⟩ by simp [g, hxB]]
    exact hlocal_id x hxA hxB
  let rfun : X → b.Complement := Set.piecewise A f g
  have hrfun : Continuous rfun := continuous_piecewise hfront hfA hgAc
  let r : C(punctureU b, b.Complement) := ⟨rfun, hrfun⟩
  have hr_on_B : ∀ (x : X) (hxB : x ∈ B), r x = ⟨(x : M), hxB⟩ := by
    intro x hxB
    by_cases hxA : x ∈ A
    · rw [show r x = f x by simp [r, rfun, hxA], show f x = localA ⟨x, hxA⟩ by simp [f, hxA]]
      exact hlocal_id x hxA hxB
    · rw [show r x = g x by simp [r, rfun, hxA], show g x = ⟨(x : M), hxB⟩ by simp [g, hxB]]
  have hrcomp : r.comp (complementIntoPuncture b) = ContinuousMap.id b.Complement := by
    ext c
    have hcU : (complementIntoPuncture b c : X) ∈ B := by
      change (c : M) ∉ b.removed
      exact c.property
    exact congrArg Subtype.val (hr_on_B (complementIntoPuncture b c) hcU)
  let Aprod : Set (unitInterval × X) := {p | p.2 ∈ A}
  let Bprod : Set (unitInterval × X) := {p | p.2 ∈ B}
  have hAprodclosed : IsClosed Aprod := by
    change IsClosed ((fun p : unitInterval × X => p.2) ⁻¹' A)
    exact hAclosed.preimage continuous_snd
  have hBprodclosed : IsClosed Bprod := by
    change IsClosed ((fun p : unitInterval × X => p.2) ⁻¹' B)
    exact hBclosed.preimage continuous_snd
  have hprodcover : Aprod ∪ Bprod = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro p
    have hp := (Set.mem_union p.2 A B).1 (hcover ▸ Set.mem_univ p.2)
    exact hp
  have hmemAprod : ∀ (t : unitInterval) (x : X), x ∈ A → (t, x) ∈ Aprod := by
    intro t x hx
    change x ∈ A
    exact hx
  have hmemBprod : ∀ (t : unitInterval) (x : X), x ∈ B → (t, x) ∈ Bprod := by
    intro t x hx
    change x ∈ B
    exact hx
  have hnotmemAprod : ∀ (t : unitInterval) (x : X), x ∉ A →
      (t, x) ∉ Aprod := by
    intro t x hx htx
    apply hx
    change x ∈ A at htx
    exact htx
  have hpA : ∀ p : Aprod, p.1.2 ∈ A := by
    intro p
    have hp := p.2
    change p.1.2 ∈ A at hp
    exact hp
  have hAproj : Continuous (fun p : Aprod => (⟨p.1.2, hpA p⟩ : A)) := by
    apply Continuous.subtype_mk
    exact continuous_snd.comp continuous_subtype_val
  have hprodmap : Continuous (fun p : Aprod =>
      (p.1.1, coord ⟨p.1.2, hpA p⟩)) := by
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (hcoord_cont.comp hAproj)
  let localHA : C(Aprod, M) :=
    ⟨fun p => b.parametrization (R (p.1.1, coord ⟨p.1.2, hpA p⟩)),
      b.parametrization.continuousOn.comp_continuous
        (R.continuous.comp hprodmap)
        (by
          intro p
          apply b.contains_two
          have h := (hRbounds p.1.1 (coord ⟨p.1.2, hpA p⟩)).2
          have hupp : ‖R (p.1.1, coord ⟨p.1.2, hpA p⟩)‖ ≤ (1 : ℝ) := by
            simpa [max_eq_left (hcoord_le ⟨p.1.2, hpA p⟩)] using h
          simpa [Metric.mem_closedBall] using (show ‖R (p.1.1,
            coord ⟨p.1.2, hpA p⟩)‖ ≤ (2 : ℝ) by linarith))⟩
  let fH : (unitInterval × X) → M := fun p =>
    if hp : p ∈ Aprod then localHA ⟨p, hp⟩ else (p.2 : M)
  let gH : (unitInterval × X) → M := fun p =>
    if hp : p ∈ Bprod then (p.2 : M) else fH p
  have hfHA : ContinuousOn fH (closure Aprod) := by
    rw [hAprodclosed.closure_eq, continuousOn_iff_continuous_restrict]
    convert localHA.continuous using 1
    ext p
    simp [fH]
  have hgHB : ContinuousOn gH Bprod := by
    rw [continuousOn_iff_continuous_restrict]
    have hid : Continuous (fun p : Bprod => (p.1.2 : M)) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
    convert hid using 1
    ext p
    simp [gH]
  have hprodsub : closure Aprodᶜ ⊆ Bprod := by
    have hsub : Aprodᶜ ⊆ Bprod := by
      intro p hp
      exact (Set.mem_union p Aprod Bprod).1 (hprodcover ▸ Set.mem_univ p) |>.resolve_left hp
    rw [← hBprodclosed.closure_eq]
    exact closure_mono hsub
  have hgHAc : ContinuousOn gH (closure Aprodᶜ) := hgHB.mono hprodsub
  let Rprod : Set (unitInterval × X) := {p | (p.2 : M) ∈ b.removed}
  have hRprodopen : IsOpen Rprod := by
    change IsOpen ((fun p : unitInterval × X => (p.2 : M)) ⁻¹' b.removed)
    exact hremoved.preimage (continuous_subtype_val.comp continuous_snd)
  have hRprodsub : Rprod ⊆ Aprod := by
    intro p hp
    change (p.2 : M) ∈ b.parametrization '' Metric.closedBall (0 : Euclidean3) 1
    exact image_mono Metric.ball_subset_closedBall hp
  have hlocalHA_id : ∀ (p : unitInterval × X) (hpA : p ∈ Aprod) (hpB : p ∈ Bprod),
      localHA ⟨p, hpA⟩ = (p.2 : M) := by
    intro p hpA hpB
    obtain ⟨y, hy, hxy⟩ := (show p.2 ∈ A from hpA)
    have hsymm : b.parametrization.symm (p.2 : X) = y := by
      rw [← hxy]
      exact b.parametrization.left_inv (hsource1 hy)
    have hy_le : ‖y‖ ≤ (1 : ℝ) := by simpa [Metric.mem_closedBall] using hy
    have hy_notlt : ¬ ‖y‖ < (1 : ℝ) := by
      intro hylt
      apply hpB
      exact ⟨y, by simpa [Metric.mem_ball] using hylt, hxy⟩
    have hy_eq : ‖y‖ = (1 : ℝ) := le_antisymm hy_le (le_of_not_gt hy_notlt)
    have hfix : R (p.1, coord ⟨p.2, hpA⟩) = coord ⟨p.2, hpA⟩ := by
      apply hRfixed
      rw [show (coord ⟨p.2, hpA⟩ : Euclidean3) = y by simp [coord, hsymm], hy_eq]
    have hparam : b.parametrization (b.parametrization.symm (p.2 : X)) = (p.2 : M) :=
      b.parametrization.right_inv (htargetA ⟨p.2, hpA⟩)
    dsimp [localHA]
    rw [hfix]
    change b.parametrization (b.parametrization.symm (p.2 : X)) = (p.2 : M)
    exact hparam
  have hprodfront : ∀ p ∈ frontier Aprod, fH p = gH p := by
    intro p hp
    have hpA : p ∈ Aprod := by
      rw [← hAprodclosed.closure_eq]
      exact hp.1
    have hpB : p ∈ Bprod := by
      by_contra hn
      have hpR : p ∈ Rprod := by
        change (p.2 : M) ∈ b.removed
        change ¬ ((p.2 : M) ∉ b.removed) at hn
        exact not_not.mp hn
      have hnhds : Aprod ∈ 𝓝 p :=
        Filter.mem_of_superset (hRprodopen.mem_nhds hpR) hRprodsub
      exact hp.2 (mem_interior_iff_mem_nhds.mpr hnhds)
    rw [show fH p = localHA ⟨p, hpA⟩ by simp [fH, hpA],
      show gH p = (p.2 : M) by simp [gH, hpB]]
    exact hlocalHA_id p hpA hpB
  let Hfun : (unitInterval × X) → M := Set.piecewise Aprod fH gH
  have hHfun : Continuous Hfun := continuous_piecewise hprodfront hfHA hgHAc
  have hHzero : ∀ x : X, Hfun (0, x) = (x : M) := by
    intro x
    by_cases hxA : x ∈ A
    · have h0A := hmemAprod 0 x hxA
      rw [show Hfun (0, x) = fH (0, x) by
        dsimp [Hfun]; exact Set.piecewise_eq_of_mem Aprod fH gH h0A]
      rw [show fH (0, x) = localHA ⟨(0, x), h0A⟩ by simp [fH, h0A]]
      have hxA' := hxA
      obtain ⟨y, hy, hxy⟩ := hxA'
      have hsymm : b.parametrization.symm (x : X) = y := by
        rw [← hxy]
        exact b.parametrization.left_inv (hsource1 hy)
      have hparam : b.parametrization (b.parametrization.symm (x : X)) = (x : M) :=
        b.parametrization.right_inv (htargetA ⟨x, hxA⟩)
      dsimp [localHA]
      rw [hRzero, show (coord ⟨x, hxA⟩ : Euclidean3) =
        b.parametrization.symm (x : X) by rfl, hparam]
    · have hxB : x ∈ B := (Set.mem_union x A B).1 (hcover ▸ Set.mem_univ x) |>.resolve_left hxA
      have h0B := hmemBprod 0 x hxB
      have h0A := hnotmemAprod 0 x hxA
      rw [show Hfun (0, x) = gH (0, x) by
        dsimp [Hfun]; exact Set.piecewise_eq_of_notMem Aprod fH gH h0A,
        show gH (0, x) = (x : M) by simp [gH, h0B]]
  have hHone : ∀ x : X, Hfun (1, x) = (r x : M) := by
    intro x
    by_cases hxA : x ∈ A
    · have h1A := hmemAprod 1 x hxA
      rw [show Hfun (1, x) = fH (1, x) by
        dsimp [Hfun]; exact Set.piecewise_eq_of_mem Aprod fH gH h1A,
        show fH (1, x) = localHA ⟨(1, x), h1A⟩ by simp [fH, h1A]]
      rw [show (r x : M) = (localA ⟨x, hxA⟩ : M) by
        simp [r, rfun, hxA, f, hxA]]
      rfl
    · have hxB : x ∈ B := (Set.mem_union x A B).1 (hcover ▸ Set.mem_univ x) |>.resolve_left hxA
      have h1B := hmemBprod 1 x hxB
      have h1A := hnotmemAprod 1 x hxA
      rw [show Hfun (1, x) = gH (1, x) by
        dsimp [Hfun]; exact Set.piecewise_eq_of_notMem Aprod fH gH h1A,
        show gH (1, x) = (x : M) by simp [gH, h1B],
        show (r x : M) = (x : M) by
          rw [hr_on_B x hxB]]
  let H : (punctureIntoManifold b).Homotopy
      ((complementIntoManifold b).comp r) :=
    { toContinuousMap := ⟨Hfun, hHfun⟩
      map_zero_left := by
        intro x
        exact hHzero x
      map_one_left := by
        intro x
        exact hHone x }
  refine ⟨r, hrcomp, H, ?_⟩
  intro t c
  have hcX : (complementIntoPuncture b c : X) ∈ B := by
    change (c : M) ∉ b.removed
    exact c.property
  have hfixed : ∀ t : unitInterval, Hfun (t, complementIntoPuncture b c) = (c : M) := by
    intro t
    by_cases hxA : (complementIntoPuncture b c : X) ∈ A
    · have htA := hmemAprod t (complementIntoPuncture b c) hxA
      rw [show Hfun (t, complementIntoPuncture b c) =
        fH (t, complementIntoPuncture b c) by
          dsimp [Hfun]; exact Set.piecewise_eq_of_mem Aprod fH gH htA,
        show fH (t, complementIntoPuncture b c) =
          localHA ⟨(t, complementIntoPuncture b c), htA⟩ by simp [fH, htA]]
      exact hlocalHA_id (t, complementIntoPuncture b c) hxA
        (hmemBprod t (complementIntoPuncture b c) hcX)
    · have htA := hnotmemAprod t (complementIntoPuncture b c) hxA
      rw [show Hfun (t, complementIntoPuncture b c) =
        gH (t, complementIntoPuncture b c) by
          dsimp [Hfun]; exact Set.piecewise_eq_of_notMem Aprod fH gH htA,
        show gH (t, complementIntoPuncture b c) =
          (c : M) by
            simp [gH, hmemBprod t (complementIntoPuncture b c) hcX]
            rfl]
  change H.toContinuousMap (t, complementIntoPuncture b c) = (c : M)
  change Hfun (t, complementIntoPuncture b c) = (c : M)
  exact hfixed t
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
