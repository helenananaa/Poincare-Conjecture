import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search note: no `lean_leansearch` tool was available in this session, so this repair
-- follows the component-wise API already present in the file.

open scoped Manifold ContDiff Topology

universe uK uVE uVM uHE uHM uE uM

open Set

variable {K : Type uK} [NontriviallyNormedField K]
variable {VE : Type uVE} [NormedAddCommGroup VE] [NormedSpace K VE]
variable {VM : Type uVM} [NormedAddCommGroup VM] [NormedSpace K VM]
variable {HE : Type uHE} [TopologicalSpace HE]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace HE E]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {IE : ModelWithCorners K VE HE} [IsManifold IE (∞ : ℕ∞ω) E]
variable {IM : ModelWithCorners K VM HM} [IsManifold IM (∞ : ℕ∞ω) M]
variable {π : E → M}

/- The following private topological lemmas isolate the only non-manifold part of the problem.
For a covering over a locally path-connected space, the restriction to any connected component is
surjective onto the corresponding component and remains a covering. -/

universe uA uB

variable {A : Type uA} {B : Type uB} [TopologicalSpace A] [TopologicalSpace B]
variable {p : A → B}

private abbrev coveringComponentMap (hp : IsCoveringMap p) (a : A) :
    connectedComponent a → connectedComponent (p a) :=
  fun z ↦ ⟨p z, hp.continuous.mapsTo_connectedComponent a z.2⟩

private theorem coveringComponentMap_surjective [LocallyPathConnectedSpace B]
    (hp : IsCoveringMap p) (a : A) : Function.Surjective (coveringComponentMap hp a) := by
  intro y
  let B₀ : Set B := connectedComponent (p a)
  letI : LocallyPathConnectedSpace B₀ := isOpen_connectedComponent.locallyPathConnectedSpace
  letI : ConnectedSpace B₀ := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : PathConnectedSpace B₀ := PathConnectedSpace.of_locallyPathConnectedSpace
  let γ₀ : Path (⟨p a, mem_connectedComponent⟩ : B₀) y :=
    PathConnectedSpace.somePath _ _
  let γ : Path (p a) y := γ₀.map continuous_subtype_val
  let Γ := hp.liftPath γ a γ.source
  have hΓ₀ : Γ 0 = a := hp.liftPath_zero γ a γ.source
  have hΓp : p (Γ 1) = y := by
    exact (congr_fun (hp.liftPath_lifts γ a γ.source) 1).trans γ.target
  refine ⟨⟨Γ 1, ?_⟩, Subtype.ext hΓp⟩
  apply pathComponent_subset_component a
  rw [mem_pathComponent_iff]
  exact ⟨⟨Γ, hΓ₀, rfl⟩⟩

private theorem coveringComponentMap_isCoveringMap [LocallyPathConnectedSpace B]
    (hp : IsCoveringMap p) (a : A) : IsCoveringMap (coveringComponentMap hp a) := by
  intro y
  obtain ⟨z, hz⟩ := coveringComponentMap_surjective hp a y
  haveI : Nonempty (p ⁻¹' ({(y : B)} : Set B)) := ⟨⟨z, congr_arg Subtype.val hz⟩⟩
  let t := (hp (y : B)).toTrivialization
  let V : Set B := pathComponentIn t.baseSet (y : B)
  have hybase : (y : B) ∈ t.baseSet := (hp (y : B)).mem_toTrivialization_baseSet
  have hyV : (y : B) ∈ V := mem_pathComponentIn_self hybase
  have hVbase : V ⊆ t.baseSet := fun _ hv ↦ pathComponentIn_subset hv
  have hVopen : IsOpen V := t.open_baseSet.pathComponentIn _
  have hVpath : IsPathConnected V := isPathConnected_pathComponentIn hybase
  have same_component (w : p ⁻¹' V) :
      (w : A) ∈ connectedComponent a ↔
        t.invFun ((y : B), (t (w : A)).2) ∈ connectedComponent a := by
    let i : p ⁻¹' ({(y : B)} : Set B) := (t (w : A)).2
    obtain ⟨γ, hγ⟩ := hVpath.joinedIn (p w) w.2 (y : B) hyV
    have hγtarget (s) : (γ s, i) ∈ t.target := by
      rw [t.target_eq]
      exact ⟨hVbase (hγ s), Set.mem_univ _⟩
    have hδcont : Continuous (fun s ↦ t.invFun (γ s, i)) := by
      change Continuous (t.invFun ∘ fun s ↦ (γ s, i))
      exact t.continuousOn_invFun.comp_continuous
        (γ.continuous.prodMk continuous_const) hγtarget
    have hδzero : t.invFun (γ 0, i) = (w : A) := by
      rw [γ.source]
      exact t.symm_apply_mk_proj (t.mem_source.mpr (hVbase w.2))
    have hδone : t.invFun (γ 1, i) = t.invFun ((y : B), i) := by
      rw [γ.target]
    have hi_mem : t.invFun ((y : B), i) ∈ connectedComponent (w : A) := by
      apply pathComponent_subset_component (w : A)
      rw [mem_pathComponent_iff]
      exact ⟨⟨⟨_, hδcont⟩, hδzero, hδone⟩⟩
    have hcomp : connectedComponent (w : A) =
        connectedComponent (t.invFun ((y : B), i)) :=
      connectedComponent_eq hi_mem
    change (w : A) ∈ connectedComponent a ↔
      t.invFun ((y : B), i) ∈ connectedComponent a
    constructor
    · intro hw
      rw [connectedComponent_eq hw, hcomp]
      exact mem_connectedComponent
    · intro hi
      rw [connectedComponent_eq hi, ← hcomp]
      exact mem_connectedComponent
  let W : Set (connectedComponent (p a)) := Subtype.val ⁻¹' V
  have hyW : y ∈ W := hyV
  have hWopen : IsOpen W := hVopen.preimage continuous_subtype_val
  have hqcont : Continuous (coveringComponentMap hp a) :=
    (hp.continuous.comp continuous_subtype_val).subtype_mk _
  have hqWopen : IsOpen (coveringComponentMap hp a ⁻¹' W) := hWopen.preimage hqcont
  let H := t.preimageHomeomorph hVbase
  let Hc : {w : p ⁻¹' V // (w : A) ∈ connectedComponent a} ≃ₜ
      {wi : V × (p ⁻¹' ({(y : B)} : Set B)) //
        t.invFun ((y : B), wi.2) ∈ connectedComponent a} :=
    H.subtype (fun w ↦ by simpa [H] using same_component w)
  let eDom : coveringComponentMap hp a ⁻¹' W ≃ₜ
      {w : p ⁻¹' V // (w : A) ∈ connectedComponent a} :=
    { toFun := fun z ↦ ⟨⟨z.1.1, z.2⟩, z.1.2⟩
      invFun := fun w ↦ ⟨⟨w.1.1, w.2⟩, w.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hVD : V ⊆ connectedComponent (p a) := fun v hv ↦ by
    rw [connectedComponent_eq y.2]
    exact hVpath.isConnected.isPreconnected.subset_connectedComponent hyV hv
  let anchor : (p ⁻¹' ({(y : B)} : Set B)) → A :=
    fun i ↦ t.invFun ((y : B), i)
  have hanchor : Continuous anchor := by
    change Continuous (t.invFun ∘ fun i ↦ ((y : B), i))
    exact t.continuousOn_invFun.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ ↦ t.mem_target.mpr hybase)
  have htcoord : Continuous (fun e :
      (coveringComponentMap hp a ⁻¹' ({y} : Set (connectedComponent (p a)))) ↦
      (t (e.1.1 : A)).2) := by
    have ht : Continuous (fun e :
        (coveringComponentMap hp a ⁻¹' ({y} : Set (connectedComponent (p a)))) ↦
        t (e.1.1 : A)) := by
      apply t.continuousOn_toFun.comp_continuous
      · fun_prop
      · intro e
        rw [t.mem_source]
        have heq : p (e.1.1 : A) = (y : B) := congr_arg Subtype.val e.2
        rw [heq]
        exact hybase
    exact continuous_snd.comp ht
  let wToV : W → V := fun w ↦ ⟨(w : B), w.2⟩
  have hwToV : Continuous wToV := by fun_prop
  let eCod : {wi : V × (p ⁻¹' ({(y : B)} : Set B)) //
        t.invFun ((y : B), wi.2) ∈ connectedComponent a} ≃ₜ
      W × (coveringComponentMap hp a ⁻¹' ({y} : Set (connectedComponent (p a)))) :=
    { toFun := fun wi ↦
        (⟨⟨wi.1.1.1, hVD wi.1.1.2⟩, wi.1.1.2⟩,
          ⟨⟨t.invFun ((y : B), wi.1.2), wi.2⟩,
            Subtype.ext (t.proj_symm_apply' hybase)⟩)
      invFun := fun we ↦
        ⟨(wToV we.1, (t (we.2.1.1 : A)).2), by
            have heq : p (we.2.1.1 : A) = (y : B) := congr_arg Subtype.val we.2.2
            have he_source : (we.2.1.1 : A) ∈ t.source :=
              t.mem_source.mpr (by rw [heq]; exact hybase)
            have hanchor_e : t.invFun ((y : B), (t (we.2.1.1 : A)).2) =
                (we.2.1.1 : A) := by
              calc
                t.invFun ((y : B), (t (we.2.1.1 : A)).2) =
                    t.invFun (p (we.2.1.1 : A), (t (we.2.1.1 : A)).2) :=
                  congrArg t.invFun (Prod.ext heq.symm rfl)
                _ = (we.2.1.1 : A) := t.symm_apply_mk_proj he_source
            rw [hanchor_e]
            exact we.2.1.2⟩
      left_inv := by
        intro wi
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · change (t (t.invFun ((y : B), wi.1.2))).2 = wi.1.2
          exact congrArg Prod.snd (t.apply_symm_apply' hybase)
      right_inv := by
        intro we
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          apply Subtype.ext
          change t.invFun ((y : B), (t (we.2.1.1 : A)).2) = (we.2.1.1 : A)
          have heq : p (we.2.1.1 : A) = (y : B) := congr_arg Subtype.val we.2.2
          have he_source : (we.2.1.1 : A) ∈ t.source :=
            t.mem_source.mpr (by rw [heq]; exact hybase)
          calc
            t.invFun ((y : B), (t (we.2.1.1 : A)).2) =
                t.invFun (p (we.2.1.1 : A), (t (we.2.1.1 : A)).2) :=
              congrArg t.invFun (Prod.ext heq.symm rfl)
            _ = (we.2.1.1 : A) := t.symm_apply_mk_proj he_source
      continuous_toFun := by
        apply Continuous.prodMk
        · fun_prop
        · exact ((hanchor.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _).subtype_mk _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact Continuous.prodMk (hwToV.comp continuous_fst) (htcoord.comp continuous_snd) }
  haveI : DiscreteTopology (p ⁻¹' ({(y : B)} : Set B)) :=
    (hp (y : B)).discreteTopology_fiber
  let fiberIncl :
      (coveringComponentMap hp a ⁻¹' ({y} : Set (connectedComponent (p a)))) →
        (p ⁻¹' ({(y : B)} : Set B)) :=
    fun e ↦ ⟨e.1.1, congr_arg Subtype.val e.2⟩
  have hFiberInclCont : Continuous fiberIncl := by fun_prop
  have hFiberInclInj : Function.Injective fiberIncl := by
    intro e e' he
    have hA : (e.1.1 : A) = (e'.1.1 : A) :=
      congr_arg (fun i : p ⁻¹' ({(y : B)} : Set B) ↦ (i : A)) he
    exact Subtype.ext (Subtype.ext hA)
  letI : DiscreteTopology
      (coveringComponentMap hp a ⁻¹' ({y} : Set (connectedComponent (p a)))) :=
    DiscreteTopology.of_continuous_injective hFiberInclCont hFiberInclInj
  refine ⟨inferInstance, W, hyW, hWopen, hqWopen, eDom.trans (Hc.trans eCod), ?_⟩
  intro z
  simp [eDom, Hc, eCod, H, coveringComponentMap]

private abbrev setRestriction {S : Set A} {T : Set B}
    (hmap : MapsTo p S T) : S → T := fun z ↦ ⟨p z, hmap z.2⟩

private theorem setRestriction_isCoveringMap {S : Set A} {T : Set B}
    (hp : IsCoveringMap p) (hpre : p ⁻¹' T = S) :
    IsCoveringMap (@setRestriction A B p S T (fun x hx ↦ by
      have : x ∈ p ⁻¹' T := hpre.symm ▸ hx
      exact this)) := by
  let hmap : MapsTo p S T := fun x hx ↦ by
    have : x ∈ p ⁻¹' T := hpre.symm ▸ hx
    exact this
  change IsCoveringMap (@setRestriction A B p S T hmap)
  let e : S ≃ₜ p ⁻¹' T := Homeomorph.setCongr hpre.symm
  have h := (hp.restrictPreimage T).comp_homeomorph e
  have heq : T.restrictPreimage p ∘ e = @setRestriction A B p S T hmap := by
    funext z
    rfl
  rw [← heq]
  exact h

private noncomputable def componentInHomeomorph (S : Set A) (x : A) (hx : x ∈ S) :
    connectedComponentIn S x ≃ₜ connectedComponent (⟨x, hx⟩ : S) :=
  ((Topology.IsEmbedding.subtypeVal.homeomorphImage
      (connectedComponent (⟨x, hx⟩ : S))).trans
    (Homeomorph.setCongr (connectedComponentIn_eq_image hx).symm)).symm

private lemma componentInHomeomorph_symm_coe (S : Set A) (x : A) (hx : x ∈ S)
    (z : connectedComponent (⟨x, hx⟩ : S)) :
    (((componentInHomeomorph S x hx).symm z : connectedComponentIn S x) : A) =
      ((z : S) : A) := by
  rfl

private lemma componentInHomeomorph_coe (S : Set A) (x : A) (hx : x ∈ S)
    (z : connectedComponentIn S x) :
    ((((componentInHomeomorph S x hx) z :
      connectedComponent (⟨x, hx⟩ : S)) : S) : A) = (z : A) := by
  have h := congr_arg (fun w : connectedComponentIn S x ↦ (w : A))
    ((componentInHomeomorph S x hx).symm_apply_apply z)
  rw [componentInHomeomorph_symm_coe] at h
  exact h

private abbrev componentInRestriction {S : Set A} {T : Set B}
    (hp : IsCoveringMap p) (hmap : MapsTo p S T) (x : S) :
    connectedComponentIn S (x : A) → connectedComponentIn T (p x) :=
  fun z ↦ ⟨p z, connectedComponentIn_mono (p x) hmap.image_subset
    (hp.continuous.mapsTo_connectedComponentIn x.2 z.2)⟩

private theorem componentInRestriction_surjective {S : Set A} {T : Set B}
    [LocallyPathConnectedSpace T] (hp : IsCoveringMap p) (hpre : p ⁻¹' T = S)
    (x : S) : Function.Surjective (componentInRestriction hp (fun z hz ↦ by
      have : z ∈ p ⁻¹' T := hpre.symm ▸ hz
      exact this) x) := by
  let hmap : MapsTo p S T := fun z hz ↦ by
    have : z ∈ p ⁻¹' T := hpre.symm ▸ hz
    exact this
  let pST : S → T := setRestriction hmap
  have hpST : IsCoveringMap pST := by
    simpa only [pST, hmap] using setRestriction_isCoveringMap hp hpre
  let eA := componentInHomeomorph S (x : A) x.2
  let eB := componentInHomeomorph T (p x) (hmap x.2)
  change Function.Surjective (componentInRestriction hp hmap x)
  intro y
  obtain ⟨z, hz⟩ := coveringComponentMap_surjective hpST x (eB y)
  refine ⟨eA.symm z, ?_⟩
  apply eB.injective
  calc
    eB (componentInRestriction hp hmap x (eA.symm z)) = coveringComponentMap hpST x z := by
      apply Subtype.ext
      apply Subtype.ext
      dsimp only [eB]
      rw [componentInHomeomorph_coe]
      change p ((eA.symm z : connectedComponentIn S (x : A)) : A) = p ((z : S) : A)
      dsimp only [eA]
      rw [componentInHomeomorph_symm_coe]
    _ = eB y := hz

private theorem componentInRestriction_isCoveringMap {S : Set A} {T : Set B}
    [LocallyPathConnectedSpace T] (hp : IsCoveringMap p) (hpre : p ⁻¹' T = S)
    (x : S) : IsCoveringMap (componentInRestriction hp (fun z hz ↦ by
      have : z ∈ p ⁻¹' T := hpre.symm ▸ hz
      exact this) x) := by
  let hmap : MapsTo p S T := fun z hz ↦ by
    have : z ∈ p ⁻¹' T := hpre.symm ▸ hz
    exact this
  let pST : S → T := setRestriction hmap
  have hpST : IsCoveringMap pST := by
    simpa only [pST, hmap] using setRestriction_isCoveringMap hp hpre
  let eA := componentInHomeomorph S (x : A) x.2
  let eB := componentInHomeomorph T (p x) (hmap x.2)
  change IsCoveringMap (componentInRestriction hp hmap x)
  have hc := (coveringComponentMap_isCoveringMap hpST x).comp_homeomorph eA
    |>.homeomorph_comp eB.symm
  have heq : eB.symm ∘ coveringComponentMap hpST x ∘ eA =
      componentInRestriction hp hmap x := by
    funext z
    apply Subtype.ext
    change p (((eA z : connectedComponent (⟨x, x.2⟩ : S)) : S) : A) = p (z : A)
    rw [componentInHomeomorph_coe]
  rw [← heq]
  exact hc

/-- A smooth covering map sends boundary points of the total space to boundary points of the base
manifold. -/
-- Proof sketch: use `IsLocalDiffeomorph.preimage_boundary` for the local-diffeomorphism part of the
-- smooth covering map, specialized to smooth manifolds and regularity `∞`.
theorem smooth_covering_mapsTo_boundary (hlocal : IsLocalDiffeomorph IE IM ∞ π) :
    MapsTo π (IE.boundary E) (IM.boundary M) := by
  intro x hx
  rw [← hlocal.preimage_boundary (by simp)] at hx
  exact hx

/-- A surjective smooth covering map maps the boundary of the total space onto the boundary of the
base manifold. -/
-- Proof sketch: combine surjectivity of `π` with `mapsTo_boundary`; any preimage of a boundary
-- point is again a boundary point by the local-diffeomorphism boundary formula.
theorem smooth_covering_image_boundary_eq (hsurj : Function.Surjective π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) :
    π '' IE.boundary E = IM.boundary M := by
  apply Set.Subset.antisymm
  · exact (smooth_covering_mapsTo_boundary hlocal).image_subset
  · intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    refine ⟨x, ?_, rfl⟩
    rw [← hlocal.preimage_boundary (by simp)]
    exact hy

/-- A smooth covering map sends each connected component of the boundary into the connected
component of the image point in the boundary of the base. -/
-- Proof sketch: `π` is continuous because a covering map is continuous; apply
-- `Continuous.mapsTo_connectedComponentIn` to the boundary, then rewrite the image of the boundary
-- using `image_boundary_eq`.
theorem smooth_covering_mapsTo_boundary_component (hcov : IsCoveringMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π)
    (x : IE.boundary E) :
    MapsTo π (connectedComponentIn (IE.boundary E) x)
      (connectedComponentIn (IM.boundary M) (π x)) := by
  intro y hy
  exact connectedComponentIn_mono (π x)
    (smooth_covering_mapsTo_boundary hlocal).image_subset
    (hcov.continuous.mapsTo_connectedComponentIn x.2 hy)

/-- The restriction of a smooth covering map to a connected component of the boundary, viewed as a
map to the connected component of the image point in the boundary of the base. -/
abbrev boundaryComponentRestriction (hcov : IsCoveringMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) (x : IE.boundary E) :
    connectedComponentIn (IE.boundary E) x →
      connectedComponentIn (IM.boundary M) (π x) :=
  fun y ↦ ⟨π y, smooth_covering_mapsTo_boundary_component hcov hlocal x y.2⟩

/-- The boundary-component restriction agrees with the original covering map on underlying
points. -/
-- Proof sketch: unfold `boundaryComponentRestriction`; its codomain subtype stores `π y` as the
-- underlying point.
theorem boundaryComponentRestriction_val (hcov : IsCoveringMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) (x : IE.boundary E)
    (y : connectedComponentIn (IE.boundary E) x) :
    ((boundaryComponentRestriction hcov hlocal x y :
      connectedComponentIn (IM.boundary M) (π x)) : M) = π y :=
    rfl

/-- Problem 5-12 (1): the restriction of a smooth covering map to a boundary connected component is
onto the corresponding boundary connected component of the image point. -/
-- Proof sketch: first restrict the ambient covering map to the whole boundary using
-- `image_boundary_eq`; then use connectedness of the target component to show the source component
-- containing `x` covers that target component surjectively.
theorem boundaryComponentRestriction_surjective
    [LocallyPathConnectedSpace (IM.boundary M)] (hsurj : Function.Surjective π)
    (hcov : IsCoveringMap π) (hlocal : IsLocalDiffeomorph IE IM ∞ π)
    (x : IE.boundary E) :
    Function.Surjective (boundaryComponentRestriction hcov hlocal x) := by
  clear hsurj
  have hpre : π ⁻¹' IM.boundary M = IE.boundary E :=
    hlocal.preimage_boundary (by simp)
  simpa only [boundaryComponentRestriction, componentInRestriction] using
    (componentInRestriction_surjective hcov hpre x)

/-- Problem 5-12 (2): the restriction of a smooth covering map to a boundary connected component
is still a covering map. -/
-- Proof sketch: restrict the ambient covering map first to the boundary and then to the connected
-- component of `π x`; identify the resulting source with the connected component of `x` in the
-- boundary.
theorem boundaryComponentRestriction_isCoveringMap
    [LocallyPathConnectedSpace (IM.boundary M)] (hcov : IsCoveringMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π)
    (x : IE.boundary E) :
    IsCoveringMap (boundaryComponentRestriction hcov hlocal x) := by
  have hpre : π ⁻¹' IM.boundary M = IE.boundary E :=
    hlocal.preimage_boundary (by simp)
  simpa only [boundaryComponentRestriction, componentInRestriction] using
    (componentInRestriction_isCoveringMap hcov hpre x)

/-- Problem 5-12 (3): the ambient smooth local-diffeomorphism property restricts to each connected
component of the boundary. -/
-- Proof sketch: the ambient map is a local diffeomorphism everywhere, so its restriction to the
-- subset `connectedComponentIn (IE.boundary E) x` is automatically an `IsLocalDiffeomorphOn`.
theorem boundaryComponentRestriction_isLocalDiffeomorphOn
    (hlocal : IsLocalDiffeomorph IE IM ∞ π)
    (x : IE.boundary E) :
    IsLocalDiffeomorphOn IE IM ∞ π (connectedComponentIn (IE.boundary E) x) :=
  hlocal.isLocalDiffeomorphOn _
