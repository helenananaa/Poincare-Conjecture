import PoincareConjecture.ProofContract.Refinement20260927.CompactTubularReuse
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedTubularInverseAssembly
open PoincareConjecture.ProofContract.Refinement20260927
theorem tubular_inverse_assembly : TubularInverseAssemblyStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro N n e T U hU hzero hinj hcover
  classical
  let D : Set (ApproxAmbient n) := T.endpoint '' U
  have himage_open : ∀ W : Set T.total, IsOpen W → W ⊆ U →
      IsOpen (T.endpoint '' W) := by
    intro W hW hWU
    have himage : T.endpoint '' W = ⋃ p, T.endpoint '' (W ∩ (T.chart p).source) := by
      ext y
      constructor
      · rintro ⟨x, hxW, rfl⟩
        have hxU : x ∈ U := hWU hxW
        obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp (hcover hxU)
        exact Set.mem_iUnion.2 ⟨p, ⟨x, ⟨hxW, hxp⟩, rfl⟩⟩
      · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_inter_iff]
        rintro ⟨p, x, ⟨hxW, _⟩, rfl⟩
        exact ⟨x, hxW, rfl⟩
    rw [himage]
    apply isOpen_iUnion
    intro p
    have heq : T.endpoint '' (W ∩ (T.chart p).source) =
        (T.chart p) '' (W ∩ (T.chart p).source) := by
      apply Set.image_congr
      intro x hx
      exact (T.chart_agrees p hx.2).symm
    rw [heq]
    exact (T.chart p).isOpen_image_of_subset_source
      (hW.inter (T.chart p).open_source) Set.inter_subset_right
  have hDopen : IsOpen D := by
    exact himage_open U hU (Set.Subset.refl U)
  let f : U → D := fun x => ⟨T.endpoint x, ⟨x, x.2, rfl⟩⟩
  have hfcont : Continuous f :=
    Continuous.subtype_mk (T.endpoint.continuous.comp continuous_subtype_val) fun x =>
      ⟨x, x.2, rfl⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hinj x.2 y.2 (congrArg Subtype.val hxy)
  have hfopen : IsOpenMap f := by
    intro s hs
    rw [isOpen_induced_iff]
    refine ⟨T.endpoint '' (Subtype.val '' s), ?_, ?_⟩
    · have hsval : IsOpen (Subtype.val '' s) := hU.isOpenMap_subtype_val s hs
      have hsub : Subtype.val '' s ⊆ U := by
        rintro x ⟨y, hy, rfl⟩
        exact y.2
      exact himage_open (Subtype.val '' s) hsval hsub
    · ext y
      change (y.val ∈ T.endpoint '' (Subtype.val '' s)) ↔ y ∈ f '' s
      constructor
      · rintro ⟨x, hxval, hxy⟩
        rcases hxval with ⟨a, haS, rfl⟩
        refine ⟨a, haS, ?_⟩
        apply Subtype.ext
        exact hxy
      · rintro ⟨a, haS, hxy⟩
        refine ⟨a.val, ⟨a, haS, rfl⟩, ?_⟩
        exact congrArg Subtype.val hxy
  have hfsurj : Function.Surjective f := by
    intro y
    rcases y.2 with ⟨x, hxU, hxy⟩
    refine ⟨⟨x, hxU⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let H : U ≃ₜ D :=
    (Equiv.ofBijective f ⟨hfinj, hfsurj⟩).toHomeomorphOfContinuousOpen hfcont hfopen
  let retractMap : C(↑D, ↑N.toTopCat) :=
    ⟨fun y => T.project (H.symm y).val,
      T.project.continuous.comp H.symm.continuous.subtype_val⟩
  have hcontains : ∀ p : ↑N.toTopCat, e.map p ∈ D := by
    intro p
    have hzU : T.zero p ∈ U := hzero ⟨p, rfl⟩
    exact ⟨T.zero p, hzU, T.endpoint_zero p⟩
  have hretract : ∀ p : ↑N.toTopCat,
      retractMap ⟨e.map p, hcontains p⟩ = p := by
    intro p
    have hzU : T.zero p ∈ U := hzero ⟨p, rfl⟩
    have hH : H ⟨T.zero p, hzU⟩ = ⟨e.map p, hcontains p⟩ := by
      apply Subtype.ext
      exact T.endpoint_zero p
    have hInv : H.symm ⟨e.map p, hcontains p⟩ = ⟨T.zero p, hzU⟩ := by
      rw [← hH]
      exact H.symm_apply_apply _
    change T.project (H.symm ⟨e.map p, hcontains p⟩).val = p
    rw [hInv, T.project_zero]
  let A : AmbientRetraction N n :=
    { embed := e.map
      domain := D
      open_domain := hDopen
      contains := hcontains
      retract := retractMap
      retract_embed := hretract }
  let localRetract : ApproxAmbient n → ↑N.toTopCat := fun y =>
    if hy : y ∈ D then retractMap ⟨y, hy⟩ else Classical.choice N.nonempty
  let R : SmoothRetractionData N n :=
    { toAmbientRetraction := A
      smooth_embed := e.smooth
      localRetract := localRetract
      agrees := by
        intro y hy
        simp [localRetract, hy, A]
      smooth_localRetract := by
        apply contMDiffOn_of_locally_contMDiffOn
        intro y hyD
        rcases hyD with ⟨x, hxU, rfl⟩
        obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp (hcover hxU)
        let c := T.chart p
        let V : Set (ApproxAmbient n) := c.target ∩ c.symm ⁻¹' U
        have hVopen : IsOpen V := c.isOpen_inter_preimage_symm hU
        have hyV : T.endpoint x ∈ V := by
          constructor
          · rw [← T.chart_agrees p hxp]
            exact c.map_source hxp
          · change c.symm (T.endpoint x) ∈ U
            rw [← T.chart_agrees p hxp, c.left_inv hxp]
            exact hxU
        refine ⟨V, hVopen, hyV, ?_⟩
        have hbase := T.smooth_projection p
        have hbase' := hbase.mono (t := D ∩ V) (by
          rintro z ⟨_, hzV⟩
          exact hzV.1)
        apply hbase'.congr
        intro z hz
        have hzV : z ∈ V := hz.2
        rcases hz.1 with ⟨x', hx'U, hzx'⟩
        have hzD : z ∈ D := hz.1
        have hsymmU : c.symm z ∈ U := hzV.2
        have hsymmsource : c.symm z ∈ c.source := c.map_target hzV.1
        have hendpointSymm : T.endpoint (c.symm z) = z := by
          rw [← T.chart_agrees p hsymmsource]
          exact c.right_inv hzV.1
        have hxeq : x' = c.symm z := hinj hx'U hsymmU (by rw [hzx', hendpointSymm])
        have hHx : H ⟨x', hx'U⟩ = ⟨z, hzD⟩ := by
          apply Subtype.ext
          exact hzx'
        have hInv : H.symm ⟨z, hzD⟩ = ⟨x', hx'U⟩ := by
          rw [← hHx]
          exact H.symm_apply_apply _
        simp only [localRetract, dif_pos hzD]
        change T.project (H.symm ⟨z, hzD⟩).val = T.project (c.symm z)
        rw [hInv]
        have hsub : (⟨x', hx'U⟩ : U) = ⟨c.symm z, hsymmU⟩ := Subtype.ext hxeq
        rw [hsub] }
  refine ⟨R, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro x hxU
    have hxD : T.endpoint x ∈ D := ⟨x, hxU, rfl⟩
    change localRetract (T.endpoint x) = T.project x
    simp only [localRetract, dif_pos hxD]
    change T.project (H.symm ⟨T.endpoint x, hxD⟩).val = T.project x
    have hHx : H ⟨x, hxU⟩ = ⟨T.endpoint x, hxD⟩ := by
      apply Subtype.ext
      rfl
    have hInv : H.symm ⟨T.endpoint x, hxD⟩ = ⟨x, hxU⟩ := by
      rw [← hHx]
      exact H.symm_apply_apply _
    rw [hInv]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedTubularInverseAssembly
