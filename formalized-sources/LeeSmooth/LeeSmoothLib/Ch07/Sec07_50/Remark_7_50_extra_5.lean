import LeeSmoothLib.Ch07.Sec07_50.Proposition_7_26
import LeeSmoothLib.Ch05.Sec05_31.Definition_5_31_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_29.Theorem_5_8
import LeeSmoothLib.Ch05.Sec05_33.Theorem_5_33
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16
import LeeSmoothLib.Ch02.Sec02_09.Example_2_14
import LeeSmoothLib.Ch07.Sec07_46.Definition_7_46_extra_3
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_11
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
import LeeSmoothLib.Ch07.Sec07_50.Theorem_7_25
import LeeSmoothLib.Ch07.Sec07_50.Definition_7_50_extra_4
import LeeSmoothLib.Ch07.Sec07_50.StabilizerSmoothLevelBundle
-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped Manifold ContDiff

universe u𝕜 uE uH uG uE' uH' uM uQ uV

section OrbitSubmanifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {I : ModelWithCorners 𝕜 E H} [LieGroup I ∞ G]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ M]
variable [MulAction G M] [ContMDiffSMul I J ∞ G M]

namespace LieSubgroup

omit [LieGroup I ∞ G] in
/-- Helper: the inclusion of a Lie subgroup carrier into the ambient
group is continuous because the stored immersion witness is pointwise continuous. -/
theorem subtypeVal_continuous (S : LieSubgroup I) :
    Continuous (Subtype.val : S.carrier → G) := by
  -- Exercise 4.16 upgrades each pointwise immersion witness for the subgroup inclusion to
  -- continuity at that point, so continuity follows pointwise.
  rw [continuous_iff_continuousAt]
  intro x
  let hImm :
      Manifold.IsImmersion (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G) :=
    S.subtype_val_isImmersion
  exact (hImm.isImmersionAt x).continuousAt

/-- Helper: a closed Lie subgroup carrier determines the canonical closed
subgroup owner with the same underlying subgroup. -/
def closedCarrierOwner (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) : ClosedSubgroup G :=
  { toSubgroup := S.carrier
    isClosed' := hS_closed }

/-- Helper: the subgroup inclusion factors through the canonical closed
subgroup with the same carrier. -/
def toClosedCarrierHom (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    S.carrier →* closedCarrierOwner S hS_closed :=
  { toFun := fun x ↦ ⟨x.1, x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl }

omit [LieGroup I ∞ G] in
/-- Helper: the factor map into the canonical closed subgroup is
continuous because it is the subgroup inclusion with the codomain repackaged as a subtype. -/
theorem toClosedCarrierHom_continuous (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Continuous (toClosedCarrierHom S hS_closed) := by
  -- Repackage continuity of the subgroup inclusion through the closed-subgroup subtype owner.
  exact
    (subtypeVal_continuous S).subtype_mk fun x ↦ by
      exact x.2

omit [LieGroup I ∞ G] in
/-- Helper: the factor map onto the canonical closed subgroup is
surjective because both domain and codomain encode the same subgroup elements. -/
theorem toClosedCarrierHom_surjective (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Function.Surjective (toClosedCarrierHom S hS_closed) := by
  rintro ⟨x, hx⟩
  -- Lift the closed-subgroup point back to the original Lie-subgroup carrier without changing the
  -- ambient group element.
  refine ⟨⟨x, hx⟩, rfl⟩

omit [LieGroup I ∞ G] in
/-- Helper: the canonical factor map into the closed-subgroup owner still
records the same ambient group element as the original subgroup inclusion. -/
theorem subtypeVal_factor_through_closedCarrierOwner (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    (Subtype.val : S.carrier → G) =
      (Subtype.val : closedCarrierOwner S hS_closed → G) ∘ toClosedCarrierHom S hS_closed := by
  -- Both sides are definitionally the same subgroup inclusion; only the codomain owner changes.
  rfl

omit [LieGroup I ∞ G] in
/-- Helper: the factor map into the canonical closed subgroup owner is
injective because both source and target remember the same ambient group element. -/
theorem toClosedCarrierHom_injective (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Function.Injective (toClosedCarrierHom S hS_closed) := by
  intro x y hxy
  -- Forgetting the codomain packaging reduces equality to equality of ambient group elements.
  apply Subtype.ext
  exact congrArg Subtype.val hxy

omit [LieGroup I ∞ G] in
/-- Helper: the canonical factor map to the closed-subgroup owner is a
bijection of underlying subgroup elements. -/
theorem toClosedCarrierHom_bijective (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Function.Bijective (toClosedCarrierHom S hS_closed) := by
  -- Combine the explicit injective and surjective carrier-transport lemmas.
  exact ⟨toClosedCarrierHom_injective S hS_closed, toClosedCarrierHom_surjective S hS_closed⟩

end LieSubgroup

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: the canonical map from `G ⧸ MulAction.stabilizer G p` onto
the orbit of `p` has image exactly `MulAction.orbit G p`. -/
theorem range_ofQuotientStabilizer_eq_orbit (p : M) :
    Set.range (MulAction.ofQuotientStabilizer G p) = MulAction.orbit G p := by
  -- Compare the range pointwise so that the forward and reverse directions use the canonical
  -- quotient-stabilizer orbit API directly.
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    -- Every point produced by the descended quotient map lies in the orbit by construction.
    exact MulAction.ofQuotientStabilizer_mem_orbit G p q
  · intro hy
    refine ⟨MulAction.orbitEquivQuotientStabilizer G p ⟨y, hy⟩, ?_⟩
    -- The orbit-stabilizer equivalence sends the chosen orbit point back to a quotient class
    -- whose image under the descended map is exactly that point.
    change
      (((MulAction.orbitEquivQuotientStabilizer G p).symm
          ((MulAction.orbitEquivQuotientStabilizer G p) ⟨y, hy⟩) : MulAction.orbit G p) : M) = y
    exact congrArg Subtype.val
      (Equiv.symm_apply_apply (MulAction.orbitEquivQuotientStabilizer G p) ⟨y, hy⟩)

omit [IsManifold J ∞ M] in
/-- Helper: once the descended map
`MulAction.ofQuotientStabilizer G p` is available as an injective immersion from a boundaryless
manifold structure on `G ⧸ MulAction.stabilizer G p`, its image gives the required immersed
submanifold structure on the orbit of `p`. -/
theorem orbitImmersedSubmanifold_fromQuotient
    {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    (p : M)
    [ChartedSpace EQ (G ⧸ MulAction.stabilizer G p)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞) (G ⧸ MulAction.stabilizer G p)]
    (hImm : IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p)) :
    ∃ S : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uG} J M,
      S.carrier = MulAction.orbit G p := by
  -- Package the injective descended quotient map as an immersed submanifold of `M`.
  refine ⟨hImm.toImmersedSubmanifold (MulAction.injective_ofQuotientStabilizer G p), ?_⟩
  -- The carrier of that immersed submanifold is exactly the orbit identified by the quotient API.
  exact range_ofQuotientStabilizer_eq_orbit p

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: transporting the stabilizer quotient along a subgroup equality
does not change the image of the descended orbit map. -/
theorem range_ofQuotientStabilizer_comp_quotientEquivOfEq_eq_orbit
    (p : M) {S : Subgroup G} (hS : S = MulAction.stabilizer G p) :
    Set.range (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS) =
      MulAction.orbit G p := by
  -- The transported quotient map still lands in the orbit because `ofQuotientStabilizer` does.
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact MulAction.ofQuotientStabilizer_mem_orbit G p _
  · intro hy
    -- Use the canonical stabilizer quotient parametrization and pull the witness back across the
    -- quotient equivalence coming from `hS`.
    rw [← range_ofQuotientStabilizer_eq_orbit p] at hy
    rcases hy with ⟨q, rfl⟩
    refine ⟨(Subgroup.quotientEquivOfEq hS).symm q, ?_⟩
    simp

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: after transporting a subgroup quotient to the stabilizer
quotient, evaluating the descended orbit map on quotient classes recovers the original orbit map
on representatives. -/
theorem descendedOrbitMap_comp_quotientEquivOfEq_mk
    (p : M) {S : Subgroup G} (hS : S = MulAction.stabilizer G p) :
    MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS ∘ QuotientGroup.mk =
      orbit_map G p := by
  -- Collapse the quotient transport on representatives so the quotient route rewrites back to
  -- the original orbit map without further `quotientEquivOfEq` normalization.
  funext g
  rw [Function.comp_apply, Function.comp_apply, Subgroup.quotientEquivOfEq_mk,
    MulAction.ofQuotientStabilizer_mk, orbit_map]

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: if a subgroup quotient is identified with the stabilizer
quotient by `hS`, the resulting quotient type is canonically equivalent to the orbit subtype. -/
noncomputable def orbitEquivQuotientOfStabilizerEq
    (p : M) {S : Subgroup G} (hS : S = MulAction.stabilizer G p) :
    G ⧸ S ≃ MulAction.orbit G p :=
  (Subgroup.quotientEquivOfEq hS).trans (MulAction.orbitEquivQuotientStabilizer G p).symm

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: the ambient-valued map underlying
`orbitEquivQuotientOfStabilizerEq` is exactly the descended orbit map. -/
theorem orbitEquivQuotientOfStabilizerEq_apply
    (p : M) {S : Subgroup G} (hS : S = MulAction.stabilizer G p) (q : G ⧸ S) :
    ((orbitEquivQuotientOfStabilizerEq p hS q : MulAction.orbit G p) : M) =
      (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS) q := by
  refine Quotient.inductionOn q ?_
  intro g
  -- Collapse both quotient parametrizations to the common representative-level action `g • p`.
  change
    (((MulAction.orbitEquivQuotientStabilizer G p).symm
        (Subgroup.quotientEquivOfEq hS (QuotientGroup.mk g)) : MulAction.orbit G p) : M) =
      (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS) (QuotientGroup.mk g)
  rw [Function.comp_apply, Subgroup.quotientEquivOfEq_mk, MulAction.ofQuotientStabilizer_mk]
  -- The canonical orbit-stabilizer equivalence sends the transported quotient class to `g • p`.
  simpa using
    (MulAction.orbitEquivQuotientStabilizer_symm_apply p (QuotientGroup.mk g))

omit [IsManifold J ∞ M] in
/-- Helper: if a quotient by a subgroup whose carrier is the stabilizer
immerses into `M` through the transported descended orbit map, its image is the orbit of `p`. -/
theorem orbitImmersedSubmanifold_fromCarrierEqQuotient
    {S : Subgroup G} {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    (p : M) (hS : S = MulAction.stabilizer G p)
    [ChartedSpace EQ (G ⧸ S)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞) (G ⧸ S)]
    (hImm : IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS)) :
    ∃ T : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uG} J M,
      T.carrier = MulAction.orbit G p := by
  -- Package the transported quotient map as an immersed submanifold using injectivity of both
  -- the stabilizer quotient map and the carrier-transport equivalence.
  refine ⟨hImm.toImmersedSubmanifold ?_, ?_⟩
  · intro q₁ q₂ hq
    apply (Subgroup.quotientEquivOfEq hS).injective
    exact MulAction.injective_ofQuotientStabilizer G p hq
  -- The carrier is still the orbit because the transported quotient map has the same range.
  exact range_ofQuotientStabilizer_comp_quotientEquivOfEq_eq_orbit p hS

omit [LieGroup I ∞ G] [IsManifold J ∞ M] [ContMDiffSMul I J ∞ G M] in
/-- Helper: once the stabilizer is realized as a Lie subgroup owner `S`,
the remaining quotient-manifold and immersion package on `G ⧸ S.carrier` is enough to finish the
orbit statement. -/
theorem orbitImmersedSubmanifold_fromLieSubgroupQuotient
    (p : M) (S : LieSubgroup I) (hS : S.carrier = MulAction.stabilizer G p)
    {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    [ChartedSpace EQ (G ⧸ S.carrier)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞) (G ⧸ S.carrier)]
    (hImm : IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS)) :
    ∃ T : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uG} J M,
      T.carrier = MulAction.orbit G p := by
  -- Once the stabilizer carrier is owned by `S`, the earlier carrier-equality quotient assembly
  -- closes the orbit statement without any additional transport work in the final theorem.
  exact orbitImmersedSubmanifold_fromCarrierEqQuotient p hS hImm

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: the descended orbit map is `G`-equivariant with respect to
the quotient action on `G ⧸ MulAction.stabilizer G p`. -/
theorem ofQuotientStabilizer_map_smul (p : M) (g : G)
    (q : G ⧸ MulAction.stabilizer G p) :
    MulAction.ofQuotientStabilizer G p (g • q) = g • MulAction.ofQuotientStabilizer G p q := by
  -- Evaluate the quotient map on a representative so the equivariance reduces to associativity of
  -- the action.
  refine Quotient.inductionOn q ?_
  intro x
  simp [MulAction.ofQuotientStabilizer_mk, smul_smul]

/-- Helper: package the descended orbit map as the canonical equivariant
map from `G ⧸ MulAction.stabilizer G p` to `M`. -/
def ofQuotientStabilizerMulActionHom (p : M) :
    (G ⧸ MulAction.stabilizer G p) →[G] M where
  toFun := MulAction.ofQuotientStabilizer G p
  map_smul' := ofQuotientStabilizer_map_smul p

include I J in
/-- Helper: the orbit map has constant rank by the equivariant rank
transport argument already used earlier in the chapter. -/
theorem orbitMapHasConstantRank [FiniteDimensional 𝕜 E'] (p : M) :
    ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r := by
  -- Repackage the orbit map as an equivariant map so Theorem 7.25 applies directly.
  let F : G →[G] M := orbitMapMulActionHom p
  have hF : ContMDiff I J ∞ F := orbitMap_contMDiff p
  have hConstRank : ∃ r : ℕ, Manifold.HasConstantRank I J F r := by
    exact
      @MulActionHom.hasConstantRank 𝕜 _ E _ _ H _ G _ _ _ I _
        E _ _ H _ G _ _ I _ _ _
        E' _ _ _ H' _ M _ _ J _ _ _ _
        F hF
  simpa [orbitMapMulActionHom] using! hConstRank

/-- Helper: the constant-rank level-set theorem equips the stabilizer of `p` with a genuine
`C^∞` embedded structure inherited from the fiber `orbit_map G p ⁻¹' {p}`.

Original invalid type (legacy Theorem 5.12): `IsEmbeddedSubmanifold` with analytic (`⊤`/`ω`)
inclusion.  Smooth input cannot produce that owner; the corrected conclusion is
`IsSmoothEmbedding` at regularity `∞`.  Rank bounds are derived at the identity, which
always lies on the fiber. -/
theorem stabilizerEmbeddedData
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓡 m) ∞ G] [LieGroup (𝓡 m) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [ContMDiffSMul (𝓡 m) (𝓡 n) ∞ G M]
    [T2Space G] [SecondCountableTopology G]
    (p : M) (hRank : HasConstantRank (𝓡 m) (𝓡 n) (orbit_map G p) r) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin (m - r)))
        ((MulAction.stabilizer G p : Set G)),
      ∃ _ : IsManifold (𝓡 (m - r)) ∞ ((MulAction.stabilizer G p : Set G)),
        let S := (MulAction.stabilizer G p : Set G)
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin (m - r))) S := cs
        IsSmoothEmbedding (𝓡 (m - r)) (𝓡 m) ∞ (Subtype.val : S → G) :=
  by
    have h := StabilizerSmoothFiber.stabilizer_has_smooth_embedded_structure
      (I := 𝓡 m) (J := 𝓡 n) p hRank
    dsimp only at h
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m from finrank_euclideanSpace_fin] at h
    exact h

include I J in
/-- Helper: the stabilizer is a closed subset because it is the fiber
over `p` of the continuous orbit map. -/
theorem stabilizerClosed
    [T2Space M] (p : M) :
    IsClosed ((MulAction.stabilizer G p : Set G)) := by
  -- Rewrite the stabilizer as the singleton fiber of the continuous orbit map.
  have hSmooth : ContMDiff I J ∞ (orbit_map G p) := by
    simpa [orbit_map] using!
      ((contMDiff_id : ContMDiff I I ∞ fun g : G ↦ g).smul
        (contMDiff_const : ContMDiff I J ∞ fun _ : G ↦ p))
  rw [← preimage_singleton_orbit_map_eq_stabilizer]
  exact isClosed_singleton.preimage hSmooth.continuous

/-- Helper: in a Hausdorff target manifold, the stabilizer of `p` carries
the canonical closed-subgroup owner coming from its closedness in `G`. -/
def stabilizerClosedSubgroup
    [T2Space M] (p : M) : ClosedSubgroup G :=
  { toSubgroup := MulAction.stabilizer G p
    isClosed' := by
      have hSmooth : ContMDiff I J ∞ (orbit_map G p) := by
        simpa [orbit_map] using!
          ((contMDiff_id : ContMDiff I I ∞ fun g : G ↦ g).smul
            (contMDiff_const : ContMDiff I J ∞ fun _ : G ↦ p))
      simpa [preimage_singleton_orbit_map_eq_stabilizer] using!
        (isClosed_singleton.preimage hSmooth.continuous :
          IsClosed ((orbit_map G p) ⁻¹' ({p} : Set M))) }

/-- Helper: once the stabilizer is known to be closed, the quotient
`G ⧸ MulAction.stabilizer G p` is Hausdorff in the canonical quotient topology. -/
theorem stabilizerQuotient_t2Space
    {J' : ModelWithCorners 𝕜 E' H'} [IsManifold J' ∞ M] [ContMDiffSMul I J' ∞ G M]
    [T2Space G] [T2Space M] (p : M) :
    T2Space (G ⧸ MulAction.stabilizer G p) := by
  -- The quotient by a closed subgroup of a topological group is Hausdorff.
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : IsClosed ((MulAction.stabilizer G p : Set G)) :=
    by
      have hSmooth : ContMDiff I J' ∞ (orbit_map G p) := by
        simpa [orbit_map] using!
          ((contMDiff_id : ContMDiff I I ∞ fun g : G ↦ g).smul
            (contMDiff_const : ContMDiff I J' ∞ fun _ : G ↦ p))
      simpa [preimage_singleton_orbit_map_eq_stabilizer] using
        (isClosed_singleton.preimage hSmooth.continuous :
          IsClosed ((orbit_map G p) ⁻¹' ({p} : Set M)))
  infer_instance

section

include I J

/-- Helper for Remark 7.50-extra-5: the stabilizer of `p` has a closed finite-dimensional
`C^∞` embedded package.  The original statement asked for `IsEmbeddedSubmanifold` (analytic
inclusion); the corrected owner is `IsSmoothEmbedding` at `∞` together with closedness of
the orbit-map fiber. -/
theorem stabilizerEmbeddedClosedData
    {m n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓡 m) ∞ G] [LieGroup (𝓡 m) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [ContMDiffSMul (𝓡 m) (𝓡 n) ∞ G M]
    [T2Space G] [SecondCountableTopology G] [T2Space M] (p : M) :
    ∃ k : ℕ,
      ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) ((MulAction.stabilizer G p : Set G)),
        ∃ _ : IsManifold (𝓡 k) ∞ ((MulAction.stabilizer G p : Set G)),
          let S := (MulAction.stabilizer G p : Set G)
          IsSmoothEmbedding (𝓡 k) (𝓡 m) ∞ (Subtype.val : S → G) ∧
            IsClosed ((MulAction.stabilizer G p : Set G)) := by
  obtain ⟨r, hRank, _, _⟩ :=
    StabilizerSmoothFiber.orbitMap_rank_with_bounds (I := 𝓡 m) (J := 𝓡 n) (G := G) (M := M) p
  let k : ℕ := m - r
  rcases stabilizerEmbeddedData (m := m) (n := n) p hRank with ⟨cs, hs, hEmb⟩
  refine ⟨k, cs, hs, hEmb, ?_⟩
  have hSmooth : ContMDiff (𝓡 m) (𝓡 n) ∞ (orbit_map G p) := orbitMap_contMDiff p
  simpa [preimage_singleton_orbit_map_eq_stabilizer] using
    (isClosed_singleton.preimage hSmooth.continuous :
      IsClosed ((orbit_map G p) ⁻¹' ({p} : Set M)))

end

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: quotient classes for `MulAction.stabilizer G p` agree exactly
when the corresponding orbit-map values agree. -/
theorem quotientMk_eq_iff_orbitMap_eq (p : M) (g₁ g₂ : G) :
    (QuotientGroup.mk g₁ : G ⧸ MulAction.stabilizer G p) = QuotientGroup.mk g₂ ↔
      orbit_map G p g₁ = orbit_map G p g₂ := by
  constructor
  · intro hq
    have hmem : g₁⁻¹ * g₂ ∈ MulAction.stabilizer G p := QuotientGroup.eq.mp hq
    have hfix : (g₁⁻¹ * g₂) • p = p := by
      simpa [MulAction.mem_stabilizer_iff] using hmem
    -- Rewrite quotient equality into a stabilizer element fixing `p`, then reassociate the action.
    calc
      orbit_map G p g₁ = g₁ • p := rfl
      _ = g₁ • ((g₁⁻¹ * g₂) • p) := by rw [hfix]
      _ = (g₁ * (g₁⁻¹ * g₂)) • p := by simp [smul_smul]
      _ = orbit_map G p g₂ := by simp [orbit_map]
  · intro hOrbit
    apply QuotientGroup.eq.mpr
    -- Equality in the orbit rewrites back to the stabilizer relation defining the quotient.
    rw [MulAction.mem_stabilizer_iff]
    calc
      (g₁⁻¹ * g₂) • p = g₁⁻¹ • (g₂ • p) := by simp [smul_smul]
      _ = g₁⁻¹ • (g₁ • p) := by
          simpa [orbit_map] using congrArg (fun x : M ↦ g₁⁻¹ • x) hOrbit.symm
      _ = p := by simp

/-- Helper: in Euclidean manifold models, the constant-rank theorem gives
the orbit map a centered local normal form at `1 : G`. -/
theorem orbitMapLocalNormalFormAtOne
    {m n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) :
    ∃ r : ℕ,
      ∃ _ : LocalNormalFormAPI.LocalCoordinateNormalFormAt
        (orbit_map G p) (1 : G)
        (LocalNormalFormAPI.rank_normal_form m n r),
        True := by
  -- Combine constant rank for the equivariant orbit map with the chapter's rank theorem.
  let IG : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)) := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
  let JM : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let _ : LieGroup IG ∞ G := by
    simpa [IG] using (inferInstance : LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G)
  let _ : IsManifold JM ∞ M := by
    simpa [JM] using
      (inferInstance : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M)
  let _ : ContMDiffSMul IG JM ∞ G M := by
    simpa [IG, JM] using
      (inferInstance :
        ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M)
  have hConstRank : ∃ r : ℕ, Manifold.HasConstantRank IG JM (orbit_map G p) r :=
    orbitMapHasConstantRank p
  rcases hConstRank with ⟨r, hRank⟩
  rcases constant_rank_local_coordinate_normal_form
      (orbitMap_contMDiff p) hRank (1 : G) with ⟨hNF, _⟩
  exact ⟨r, hNF, trivial⟩

/-- Helper for Remark 7.50-extra-5: the Euclidean first-coordinate projection is a smooth
submersion. -/
def orbitHeadProjection {m r : ℕ} (hr : r ≤ m) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin r) :=
  fun x ↦ WithLp.toLp 2 fun i ↦ x (Fin.castLE hr i)

/-- Helper for Remark 7.50-extra-5: the first-coordinate projection on Euclidean space is
continuous. -/
theorem continuous_orbitHeadProjection
    {m r : ℕ} (hr : r ≤ m) :
    Continuous (orbitHeadProjection hr) := by
  -- The first-coordinate projection is coordinatewise continuous on Euclidean space.
  have hcoord :
      Continuous fun x : EuclideanSpace ℝ (Fin m) ↦
        fun i : Fin r ↦ x (Fin.castLE hr i) :=
    continuous_pi fun i ↦
      PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) (Fin.castLE hr i)
  simpa [orbitHeadProjection] using!
    (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp hcoord

/-- Helper for Remark 7.50-extra-5: the standard rank-`r` inclusion is a right inverse to the
first-coordinate projection. -/
theorem orbitHeadProjection_rankNormalForm
    {m r : ℕ} (hr : r ≤ m) (x : EuclideanSpace ℝ (Fin r)) :
    orbitHeadProjection hr (LocalNormalFormAPI.rank_normal_form r m r x) = x := by
  -- On the first `r` target coordinates, the rank normal form is literally the identity.
  ext i
  change LocalNormalFormAPI.rank_normal_form r m r x (Fin.castLE hr i) = x i
  exact LocalNormalFormAPI.rank_normal_form_apply_of_lt i.2 i.2 x

/-- Helper for Remark 7.50-extra-5: the Euclidean first-coordinate projection is a smooth
submersion. -/
theorem orbitHeadProjection_isSmoothSubmersion
    {m r : ℕ} (hr : r ≤ m) :
    IsSmoothSubmersion (𝓡 m) (𝓡 r) (orbitHeadProjection hr) := by
  -- Package the coordinate projection as a continuous linear map so smoothness and derivative
  -- surjectivity are both reduced to linear algebra on Euclidean space.
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    { toFun := orbitHeadProjection hr
      map_add' := by
        intro x y
        ext i
        simp [orbitHeadProjection]
      map_smul' := by
        intro c x
        ext i
        simp [orbitHeadProjection]
      cont := continuous_orbitHeadProjection hr }
  refine ⟨?_, ?_⟩
  · -- Linear maps between Euclidean model spaces are smooth.
    simpa [L] using
      (L.contMDiff : ContMDiff (𝓡 m) (𝓡 r) ∞ L)
  · intro x
    rw [mfderiv_eq_fderiv]
    have hderiv :
        fderiv ℝ (orbitHeadProjection hr) x = L := by
      simpa [L, orbitHeadProjection] using (L.hasFDerivAt).fderiv
    rw [hderiv]
    -- Surjectivity comes from the standard zero-tail inclusion right inverse.
    intro y
    refine ⟨LocalNormalFormAPI.rank_normal_form r m r y, ?_⟩
    exact orbitHeadProjection_rankNormalForm hr y

/-- Helper for Remark 7.50-extra-5: the Euclidean first-coordinate projection is an open map. -/
theorem orbitHeadProjection_isOpenMap
    {m r : ℕ} (hr : r ≤ m) :
    IsOpenMap (orbitHeadProjection hr) := by
  -- Package the coordinate projection as a continuous linear map and apply the Banach open
  -- mapping theorem using the explicit zero-tail right inverse.
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    { toFun := orbitHeadProjection hr
      map_add' := by
        intro x y
        ext i
        simp [orbitHeadProjection]
      map_smul' := by
        intro c x
        ext i
        simp [orbitHeadProjection]
      cont := continuous_orbitHeadProjection hr }
  have hsurj : Function.Surjective L := by
    intro y
    refine ⟨LocalNormalFormAPI.rank_normal_form r m r y, ?_⟩
    exact orbitHeadProjection_rankNormalForm hr y
  -- The projection is the underlying map of this surjective continuous linear map.
  simpa [L] using L.isOpenMap hsurj

/-- Helper for Remark 7.50-extra-5: applying the target head projection to the rank normal form
recovers the source head projection. -/
theorem headProjection_rankNormalForm
    {m n r : ℕ} (hrm : r ≤ m) (hrn : r ≤ n)
    (x : EuclideanSpace ℝ (Fin m)) :
    orbitHeadProjection hrn (LocalNormalFormAPI.rank_normal_form m n r x) =
      orbitHeadProjection hrm x := by
  -- On the first `r` target coordinates, the rank normal form literally returns the matching
  -- source coordinate.
  ext i
  change LocalNormalFormAPI.rank_normal_form m n r x (Fin.castLE hrn i) = x (Fin.castLE hrm i)
  exact LocalNormalFormAPI.rank_normal_form_apply_of_lt i.2 (lt_of_lt_of_le i.2 hrm) x

/-- Helper for Remark 7.50-extra-5: the rank normal form depends only on the first `r` source
coordinates. -/
theorem rankNormalForm_eq_iff_headProjection_eq
    {m n r : ℕ} (hrm : r ≤ m) (hrn : r ≤ n)
    {x y : EuclideanSpace ℝ (Fin m)} :
    LocalNormalFormAPI.rank_normal_form m n r x =
      LocalNormalFormAPI.rank_normal_form m n r y ↔
      orbitHeadProjection hrm x = orbitHeadProjection hrm y := by
  constructor
  · intro hEq
    -- Compare the first `r` target coordinates of the two equal normal-form values.
    calc
      orbitHeadProjection hrm x =
          orbitHeadProjection hrn (LocalNormalFormAPI.rank_normal_form m n r x) := by
            symm
            exact headProjection_rankNormalForm hrm hrn x
      _ = orbitHeadProjection hrn (LocalNormalFormAPI.rank_normal_form m n r y) := by
            rw [hEq]
      _ = orbitHeadProjection hrm y := headProjection_rankNormalForm hrm hrn y
  · intro hHead
    -- Split target coordinates into the first `r` slots and the zero tail forced by the normal
    -- form.
    ext i
    rcases lt_or_ge i.1 r with hi | hi
    · have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin r) ↦ v ⟨i.1, hi⟩) hHead
      rw [LocalNormalFormAPI.rank_normal_form_apply_of_lt hi (lt_of_lt_of_le hi hrm) x,
        LocalNormalFormAPI.rank_normal_form_apply_of_lt hi (lt_of_lt_of_le hi hrm) y]
      simpa [orbitHeadProjection] using hcoord
    · have hnot : ¬ i.1 < r := Nat.not_lt_of_ge hi
      simpa [_root_.rank_normal_form, hnot]

/-- Helper: on a neighborhood where the orbit map is in local normal
form, quotient classes are detected by equality of the normal-form coordinates. -/
theorem quotientMk_eq_iff_rankNormalForm_eqOnOrbitNormalFormNeighborhood
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    {g₁ g₂ : G}
    (hg₁ : g₁ ∈ hNF.domChart.source)
    (hg₂ : g₂ ∈ hNF.domChart.source) :
    ((QuotientGroup.mk g₁ : G ⧸ MulAction.stabilizer G p) = QuotientGroup.mk g₂) ↔
      LocalNormalFormAPI.rank_normal_form m n r (hNF.domChart g₁) =
        LocalNormalFormAPI.rank_normal_form m n r (hNF.domChart g₂) := by
  have hOrbit1 : orbit_map G p g₁ ∈ hNF.codChart.source := hNF.mapsTo hg₁
  have hOrbit2 : orbit_map G p g₂ ∈ hNF.codChart.source := hNF.mapsTo hg₂
  have hChart1 :
      hNF.codChart (orbit_map G p g₁) =
        LocalNormalFormAPI.rank_normal_form m n r (hNF.domChart g₁) := by
    -- Evaluate the local normal-form equation on the image of `g₁` under the source chart.
    have hEq := hNF.eqOn (hNF.domChart.map_source hg₁)
    simpa [Function.comp, OpenPartialHomeomorph.left_inv hNF.domChart hg₁] using hEq
  have hChart2 :
      hNF.codChart (orbit_map G p g₂) =
        LocalNormalFormAPI.rank_normal_form m n r (hNF.domChart g₂) := by
    -- The same chart computation identifies the orbit-map value of `g₂`.
    have hEq := hNF.eqOn (hNF.domChart.map_source hg₂)
    simpa [Function.comp, OpenPartialHomeomorph.left_inv hNF.domChart hg₂] using hEq
  constructor
  · intro hq
    -- Quotient equality first gives equality in the orbit, then the normal-form chart rewrites it.
    have hOrbitEq : orbit_map G p g₁ = orbit_map G p g₂ :=
      (quotientMk_eq_iff_orbitMap_eq p g₁ g₂).mp hq
    rw [← hChart1, ← hChart2, hOrbitEq]
  · intro hRankEq
    -- Equality of the normal-form coordinates pulls back through the target chart to the orbit.
    have hOrbitChartEq :
        hNF.codChart (orbit_map G p g₁) = hNF.codChart (orbit_map G p g₂) := by
      rw [hChart1, hChart2, hRankEq]
    have hOrbitEq : orbit_map G p g₁ = orbit_map G p g₂ := by
      calc
        orbit_map G p g₁ =
            hNF.codChart.symm (hNF.codChart (orbit_map G p g₁)) := by
              symm
              exact OpenPartialHomeomorph.left_inv hNF.codChart hOrbit1
        _ = hNF.codChart.symm (hNF.codChart (orbit_map G p g₂)) := by rw [hOrbitChartEq]
        _ = orbit_map G p g₂ := OpenPartialHomeomorph.left_inv hNF.codChart hOrbit2
    exact (quotientMk_eq_iff_orbitMap_eq p g₁ g₂).mpr hOrbitEq

/-- Helper for Remark 7.50-extra-5: on a normal-form neighborhood for the orbit map, quotient
classes are already detected by equality of the first `r` source coordinates. -/
theorem quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n)
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    {g₁ g₂ : G}
    (hg₁ : g₁ ∈ hNF.domChart.source)
    (hg₂ : g₂ ∈ hNF.domChart.source) :
    ((QuotientGroup.mk g₁ : G ⧸ MulAction.stabilizer G p) = QuotientGroup.mk g₂) ↔
      orbitHeadProjection hrm (hNF.domChart g₁) =
        orbitHeadProjection hrm (hNF.domChart g₂) := by
  -- First convert quotient equality into equality of the local normal-form values, then normalize
  -- that equality to the first `r` source coordinates.
  rw [← rankNormalForm_eq_iff_headProjection_eq hrm hrn]
  exact
    quotientMk_eq_iff_rankNormalForm_eqOnOrbitNormalFormNeighborhood
      p hNF hg₁ hg₂

/-- Helper for Remark 7.50-extra-5: the quotient image of the source patch in the orbit-map
normal form is open in the stabilizer quotient. -/
theorem orbitQuotientPatchImage_open
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpen (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) := by
  letI : IsTopologicalGroup G :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
  -- The quotient projection is open, so it carries the open source patch to an open quotient
  -- patch.
  simpa using
    (QuotientGroup.isOpenMap_coe _ hNF.domChart.open_source)

/-- Helper for Remark 7.50-extra-5: restricting the quotient projection to the source patch
produces the open-quotient map onto the quotient patch used for descending coordinates. -/
theorem orbitQuotientPatchProjection_isOpenQuotientMap
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpenQuotientMap (fun g : hNF.domChart.source ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  letI : IsTopologicalGroup G :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
  let Uq : Set (G ⧸ MulAction.stabilizer G p) :=
    ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source
  have hUq_open : IsOpen Uq := orbitQuotientPatchImage_open p hNF
  refine ⟨?_, ?_, ?_⟩
  · intro q
    rcases q.2 with ⟨g, hg, hgq⟩
    -- Every quotient-patch point has a representative inside the chosen source patch.
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    simpa using hgq
  · -- The restricted quotient projection is continuous because the ambient quotient map is.
    exact
      (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk
          (fun g ↦ by
            exact ⟨(g : G), g.2, rfl⟩)
  · intro s hs
    -- Open subsets of the source patch stay open after first forgetting the subtype and then
    -- applying the ambient open quotient map.
    have hUqEmbedding :
        Topology.IsOpenEmbedding (Subtype.val : Uq → G ⧸ MulAction.stabilizer G p) :=
      hUq_open.isOpenEmbedding_subtypeVal
    rw [hUqEmbedding.isOpen_iff_image_isOpen]
    have hDomChartOpenSource : IsOpen hNF.domChart.source := hNF.domChart.open_source
    have hSourceEmbedding :
        Topology.IsOpenEmbedding (Subtype.val : hNF.domChart.source → G) :=
      hDomChartOpenSource.isOpenEmbedding_subtypeVal
    have hSourceOpenMap : IsOpenMap (Subtype.val : hNF.domChart.source → G) :=
      hSourceEmbedding.isOpenMap
    have hsAmbient : IsOpen ((Subtype.val : hNF.domChart.source → G) '' s) := by
      exact hSourceOpenMap s hs
    simpa [Uq, Set.image_image] using
      (QuotientGroup.isOpenMap_coe
        ((Subtype.val : hNF.domChart.source → G) '' s) hsAmbient)

/-- Helper for Remark 7.50-extra-5: the head projection carries the target patch of the source
chart to an open subset of `EuclideanSpace ℝ (Fin r)`. -/
theorem orbitHeadProjection_targetPatchImage_open
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpen (orbitHeadProjection hrm '' hNF.domChart.target) := by
  -- The target chart is open, and the Euclidean head projection is an open map.
  exact orbitHeadProjection_isOpenMap hrm _ hNF.domChart.open_target

/-- Helper for Remark 7.50-extra-5: restricting the Euclidean head projection to the target patch
produces the open-quotient map onto its image. -/
theorem orbitHeadProjection_targetPatch_isOpenQuotientMap
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpenQuotientMap (fun x : hNF.domChart.target ↦
      (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
        orbitHeadProjection hrm '' hNF.domChart.target)) := by
  let W : Set (EuclideanSpace ℝ (Fin r)) := orbitHeadProjection hrm '' hNF.domChart.target
  have hW_open : IsOpen W := orbitHeadProjection_targetPatchImage_open hrm p hNF
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rcases y.2 with ⟨x, hx, hxy⟩
    -- By construction, every point in the image patch comes from a target-patch point.
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simpa using hxy
  · -- Restrict the continuous Euclidean projection to the open target patch.
    exact ((continuous_orbitHeadProjection hrm).comp continuous_subtype_val).subtype_mk
      (fun x ↦ by
        exact ⟨(x : EuclideanSpace ℝ (Fin m)), x.2, rfl⟩)
  · intro s hs
    -- Open subsets of the target patch stay open after forgetting the subtype and applying the
    -- ambient open projection.
    have hWEmbedding :
        Topology.IsOpenEmbedding (Subtype.val : W → EuclideanSpace ℝ (Fin r)) :=
      hW_open.isOpenEmbedding_subtypeVal
    rw [hWEmbedding.isOpen_iff_image_isOpen]
    have hDomChartOpenTarget : IsOpen hNF.domChart.target := hNF.domChart.open_target
    have hTargetEmbedding :
        Topology.IsOpenEmbedding
          (Subtype.val : hNF.domChart.target → EuclideanSpace ℝ (Fin m)) :=
      hDomChartOpenTarget.isOpenEmbedding_subtypeVal
    have hTargetOpenMap :
        IsOpenMap (Subtype.val : hNF.domChart.target → EuclideanSpace ℝ (Fin m)) :=
      hTargetEmbedding.isOpenMap
    have hsAmbient :
        IsOpen ((Subtype.val : hNF.domChart.target → EuclideanSpace ℝ (Fin m)) '' s) := by
      exact hTargetOpenMap s hs
    simpa [W, Set.image_image] using orbitHeadProjection_isOpenMap hrm _ hsAmbient

/-- Helper for Remark 7.50-extra-5: the quotient patch at the identity coset carries the forward
local coordinate obtained by descending the head projection through the quotient patch map. -/
noncomputable def orbitQuotientPatchForward
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    C((((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source),
      orbitHeadProjection hrm '' hNF.domChart.target) := by
  let proj :
      C(hNF.domChart.source,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨(fun g ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source))), ?_⟩
    simpa using (orbitQuotientPatchProjection_isOpenQuotientMap p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitQuotientPatchProjection_isOpenQuotientMap p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.source, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨?_, ?_⟩
    · intro g
      refine ⟨orbitHeadProjection hrm (hNF.domChart g), ?_⟩
      exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩
    · -- Restrict the chart to its source patch, then compose with the Euclidean head projection.
      have hChartOn := hNF.domChart.continuousOn_toFun
      have hChart : Continuous fun g : hNF.domChart.source ↦ hNF.domChart g :=
        hChartOn.restrict
      have hHead :
          Continuous fun g : hNF.domChart.source ↦
            orbitHeadProjection hrm (hNF.domChart g) :=
        (continuous_orbitHeadProjection hrm).comp hChart
      exact
        Continuous.subtype_mk hHead
          (fun g ↦ by
            show orbitHeadProjection hrm (hNF.domChart g) ∈
                orbitHeadProjection hrm '' hNF.domChart.target
            exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩)
  -- Descend the representative-level coordinate through the open quotient map on the source patch.
  exact
    hproj.lift raw
      (fun a b hab ↦ by
        apply Subtype.ext
        -- Fiberwise quotient equality is exactly the normal-form head-projection criterion.
        exact
          (quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
            hrm hrn p hNF a.2 b.2).mp
            (by simpa [proj] using congrArg Subtype.val hab))

/-- Helper for Remark 7.50-extra-5: the identity-coset quotient patch also carries the inverse
local coordinate obtained by descending the inverse source chart through the head-projection patch
map. -/
noncomputable def orbitQuotientPatchInverse
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    C((orbitHeadProjection hrm '' hNF.domChart.target),
      (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  let proj :
      C(hNF.domChart.target, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨(fun x ↦
      (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
        orbitHeadProjection hrm '' hNF.domChart.target)), ?_⟩
    simpa using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.target,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨?_, ?_⟩
    · intro x
      refine ⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p), ?_⟩
      exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩
    · -- Restrict the inverse chart to the target patch, then compose with the quotient projection.
      have hSymmOn := hNF.domChart.continuousOn_invFun
      have hSymm : Continuous fun x : hNF.domChart.target ↦ hNF.domChart.symm x :=
        hSymmOn.restrict
      have hMk :
          Continuous fun x : hNF.domChart.target ↦
            (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) :=
        QuotientGroup.continuous_mk.comp hSymm
      exact
        Continuous.subtype_mk hMk
          (fun x ↦ by
            show (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) ∈
                ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source
            exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩)
  -- Descend the representative-level inverse coordinate through the head-projection quotient map.
  exact
    hproj.lift raw
      (fun a b hab ↦ by
        apply Subtype.ext
        -- Equal head projections on the target patch lift back to the same quotient class.
        refine
          (quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
            hrm hrn p hNF
            (hNF.domChart.map_target a.2) (hNF.domChart.map_target b.2)).mpr ?_
        simpa [OpenPartialHomeomorph.right_inv hNF.domChart a.2,
          OpenPartialHomeomorph.right_inv hNF.domChart b.2, proj] using
          (congrArg Subtype.val hab))

/-- Helper for Remark 7.50-extra-5: on the canonical quotient-patch representative, the descended
forward coordinate map agrees with the source-chart head projection used to define it. -/
theorem orbitQuotientPatchForward_comp_projection
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    ((orbitQuotientPatchForward hrm hrn p hNF :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) →
          orbitHeadProjection hrm '' hNF.domChart.target) ∘
      (fun g : hNF.domChart.source ↦
        (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)))) =
      fun g : hNF.domChart.source ↦
        (⟨orbitHeadProjection hrm (hNF.domChart g), ⟨hNF.domChart g, hNF.domChart.map_source g.2,
          rfl⟩⟩ : orbitHeadProjection hrm '' hNF.domChart.target) := by
  let proj :
      C(hNF.domChart.source,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨(fun g ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source))), ?_⟩
    simpa using (orbitQuotientPatchProjection_isOpenQuotientMap p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitQuotientPatchProjection_isOpenQuotientMap p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.source, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨?_, ?_⟩
    · intro g
      exact ⟨orbitHeadProjection hrm (hNF.domChart g), ⟨hNF.domChart g, hNF.domChart.map_source g.2,
        rfl⟩⟩
    · have hChartOn := hNF.domChart.continuousOn_toFun
      have hChart : Continuous fun g : hNF.domChart.source ↦ hNF.domChart g :=
        hChartOn.restrict
      have hHead :
          Continuous fun g : hNF.domChart.source ↦ orbitHeadProjection hrm (hNF.domChart g) :=
        (continuous_orbitHeadProjection hrm).comp hChart
      exact
        Continuous.subtype_mk hHead
          (fun g ↦ by
            exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩)
  have hfactor : Function.FactorsThrough raw proj := by
    intro a b hab
    apply Subtype.ext
    exact
      (quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
        hrm hrn p hNF a.2 b.2).mp
        (by simpa [proj] using congrArg Subtype.val hab)
  -- Compare the descended continuous map with its representative-level model before evaluation.
  funext g
  have hcomp :
      (hproj.lift raw hfactor).comp proj = raw :=
    Topology.IsQuotientMap.lift_comp hproj raw hfactor
  change ((hproj.lift raw hfactor).comp proj) g = raw g
  exact congrArg (fun f ↦ f g) hcomp

/-- Helper for Remark 7.50-extra-5: on the canonical head-projection representative, the descended
inverse coordinate map agrees with the inverse source chart used to define it. -/
theorem orbitQuotientPatchInverse_comp_projection
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    ((orbitQuotientPatchInverse hrm hrn p hNF :
        orbitHeadProjection hrm '' hNF.domChart.target →
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) ∘
      (fun x : hNF.domChart.target ↦
        (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
          orbitHeadProjection hrm '' hNF.domChart.target))) =
      fun x : hNF.domChart.target ↦
        (⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p),
          ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩⟩ :
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  let proj :
      C(hNF.domChart.target, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨(fun x ↦
      (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
        orbitHeadProjection hrm '' hNF.domChart.target)), ?_⟩
    simpa using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.target,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨?_, ?_⟩
    · intro x
      exact ⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p),
        ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩⟩
    · have hSymmOn := hNF.domChart.continuousOn_invFun
      have hSymm : Continuous fun x : hNF.domChart.target ↦ hNF.domChart.symm x :=
        hSymmOn.restrict
      have hMk :
          Continuous fun x : hNF.domChart.target ↦
            (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) :=
        QuotientGroup.continuous_mk.comp hSymm
      exact
        Continuous.subtype_mk hMk
          (fun x ↦ by
            exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩)
  have hfactor : Function.FactorsThrough raw proj := by
    intro a b hab
    apply Subtype.ext
    refine
      (quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
        hrm hrn p hNF
        (hNF.domChart.map_target a.2) (hNF.domChart.map_target b.2)).mpr ?_
    simpa [OpenPartialHomeomorph.right_inv hNF.domChart a.2,
      OpenPartialHomeomorph.right_inv hNF.domChart b.2, proj] using
      (congrArg Subtype.val hab)
  -- Compare the descended inverse with the representative-level inverse before evaluation.
  funext x
  have hcomp :
      (hproj.lift raw hfactor).comp proj = raw :=
    Topology.IsQuotientMap.lift_comp hproj raw hfactor
  change ((hproj.lift raw hfactor).comp proj) x = raw x
  exact congrArg (fun f ↦ f x) hcomp

/-- Helper for Remark 7.50-extra-5: after projecting to the first `r` source coordinates, the
rank normal form depends only on those coordinates. -/
theorem rankNormalForm_factor_through_headProjection
    {m n r : ℕ} (hrm : r ≤ m)
    (x : EuclideanSpace ℝ (Fin m)) :
    LocalNormalFormAPI.rank_normal_form m n r x =
      LocalNormalFormAPI.rank_normal_form r n r (orbitHeadProjection hrm x) := by
  -- Compare target coordinates directly: both normal forms have the same leading `r` coordinates
  -- and the same zero tail.
  ext i
  rcases lt_or_ge i.1 r with hi | hi
  · rw [LocalNormalFormAPI.rank_normal_form_apply_of_lt hi (lt_of_lt_of_le hi hrm) x]
    rw [LocalNormalFormAPI.rank_normal_form_apply_of_lt hi hi (orbitHeadProjection hrm x)]
    simp [orbitHeadProjection]
  · have hnot : ¬ i.1 < r := Nat.not_lt_of_ge hi
    simp [_root_.rank_normal_form, hnot]

/-- Helper for Remark 7.50-extra-5: the descended forward and inverse patch coordinates at the
identity coset package into a genuine homeomorphism between the quotient patch owner and the open
head-projection image patch. -/
noncomputable def orbitQuotientPatchAtOneHomeomorph
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) ≃ₜ
      orbitHeadProjection hrm '' hNF.domChart.target where
  toEquiv :=
    { toFun := orbitQuotientPatchForward hrm hrn p hNF
      invFun := orbitQuotientPatchInverse hrm hrn p hNF
      left_inv := by
        rintro ⟨q, hq⟩
        rcases hq with ⟨g, hg, rfl⟩
        let gU : hNF.domChart.source := ⟨g, hg⟩
        let qU :
            (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
          ⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨g, hg, rfl⟩⟩
        let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
          ⟨orbitHeadProjection hrm (hNF.domChart gU), ⟨hNF.domChart gU, hNF.domChart.map_source hg, rfl⟩⟩
        apply Subtype.ext
        -- Compare both descended patch maps with their representative-level formulas before the
        -- chart inverse collapses back to the original source-patch point.
        have hForward :=
          congrArg
            (fun f : hNF.domChart.source →
                orbitHeadProjection hrm '' hNF.domChart.target => f gU)
            (orbitQuotientPatchForward_comp_projection
              hrm hrn p hNF)
        have hInverse :=
          congrArg
            (fun f : hNF.domChart.target →
                (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) =>
              f ⟨hNF.domChart gU, hNF.domChart.map_source hg⟩)
            (orbitQuotientPatchInverse_comp_projection
              hrm hrn p hNF)
        have hForwardEval :
            orbitQuotientPatchForward hrm hrn p hNF qU = xW := by
          simpa [gU, qU, xW] using hForward
        have hInverseEval :
            orbitQuotientPatchInverse hrm hrn p hNF xW = qU := by
          simpa [gU, qU, xW, OpenPartialHomeomorph.left_inv hNF.domChart hg] using hInverse
        rw [hForwardEval, hInverseEval]
      right_inv := by
        rintro ⟨x, hx⟩
        rcases hx with ⟨y, hy, rfl⟩
        let yV : hNF.domChart.target := ⟨y, hy⟩
        let gU : hNF.domChart.source := ⟨hNF.domChart.symm yV, hNF.domChart.map_target hy⟩
        let qU :
            (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
          ⟨(QuotientGroup.mk (hNF.domChart.symm yV) : G ⧸ MulAction.stabilizer G p),
            ⟨hNF.domChart.symm yV, hNF.domChart.map_target hy, rfl⟩⟩
        let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
          ⟨orbitHeadProjection hrm y, ⟨y, hy, rfl⟩⟩
        apply Subtype.ext
        -- Route correction: prove the inverse law on the target owner through the canonical
        -- target-patch representative, not by reopening quotient representatives.
        have hInverse :=
          congrArg
            (fun f : hNF.domChart.target →
                (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) =>
              f yV)
            (orbitQuotientPatchInverse_comp_projection
              hrm hrn p hNF)
        have hForward :=
          congrArg
            (fun f : hNF.domChart.source →
                orbitHeadProjection hrm '' hNF.domChart.target =>
              f gU)
            (orbitQuotientPatchForward_comp_projection
              hrm hrn p hNF)
        have hInverseEval :
            orbitQuotientPatchInverse hrm hrn p hNF xW = qU := by
          simpa [yV, gU, qU, xW] using hInverse
        have hForwardEval :
            orbitQuotientPatchForward hrm hrn p hNF qU = xW := by
          simpa [yV, gU, qU, xW, OpenPartialHomeomorph.right_inv hNF.domChart hy] using hForward
        rw [hInverseEval, hForwardEval] }
  continuous_toFun :=
    (orbitQuotientPatchForward hrm hrn p hNF).continuous
  continuous_invFun :=
    (orbitQuotientPatchInverse hrm hrn p hNF).continuous


/-- Helper for Remark 7.50-extra-5: the left action of `G` on the stabilizer quotient is a
homeomorphism with inverse given by left multiplication by `g⁻¹`. -/
noncomputable def quotientLeftTranslationHomeomorph
    [LieGroup I ∞ G] (p : M) (g : G) :
    (G ⧸ MulAction.stabilizer G p) ≃ₜ (G ⧸ MulAction.stabilizer G p) where
  toEquiv :=
    { toFun := fun q ↦ g • q
      invFun := fun q ↦ g⁻¹ • q
      left_inv := by
        intro q
        -- Cancel the two left actions in the quotient action.
        simp [smul_smul]
      right_inv := by
        intro q
        -- The inverse action is again left multiplication, now by `g⁻¹`.
        simp [smul_smul] }
  continuous_toFun := by
    -- The quotient inherits the continuous left action from the topological group structure on `G`.
    letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    simpa using (continuous_const_smul g :
      Continuous fun q : G ⧸ MulAction.stabilizer G p ↦ g • q)
  continuous_invFun := by
    -- Apply the same continuity statement to the inverse group element.
    letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    simpa using (continuous_const_smul g⁻¹ :
      Continuous fun q : G ⧸ MulAction.stabilizer G p ↦ g⁻¹ • q)

/-- Helper for Remark 7.50-extra-5: an ambient Euclidean chart transports its target-side
self-modeled atlas back to the chart-source subtype. -/
noncomputable abbrev transportedSelfModeledPatchChartedSpace
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {N : Type*} [TopologicalSpace N] [ChartedSpace ES N]
    {S : Type*} [TopologicalSpace S] (e : N ≃ₜ S) :
    ChartedSpace ES S := by
  let _ : ChartedSpace N S :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  -- Transport the self-modeled source charts explicitly through the singleton-chart homeomorphism.
  exact ChartedSpace.comp ES N S

/-- Helper for Remark 7.50-extra-5: transporting a self-modeled atlas across a homeomorphism
preserves the smooth manifold structure. -/
lemma transportedSelfModeledPatchIsManifold
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {n : ℕ∞ω}
    {N : Type*} [TopologicalSpace N] [ChartedSpace ES N]
    [IsManifold (modelWithCornersSelf 𝕜 ES) n N]
    {S : Type*} [TopologicalSpace S] (e : N ≃ₜ S) :
    let _ : ChartedSpace ES S := by
      let _ : ChartedSpace N S := (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
        ext x
        simp)
      exact ChartedSpace.comp ES N S
    IsManifold (modelWithCornersSelf 𝕜 ES) n S := by
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace ES S := by
    let _ : ChartedSpace N S := eS.singletonChartedSpace (by
      ext x
      simp [eS])
    exact ChartedSpace.comp ES N S
  have hGroupoid :
      HasGroupoid S (contDiffGroupoid n (modelWithCornersSelf 𝕜 ES)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext x
        simp [eS]) f hf
    have hf'Eq : f' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext x
        simp [eS]) f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- After normalizing the singleton-chart transport, compatibility reduces to the source atlas.
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
          contDiffGroupoid n (modelWithCornersSelf 𝕜 ES) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- The explicit transported atlas therefore defines the desired smooth manifold structure.
  exact IsManifold.mk' (modelWithCornersSelf 𝕜 ES) n S

/-- Helper for Remark 7.50-extra-5: an ambient Euclidean chart transports its target-side
self-modeled atlas back to the chart-source subtype. -/
noncomputable abbrev chartSourceEuclideanOwner
    {n : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace 𝕜 (Fin n)))
    (h : Nonempty e.target) :
    ChartedSpace (EuclideanSpace 𝕜 (Fin n)) e.source :=
  -- Route correction: transport the self-modeled Euclidean patch owner along the chart
  -- homeomorphism, instead of postulating a global auxiliary target owner on all of `M`.
  let U : TopologicalSpace.Opens (EuclideanSpace 𝕜 (Fin n)) := ⟨e.target, e.open_target⟩
  let eU : OpenPartialHomeomorph U (EuclideanSpace 𝕜 (Fin n)) :=
    U.openPartialHomeomorphSubtypeCoe h
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin n)) U :=
    eU.singletonChartedSpace (by
      simpa [eU] using U.openPartialHomeomorphSubtypeCoe_source h)
  let _ :
      ChartedSpace (EuclideanSpace 𝕜 (Fin n))
        (e.target : Set (EuclideanSpace 𝕜 (Fin n))) := by
    change ChartedSpace (EuclideanSpace 𝕜 (Fin n)) U
    infer_instance
  let eST : (e.target : Set (EuclideanSpace 𝕜 (Fin n))) ≃ₜ e.source :=
    e.toHomeomorphSourceTarget.symm
  let _ : ChartedSpace (e.target : Set (EuclideanSpace 𝕜 (Fin n))) e.source :=
    (eST.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp [eST])
  ChartedSpace.comp (EuclideanSpace 𝕜 (Fin n))
    (e.target : Set (EuclideanSpace 𝕜 (Fin n))) e.source

/-- Helper for Remark 7.50-extra-5: the chart-source subtype transported from an ambient Euclidean
chart is itself a smooth boundaryless manifold in the self-modeled Euclidean owner. -/
lemma chartSourceEuclideanOwner_isManifold
    {n : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace 𝕜 (Fin n)))
    (h : Nonempty e.target) :
    let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin n)) e.source := chartSourceEuclideanOwner e h
    IsManifold
      (modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin n)))
      (⊤ : WithTop ℕ∞) e.source := by
  -- The transported singleton-chart atlas inherits the standard Euclidean manifold structure from
  -- the open target patch.
  let U : TopologicalSpace.Opens (EuclideanSpace 𝕜 (Fin n)) := ⟨e.target, e.open_target⟩
  let eU : OpenPartialHomeomorph U (EuclideanSpace 𝕜 (Fin n)) :=
    U.openPartialHomeomorphSubtypeCoe h
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin n)) U :=
    eU.singletonChartedSpace (by
      simpa [eU] using U.openPartialHomeomorphSubtypeCoe_source h)
  let _ :
      ChartedSpace (EuclideanSpace 𝕜 (Fin n))
        (e.target : Set (EuclideanSpace 𝕜 (Fin n))) := by
      change ChartedSpace (EuclideanSpace 𝕜 (Fin n)) U
      infer_instance
  let _ :
      IsManifold
        (modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin n)))
        (⊤ : WithTop ℕ∞)
        (e.target : Set (EuclideanSpace 𝕜 (Fin n))) := by
      change IsManifold
          (modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin n)))
          (⊤ : WithTop ℕ∞) U
      exact eU.isManifold_singleton (by
        simpa [eU] using U.openPartialHomeomorphSubtypeCoe_source h)
  exact
    transportedSelfModeledPatchIsManifold
      (e.toHomeomorphSourceTarget.symm)

/-- Helper for Remark 7.50-extra-5: the inverse branch of a maximal-atlas Euclidean chart is an
immersion from the open target patch back into the ambient manifold. -/
lemma euclideanChartInverse_isImmersion
    {n : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h : Nonempty e.target)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) e.target]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) e.target]
    (he : e ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) M)
    (heU :
      let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨e.target, e.open_target⟩
      U.openPartialHomeomorphSubtypeCoe h ∈
        IsManifold.maximalAtlas
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (⊤ : WithTop ℕ∞) e.target) :
    IsImmersion
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞)
      (fun x : e.target ↦ e.symm x) := by
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨e.target, e.open_target⟩
  let eU : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin n)) :=
    U.openPartialHomeomorphSubtypeCoe h
  -- In the canonical target-patch chart and the ambient chart `e`, the inverse branch is the
  -- identity on Euclidean coordinates.
  refine ⟨PUnit, inferInstance, inferInstance, ?_⟩
  intro x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    (.prodUnique ℝ (EuclideanSpace ℝ (Fin n)) PUnit) eU e ?_ ?_ ?_ ?_ ?_ ?_
  · -- The canonical open-subtype chart is defined on all of the target patch.
    simpa [eU] using (show x ∈ eU.source from by simp [eU])
  · -- The ambient chart inverse sends each target-patch point back to the source patch.
    exact e.map_target x.2
  · -- The canonical target-patch chart is the preferred maximal-atlas chart on the open subtype.
    simpa [U, eU] using heU
  · -- The ambient chart was assumed to lie in the original maximal atlas.
    exact he
  · intro y hy
    -- Every point in the target-patch chart source already lies in `e.target`.
    exact e.map_target y.2
  · intro u hu
    have hu_target : u ∈ eU.target := by
      simpa [eU, OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe] using hu
    have hInversePatch :
        (((eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U) :
          EuclideanSpace ℝ (Fin n)) = u := by
      simpa [eU, OpenPartialHomeomorph.extend_coe_symm] using eU.right_inv hu_target
    have hAmbientRightInv :
        e
            (e.symm
              (((eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U) :
                EuclideanSpace ℝ (Fin n))) =
          (((eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U) :
            EuclideanSpace ℝ (Fin n)) := by
      exact e.right_inv (((eU.extend
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U).2)
    -- After normalizing the open-subtype inverse, the chart inverse followed by `e` is the
    -- identity on the Euclidean target coordinate.
    calc
      ((e.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) ∘
          (fun x : e.target ↦ e.symm x) ∘
            (eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm) u
          =
        e
          (e.symm
            (((eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U) :
              EuclideanSpace ℝ (Fin n))) := by
              simp [Function.comp, OpenPartialHomeomorph.extend_coe,
                OpenPartialHomeomorph.extend_coe_symm]
      _ = (((eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U) :
            EuclideanSpace ℝ (Fin n)) := hAmbientRightInv
      _ = u := hInversePatch

/-- Helper for Remark 7.50-extra-5: the inverse branch of a maximal-atlas Euclidean chart is an
immersion from the open target patch back into the ambient manifold for the Euclidean self owner.
-/
lemma ambientChartInverse_isImmersion
    {n : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h : Nonempty e.target)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) e.target]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) e.target]
    (he : e ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) M)
    (heU :
      let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨e.target, e.open_target⟩
      U.openPartialHomeomorphSubtypeCoe h ∈
        IsManifold.maximalAtlas
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (⊤ : WithTop ℕ∞) e.target) :
    IsImmersion
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞)
      (fun x : e.target ↦ e.symm x) := by
  -- Route correction: the earlier `J`-owner version was ill-typed because `e` is a Euclidean
  -- chart, so maximal-atlas membership can only be asked for the Euclidean self owner here.
  exact euclideanChartInverse_isImmersion e h he heU

/-- Helper for Remark 7.50-extra-5: the orbit map has one fixed rank `r`, and at every
representative `g : G` the constant-rank theorem gives local coordinates with normal form
`rank_normal_form m n r`. -/
theorem orbitMapLocalNormalFormAtRepresentative
    {m n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) :
    ∃ r : ℕ,
      ∀ g : G,
        ∃ h : LocalNormalFormAPI.LocalCoordinateNormalFormAt
          (orbit_map G p) g (LocalNormalFormAPI.rank_normal_form m n r),
          True := by
  -- First pin down the global constant rank of the orbit map.
  let IG : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)) := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
  let JM : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let _ : LieGroup IG ∞ G := by
    simpa [IG] using (inferInstance : LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G)
  let _ : IsManifold JM ∞ M := by
    simpa [JM] using
      (inferInstance : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M)
  let _ : ContMDiffSMul IG JM ∞ G M := by
    simpa [IG, JM] using
      (inferInstance :
        ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M)
  have hConstRank : ∃ r : ℕ, Manifold.HasConstantRank IG JM (orbit_map G p) r :=
    orbitMapHasConstantRank p
  rcases hConstRank with ⟨r, hRank⟩
  refine ⟨r, ?_⟩
  intro g
  -- Then apply the constant-rank local normal form theorem at the chosen representative.
  rcases constant_rank_local_coordinate_normal_form
      (orbitMap_contMDiff p) hRank g with ⟨hNF, _⟩
  exact ⟨hNF, trivial⟩

/-- Helper for Remark 7.50-extra-5: once the orbit-map normal form is centered at a representative
`g₀`, equality of quotient classes on that source patch is still detected by the Euclidean head
projection. -/
theorem quotientMk_eq_iff_headProjection_eqOnRepresentativeNeighborhood
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ g₁ g₂ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    (hg₁ : g₁ ∈ hNF.domChart.source)
    (hg₂ : g₂ ∈ hNF.domChart.source) :
    ((QuotientGroup.mk g₁ : G ⧸ MulAction.stabilizer G p) = QuotientGroup.mk g₂) ↔
      orbitHeadProjection hrm (hNF.domChart g₁) =
        orbitHeadProjection hrm (hNF.domChart g₂) := by
  -- Route correction: the quotient-detection argument only uses the representative-local normal
  -- form itself, so it works unchanged away from the identity patch.
  exact
    quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
      hrm hrn p hNF hg₁ hg₂

/-- Helper for Remark 7.50-extra-5: the quotient image of a representative-local normal-form
source patch is open in the stabilizer quotient. -/
theorem orbitQuotientPatchImage_openAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpen (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) := by
  -- The open-image descent never used that the normal form was centered at `1`.
  exact orbitQuotientPatchImage_open p hNF

/-- Helper for Remark 7.50-extra-5: the restricted quotient projection on a representative-local
normal-form source patch is an open quotient map. -/
theorem orbitQuotientPatchProjection_isOpenQuotientMapAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpenQuotientMap (fun g : hNF.domChart.source ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  -- The quotient-descent map is again identical to the identity-centered version; only the chosen
  -- local normal form has changed.
  exact orbitQuotientPatchProjection_isOpenQuotientMap p hNF

/-- Helper for Remark 7.50-extra-5: the representative-local quotient patch carries the forward
local coordinate obtained by descending the head projection through the quotient patch map. -/
noncomputable def orbitQuotientPatchForwardAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    C((((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source),
      orbitHeadProjection hrm '' hNF.domChart.target) := by
  let proj :
      C(hNF.domChart.source,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨(fun g ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source))), ?_⟩
    simpa using
      (orbitQuotientPatchProjection_isOpenQuotientMapAtRepresentative p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitQuotientPatchProjection_isOpenQuotientMapAtRepresentative p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.source, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨?_, ?_⟩
    · intro g
      refine ⟨orbitHeadProjection hrm (hNF.domChart g), ?_⟩
      exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩
    · -- Restrict the representative chart to its source patch before projecting to the shared
      -- Euclidean head coordinates.
      have hChartOn := hNF.domChart.continuousOn_toFun
      have hChart : Continuous fun g : hNF.domChart.source ↦ hNF.domChart g :=
        hChartOn.restrict
      have hHead :
          Continuous fun g : hNF.domChart.source ↦
            orbitHeadProjection hrm (hNF.domChart g) :=
        (continuous_orbitHeadProjection hrm).comp hChart
      exact
        Continuous.subtype_mk hHead
          (fun g ↦ by
            show orbitHeadProjection hrm (hNF.domChart g) ∈
                orbitHeadProjection hrm '' hNF.domChart.target
            exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩)
  -- Route correction: the quotient descent only depends on the representative-local normal form,
  -- not on the center being `1`, so the same quotient-map lift works unchanged here.
  exact
    hproj.lift raw
      (fun a b hab ↦ by
        apply Subtype.ext
        exact
          (quotientMk_eq_iff_headProjection_eqOnRepresentativeNeighborhood
            hrm hrn p hNF a.2 b.2).mp
            (by simpa [proj] using congrArg Subtype.val hab))

/-- Helper for Remark 7.50-extra-5: the representative-local quotient patch also carries the
inverse local coordinate obtained by descending the inverse source chart through the head-projection
patch map. -/
noncomputable def orbitQuotientPatchInverseAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    C((orbitHeadProjection hrm '' hNF.domChart.target),
      (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  let proj :
      C(hNF.domChart.target, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨(fun x ↦
      (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
        orbitHeadProjection hrm '' hNF.domChart.target)), ?_⟩
    simpa using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.target,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨?_, ?_⟩
    · intro x
      refine ⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p), ?_⟩
      exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩
    · -- Restrict the representative inverse chart to the target patch before quotienting the
      -- representative back to the stabilizer quotient.
      have hSymmOn := hNF.domChart.continuousOn_invFun
      have hSymm : Continuous fun x : hNF.domChart.target ↦ hNF.domChart.symm x :=
        hSymmOn.restrict
      have hMk :
          Continuous fun x : hNF.domChart.target ↦
            (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) :=
        QuotientGroup.continuous_mk.comp hSymm
      exact
        Continuous.subtype_mk hMk
          (fun x ↦ by
            show (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) ∈
                ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source
            exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩)
  -- Equal head projections on the representative-local target patch still lift to the same
  -- stabilizer quotient class.
  exact
    hproj.lift raw
      (fun a b hab ↦ by
        apply Subtype.ext
        refine
          (quotientMk_eq_iff_headProjection_eqOnRepresentativeNeighborhood
            hrm hrn p hNF
            (hNF.domChart.map_target a.2) (hNF.domChart.map_target b.2)).mpr ?_
        simpa [OpenPartialHomeomorph.right_inv hNF.domChart a.2,
          OpenPartialHomeomorph.right_inv hNF.domChart b.2, proj] using
          (congrArg Subtype.val hab))

/-- Helper for Remark 7.50-extra-5: on the canonical representative-local quotient-patch
representative, the descended forward coordinate map agrees with the source-chart head projection
used to define it. -/
theorem orbitQuotientPatchForwardAtRepresentative_comp_projection
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    ((orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) →
          orbitHeadProjection hrm '' hNF.domChart.target) ∘
      (fun g : hNF.domChart.source ↦
        (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)))) =
      fun g : hNF.domChart.source ↦
        (⟨orbitHeadProjection hrm (hNF.domChart g), ⟨hNF.domChart g, hNF.domChart.map_source g.2,
          rfl⟩⟩ : orbitHeadProjection hrm '' hNF.domChart.target) := by
  let proj :
      C(hNF.domChart.source,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨(fun g ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source))), ?_⟩
    simpa using
      (orbitQuotientPatchProjection_isOpenQuotientMapAtRepresentative p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitQuotientPatchProjection_isOpenQuotientMapAtRepresentative p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.source, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨?_, ?_⟩
    · intro g
      exact ⟨orbitHeadProjection hrm (hNF.domChart g), ⟨hNF.domChart g, hNF.domChart.map_source g.2,
        rfl⟩⟩
    · have hChartOn := hNF.domChart.continuousOn_toFun
      have hChart : Continuous fun g : hNF.domChart.source ↦ hNF.domChart g :=
        hChartOn.restrict
      have hHead :
          Continuous fun g : hNF.domChart.source ↦ orbitHeadProjection hrm (hNF.domChart g) :=
        (continuous_orbitHeadProjection hrm).comp hChart
      exact
        Continuous.subtype_mk hHead
          (fun g ↦ by
            exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩)
  have hfactor : Function.FactorsThrough raw proj := by
    intro a b hab
    apply Subtype.ext
    exact
      (quotientMk_eq_iff_headProjection_eqOnRepresentativeNeighborhood
        hrm hrn p hNF a.2 b.2).mp
        (by simpa [proj] using congrArg Subtype.val hab)
  -- Compare the descended representative-local forward map with its model before evaluation.
  funext g
  have hcomp :
      (hproj.lift raw hfactor).comp proj = raw :=
    Topology.IsQuotientMap.lift_comp hproj raw hfactor
  change ((hproj.lift raw hfactor).comp proj) g = raw g
  exact congrArg (fun f ↦ f g) hcomp

/-- Helper for Remark 7.50-extra-5: on the canonical representative-local head-projection
representative, the descended inverse coordinate map agrees with the inverse source chart used to
define it. -/
theorem orbitQuotientPatchInverseAtRepresentative_comp_projection
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    ((orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF :
        orbitHeadProjection hrm '' hNF.domChart.target →
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) ∘
      (fun x : hNF.domChart.target ↦
        (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
          orbitHeadProjection hrm '' hNF.domChart.target))) =
      fun x : hNF.domChart.target ↦
        (⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p),
          ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩⟩ :
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  let proj :
      C(hNF.domChart.target, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨(fun x ↦
      (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
        orbitHeadProjection hrm '' hNF.domChart.target)), ?_⟩
    simpa using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.target,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨?_, ?_⟩
    · intro x
      exact ⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p),
        ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩⟩
    · have hSymmOn := hNF.domChart.continuousOn_invFun
      have hSymm : Continuous fun x : hNF.domChart.target ↦ hNF.domChart.symm x :=
        hSymmOn.restrict
      have hMk :
          Continuous fun x : hNF.domChart.target ↦
            (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) :=
        QuotientGroup.continuous_mk.comp hSymm
      exact
        Continuous.subtype_mk hMk
          (fun x ↦ by
            exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩)
  have hfactor : Function.FactorsThrough raw proj := by
    intro a b hab
    apply Subtype.ext
    refine
      (quotientMk_eq_iff_headProjection_eqOnRepresentativeNeighborhood
        hrm hrn p hNF
        (hNF.domChart.map_target a.2) (hNF.domChart.map_target b.2)).mpr ?_
    simpa [OpenPartialHomeomorph.right_inv hNF.domChart a.2,
      OpenPartialHomeomorph.right_inv hNF.domChart b.2, proj] using
      (congrArg Subtype.val hab)
  -- Compare the descended representative-local inverse with the inverse-chart model before
  -- evaluation.
  funext x
  have hcomp :
      (hproj.lift raw hfactor).comp proj = raw :=
    Topology.IsQuotientMap.lift_comp hproj raw hfactor
  change ((hproj.lift raw hfactor).comp proj) x = raw x
  exact congrArg (fun f ↦ f x) hcomp

/-- Helper for Remark 7.50-extra-5: the descended forward and inverse patch coordinates at an
arbitrary representative package into a genuine homeomorphism between the quotient patch owner and
the open head-projection image patch. -/
noncomputable def orbitQuotientPatchAtRepresentativeHomeomorph
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) ≃ₜ
      orbitHeadProjection hrm '' hNF.domChart.target where
  toEquiv :=
    { toFun := orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF
      invFun := orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF
      left_inv := by
        rintro ⟨q, hq⟩
        rcases hq with ⟨g, hg, rfl⟩
        let gU : hNF.domChart.source := ⟨g, hg⟩
        let qU :
            (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
          ⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨g, hg, rfl⟩⟩
        let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
          ⟨orbitHeadProjection hrm (hNF.domChart gU),
            ⟨hNF.domChart gU, hNF.domChart.map_source hg, rfl⟩⟩
        apply Subtype.ext
        -- Reduce both descended representative-local patch maps to their representative formulas
        -- before cancelling the chart inverse.
        have hForward :=
          congrArg
            (fun f : hNF.domChart.source →
                orbitHeadProjection hrm '' hNF.domChart.target => f gU)
            (orbitQuotientPatchForwardAtRepresentative_comp_projection
              hrm hrn p hNF)
        have hInverse :=
          congrArg
            (fun f : hNF.domChart.target →
                (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) =>
              f ⟨hNF.domChart gU, hNF.domChart.map_source hg⟩)
            (orbitQuotientPatchInverseAtRepresentative_comp_projection
              hrm hrn p hNF)
        have hForwardEval :
            orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF qU = xW := by
          simpa [gU, qU, xW] using hForward
        have hInverseEval :
            orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW = qU := by
          simpa [gU, qU, xW, OpenPartialHomeomorph.left_inv hNF.domChart hg] using hInverse
        rw [hForwardEval, hInverseEval]
      right_inv := by
        rintro ⟨x, hx⟩
        rcases hx with ⟨y, hy, rfl⟩
        let yV : hNF.domChart.target := ⟨y, hy⟩
        let gU : hNF.domChart.source := ⟨hNF.domChart.symm yV, hNF.domChart.map_target hy⟩
        let qU :
            (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
          ⟨(QuotientGroup.mk (hNF.domChart.symm yV) : G ⧸ MulAction.stabilizer G p),
            ⟨hNF.domChart.symm yV, hNF.domChart.map_target hy, rfl⟩⟩
        let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
          ⟨orbitHeadProjection hrm y, ⟨y, hy, rfl⟩⟩
        apply Subtype.ext
        -- Route correction: use the canonical target-patch representative on the arbitrary patch
        -- as well, so the inverse law stays in the same spelling world as the identity patch.
        have hInverse :=
          congrArg
            (fun f : hNF.domChart.target →
                (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) =>
              f yV)
            (orbitQuotientPatchInverseAtRepresentative_comp_projection
              hrm hrn p hNF)
        have hForward :=
          congrArg
            (fun f : hNF.domChart.source →
                orbitHeadProjection hrm '' hNF.domChart.target =>
              f gU)
            (orbitQuotientPatchForwardAtRepresentative_comp_projection
              hrm hrn p hNF)
        have hInverseEval :
            orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW = qU := by
          simpa [yV, gU, qU, xW] using hInverse
        have hForwardEval :
            orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF qU = xW := by
          simpa [yV, gU, qU, xW, OpenPartialHomeomorph.right_inv hNF.domChart hy] using hForward
        rw [hInverseEval, hForwardEval] }
  continuous_toFun :=
    (orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF).continuous
  continuous_invFun :=
    (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF).continuous

/-- Helper for Remark 7.50-extra-5: in representative-local quotient coordinates, the descended
orbit map is written by the canonical rank-`r` inclusion. -/
theorem ofQuotientStabilizer_writtenInRepresentativePatch
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    hNF.codChart ∘ MulAction.ofQuotientStabilizer G p ∘ Subtype.val ∘
        orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF =
      fun x : orbitHeadProjection hrm '' hNF.domChart.target ↦
        LocalNormalFormAPI.rank_normal_form r n r x.1 := by
  funext x
  rcases x.2 with ⟨y, hy, hxy⟩
  let yV : hNF.domChart.target := ⟨y, hy⟩
  let qU :
      (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
    ⟨(QuotientGroup.mk (hNF.domChart.symm yV) : G ⧸ MulAction.stabilizer G p),
      ⟨hNF.domChart.symm yV, hNF.domChart.map_target hy, rfl⟩⟩
  let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
    ⟨orbitHeadProjection hrm y, ⟨y, hy, rfl⟩⟩
  have hxW : x = xW := by
    -- Identify the arbitrary point in the image patch with its canonical representative.
    apply Subtype.ext
    exact hxy.symm
  have hInverse :=
    congrArg
      (fun f : hNF.domChart.target →
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) =>
        f yV)
      (orbitQuotientPatchInverseAtRepresentative_comp_projection
        hrm hrn p hNF)
  have hInverseEval :
      orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW = qU := by
    -- Evaluate the descended inverse on the canonical target-patch representative.
    simpa [yV, qU, xW] using hInverse
  have hChartEq :
      hNF.codChart (MulAction.ofQuotientStabilizer G p qU) =
        LocalNormalFormAPI.rank_normal_form m n r y := by
    -- The representative chosen by the inverse patch map lies on the normal-form branch of `hNF`.
    simpa [Function.comp, yV, qU, orbit_map, MulAction.ofQuotientStabilizer_mk,
      OpenPartialHomeomorph.right_inv hNF.domChart hy] using hNF.eqOn hy
  -- Compare the written-in-charts expression first with the representative-level inverse, then
  -- collapse the remaining `m`-coordinate normal form through the head projection.
  calc
    hNF.codChart
        (MulAction.ofQuotientStabilizer G p
          (Subtype.val (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF x)))
        = hNF.codChart
            (MulAction.ofQuotientStabilizer G p
              (Subtype.val (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW))) := by
                rw [hxW]
    hNF.codChart
        (MulAction.ofQuotientStabilizer G p
          (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW))
        = hNF.codChart (MulAction.ofQuotientStabilizer G p qU) := by
            rw [hInverseEval]
    _ = LocalNormalFormAPI.rank_normal_form m n r y := hChartEq
    _ = LocalNormalFormAPI.rank_normal_form r n r (orbitHeadProjection hrm y) := by
          exact rankNormalForm_factor_through_headProjection (n := n) hrm y
    _ = LocalNormalFormAPI.rank_normal_form r n r x.1 := by
          rw [hxW]

/-- Helper for Remark 7.50-extra-5: the constant rank of the orbit map cannot exceed the source
dimension of the Lie group. -/
theorem orbitMapConstantRank_le_sourceFinrank
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] (p : M)
    {r : ℕ} (hRank : Manifold.HasConstantRank I J (orbit_map G p) r) :
    r ≤ Module.finrank 𝕜 E := by
  let _ : FiniteDimensional 𝕜 (TangentSpace I (1 : G)) := by
    simpa using! (inferInstance : FiniteDimensional 𝕜 E)
  have hRankAt :
      rankAt I J (orbit_map G p) (1 : G) =
        Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) :=
    rankAt_eq_finrank_range_mfderiv (orbit_map G p) (1 : G)
  have hRankOne :
      Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) = r := by
    -- Evaluate the constant-rank witness at the identity and rewrite the rank through `mfderiv`.
    simpa [hRank.2 (1 : G)] using hRankAt.symm
  have hRangeLe :
      Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) ≤
        Module.finrank 𝕜 E := by
    -- The image of the derivative is the range of a linear map out of the source tangent space.
    simpa using!
      (LinearMap.finrank_range_le
        ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap))
  omega

/-- Helper for Remark 7.50-extra-5: the constant rank of the orbit map cannot exceed the target
dimension of the ambient manifold. -/
theorem orbitMapConstantRank_le_targetFinrank
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] (p : M)
    {r : ℕ} (hRank : Manifold.HasConstantRank I J (orbit_map G p) r) :
    r ≤ Module.finrank 𝕜 E' := by
  let _ : FiniteDimensional 𝕜 (TangentSpace J (orbit_map G p (1 : G))) := by
    simpa [orbit_map] using! (inferInstance : FiniteDimensional 𝕜 E')
  have hRankAt :
      rankAt I J (orbit_map G p) (1 : G) =
        Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) :=
    rankAt_eq_finrank_range_mfderiv (orbit_map G p) (1 : G)
  have hRankOne :
      Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) = r := by
    -- The constant-rank witness still reads off the derivative rank at the identity.
    simpa [hRank.2 (1 : G)] using hRankAt.symm
  have hRangeLe :
      Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) ≤
        Module.finrank 𝕜 E' := by
    -- The derivative image is a submodule of the target tangent space at `p = orbit_map G p 1`.
    simpa [orbit_map] using!
      (Submodule.finrank_le
        ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range))
  omega

/-- Helper for Remark 7.50-extra-5: the constant-rank route packages a single global rank together
with both ambient finiteness bounds needed by the quotient-patch normal form. -/
theorem orbitMapConstantRankBounds
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] (p : M) :
    ∃ r : ℕ, ∃ hRank : Manifold.HasConstantRank I J (orbit_map G p) r,
      r ≤ Module.finrank 𝕜 E ∧ r ≤ Module.finrank 𝕜 E' := by
  rcases orbitMapHasConstantRank (I := I) (J := J) (G := G) (M := M) p with ⟨r, hRank⟩
  refine ⟨r, hRank, ?_⟩
  constructor
  · -- The source-dimension bound is the first half of the constant-rank package used later.
    exact orbitMapConstantRank_le_sourceFinrank (I := I) (J := J) p hRank
  · -- The target-dimension bound is the second half of the same package.
    exact orbitMapConstantRank_le_targetFinrank (I := I) (J := J) p hRank

/-- Helper for Remark 7.50-extra-5: transporting a self-modeled source patch across a
homeomorphism preserves immersions into the fixed ambient target `M`. -/
lemma transportedAmbientMapIsImmersionPatch
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {n : ℕ∞ω}
    {N : Type*} [TopologicalSpace N] [ChartedSpace ES N]
    [IsManifold (modelWithCornersSelf 𝕜 ES) n N]
    {S : Type*} [TopologicalSpace S] {g : N → M} {ι : S → M}
    (hg : IsImmersion (modelWithCornersSelf 𝕜 ES) J n g)
    (e : N ≃ₜ S) (he : ∀ x, ι (e x) = g x) :
    let _ : ChartedSpace ES S := transportedSelfModeledPatchChartedSpace (𝕜 := 𝕜) e
    let _ : IsManifold (modelWithCornersSelf 𝕜 ES) n S :=
      transportedSelfModeledPatchIsManifold (𝕜 := 𝕜) e
    IsImmersion (modelWithCornersSelf 𝕜 ES) J n ι := by
  let instCharted : ChartedSpace ES S := transportedSelfModeledPatchChartedSpace (𝕜 := 𝕜) e
  let _ : ChartedSpace ES S := instCharted
  let instManifold : IsManifold (modelWithCornersSelf 𝕜 ES) n S :=
    transportedSelfModeledPatchIsManifold (𝕜 := 𝕜) e
  let _ : IsManifold (modelWithCornersSelf 𝕜 ES) n S := instManifold
  let hCompImm := hg.isImmersionOfComplement_complement
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext z
    simp [eS])
  -- Route correction: move the homeomorphism transport entirely to the source side, so the
  -- codomain chart data from the original immersion proof is reused without any new target owner.
  refine ⟨hg.complement, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm (e.symm x)
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv (eS.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · -- The transported source chart still contains the chosen point.
    simpa [eS, OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
  · -- The codomain chart condition is exactly the old pointwise condition for `g`.
    have hxe : g (e.symm x) = ι x := by
      simpa using (he (e.symm x)).symm
    simpa [hxe] using hx.mem_codChart_source
  · -- Maximal-atlas membership on the transported source reduces to the original source chart.
    intro d hd
    rcases hd with ⟨f, hf, c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext z
        simp [eS]) f hf
    subst f
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    constructor
    · have hleft :
          ((hx.domChart.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
            contDiffGroupoid n (modelWithCornersSelf 𝕜 ES) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').1
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hleft
    · have hright :
          ((c'.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ hx.domChart) ∈
            contDiffGroupoid n (modelWithCornersSelf 𝕜 ES) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').2
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hright
  · exact hx.codChart_mem_maximalAtlas
  · -- Source points in the transported chart map into the codomain chart source because
    -- `ι ∘ e = g`.
    intro z hz
    have hz' : e.symm z ∈ hx.domChart.source := by
      simpa [eS, OpenPartialHomeomorph.trans_source] using hz
    have hze : g (e.symm z) = ι z := by
      simpa using (he (e.symm z)).symm
    simpa [hze] using hx.source_subset_preimage_source hz'
  · -- After normalizing the transported source chart, the written-in-charts formula is exactly
    -- the old one for `g`.
    intro u hu
    have hu' : u ∈ (hx.domChart.extend (modelWithCornersSelf 𝕜 ES)).target := by
      simpa [eS, OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
    have hpoint : ι (e (hx.domChart.symm u)) = g (hx.domChart.symm u) := by
      exact he (hx.domChart.symm u)
    simpa
      [eS, OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe, hpoint] using
      hx.writtenInCharts hu'

/-- Helper for Remark 7.50-extra-5: the Euclidean rank-`r` normal form
`rank_normal_form r n r` is an immersion. -/
theorem rankNormalFormSelf_isImmersion
    {n r : ℕ} (hr : r ≤ n) :
    IsImmersion (𝓡 r) (𝓡 n) ∞
      (LocalNormalFormAPI.rank_normal_form r n r) := by
  change IsImmersion (𝓡 r) (𝓡 n) ∞ (_root_.rank_normal_form r n r)
  let L : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := _root_.rank_normal_form r n r
      map_add' := by
        intro x y
        ext i
        by_cases hi : i.1 < r
        · simp [_root_.rank_normal_form, hi]
        · simp [_root_.rank_normal_form, hi]
      map_smul' := by
        intro c x
        ext i
        by_cases hi : i.1 < r
        · simp [_root_.rank_normal_form, hi]
        · simp [_root_.rank_normal_form, hi]
      cont := by
        -- The normal form is coordinatewise continuous on Euclidean space.
        have hcoord :
            Continuous fun x : EuclideanSpace ℝ (Fin r) ↦
              fun i : Fin n ↦
                if hri : i.1 < r then x ⟨i.1, hri⟩ else 0 := by
          refine continuous_pi ?_
          intro i
          by_cases hi : i.1 < r
          · simpa [hi] using
              (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℝ) ⟨i.1, hi⟩)
          · simpa [hi] using
              (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin r) ↦ (0 : ℝ))
        have hEq :
            (_root_.rank_normal_form r n r) =
              (WithLp.toLp 2 ∘
                fun x : EuclideanSpace ℝ (Fin r) ↦
                  fun i : Fin n ↦
                    if hri : i.1 < r then x ⟨i.1, hri⟩ else 0) := by
          funext x
          ext i
          by_cases hi : i.1 < r
          · simp [_root_.rank_normal_form, hi]
          · simp [_root_.rank_normal_form, hi]
        rw [hEq]
        simpa [Function.comp] using
          (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp hcoord }
  have hCont :
      ContMDiff (𝓡 r) (𝓡 n) ∞
        (_root_.rank_normal_form r n r) := by
    -- Rewrite the normal form as a continuous linear map to obtain smoothness.
    simpa [L] using (L.contMDiff : ContMDiff (𝓡 r) (𝓡 n) ∞ L)
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hCont).2 ?_
  intro x
  rw [mfderiv_eq_fderiv]
  have hDeriv :
      fderiv ℝ (_root_.rank_normal_form r n r) x = L := by
    simpa [L] using (L.hasFDerivAt : HasFDerivAt L L x).fderiv
  rw [hDeriv]
  intro v w hvw
  -- Apply the left-inverse projection to compare source vectors coordinatewise.
  have hproj := congrArg (orbitHeadProjection hr) hvw
  have hproj' : orbitHeadProjection hr (L v) = orbitHeadProjection hr (L w) := hproj
  have hv : v = orbitHeadProjection hr (L v) := by
    -- The head projection is a left inverse for the zero-tail inclusion.
    symm
    simpa [L] using orbitHeadProjection_rankNormalForm hr v
  have hw : orbitHeadProjection hr (L w) = w := by
    -- Apply the same left-inverse identity on the second source vector.
    simpa [L] using orbitHeadProjection_rankNormalForm hr w
  -- Transport equality through the left inverse of `L`.
  exact hv.trans (hproj'.trans hw)

/-- Helper for Remark 7.50-extra-5: every representative-local quotient source
patch contains the quotient class of its chosen representative. -/
theorem orbitQuotientPatch_nonemptyAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    Nonempty (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) := by
  refine ⟨⟨(QuotientGroup.mk g₀ : G ⧸ MulAction.stabilizer G p), ?_⟩⟩
  exact ⟨g₀, hNF.domChart_centered.1, rfl⟩

/-- Helper for Remark 7.50-extra-5: the Euclidean target patch for a representative-local
quotient chart is nonempty because it contains the projected source center. -/
theorem orbitHeadProjection_targetPatch_nonemptyAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    Nonempty (orbitHeadProjection hrm '' hNF.domChart.target) := by
  refine ⟨⟨orbitHeadProjection hrm (hNF.domChart g₀), ?_⟩⟩
  exact ⟨hNF.domChart g₀, hNF.domChart.map_source hNF.domChart_centered.1, rfl⟩

/-- Helper for Remark 7.50-extra-5: package a representative-local quotient patch as an actual
Euclidean chart on the ambient quotient. -/
noncomputable def quotientRepresentativeChart
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    OpenPartialHomeomorph (G ⧸ MulAction.stabilizer G p)
      (EuclideanSpace ℝ (Fin r)) :=
  let Uq : TopologicalSpace.Opens (G ⧸ MulAction.stabilizer G p) :=
    ⟨((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source,
      orbitQuotientPatchImage_openAtRepresentative p hNF⟩
  let W : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin r)) :=
    ⟨orbitHeadProjection hrm '' hNF.domChart.target,
      orbitHeadProjection_targetPatchImage_open hrm p hNF⟩
  let eU : OpenPartialHomeomorph Uq W :=
    (orbitQuotientPatchAtRepresentativeHomeomorph hrm hrn p hNF).toOpenPartialHomeomorph
  let eW : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin r)) :=
    W.openPartialHomeomorphSubtypeCoe
      (orbitHeadProjection_targetPatch_nonemptyAtRepresentative hrm p hNF)
  let eUW : OpenPartialHomeomorph Uq (EuclideanSpace ℝ (Fin r)) := eU.trans eW
  eUW.lift_openEmbedding Uq.2.isOpenEmbedding_subtypeVal

/-- Helper for Remark 7.50-extra-5: the representative-local quotient chart is defined exactly on
the quotient image of the chosen source patch. -/
theorem quotientRepresentativeChart_source
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    (quotientRepresentativeChart hrm hrn p hNF).source =
      ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source := by
  -- Normalize the lifted source explicitly so later atlas packaging can read chart membership from
  -- the chosen representative patch data.
  ext q
  simp [quotientRepresentativeChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.trans_source,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source]

/-- Helper for Remark 7.50-extra-5: fixing the constant-rank witness and a quotient point `q`,
the representative `q.out` determines one local quotient chart whose source already contains `q`. -/
theorem existsRepresentativeLocalQuotientChartAt
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M)
    (hRank : Manifold.HasConstantRank
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (orbit_map G p) r)
    (hrm : r ≤ m) (hrn : r ≤ n)
    (q : G ⧸ MulAction.stabilizer G p) :
    ∃ hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
        (orbit_map G p) q.out
        (LocalNormalFormAPI.rank_normal_form m n r),
      q ∈ (quotientRepresentativeChart hrm hrn p hNF).source := by
  rcases constant_rank_local_coordinate_normal_form
      (orbitMap_contMDiff p) hRank q.out with ⟨hNF, _⟩
  refine ⟨hNF, ?_⟩
  -- The chosen quotient point is literally the quotient class of its stored representative `q.out`.
  rw [quotientRepresentativeChart_source hrm hrn p hNF]
  exact ⟨q.out, hNF.domChart_centered.1, QuotientGroup.out_eq' q⟩

/-- Helper for Remark 7.50-extra-5: choose one representative-local quotient chart at each quotient
point using the fixed constant-rank witness. -/
noncomputable def representativeLocalQuotientChartAt
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M)
    (hRank : Manifold.HasConstantRank
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (orbit_map G p) r)
    (hrm : r ≤ m) (hrn : r ≤ n)
    (q : G ⧸ MulAction.stabilizer G p) :
    OpenPartialHomeomorph (G ⧸ MulAction.stabilizer G p) (EuclideanSpace ℝ (Fin r)) :=
  quotientRepresentativeChart hrm hrn p
    (Classical.choose (existsRepresentativeLocalQuotientChartAt p hRank hrm hrn q))

/-- Helper for Remark 7.50-extra-5: the chosen representative-local quotient chart at `q` is
indeed centered on `q` in the sense required by `ChartedSpace.mem_chart_source`. -/
theorem representativeLocalQuotientChartAt_mem_source
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M)
    (hRank : Manifold.HasConstantRank
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (orbit_map G p) r)
    (hrm : r ≤ m) (hrn : r ≤ n)
    (q : G ⧸ MulAction.stabilizer G p) :
    q ∈ (representativeLocalQuotientChartAt p hRank hrm hrn q).source := by
  -- Unfold the chosen chart once and read the stored source-membership witness from the choice
  -- theorem so later charted-space packaging avoids replaying the representative choice.
  simpa [representativeLocalQuotientChartAt] using
    (Classical.choose_spec (existsRepresentativeLocalQuotientChartAt p hRank hrm hrn q))

/-- Helper for Remark 7.50-extra-5: the chosen representative-local quotient chart belongs to the
atlas generated by the chart selector itself. -/
theorem representativeLocalQuotientChartAt_mem_atlas
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M)
    (hRank : Manifold.HasConstantRank
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (orbit_map G p) r)
    (hrm : r ≤ m) (hrn : r ≤ n)
    (q : G ⧸ MulAction.stabilizer G p) :
    representativeLocalQuotientChartAt p hRank hrm hrn q ∈
      Set.range (representativeLocalQuotientChartAt p hRank hrm hrn) := by
  -- The chart selector is its own atlas generator, so membership is immediate from the witness
  -- point `q`.
  exact ⟨q, rfl⟩

/-- Helper for Remark 7.50-extra-5: once the Euclidean constant-rank witness is fixed, the chosen
representative-local quotient charts already define the underlying `ChartedSpace` data on the
stabilizer quotient. -/
@[reducible] noncomputable def representativeLocalQuotientChartedSpace
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M)
    (hRank : Manifold.HasConstantRank
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (orbit_map G p) r)
    (hrm : r ≤ m) (hrn : r ≤ n) :
    ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) where
  atlas := Set.range (representativeLocalQuotientChartAt p hRank hrm hrn)
  chartAt := representativeLocalQuotientChartAt p hRank hrm hrn
  mem_chart_source := representativeLocalQuotientChartAt_mem_source p hRank hrm hrn
  chart_mem_atlas := representativeLocalQuotientChartAt_mem_atlas p hRank hrm hrn

/-- Helper for Remark 7.50-extra-5: fix one identity-centered normal form and generate every
quotient chart by translating that single chart along quotient left multiplication. -/
noncomputable def translatedIdentityQuotientChartAt
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q : G ⧸ MulAction.stabilizer G p) :
    OpenPartialHomeomorph (G ⧸ MulAction.stabilizer G p) (EuclideanSpace ℝ (Fin r)) :=
  -- Route correction: use one fixed identity chart and transport it by quotient left
  -- translations, instead of comparing unrelated `Classical.choose` normal forms.
  (quotientLeftTranslationHomeomorph
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm.toOpenPartialHomeomorph.trans
    (quotientRepresentativeChart hrm hrn p hNF)

/-- Helper for Remark 7.50-extra-5: the translated identity chart at `q` is centered on `q`. -/
theorem translatedIdentityQuotientChartAt_mem_source
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q : G ⧸ MulAction.stabilizer G p) :
    q ∈ (translatedIdentityQuotientChartAt hrm hrn p hNF q).source := by
  have hBase :
      (QuotientGroup.mk (1 : G) : G ⧸ MulAction.stabilizer G p) ∈
        (quotientRepresentativeChart hrm hrn p hNF).source := by
    -- The fixed identity patch contains the identity coset because the normal form is centered at
    -- `1 : G`.
    rw [quotientRepresentativeChart_source hrm hrn p hNF]
    exact ⟨1, hNF.domChart_centered.1, rfl⟩
  have hTranslate :
      ((quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm q :
        G ⧸ MulAction.stabilizer G p) =
        QuotientGroup.mk (1 : G) := by
    -- Moving `q` back by its chosen representative lands at the identity coset.
    have hOut :
        (QuotientGroup.mk q.out : G ⧸ MulAction.stabilizer G p) = q :=
      QuotientGroup.out_eq' q
    have hSmul :
        q.out⁻¹ • q =
          q.out⁻¹ • (QuotientGroup.mk q.out : G ⧸ MulAction.stabilizer G p) := by
      simpa using congrArg
        (fun q' : G ⧸ MulAction.stabilizer G p ↦ q.out⁻¹ • q') hOut.symm
    calc
      ((quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm q :
          G ⧸ MulAction.stabilizer G p)
          = q.out⁻¹ • q := by
            rfl
      _ = q.out⁻¹ • (QuotientGroup.mk q.out : G ⧸ MulAction.stabilizer G p) := hSmul
      _ = QuotientGroup.mk (1 : G) := by
            change (QuotientGroup.mk (q.out⁻¹ * q.out) : G ⧸ MulAction.stabilizer G p) =
              QuotientGroup.mk (1 : G)
            simp
  have hPulled :
      ((quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm q :
        G ⧸ MulAction.stabilizer G p) ∈
        (quotientRepresentativeChart hrm hrn p hNF).source := by
    simpa [hTranslate] using hBase
  -- Unfold one transport layer: membership in the translated chart source is exactly membership of
  -- the pulled-back point in the fixed identity chart source.
  simpa [translatedIdentityQuotientChartAt, OpenPartialHomeomorph.trans_source] using hPulled

/-- Helper for Remark 7.50-extra-5: every translated identity chart lies in the atlas generated by
the translated chart selector itself. -/
theorem translatedIdentityQuotientChartAt_mem_atlas
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q : G ⧸ MulAction.stabilizer G p) :
    translatedIdentityQuotientChartAt hrm hrn p hNF q ∈
      Set.range (translatedIdentityQuotientChartAt hrm hrn p hNF) := by
  -- The translated-chart selector is its own atlas generator.
  exact ⟨q, rfl⟩

/-- Helper for Remark 7.50-extra-5: the translated identity chart family already determines the
underlying `ChartedSpace` data on the stabilizer quotient. -/
@[reducible] noncomputable def translatedIdentityQuotientChartedSpace
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) where
  atlas := Set.range (translatedIdentityQuotientChartAt hrm hrn p hNF)
  chartAt := translatedIdentityQuotientChartAt hrm hrn p hNF
  mem_chart_source := translatedIdentityQuotientChartAt_mem_source hrm hrn p hNF
  chart_mem_atlas := translatedIdentityQuotientChartAt_mem_atlas hrm hrn p hNF

/-- Helper for Remark 7.50-extra-5: composing one quotient left translation with the inverse of
another collapses to the single left translation by the relative group element. -/
theorem quotientLeftTranslationHomeomorph_trans_symm
    {m : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    (p : M) (g h : G) :
    (quotientLeftTranslationHomeomorph
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p g).trans
      (quotientLeftTranslationHomeomorph
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p h).symm =
      quotientLeftTranslationHomeomorph
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p (h⁻¹ * g) := by
  -- Compare both homeomorphisms pointwise: each side acts by the same left multiplication on the
  -- quotient.
  ext q <;> simp [quotientLeftTranslationHomeomorph, smul_smul, mul_assoc]

/-- Helper for Remark 7.50-extra-5: every translated-chart overlap is the fixed identity chart
conjugating the single quotient left translation by `q'.out⁻¹ * q.out`. -/
theorem translatedIdentityChartTransition_eq_fixedLeftTranslation
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q q' : G ⧸ MulAction.stabilizer G p) :
    ((translatedIdentityQuotientChartAt hrm hrn p hNF q).symm.trans
      (translatedIdentityQuotientChartAt hrm hrn p hNF q')) =
      (quotientRepresentativeChart hrm hrn p hNF).symm.trans
        ((quotientLeftTranslationHomeomorph
            (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p (q'.out⁻¹ * q.out)).toOpenPartialHomeomorph.trans
          (quotientRepresentativeChart hrm hrn p hNF)) := by
  -- Route correction: expand both translated charts back to the fixed identity chart before
  -- comparing overlaps, so the representative-choice seam disappears.
  rw [translatedIdentityQuotientChartAt, translatedIdentityQuotientChartAt]
  -- The transition is the fixed chart on both ends with only the middle source translation left.
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  -- Collapse the two translated source symmetries to one left translation before reattaching the
  -- fixed chart on both sides.
  have hmiddle :
      (quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm.toOpenPartialHomeomorph.symm.trans
        (quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q'.out).symm.toOpenPartialHomeomorph =
        (quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p (q'.out⁻¹ * q.out)).toOpenPartialHomeomorph := by
    -- The inverse of the inverse translated chart is the original left translation.
    rw [show
        (quotientLeftTranslationHomeomorph
            (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm.toOpenPartialHomeomorph.symm =
          (quotientLeftTranslationHomeomorph
            (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).toOpenPartialHomeomorph by
          rfl]
    rw [← Homeomorph.trans_toOpenPartialHomeomorph]
    rw [quotientLeftTranslationHomeomorph_trans_symm]
  -- After the middle normalization, both sides are the same fixed-chart conjugation.
  simpa [OpenPartialHomeomorph.trans_assoc] using
    congrArg
      (fun e ↦
        (quotientRepresentativeChart hrm hrn p hNF).symm.trans
          (e.trans (quotientRepresentativeChart hrm hrn p hNF)))
      hmiddle

/-- Helper for Remark 7.50-extra-5: on the canonical target-patch representative, the fixed
left-translation conjugation of the quotient patch is written by the explicit head-projection
formula coming from the translated representative. -/
theorem fixedLeftTranslation_patch_formula
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    {g₀ g : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    (x : hNF.domChart.target)
    (hxg : g * hNF.domChart.symm x ∈ hNF.domChart.source) :
    ∃ qU :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source),
      Subtype.val qU =
          g •
            Subtype.val
              (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF
                (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
                  orbitHeadProjection hrm '' hNF.domChart.target)) ∧
        orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF qU =
          (⟨orbitHeadProjection hrm (hNF.domChart (g * hNF.domChart.symm x)),
            ⟨hNF.domChart (g * hNF.domChart.symm x),
              hNF.domChart.map_source hxg, rfl⟩⟩ :
            orbitHeadProjection hrm '' hNF.domChart.target) := by
  let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
    ⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩
  let gxU : hNF.domChart.source := ⟨g * hNF.domChart.symm x, hxg⟩
  let qU :
      (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
    ⟨(QuotientGroup.mk (g * hNF.domChart.symm x) :
        G ⧸ MulAction.stabilizer G p),
      ⟨g * hNF.domChart.symm x, hxg, rfl⟩⟩
  let yW : orbitHeadProjection hrm '' hNF.domChart.target :=
    ⟨orbitHeadProjection hrm (hNF.domChart gxU),
      ⟨hNF.domChart gxU, hNF.domChart.map_source hxg, rfl⟩⟩
  have hForward :=
    congrArg
      (fun f : hNF.domChart.source →
          orbitHeadProjection hrm '' hNF.domChart.target =>
        f gxU)
      (orbitQuotientPatchForwardAtRepresentative_comp_projection
        hrm hrn p hNF)
  have hForwardEval :
      orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF qU = yW := by
    simpa [gxU, qU, yW] using hForward
  have hInverse :=
    congrArg
      (fun f : hNF.domChart.target →
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) ↦
        f x)
      (orbitQuotientPatchInverseAtRepresentative_comp_projection
        hrm hrn p hNF)
  have hInverseEval :
      orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW =
        (⟨(QuotientGroup.mk (hNF.domChart.symm x) :
            G ⧸ MulAction.stabilizer G p),
          ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩⟩ :
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    simpa [xW] using hInverse
  have hqVal :
      Subtype.val qU =
        g •
          Subtype.val
            (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW) := by
    -- The inverse patch chooses the representative `hNF.domChart.symm x`, and left translation
    -- by `g` carries its quotient class to the class of `g * hNF.domChart.symm x`.
    rw [hInverseEval]
    change
      (QuotientGroup.mk (g * hNF.domChart.symm x) :
        G ⧸ MulAction.stabilizer G p) =
        g • (QuotientGroup.mk (hNF.domChart.symm x) :
          G ⧸ MulAction.stabilizer G p)
    rfl
  refine ⟨qU, hqVal, ?_⟩
  simpa [yW] using hForwardEval

/-- Helper for Remark 7.50-extra-5: on the actual representative-patch overlap, the explicit
translated head-projection formula is `C^∞`. -/
theorem fixedLeftTranslation_headProjectionPatch_contDiffOn
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (g : G) :
    ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin r)))
      ∞
      (fun y : EuclideanSpace ℝ (Fin m) ↦
        orbitHeadProjection hrm (hNF.domChart (g * hNF.domChart.symm y)))
      {y | y ∈ hNF.domChart.target ∧ g * hNF.domChart.symm y ∈ hNF.domChart.source} := by
  have hChartInv :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        ∞
        hNF.domChart.symm hNF.domChart.target := by
    -- The inverse branch of the normal-form chart is smooth on its target because the chart lies
    -- in the maximal atlas.
    simpa using contMDiffOn_symm_of_mem_maximalAtlas hNF.domChart_mem_maximalAtlas
  have hLeftMul :
      ContMDiff
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        ∞
        (fun x : G ↦ g * x) := by
    -- Fixed left multiplication is the ambient action of `G` on itself, hence smooth.
    simpa using
      (MulActionHom.contMDiff_const_smul
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (IX := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (X := G) g)
  have hTranslated :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        ∞
        (fun y : EuclideanSpace ℝ (Fin m) ↦ g * hNF.domChart.symm y)
        hNF.domChart.target := by
    -- Compose the smooth chart inverse with fixed left multiplication.
    simpa [Function.comp] using! hLeftMul.comp_contMDiffOn hChartInv
  have hChart :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        ∞
        hNF.domChart hNF.domChart.source := by
    -- The forward branch of the normal-form chart is smooth on its source for the same atlas
    -- reason.
    simpa using contMDiffOn_of_mem_maximalAtlas hNF.domChart_mem_maximalAtlas
  have hWritten :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        ∞
        (fun y : EuclideanSpace ℝ (Fin m) ↦ hNF.domChart (g * hNF.domChart.symm y))
        {y | y ∈ hNF.domChart.target ∧ g * hNF.domChart.symm y ∈ hNF.domChart.source} := by
    -- Restrict the translated chart inverse to the actual overlap where the forward chart is
    -- defined.
    refine hChart.comp (hTranslated.mono ?_) ?_
    · intro y hy
      exact hy.1
    intro y hy
    exact hy.2
  -- Finish by composing with the smooth linear head projection.
  simpa [Function.comp] using!
    (orbitHeadProjection_isSmoothSubmersion hrm).contMDiff.comp_contMDiffOn hWritten

/-- A smooth affine section of the head projection through a prescribed source coordinate. -/
private def orbitHeadSectionAt
    {m r : ℕ} (hrm : r ≤ m) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin m) :=
  fun z ↦ LocalNormalFormAPI.rank_normal_form r m r z +
    (x - LocalNormalFormAPI.rank_normal_form r m r (orbitHeadProjection hrm x))

private theorem orbitHeadSectionAt_contDiff
    {m r : ℕ} (hrm : r ≤ m) (x : EuclideanSpace ℝ (Fin m)) :
    ContDiff ℝ ∞ (orbitHeadSectionAt hrm x) := by
  have hRank : ContDiff ℝ ∞ (LocalNormalFormAPI.rank_normal_form r m r) :=
    (rankNormalFormSelf_isImmersion hrm).contMDiff.contDiff
  exact hRank.add contDiff_const

@[simp] private theorem orbitHeadSectionAt_head
    {m r : ℕ} (hrm : r ≤ m) (x : EuclideanSpace ℝ (Fin m)) :
    orbitHeadSectionAt hrm x (orbitHeadProjection hrm x) = x := by
  simp [orbitHeadSectionAt]

private theorem headProjection_orbitHeadSectionAt
    {m r : ℕ} (hrm : r ≤ m) (x : EuclideanSpace ℝ (Fin m))
    (z : EuclideanSpace ℝ (Fin r)) :
    orbitHeadProjection hrm (orbitHeadSectionAt hrm x z) = z := by
  ext i
  simp [orbitHeadSectionAt, orbitHeadProjection,
    LocalNormalFormAPI.rank_normal_form, _root_.rank_normal_form]

/-- The head-projection formula remains smooth after both a fixed left and a fixed right
translation.  The right translation is needed on an overlap because two representatives of the
same stabilizer coset differ by a fixed stabilizer element. -/
private theorem fixedLeftRightTranslation_headProjectionPatch_contDiffOn
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (g h : G) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin m) ↦
        orbitHeadProjection hrm (hNF.domChart (g * hNF.domChart.symm y * h)))
      {y | y ∈ hNF.domChart.target ∧
        g * hNF.domChart.symm y * h ∈ hNF.domChart.source} := by
  have hChartInv :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
        hNF.domChart.symm hNF.domChart.target := by
    simpa using contMDiffOn_symm_of_mem_maximalAtlas hNF.domChart_mem_maximalAtlas
  have hMul :
      ContMDiff
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
        (fun x : G ↦ g * x * h) := by
    have hleft :
        ContMDiff
          (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
          (fun x : G ↦ g * x) := by
      simpa using
        (MulActionHom.contMDiff_const_smul
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
          (IX := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (X := G) g)
    exact hleft.mul contMDiff_const
  have hTranslated :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
        (fun y : EuclideanSpace ℝ (Fin m) ↦ g * hNF.domChart.symm y * h)
        hNF.domChart.target := by
    simpa [Function.comp] using! hMul.comp_contMDiffOn hChartInv
  have hChart :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
        hNF.domChart hNF.domChart.source := by
    simpa using contMDiffOn_of_mem_maximalAtlas hNF.domChart_mem_maximalAtlas
  have hWritten :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
        (fun y : EuclideanSpace ℝ (Fin m) ↦
          hNF.domChart (g * hNF.domChart.symm y * h))
        {y | y ∈ hNF.domChart.target ∧
          g * hNF.domChart.symm y * h ∈ hNF.domChart.source} := by
    refine hChart.comp (hTranslated.mono ?_) ?_
    · exact fun _ hy ↦ hy.1
    · exact fun _ hy ↦ hy.2
  exact
    ((orbitHeadProjection_isSmoothSubmersion hrm).contMDiff.comp_contMDiffOn
      hWritten).contDiffOn

private theorem quotientRepresentativeChart_target_eq
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    (quotientRepresentativeChart hrm hrn p hNF).target =
      orbitHeadProjection hrm '' hNF.domChart.target := by
  ext x
  simp [quotientRepresentativeChart, OpenPartialHomeomorph.lift_openEmbedding_target,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]

private theorem quotientRepresentativeChart_symm_headProjection
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    (x : hNF.domChart.target) :
    (quotientRepresentativeChart hrm hrn p hNF).symm
        (orbitHeadProjection hrm x) =
      Subtype.val
        (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF
          (⟨orbitHeadProjection hrm x, ⟨x, x.2, rfl⟩⟩ :
            orbitHeadProjection hrm '' hNF.domChart.target)) := by
  simp [quotientRepresentativeChart,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe]
  apply congrArg (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF)
  apply Subtype.ext
  let W : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin r)) :=
    ⟨orbitHeadProjection hrm '' hNF.domChart.target,
      orbitHeadProjection_targetPatchImage_open hrm p hNF⟩
  let eW : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin r)) :=
    W.openPartialHomeomorphSubtypeCoe
      (orbitHeadProjection_targetPatch_nonemptyAtRepresentative hrm p hNF)
  have hz : orbitHeadProjection hrm (x : EuclideanSpace ℝ (Fin m)) ∈ eW.target := by
    simpa [eW, W, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using
      (show orbitHeadProjection hrm (x : EuclideanSpace ℝ (Fin m)) ∈
          orbitHeadProjection hrm '' hNF.domChart.target from ⟨x, x.2, rfl⟩)
  change ((eW.symm (orbitHeadProjection hrm (x : EuclideanSpace ℝ (Fin m))) : W) :
    EuclideanSpace ℝ (Fin r)) = orbitHeadProjection hrm (x : EuclideanSpace ℝ (Fin m))
  exact eW.right_inv hz

private theorem quotientRepresentativeChart_apply_patch
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    (qU : (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) :
    (quotientRepresentativeChart hrm hrn p hNF) (qU : G ⧸ MulAction.stabilizer G p) =
      Subtype.val (orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF qU) := by
  simp [quotientRepresentativeChart, OpenPartialHomeomorph.lift_openEmbedding_apply,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe]
  rfl

private theorem quotientRepresentativeChart_symm_headProjection_eq_mk
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    (x : hNF.domChart.target) :
    (quotientRepresentativeChart hrm hrn p hNF).symm
        (orbitHeadProjection hrm x) =
      QuotientGroup.mk (hNF.domChart.symm x) := by
  rw [quotientRepresentativeChart_symm_headProjection hrm hrn p hNF x]
  have hInv := congrArg
    (fun f : hNF.domChart.target →
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) ↦ f x)
    (orbitQuotientPatchInverseAtRepresentative_comp_projection hrm hrn p hNF)
  exact congrArg Subtype.val hInv

private theorem quotientRepresentativeChart_apply_mk
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    (a : G) (ha : a ∈ hNF.domChart.source) :
    (quotientRepresentativeChart hrm hrn p hNF)
        (QuotientGroup.mk a : G ⧸ MulAction.stabilizer G p) =
      orbitHeadProjection hrm (hNF.domChart a) := by
  let qU : (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
    ⟨QuotientGroup.mk a, ⟨a, ha, rfl⟩⟩
  rw [show (QuotientGroup.mk a : G ⧸ MulAction.stabilizer G p) = qU by rfl]
  rw [quotientRepresentativeChart_apply_patch hrm hrn p hNF qU]
  have hForward := congrArg
    (fun f : hNF.domChart.source →
        orbitHeadProjection hrm '' hNF.domChart.target => f ⟨a, ha⟩)
    (orbitQuotientPatchForwardAtRepresentative_comp_projection hrm hrn p hNF)
  exact congrArg Subtype.val hForward

/-- Helper for Remark 7.50-extra-5: every overlap of the translated identity quotient charts is
`C^∞` on its source. -/
theorem translatedIdentityChartTransition_contDiffOn
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q q' : G ⧸ MulAction.stabilizer G p) :
    ContDiffOn ℝ ∞
      (((translatedIdentityQuotientChartAt hrm hrn p hNF q).symm.trans
        (translatedIdentityQuotientChartAt hrm hrn p hNF q')) :
          OpenPartialHomeomorph
            (EuclideanSpace ℝ (Fin r))
            (EuclideanSpace ℝ (Fin r)))
      (((translatedIdentityQuotientChartAt hrm hrn p hNF q).symm.trans
        (translatedIdentityQuotientChartAt hrm hrn p hNF q')).source) := by
  rw [translatedIdentityChartTransition_eq_fixedLeftTranslation hrm hrn p hNF q q']
  let e := quotientRepresentativeChart hrm hrn p hNF
  let g : G := q'.out⁻¹ * q.out
  let L := (quotientLeftTranslationHomeomorph
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p g).toOpenPartialHomeomorph
  change ContDiffOn ℝ ∞ (e.symm.trans (L.trans e)) (e.symm.trans (L.trans e)).source
  intro z hz
  have hzSource := hz
  rw [OpenPartialHomeomorph.trans_source] at hzSource
  have hzTarget : z ∈ e.target := hzSource.1
  have hzImage : z ∈ orbitHeadProjection hrm '' hNF.domChart.target := by
    rw [← quotientRepresentativeChart_target_eq hrm hrn p hNF]
    exact hzTarget
  rcases hzImage with ⟨x0, hx0, hxz⟩
  let x : hNF.domChart.target := ⟨x0, hx0⟩
  have hxz' : orbitHeadProjection hrm (x : EuclideanSpace ℝ (Fin m)) = z := hxz
  have hzTranslatedSource : L (e.symm z) ∈ e.source := by
    have hrest := hzSource.2
    rw [OpenPartialHomeomorph.trans_source] at hrest
    exact hrest.2
  have hzTranslatedImage : L (e.symm z) ∈
      ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source := by
    rw [← quotientRepresentativeChart_source hrm hrn p hNF]
    exact hzTranslatedSource
  rcases hzTranslatedImage with ⟨b, hb, hbq⟩
  let a : G := hNF.domChart.symm x
  have heSymm : e.symm z = (QuotientGroup.mk a : G ⧸ MulAction.stabilizer G p) := by
    rw [← hxz']
    exact quotientRepresentativeChart_symm_headProjection_eq_mk hrm hrn p hNF x
  have hbclass :
      (QuotientGroup.mk b : G ⧸ MulAction.stabilizer G p) = QuotientGroup.mk (g * a) := by
    calc
      (QuotientGroup.mk b : G ⧸ MulAction.stabilizer G p) = L (e.symm z) := hbq
      _ = g • (QuotientGroup.mk a : G ⧸ MulAction.stabilizer G p) := by
        rw [heSymm]
        rfl
      _ = QuotientGroup.mk (g * a) := rfl
  let h : G := (g * a)⁻¹ * b
  have hh : h ∈ MulAction.stabilizer G p := QuotientGroup.eq.mp hbclass.symm
  have hgab : g * a * h = b := by simp [h, mul_assoc]
  let s : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin m) :=
    orbitHeadSectionAt hrm x
  have hsmooth : ContDiff ℝ ∞ s := orbitHeadSectionAt_contDiff hrm x
  have hsz : s z = x := by
    rw [← hxz']
    exact orbitHeadSectionAt_head hrm x
  let A : Set (EuclideanSpace ℝ (Fin m)) :=
    {y | y ∈ hNF.domChart.target ∧ g * hNF.domChart.symm y * h ∈ hNF.domChart.source}
  have hxA : (x : EuclideanSpace ℝ (Fin m)) ∈ A := by
    exact ⟨x.2, by simpa [a, hgab] using hb⟩
  have hAopen : IsOpen A := by
    letI : IsTopologicalGroup G :=
      topologicalGroup_of_lieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
    have hmulCont : Continuous (fun y : G ↦ g * y * h) :=
      (continuous_const_mul g).mul continuous_const
    have hpre : IsOpen ((fun y : G ↦ g * y * h) ⁻¹' hNF.domChart.source) :=
      hNF.domChart.open_source.preimage hmulCont
    change IsOpen (hNF.domChart.target ∩
      hNF.domChart.symm ⁻¹' ((fun y : G ↦ g * y * h) ⁻¹' hNF.domChart.source))
    exact hNF.domChart.isOpen_inter_preimage_symm hpre
  let phi : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r) :=
    fun w ↦ orbitHeadProjection hrm
      (hNF.domChart (g * hNF.domChart.symm (s w) * h))
  have hphiAt : ContDiffAt ℝ ∞ phi z := by
    have hlocal : ContDiffAt ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin m) ↦ orbitHeadProjection hrm
          (hNF.domChart (g * hNF.domChart.symm y * h))) x :=
      hAopen.contDiffOn_iff.mp
        (fixedLeftRightTranslation_headProjectionPatch_contDiffOn hrm p hNF g h) hxA
    have hlocal' : ContDiffAt ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin m) ↦ orbitHeadProjection hrm
          (hNF.domChart (g * hNF.domChart.symm y * h))) (s z) := by
      simpa [hsz] using hlocal
    change ContDiffAt ℝ ∞
      ((fun y : EuclideanSpace ℝ (Fin m) ↦ orbitHeadProjection hrm
        (hNF.domChart (g * hNF.domChart.symm y * h))) ∘ s) z
    exact hlocal'.comp z hsmooth.contDiffAt
  apply hphiAt.contDiffWithinAt.congr_of_eventuallyEq_of_mem
  · have hsA : s ⁻¹' A ∈ nhds z := by
      apply (hAopen.preimage hsmooth.continuous).mem_nhds
      simpa [hsz] using hxA
    change ∀ᶠ w in nhds z ⊓ Filter.principal (e.symm.trans (L.trans e)).source,
      (e.symm.trans (L.trans e)) w = phi w
    rw [Filter.eventually_inf_principal]
    filter_upwards [hsA] with w hwA hwSource
    have hwA' : s w ∈ A := hwA
    let xw : hNF.domChart.target := ⟨s w, hwA'.1⟩
    have hhead : orbitHeadProjection hrm (xw : EuclideanSpace ℝ (Fin m)) = w :=
      headProjection_orbitHeadSectionAt hrm x w
    have heSymmW : e.symm w =
        (QuotientGroup.mk (hNF.domChart.symm xw) :
          G ⧸ MulAction.stabilizer G p) := by
      rw [← hhead]
      exact quotientRepresentativeChart_symm_headProjection_eq_mk hrm hrn p hNF xw
    let c : G := g * hNF.domChart.symm xw * h
    have hc : c ∈ hNF.domChart.source := hwA'.2
    have hclass :
        (QuotientGroup.mk c : G ⧸ MulAction.stabilizer G p) =
          g • (QuotientGroup.mk (hNF.domChart.symm xw) :
            G ⧸ MulAction.stabilizer G p) := by
      change (QuotientGroup.mk c : G ⧸ MulAction.stabilizer G p) =
        QuotientGroup.mk (g * hNF.domChart.symm xw)
      apply QuotientGroup.eq.mpr
      change c⁻¹ * (g * hNF.domChart.symm xw) ∈ MulAction.stabilizer G p
      simpa [c, mul_assoc] using (MulAction.stabilizer G p).inv_mem hh
    calc
      (e.symm.trans (L.trans e)) w = e (L (e.symm w)) := rfl
      _ = e (g • (QuotientGroup.mk (hNF.domChart.symm xw) :
          G ⧸ MulAction.stabilizer G p)) := by
            rw [heSymmW]
            change e (g • (QuotientGroup.mk (hNF.domChart.symm xw) :
              G ⧸ MulAction.stabilizer G p)) = _
            rfl
      _ = e (QuotientGroup.mk c : G ⧸ MulAction.stabilizer G p) := by rw [hclass]
      _ = orbitHeadProjection hrm (hNF.domChart c) :=
        quotientRepresentativeChart_apply_mk hrm hrn p hNF c hc
      _ = phi w := rfl
  · exact hz

/-- Helper for Remark 7.50-extra-5: the translated identity quotient atlas defines a smooth
boundaryless manifold structure on `G ⧸ MulAction.stabilizer G p`. -/
theorem translatedIdentityQuotientChartedSpace_isManifold
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) :=
      translatedIdentityQuotientChartedSpace hrm hrn p hNF
    IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ∞
      (G ⧸ MulAction.stabilizer G p) := by
  let cs : ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) :=
    translatedIdentityQuotientChartedSpace hrm hrn p hNF
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) := cs
  -- The translated charts generate the whole atlas, so smooth compatibility reduces to the
  -- single transition lemma proved above for arbitrary `q` and `q'`.
  refine isManifold_of_contDiffOn (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin r)))
    (n := ∞) (M := G ⧸ MulAction.stabilizer G p) ?_
  intro e e' he he'
  rcases he with ⟨q, rfl⟩
  rcases he' with ⟨q', rfl⟩
  simpa using translatedIdentityChartTransition_contDiffOn hrm hrn p hNF q q'

private theorem orbitMemContDiffGroupoidOfLocalStructomorphOnSource
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜' E'']
    {H'' : Type*} [TopologicalSpace H'']
    {K : ModelWithCorners 𝕜' E'' H''}
    {f : OpenPartialHomeomorph H'' H''}
    (hf : ChartedSpace.LiftPropOn
      ((contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt) f f.source) :
    f ∈ contDiffGroupoid ∞ K := by
  refine (contDiffGroupoid ∞ K).locality ?_
  intro x hx
  have hfx := hf x hx
  have hfx' := hfx
  simp only [ChartedSpace.liftPropWithinAt_iff', chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_symm] at hfx'
  obtain ⟨-, hfx_prop⟩ := hfx'
  have hfx_prop' :
      (contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt f f.source x := by
    simpa using hfx_prop
  rw [OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
    (G := contDiffGroupoid ∞ K) (f := f)] at hfx_prop'
  obtain ⟨e, he, hsource, hEq, hxe⟩ := hfx_prop' hx
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  have hEq' : Set.EqOn f e (f.source ∩ e.source) := by
    intro y hy
    exact hEq hy.2
  have hrestr : f.restr e.source ≈ e.restr f.source :=
    OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hEq'
  have hEqOnSource : f.restr e.source ≈ e := by
    simpa [OpenPartialHomeomorph.restr_eq_of_source_subset hsource] using hrestr
  exact (contDiffGroupoid ∞ K).mem_of_eqOnSource he hEqOnSource

private theorem orbitWrittenInDiffeomorphMemContDiffGroupoid
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜' E'']
    {H'' : Type*} [TopologicalSpace H'']
    {K : ModelWithCorners 𝕜' E'' H''}
    {P Q : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]
    [TopologicalSpace Q] [ChartedSpace H'' Q] [IsManifold K ∞ Q]
    (Phi : P ≃ₘ⟮K, K⟯ Q)
    {e : OpenPartialHomeomorph P H''}
    {c : OpenPartialHomeomorph Q H''}
    (he : e ∈ IsManifold.maximalAtlas K ∞ P)
    (hc : c ∈ IsManifold.maximalAtlas K ∞ Q) :
    (e.symm.trans Phi.toHomeomorph.toOpenPartialHomeomorph).trans c ∈
      contDiffGroupoid ∞ K := by
  let f : OpenPartialHomeomorph H'' H'' :=
    (e.symm.trans Phi.toHomeomorph.toOpenPartialHomeomorph).trans c
  have hPhi :
      ChartedSpace.LiftPropOn
        ((contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt)
        Phi.toHomeomorph.toOpenPartialHomeomorph
        Phi.toHomeomorph.toOpenPartialHomeomorph.source := by
    exact (isLocalStructomorphOn_contDiffGroupoid_iff
      (I := K) (n := (∞ : ℕ∞ω))
      (f := Phi.toHomeomorph.toOpenPartialHomeomorph)).2
      ⟨by simpa using Phi.contMDiff_toFun.contMDiffOn,
       by simpa using Phi.contMDiff_invFun.contMDiffOn⟩
  refine orbitMemContDiffGroupoidOfLocalStructomorphOnSource (K := K) ?_
  intro y hy
  rw [ChartedSpace.liftPropWithinAt_iff']
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    OpenPartialHomeomorph.refl_symm, Set.preimage_id_eq]
  refine ⟨f.continuousOn_toFun.continuousWithinAt hy, ?_⟩
  intro hyf
  have hy_chart :
      y ∈ e.target ∩ e.symm ⁻¹' (Phi.toHomeomorph.toOpenPartialHomeomorph.source ∩
        Phi.toHomeomorph.toOpenPartialHomeomorph ⁻¹' c.source) := by
    have hyf' := hyf
    simp only [f, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      Set.mem_preimage] at hyf'
    rcases hyf' with ⟨⟨hy_target, hy_source⟩, hy_csource⟩
    exact ⟨hy_target, hy_source, hy_csource⟩
  have htransport :
      (contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt
        (c ∘ Phi.toHomeomorph.toOpenPartialHomeomorph ∘ e.symm)
        (e.symm ⁻¹' Phi.toHomeomorph.toOpenPartialHomeomorph.source) y := by
    exact StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
      (hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid ∞ K))
      he hc hPhi hy_chart
  rcases htransport hy_chart.2.1 with ⟨phi, hphi, hEq, hyphi⟩
  refine ⟨phi, hphi, ?_, hyphi⟩
  intro z hz
  have hz_big :
      z ∈ (e.symm ⁻¹' Phi.toHomeomorph.toOpenPartialHomeomorph.source) ∩ phi.source := by
    refine ⟨?_, hz.2⟩
    have hz' := hz.1
    simp only [f, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      Set.mem_preimage] at hz'
    exact hz'.1.2
  simpa [f, OpenPartialHomeomorph.coe_trans, Function.comp_assoc] using hEq hz_big

private theorem orbitPulledChartMemMaximalAtlasOfDiffeomorph
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜' E'']
    {H'' : Type*} [TopologicalSpace H'']
    {K : ModelWithCorners 𝕜' E'' H''}
    {P Q : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]
    [TopologicalSpace Q] [ChartedSpace H'' Q] [IsManifold K ∞ Q]
    (Phi : P ≃ₘ⟮K, K⟯ Q)
    {e : OpenPartialHomeomorph Q H''}
    (he : e ∈ IsManifold.maximalAtlas K ∞ Q) :
    Phi.toHomeomorph.toOpenPartialHomeomorph.trans e ∈
      IsManifold.maximalAtlas K ∞ P := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro c hc
  have hc_max : c ∈ IsManifold.maximalAtlas K ∞ P :=
    IsManifold.subset_maximalAtlas (I := K) (n := ∞) hc
  constructor
  · simpa [OpenPartialHomeomorph.trans_assoc,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using
      orbitWrittenInDiffeomorphMemContDiffGroupoid
        (K := K) (Phi := Phi.symm) (e := e) (c := c) he hc_max
  · simpa [OpenPartialHomeomorph.trans_assoc,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using
      orbitWrittenInDiffeomorphMemContDiffGroupoid
        (K := K) (Phi := Phi) (e := c) (c := e) hc_max he

private theorem orbitSelfMaximalChartMemContDiffGroupoid
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜' E'']
    {e : OpenPartialHomeomorph E'' E''}
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf 𝕜' E'') ∞ E'') :
    e ∈ contDiffGroupoid ∞ (modelWithCornersSelf 𝕜' E'') := by
  have hcompat := IsManifold.mem_maximalAtlas_iff.mp he
    (OpenPartialHomeomorph.refl E'') (chart_mem_atlas E'' (0 : E''))
  simpa using hcompat.2

private theorem quotientRepresentativeChart_writtenInTargetChart
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓡 m) ∞ G]
    [LieGroup (𝓡 m) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [ContMDiffSMul (𝓡 m) (𝓡 n) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    Set.EqOn
      (hNF.codChart ∘ MulAction.ofQuotientStabilizer G p ∘
        (quotientRepresentativeChart hrm hrn p hNF).symm)
      (LocalNormalFormAPI.rank_normal_form r n r)
      (quotientRepresentativeChart hrm hrn p hNF).target := by
  intro u hu
  have huImage : u ∈ orbitHeadProjection hrm '' hNF.domChart.target := by
    rw [← quotientRepresentativeChart_target_eq hrm hrn p hNF]
    exact hu
  rcases huImage with ⟨x, hx, hxu⟩
  let xV : hNF.domChart.target := ⟨x, hx⟩
  have hSymm :
      (quotientRepresentativeChart hrm hrn p hNF).symm u =
        (QuotientGroup.mk (hNF.domChart.symm xV) :
          G ⧸ MulAction.stabilizer G p) := by
    rw [← hxu]
    exact quotientRepresentativeChart_symm_headProjection_eq_mk
      hrm hrn p hNF xV
  have hNormal := hNF.eqOn hx
  calc
    (hNF.codChart ∘ MulAction.ofQuotientStabilizer G p ∘
        (quotientRepresentativeChart hrm hrn p hNF).symm) u =
        hNF.codChart
          (MulAction.ofQuotientStabilizer G p
            (QuotientGroup.mk (hNF.domChart.symm xV))) := by
              simp only [Function.comp_apply, hSymm]
    _ = LocalNormalFormAPI.rank_normal_form m n r x := by
          simpa [orbit_map, MulAction.ofQuotientStabilizer_mk, xV,
            OpenPartialHomeomorph.right_inv hNF.domChart hx] using hNormal
    _ = LocalNormalFormAPI.rank_normal_form r n r (orbitHeadProjection hrm x) :=
          rankNormalForm_factor_through_headProjection (n := n) hrm x
    _ = LocalNormalFormAPI.rank_normal_form r n r u := by rw [hxu]

private theorem translatedIdentityQuotientMap_writtenInCharts
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓡 m) ∞ G]
    [LieGroup (𝓡 m) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [ContMDiffSMul (𝓡 m) (𝓡 n) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q : G ⧸ MulAction.stabilizer G p) :
    let d := translatedIdentityQuotientChartAt hrm hrn p hNF q
    let Phi := MulActionHom.smulDiffeomorph
      (I := 𝓡 m) (IX := 𝓡 n) (X := M) q.out⁻¹
    let c := Phi.toHomeomorph.toOpenPartialHomeomorph.trans hNF.codChart
    Set.EqOn (c ∘ MulAction.ofQuotientStabilizer G p ∘ d.symm)
      (LocalNormalFormAPI.rank_normal_form r n r) d.target := by
  dsimp only
  intro u hu
  have huBase : u ∈ (quotientRepresentativeChart hrm hrn p hNF).target := by
    simpa [translatedIdentityQuotientChartAt,
      OpenPartialHomeomorph.trans_target] using hu
  have hBase := quotientRepresentativeChart_writtenInTargetChart
    hrm hrn p hNF huBase
  change hNF.codChart
      (q.out⁻¹ • MulAction.ofQuotientStabilizer G p
        (q.out • (quotientRepresentativeChart hrm hrn p hNF).symm u)) =
      LocalNormalFormAPI.rank_normal_form r n r u
  rw [ofQuotientStabilizer_map_smul, inv_smul_smul]
  simpa [Function.comp_apply] using hBase

/-- Helper for Remark 7.50-extra-5: once the translated identity quotient atlas is installed, the
descended orbit map `MulAction.ofQuotientStabilizer G p` is a global immersion into the Euclidean
target owner coming from the fixed normal-form chart. -/
theorem translatedIdentityQuotientMap_isImmersion
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) :=
      translatedIdentityQuotientChartedSpace hrm hrn p hNF
    let _ : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ∞
        (G ⧸ MulAction.stabilizer G p) :=
      translatedIdentityQuotientChartedSpace_isManifold hrm hrn p hNF
    IsImmersion
      (𝓘(ℝ, EuclideanSpace ℝ (Fin r)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞
      (MulAction.ofQuotientStabilizer G p) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin r))
      (G ⧸ MulAction.stabilizer G p) :=
    translatedIdentityQuotientChartedSpace hrm hrn p hNF
  let _ : IsManifold (𝓡 r) ∞ (G ⧸ MulAction.stabilizer G p) :=
    translatedIdentityQuotientChartedSpace_isManifold hrm hrn p hNF
  rcases rankNormalFormSelf_isImmersion hrn with ⟨F, instFGroup, instFSpace, hRank⟩
  let _ : NormedAddCommGroup F := instFGroup
  let _ : NormedSpace ℝ F := instFSpace
  refine ⟨F, instFGroup, instFSpace, ?_⟩
  intro q
  let d := translatedIdentityQuotientChartAt hrm hrn p hNF q
  let Phi := MulActionHom.smulDiffeomorph
    (I := 𝓡 m) (IX := 𝓡 n) (X := M) q.out⁻¹
  let c := Phi.toHomeomorph.toOpenPartialHomeomorph.trans hNF.codChart
  let u₀ : EuclideanSpace ℝ (Fin r) := d q
  let hR := hRank u₀
  let D : OpenPartialHomeomorph
      (G ⧸ MulAction.stabilizer G p) (EuclideanSpace ℝ (Fin r)) :=
    d.trans hR.domChart
  let C : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    c.trans hR.codChart
  have hdAtlas : d ∈ atlas (EuclideanSpace ℝ (Fin r))
      (G ⧸ MulAction.stabilizer G p) := by
    exact translatedIdentityQuotientChartAt_mem_atlas hrm hrn p hNF q
  have hdMax : d ∈ IsManifold.maximalAtlas (𝓡 r) ∞
      (G ⧸ MulAction.stabilizer G p) :=
    IsManifold.subset_maximalAtlas (I := 𝓡 r) (n := ∞) hdAtlas
  have hcMax : c ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := by
    exact orbitPulledChartMemMaximalAtlasOfDiffeomorph
      (K := 𝓡 n) Phi hNF.codChart_mem_maximalAtlas
  have hDMax : D ∈ IsManifold.maximalAtlas (𝓡 r) ∞
      (G ⧸ MulAction.stabilizer G p) := by
    exact Manifold.IsImmersionAtOfComplement.trans_mem_maximalAtlas_of_mem_groupoid
      hdMax (orbitSelfMaximalChartMemContDiffGroupoid hR.domChart_mem_maximalAtlas)
  have hCMax : C ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := by
    exact Manifold.IsImmersionAtOfComplement.trans_mem_maximalAtlas_of_mem_groupoid
      hcMax (orbitSelfMaximalChartMemContDiffGroupoid hR.codChart_mem_maximalAtlas)
  have hqD : q ∈ D.source := by
    change q ∈ (d.trans hR.domChart).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨translatedIdentityQuotientChartAt_mem_source hrm hrn p hNF q, ?_⟩
    exact hR.mem_domChart_source
  have hfqC : MulAction.ofQuotientStabilizer G p q ∈ C.source := by
    change MulAction.ofQuotientStabilizer G p q ∈ (c.trans hR.codChart).source
    rw [OpenPartialHomeomorph.trans_source]
    have hOut : (QuotientGroup.mk q.out : G ⧸ MulAction.stabilizer G p) = q :=
      QuotientGroup.out_eq' q
    have hfc : MulAction.ofQuotientStabilizer G p q ∈ c.source := by
      dsimp [c, Phi]
      refine ⟨by simp, ?_⟩
      change q.out⁻¹ • MulAction.ofQuotientStabilizer G p q ∈ hNF.codChart.source
      have hOfQ : MulAction.ofQuotientStabilizer G p q = q.out • p := by
        calc
          MulAction.ofQuotientStabilizer G p q =
              MulAction.ofQuotientStabilizer G p (QuotientGroup.mk q.out) :=
            congrArg (MulAction.ofQuotientStabilizer G p) hOut.symm
          _ = q.out • p := MulAction.ofQuotientStabilizer_mk G p q.out
      rw [hOfQ, inv_smul_smul]
      simpa [orbit_map] using hNF.codChart_centered.1
    refine ⟨hfc, ?_⟩
    have hWritten := translatedIdentityQuotientMap_writtenInCharts
      hrm hrn p hNF q
      (show d q ∈ d.target from d.map_source
        (translatedIdentityQuotientChartAt_mem_source hrm hrn p hNF q))
    have hcValue : c (MulAction.ofQuotientStabilizer G p q) =
        LocalNormalFormAPI.rank_normal_form r n r u₀ := by
      change c
          (MulAction.ofQuotientStabilizer G p (d.symm (d q))) =
        LocalNormalFormAPI.rank_normal_form r n r (d q) at hWritten
      simpa [u₀, OpenPartialHomeomorph.left_inv d
        (translatedIdentityQuotientChartAt_mem_source hrm hrn p hNF q)] using hWritten
    change c (MulAction.ofQuotientStabilizer G p q) ∈ hR.codChart.source
    rw [hcValue]
    exact hR.mem_codChart_source
  have hfContinuous : Continuous (MulAction.ofQuotientStabilizer G p) := by
    rw [(QuotientGroup.isQuotientMap_mk
      (MulAction.stabilizer G p)).continuous_iff]
    have hComp : MulAction.ofQuotientStabilizer G p ∘ QuotientGroup.mk =
        orbit_map G p := by
      funext g
      simp [Function.comp, orbit_map, MulAction.ofQuotientStabilizer_mk]
    rw [hComp]
    exact (orbitMap_contMDiff (I := 𝓡 m) (J := 𝓡 n) (G := G) p).continuous
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    hfContinuous.continuousAt hR.equiv D C hqD hfqC hDMax hCMax ?_
  intro u hu
  have huD : u ∈ D.target := by
    simpa [D, OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe] using hu
  have huParts := huD
  change u ∈ (d.trans hR.domChart).target at huParts
  rw [OpenPartialHomeomorph.trans_target] at huParts
  have hvTarget : hR.domChart.symm u ∈ d.target := huParts.2
  have hWritten := translatedIdentityQuotientMap_writtenInCharts
    hrm hrn p hNF q hvTarget
  have huRext : u ∈ (hR.domChart.extend (𝓡 r)).target := by
    simpa [OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe] using huParts.1
  have hRWritten := hR.writtenInCharts huRext
  calc
    ((C.extend (𝓡 n)) ∘ MulAction.ofQuotientStabilizer G p ∘
        (D.extend (𝓡 r)).symm) u =
        hR.codChart
          (c (MulAction.ofQuotientStabilizer G p
            (d.symm (hR.domChart.symm u)))) := by
              simp [D, C, Function.comp_apply, OpenPartialHomeomorph.extend_coe,
                OpenPartialHomeomorph.extend_coe_symm,
                OpenPartialHomeomorph.coe_trans]
    _ = hR.codChart
        (LocalNormalFormAPI.rank_normal_form r n r (hR.domChart.symm u)) :=
      congrArg hR.codChart hWritten
    _ = (hR.equiv ∘ fun x ↦ (x, (0 : F))) u := by
      simpa [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
        OpenPartialHomeomorph.extend_coe_symm] using hRWritten

private theorem orbitSelfContDiffOnExtChartTransition
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜' V]
    {HV : Type*} [TopologicalSpace HV]
    {P : Type*} [TopologicalSpace P] [ChartedSpace HV P]
    {K : ModelWithCorners 𝕜' V HV} [IsManifold K ∞ P]
    [BoundarylessManifold K P] (x y : P) :
    ContDiffOn 𝕜' ∞
      (((extChartAt K x).symm.trans (extChartAt K y)) : PartialEquiv V V)
      (((extChartAt K x).symm.trans (extChartAt K y)).source) := by
  simpa [extChartAt, ModelWithCorners.extendCoordChange] using
    (K.contDiffOn_extendCoordChange
      (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas y))

private theorem orbitSelfIsOpenExtChartTarget
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜' V]
    {HV : Type*} [TopologicalSpace HV]
    {P : Type*} [TopologicalSpace P] [ChartedSpace HV P]
    {K : ModelWithCorners 𝕜' V HV} [IsManifold K ∞ P]
    [BoundarylessManifold K P] (x : P) :
    IsOpen (extChartAt K x).target := by
  have hInterior : interior (extChartAt K x).target = (extChartAt K x).target := by
    ext z
    constructor
    · exact fun hz ↦ interior_subset hz
    · intro hz
      let y : P := (chartAt HV x).symm (K.symm z)
      have hzData : z ∈ Set.range K ∧ K.symm z ∈ (chartAt HV x).target := by
        simpa [extChartAt_target, Set.mem_preimage, Set.mem_inter_iff] using hz
      have hySource : y ∈ (chartAt HV x).source := by
        simpa [y] using (chartAt HV x).map_target hzData.2
      have hyImage : extChartAt K x y ∈ interior (extChartAt K x).target := by
        exact
          (show K.IsInteriorPoint y ↔
              extChartAt K x y ∈ interior (extChartAt K x).target from
            @ModelWithCorners.isInteriorPoint_iff_of_mem_atlas 𝕜' _ V _ _ HV _ K P _ _ ∞
              inferInstance (chartAt HV x) y (by simp) (chart_mem_atlas HV x) hySource).1
            BoundarylessManifold.isInteriorPoint
      have hyEq : extChartAt K x y = z := by
        simpa [y] using (extChartAt K x).right_inv hz
      rw [hyEq] at hyImage
      exact hyImage
  rw [← hInterior]
  exact isOpen_interior

private noncomputable def orbitSelfExtChart
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜' V]
    {HV : Type*} [TopologicalSpace HV]
    {P : Type*} [TopologicalSpace P] [ChartedSpace HV P]
    (K : ModelWithCorners 𝕜' V HV) [IsManifold K ∞ P]
    [BoundarylessManifold K P] (x : P) : OpenPartialHomeomorph P V where
  toPartialEquiv := extChartAt K x
  open_source := isOpen_extChartAt_source x
  open_target := orbitSelfIsOpenExtChartTarget x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x

@[reducible] private noncomputable def orbitSelfChartedSpace
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜' V]
    {HV : Type*} [TopologicalSpace HV]
    {P : Type*} [TopologicalSpace P] [ChartedSpace HV P]
    (K : ModelWithCorners 𝕜' V HV) [IsManifold K ∞ P]
    [BoundarylessManifold K P] : ChartedSpace V P where
  atlas := Set.range (orbitSelfExtChart K)
  chartAt := orbitSelfExtChart K
  mem_chart_source x := mem_extChartAt_source x
  chart_mem_atlas x := ⟨x, rfl⟩

@[simp] private theorem orbitSelfChartAtEq
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜' V]
    {HV : Type*} [TopologicalSpace HV]
    {P : Type*} [TopologicalSpace P] [ChartedSpace HV P]
    (K : ModelWithCorners 𝕜' V HV) [IsManifold K ∞ P]
    [BoundarylessManifold K P] (x : P) :
    let _ : ChartedSpace V P := orbitSelfChartedSpace K
    chartAt V x = orbitSelfExtChart K x := rfl

private theorem orbitSelfIsManifold
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜' V]
    {HV : Type*} [TopologicalSpace HV]
    {P : Type*} [TopologicalSpace P] [ChartedSpace HV P]
    (K : ModelWithCorners 𝕜' V HV) [IsManifold K ∞ P]
    [BoundarylessManifold K P] :
    let _ : ChartedSpace V P := orbitSelfChartedSpace K
    IsManifold (modelWithCornersSelf 𝕜' V) ∞ P := by
  let _ : ChartedSpace V P := orbitSelfChartedSpace K
  exact isManifold_of_contDiffOn (modelWithCornersSelf 𝕜' V) (∞ : ℕ∞ω) P
    (fun e e' he he' ↦ by
      rcases he with ⟨x, rfl⟩
      rcases he' with ⟨y, rfl⟩
      simpa [orbitSelfExtChart] using orbitSelfContDiffOnExtChartTransition x y)

private theorem orbitSelfContMDiffIdFrom
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜' V]
    {HV : Type*} [TopologicalSpace HV]
    {P : Type*} [TopologicalSpace P] [ChartedSpace HV P]
    (K : ModelWithCorners 𝕜' V HV) [IsManifold K ∞ P]
    [BoundarylessManifold K P] :
    let _ : ChartedSpace V P := orbitSelfChartedSpace K
    let _ : IsManifold (modelWithCornersSelf 𝕜' V) ∞ P := orbitSelfIsManifold K
    ContMDiff (modelWithCornersSelf 𝕜' V) K ∞ (fun x : P ↦ x) := by
  let _ : ChartedSpace V P := orbitSelfChartedSpace K
  let _ : IsManifold (modelWithCornersSelf 𝕜' V) ∞ P := orbitSelfIsManifold K
  rw [contMDiff_iff]
  refine ⟨continuous_id, ?_⟩
  intro x y
  simpa [orbitSelfChartAtEq, orbitSelfExtChart] using!
    orbitSelfContDiffOnExtChartTransition (K := K) x y

private theorem orbitSelfContMDiffIdTo
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜' V]
    {HV : Type*} [TopologicalSpace HV]
    {P : Type*} [TopologicalSpace P] [ChartedSpace HV P]
    (K : ModelWithCorners 𝕜' V HV) [IsManifold K ∞ P]
    [BoundarylessManifold K P] :
    let _ : ChartedSpace V P := orbitSelfChartedSpace K
    let _ : IsManifold (modelWithCornersSelf 𝕜' V) ∞ P := orbitSelfIsManifold K
    ContMDiff K (modelWithCornersSelf 𝕜' V) ∞ (fun x : P ↦ x) := by
  let _ : ChartedSpace V P := orbitSelfChartedSpace K
  let _ : IsManifold (modelWithCornersSelf 𝕜' V) ∞ P := orbitSelfIsManifold K
  rw [contMDiff_iff]
  refine ⟨continuous_id, ?_⟩
  intro x y
  simpa [orbitSelfChartAtEq, orbitSelfExtChart] using!
    orbitSelfContDiffOnExtChartTransition (K := K) x y

private theorem orbitSelfIdentityIsImmersion
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace 𝕜' V]
    {HV : Type*} [TopologicalSpace HV]
    {P : Type*} [TopologicalSpace P] [ChartedSpace HV P]
    (K : ModelWithCorners 𝕜' V HV) [IsManifold K ∞ P]
    [BoundarylessManifold K P] [FiniteDimensional 𝕜' V] :
    let _ : ChartedSpace V P := orbitSelfChartedSpace K
    let _ : IsManifold (modelWithCornersSelf 𝕜' V) ∞ P := orbitSelfIsManifold K
    IsImmersion (modelWithCornersSelf 𝕜' V) K ∞ (fun x : P ↦ x) := by
  let _ : ChartedSpace V P := orbitSelfChartedSpace K
  let _ : IsManifold (modelWithCornersSelf 𝕜' V) ∞ P := orbitSelfIsManifold K
  refine ⟨PUnit.{uV + 1}, inferInstance, inferInstance, ?_⟩
  intro x
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt continuousAt_id
    (.prodUnique 𝕜' V PUnit.{uV + 1}) (chartAt V x) (chartAt HV x) ?_ ?_ ?_ ?_ ?_
  · exact mem_extChartAt_source x
  · exact mem_chart_source HV x
  · exact IsManifold.chart_mem_maximalAtlas x
  · exact IsManifold.chart_mem_maximalAtlas x
  · intro y hy
    have hy' : y ∈ (orbitSelfExtChart K x).target := by
      simpa [orbitSelfChartAtEq] using hy
    simpa [orbitSelfChartAtEq, orbitSelfExtChart, Function.comp] using
      (orbitSelfExtChart K x).right_inv hy'

/-- Transporting a boundaryless model along a continuous linear equivalence of the model
vector space keeps the model boundaryless. -/
private theorem transContinuousLinearEquiv_boundaryless
    {E E' H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] (e : E ≃L[ℝ] E') :
    (I.transContinuousLinearEquiv e).Boundaryless where
  range_eq_univ := by
    rw [ModelWithCorners.transContinuousLinearEquiv_range, ModelWithCorners.range_eq_univ,
      Set.image_univ]
    exact e.surjective.range_eq

/-- A smooth diffeomorphism between finite-dimensional boundaryless manifolds is an immersion.
This is the model-change bridge needed below; the differential is the continuous linear
equivalence supplied by the local-diffeomorphism API. -/
private theorem orbitDiffeomorphIsImmersion
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    {P : Type*} [TopologicalSpace P] [ChartedSpace H₁ P]
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H₂ Q]
    {K₁ : ModelWithCorners ℝ E₁ H₁} {K₂ : ModelWithCorners ℝ E₂ H₂}
    [IsManifold K₁ ∞ P] [IsManifold K₂ ∞ Q]
    [K₁.Boundaryless] [K₂.Boundaryless]
    [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]
    (Phi : P ≃ₘ⟮K₁, K₂⟯ Q) : IsImmersion K₁ K₂ ∞ Phi := by
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv Phi.contMDiff).2 ?_
  intro x
  rw [← Phi.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact (Phi.mfderivToContinuousLinearEquiv (by simp) x).injective

/-- Helper for Remark 7.50-extra-5: once the descended quotient map is an immersion into an
auxiliary target owner on the same carrier `M`, composing with the identity immersion back to the
original target model `J` upgrades it to the required original-model immersion. -/
theorem ofQuotientStabilizer_isImmersion_originalModel
    {EM'' : Type uE'} [NormedAddCommGroup EM''] [NormedSpace 𝕜 EM'']
    [ChartedSpace EM'' M]
    [IsManifold (modelWithCornersSelf 𝕜 EM'') ∞ M]
    [J.Boundaryless]
    (p : M)
    (hIdImm : IsImmersion (modelWithCornersSelf 𝕜 EM'') J ∞
      (fun x : M ↦ x))
    {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    [ChartedSpace EQ (G ⧸ MulAction.stabilizer G p)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) ∞
      (G ⧸ MulAction.stabilizer G p)]
    (hQuotImm : IsImmersion (modelWithCornersSelf 𝕜 EQ)
      (modelWithCornersSelf 𝕜 EM'') ∞
      (MulAction.ofQuotientStabilizer G p)) :
    IsImmersion (modelWithCornersSelf 𝕜 EQ) J ∞
      (MulAction.ofQuotientStabilizer G p) := by
  -- Compose the auxiliary-target immersion with the identity immersion back to the original model.
  simpa [Function.comp] using!
    Manifold.IsImmersion.ex416_comp hIdImm hQuotImm

/-- Helper for Remark 7.50-extra-5: an auxiliary target owner on `M` is enough for the quotient
bridge once the identity map back to `J` is known to be an immersion. -/
theorem stabilizerQuotientManifoldBridge_of_auxiliaryTargetModel
    {EM'' : Type uE'} [NormedAddCommGroup EM''] [NormedSpace 𝕜 EM'']
    [ChartedSpace EM'' M]
    [IsManifold (modelWithCornersSelf 𝕜 EM'') ∞ M]
    [J.Boundaryless]
    (p : M)
    (hIdImm : IsImmersion (modelWithCornersSelf 𝕜 EM'') J ∞
      (fun x : M ↦ x))
    {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    [ChartedSpace EQ (G ⧸ MulAction.stabilizer G p)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) ∞
      (G ⧸ MulAction.stabilizer G p)]
    (hQuotImm : IsImmersion (modelWithCornersSelf 𝕜 EQ)
      (modelWithCornersSelf 𝕜 EM'') ∞
      (MulAction.ofQuotientStabilizer G p)) :
    ∃ (EQ : Type uQ), ∃ _ : NormedAddCommGroup EQ, ∃ _ : NormedSpace 𝕜 EQ,
      ∃ _ : ChartedSpace EQ (G ⧸ MulAction.stabilizer G p),
        ∃ _ : IsManifold (modelWithCornersSelf 𝕜 EQ) ∞
            (G ⧸ MulAction.stabilizer G p),
          IsImmersion (modelWithCornersSelf 𝕜 EQ) J ∞
            (MulAction.ofQuotientStabilizer G p) := by
  -- Package the quotient charted-space owner together with the transported original-model
  -- immersion.
  refine ⟨EQ, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ofQuotientStabilizer_isImmersion_originalModel p hIdImm hQuotImm

omit [LieGroup I ∞ G] [IsManifold J ∞ M] [ContMDiffSMul I J ∞ G M] in
/-- Helper: the orbit map corestricts to a canonical map onto the literal
orbit subtype. -/
def orbitMapToOrbit (p : M) : G → MulAction.orbit G p :=
  fun g ↦ ⟨orbit_map G p g, ⟨g, rfl⟩⟩

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: forgetting the orbit subtype on `orbitMapToOrbit` recovers the
original orbit map. -/
theorem orbitMapToOrbit_coe_apply (p : M) (g : G) :
    ((orbitMapToOrbit p g : MulAction.orbit G p) : M) = orbit_map G p g := rfl

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: every orbit point is represented by some group element under
the corestricted orbit map. -/
theorem orbitMapToOrbit_surjective (p : M) :
    Function.Surjective (fun g : G ↦ orbitMapToOrbit p g) := by
  intro q
  rcases q.2 with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  -- Compare the subtype-valued orbit map at the representative furnished by orbit membership.
  apply Subtype.ext
  simpa [orbitMapToOrbit, orbit_map] using hg

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: the subtype inclusion of the literal orbit subtype has image
exactly the orbit subset in `M`. -/
theorem range_subtypeVal_orbit (p : M) :
    Set.range (Subtype.val : MulAction.orbit G p → M) = MulAction.orbit G p := by
  -- Compare the subtype-inclusion range pointwise so the carrier normalization is purely
  -- set-theoretic and independent of any manifold structure placed on the orbit subtype.
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact q.2
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

omit [IsManifold J ∞ M] in
/-- Helper: a local-slice condition on the literal orbit subtype would
already force an embedded-submanifold structure in the ambient subspace topology. -/
theorem orbitLocalSliceCondition_givesEmbeddedSubtype
    {n r : ℕ}
    [TopologicalManifold n M]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]
    (p : M)
    (hSlice : Set.SatisfiesLocalSliceCondition n (MulAction.orbit G p) r) :
    ∃ tm : TopologicalManifold r (MulAction.orbit G p),
      let _ : TopologicalManifold r (MulAction.orbit G p) := tm
      ∃ hs : IsManifold (𝓡 r) (⊤ : WithTop ℕ∞) (MulAction.orbit G p),
        let _ : IsManifold (𝓡 r) (⊤ : WithTop ℕ∞) (MulAction.orbit G p) := hs
        IsEmbeddedSubmanifold (𝓡 n) (𝓡 r) (MulAction.orbit G p) := by
  -- Theorem 5.8 identifies a local-slice atlas on the literal orbit subtype with an embedded
  -- submanifold structure for the same subtype topology.
  exact
    local_slice_condition_has_embedded_submanifold_structure
      (MulAction.orbit G p) hSlice

omit [TopologicalSpace G] [IsManifold J ∞ M] in
/-- Helper: once the literal orbit subtype carries a weakly embedded
boundaryless manifold structure, the Chapter 5 embedded-to-immersed bridge packages it as an
immersed submanifold with carrier exactly that orbit. -/
theorem orbitSubtype_toImmersedSubmanifold
    {EO : Type uQ} [NormedAddCommGroup EO] [NormedSpace 𝕜 EO]
    (p : M)
    [IsManifold J ω M]
    [ChartedSpace EO (MulAction.orbit G p)]
    [IsManifold (modelWithCornersSelf 𝕜 EO) (⊤ : WithTop ℕ∞) (MulAction.orbit G p)]
    [IsWeaklyEmbeddedSubmanifold J (modelWithCornersSelf 𝕜 EO) (MulAction.orbit G p)] :
    ∃ S : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uM} J M,
      S.carrier = MulAction.orbit G p := by
  letI : IsEmbeddedSubmanifold J (modelWithCornersSelf 𝕜 EO) (MulAction.orbit G p) :=
    inferInstance
  let hOrbitEmb : IsEmbeddedSubmanifold J (modelWithCornersSelf 𝕜 EO) (MulAction.orbit G p) :=
    inferInstance
  let T : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uM} J M :=
    hOrbitEmb.toImmersedSubmanifold
  -- The weakly embedded orbit subtype is already embedded, so the standard Chapter 5 bridge turns
  -- its subtype inclusion into an immersed submanifold of the ambient manifold.
  refine ⟨T, ?_⟩
  -- The resulting carrier is the image of `Subtype.val`, which is exactly the orbit subset.
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Helper for Remark 7.50-extra-5: in the real theorem context, once the constant-rank witness
for the orbit map is fixed, the only missing work is the representative-local quotient atlas and
its written-in-charts immersion formula for `MulAction.ofQuotientStabilizer G p`. -/
theorem stabilizerQuotientManifoldBridge
    {EG : Type uE} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace EG G]
    {EM : Type uE'} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type uH'} [TopologicalSpace HM]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
    {J : ModelWithCorners ℝ EM HM} [IsManifold J ∞ M] [J.Boundaryless]
    [MulAction G M]
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    [LieGroup (modelWithCornersSelf ℝ EG) ∞ G]
    [ContMDiffSMul (modelWithCornersSelf ℝ EG) J ∞ G M]
    (p : M) :
    ∃ (EQ : Type uQ), ∃ _ : NormedAddCommGroup EQ, ∃ _ : NormedSpace ℝ EQ,
      ∃ _ : ChartedSpace EQ (G ⧸ MulAction.stabilizer G p),
        ∃ _ : IsManifold (modelWithCornersSelf ℝ EQ) ∞
            (G ⧸ MulAction.stabilizer G p),
          IsImmersion (modelWithCornersSelf ℝ EQ) J ∞
            (MulAction.ofQuotientStabilizer G p) := by
  let m := Module.finrank ℝ EG
  let n := Module.finrank ℝ EM
  let eG : EG ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let eM : EM ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let I : ModelWithCorners ℝ EG EG := modelWithCornersSelf ℝ EG
  let KG : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) EG :=
    I.transContinuousLinearEquiv eG
  let KM : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) HM :=
    J.transContinuousLinearEquiv eM
  letI : KG.Boundaryless := transContinuousLinearEquiv_boundaryless I eG
  letI : KM.Boundaryless := transContinuousLinearEquiv_boundaryless J eM
  let phiG : G ≃ₘ⟮I, KG⟯ G :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv I G eG
  let phiM : M ≃ₘ⟮J, KM⟯ M :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv J M eM
  let _ : LieGroup I ∞ G := by
    simpa [I] using (inferInstance : LieGroup (modelWithCornersSelf ℝ EG) ∞ G)
  let _ : ContMDiffSMul I J ∞ G M := by
    simpa [I] using
      (inferInstance : ContMDiffSMul (modelWithCornersSelf ℝ EG) J ∞ G M)
  let boundaryKG : BoundarylessManifold KG G := phiG.boundarylessManifold (by simp)
  let boundaryKM : BoundarylessManifold KM M := phiM.boundarylessManifold (by simp)
  letI : BoundarylessManifold KG G := boundaryKG
  letI : BoundarylessManifold KM M := boundaryKM
  have hMulKG : ContMDiff (KG.prod KG) KG ∞ (fun z : G × G ↦ z.1 * z.2) := by
    have hleft : ContMDiff (KG.prod KG) I ∞ (fun z : G × G ↦ z.1) := by
      exact phiG.contMDiff_invFun.comp
        (contMDiff_fst : ContMDiff (KG.prod KG) KG ∞ (fun z : G × G ↦ z.1))
    have hright : ContMDiff (KG.prod KG) I ∞ (fun z : G × G ↦ z.2) := by
      exact phiG.contMDiff_invFun.comp
        (contMDiff_snd : ContMDiff (KG.prod KG) KG ∞ (fun z : G × G ↦ z.2))
    convert phiG.contMDiff_toFun.comp (hleft.mul hright) using 1 <;> rfl
  have hInvKG : ContMDiff KG KG ∞ (fun g : G ↦ g⁻¹) := by
    convert phiG.contMDiff_toFun.comp phiG.contMDiff_invFun.inv using 1 <;> rfl
  let _ : LieGroup KG ∞ G :=
    { contMDiff_mul := hMulKG
      contMDiff_inv := hInvKG }
  have hActKM : ContMDiff (KG.prod KM) KM ∞ (fun z : G × M ↦ z.1 • z.2) := by
    have hleft : ContMDiff (KG.prod KM) I ∞ (fun z : G × M ↦ z.1) := by
      exact phiG.contMDiff_invFun.comp
        (contMDiff_fst : ContMDiff (KG.prod KM) KG ∞ (fun z : G × M ↦ z.1))
    have hright : ContMDiff (KG.prod KM) J ∞ (fun z : G × M ↦ z.2) := by
      exact phiM.contMDiff_invFun.comp
        (contMDiff_snd : ContMDiff (KG.prod KM) KM ∞ (fun z : G × M ↦ z.2))
    convert phiM.contMDiff_toFun.comp (hleft.smul hright) using 1 <;> rfl
  let instActKM : ContMDiffSMul KG KM ∞ G M := ⟨hActKM⟩
  let _ : ContMDiffSMul KG KM ∞ G M := instActKM

  -- Rechart both carriers by their Euclidean self models.  The identity diffeomorphisms below
  -- retain the transported group and action operations.
  let csG : ChartedSpace (EuclideanSpace ℝ (Fin m)) G := orbitSelfChartedSpace KG
  let csM : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := orbitSelfChartedSpace KM
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) G := csG
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := csM
  let manG : IsManifold (𝓡 m) ∞ G := orbitSelfIsManifold KG
  let manM : IsManifold (𝓡 n) ∞ M := orbitSelfIsManifold KM
  let _ : IsManifold (𝓡 m) ∞ G := manG
  let _ : IsManifold (𝓡 n) ∞ M := manM
  let psiG : G ≃ₘ⟮KG, 𝓡 m⟯ G :=
    { toEquiv := Equiv.refl G
      contMDiff_toFun := orbitSelfContMDiffIdTo KG
      contMDiff_invFun := orbitSelfContMDiffIdFrom KG }
  let psiM : M ≃ₘ⟮KM, 𝓡 n⟯ M :=
    { toEquiv := Equiv.refl M
      contMDiff_toFun := orbitSelfContMDiffIdTo KM
      contMDiff_invFun := orbitSelfContMDiffIdFrom KM }
  have hMulSelf : ContMDiff ((𝓡 m).prod (𝓡 m)) (𝓡 m) ∞
      (fun z : G × G ↦ z.1 * z.2) := by
    have hleft : ContMDiff ((𝓡 m).prod (𝓡 m)) KG ∞ (fun z : G × G ↦ z.1) := by
      exact psiG.contMDiff_invFun.comp
        (contMDiff_fst : ContMDiff ((𝓡 m).prod (𝓡 m)) (𝓡 m) ∞
          (fun z : G × G ↦ z.1))
    have hright : ContMDiff ((𝓡 m).prod (𝓡 m)) KG ∞ (fun z : G × G ↦ z.2) := by
      exact psiG.contMDiff_invFun.comp
        (contMDiff_snd : ContMDiff ((𝓡 m).prod (𝓡 m)) (𝓡 m) ∞
          (fun z : G × G ↦ z.2))
    convert psiG.contMDiff_toFun.comp (hleft.mul hright) using 1 <;> rfl
  have hInvSelf : ContMDiff (𝓡 m) (𝓡 m) ∞ (fun g : G ↦ g⁻¹) := by
    convert psiG.contMDiff_toFun.comp psiG.contMDiff_invFun.inv using 1 <;> rfl
  let _ : LieGroup (𝓡 m) ∞ G :=
    { contMDiff_mul := hMulSelf
      contMDiff_inv := hInvSelf }
  have hActSelf : ContMDiff ((𝓡 m).prod (𝓡 n)) (𝓡 n) ∞
      (fun z : G × M ↦ z.1 • z.2) := by
    have hleft : ContMDiff ((𝓡 m).prod (𝓡 n)) KG ∞ (fun z : G × M ↦ z.1) := by
      exact psiG.contMDiff_invFun.comp
        (contMDiff_fst : ContMDiff ((𝓡 m).prod (𝓡 n)) (𝓡 m) ∞
          (fun z : G × M ↦ z.1))
    have hright : ContMDiff ((𝓡 m).prod (𝓡 n)) KM ∞ (fun z : G × M ↦ z.2) := by
      exact psiM.contMDiff_invFun.comp
        (contMDiff_snd : ContMDiff ((𝓡 m).prod (𝓡 n)) (𝓡 n) ∞
          (fun z : G × M ↦ z.2))
    convert psiM.contMDiff_toFun.comp (hleft.smul hright) using 1 <;> rfl
  let instActSelf : ContMDiffSMul (𝓡 m) (𝓡 n) ∞ G M := ⟨hActSelf⟩
  let _ : ContMDiffSMul (𝓡 m) (𝓡 n) ∞ G M := instActSelf

  rcases orbitMapConstantRankBounds (I := 𝓡 m) (J := 𝓡 n) (G := G) (M := M) p with
    ⟨r, hRank, hrmRaw, hrnRaw⟩
  have hrm : r ≤ m := by simpa [m] using hrmRaw
  have hrn : r ≤ n := by simpa [n] using hrnRaw
  rcases constant_rank_local_coordinate_normal_form
      (orbitMap_contMDiff p) hRank (1 : G) with ⟨hNF, _⟩
  let csQ : ChartedSpace (EuclideanSpace ℝ (Fin r))
      (G ⧸ MulAction.stabilizer G p) :=
    translatedIdentityQuotientChartedSpace (m := m) (n := n) hrm hrn p hNF
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin r))
      (G ⧸ MulAction.stabilizer G p) := csQ
  let manQ : IsManifold (𝓡 r) ∞ (G ⧸ MulAction.stabilizer G p) :=
    translatedIdentityQuotientChartedSpace_isManifold (m := m) (n := n) hrm hrn p hNF
  let _ : IsManifold (𝓡 r) ∞ (G ⧸ MulAction.stabilizer G p) := manQ
  have hQuotImm : IsImmersion (𝓡 r) (𝓡 n) ∞
      (MulAction.ofQuotientStabilizer G p) :=
    translatedIdentityQuotientMap_isImmersion (m := m) (n := n) hrm hrn p hNF
  letI : BoundarylessManifold KM M := boundaryKM
  have hSelfToKM : IsImmersion (𝓡 n) KM ∞ (fun x : M ↦ x) :=
    orbitSelfIdentityIsImmersion KM
  have hKMToJ : IsImmersion KM J ∞ (fun x : M ↦ x) := by
    have hfun : (phiM.symm : M → M) = (fun x : M ↦ x) := by
      ext x
      rfl
    simpa [hfun] using orbitDiffeomorphIsImmersion phiM.symm
  have hSelfToJ : IsImmersion (𝓡 n) J ∞ (fun x : M ↦ x) := by
    simpa [Function.comp_def] using!
      Manifold.IsImmersion.ex416_comp hKMToJ hSelfToKM

  -- Lift the quotient model into the universe requested by the statement.  Recharting once more
  -- by the lifted self model preserves the quotient carrier and its immersion.
  let EQ := ULift.{uQ} (EuclideanSpace ℝ (Fin r))
  let eQ : EuclideanSpace ℝ (Fin r) ≃L[ℝ] EQ := ContinuousLinearEquiv.ulift.symm
  let KQ : ModelWithCorners ℝ EQ (EuclideanSpace ℝ (Fin r)) :=
    (𝓡 r).transContinuousLinearEquiv eQ
  letI : KQ.Boundaryless := transContinuousLinearEquiv_boundaryless (𝓡 r) eQ
  let phiQ : (G ⧸ MulAction.stabilizer G p) ≃ₘ⟮𝓡 r, KQ⟯
      (G ⧸ MulAction.stabilizer G p) :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv (𝓡 r)
      (G ⧸ MulAction.stabilizer G p) eQ
  let boundaryKQ : BoundarylessManifold KQ (G ⧸ MulAction.stabilizer G p) :=
    phiQ.boundarylessManifold (by simp)
  letI : BoundarylessManifold KQ (G ⧸ MulAction.stabilizer G p) := boundaryKQ
  let csQLift : ChartedSpace EQ (G ⧸ MulAction.stabilizer G p) :=
    orbitSelfChartedSpace KQ
  let _ : ChartedSpace EQ (G ⧸ MulAction.stabilizer G p) := csQLift
  let manQLift : IsManifold (modelWithCornersSelf ℝ EQ) ∞
      (G ⧸ MulAction.stabilizer G p) := orbitSelfIsManifold KQ
  let _ : IsManifold (modelWithCornersSelf ℝ EQ) ∞
      (G ⧸ MulAction.stabilizer G p) := manQLift
  have hLiftToKQ : IsImmersion (modelWithCornersSelf ℝ EQ) KQ ∞
      (fun q : G ⧸ MulAction.stabilizer G p ↦ q) :=
    orbitSelfIdentityIsImmersion KQ
  have hKQToOld : IsImmersion KQ (𝓡 r) ∞
      (fun q : G ⧸ MulAction.stabilizer G p ↦ q) := by
    have hfun :
        (phiQ.symm : G ⧸ MulAction.stabilizer G p → G ⧸ MulAction.stabilizer G p) =
          (fun q : G ⧸ MulAction.stabilizer G p ↦ q) := by
      ext q
      rfl
    simpa [hfun] using orbitDiffeomorphIsImmersion phiQ.symm
  have hLiftToOld : IsImmersion (modelWithCornersSelf ℝ EQ) (𝓡 r) ∞
      (fun q : G ⧸ MulAction.stabilizer G p ↦ q) := by
    simpa [Function.comp_def] using!
      Manifold.IsImmersion.ex416_comp hKQToOld hLiftToKQ
  have hLiftQuot : IsImmersion (modelWithCornersSelf ℝ EQ) (𝓡 n) ∞
      (MulAction.ofQuotientStabilizer G p) := by
    simpa [Function.comp_def] using!
      Manifold.IsImmersion.ex416_comp hQuotImm hLiftToOld
  have hLiftQuotJ : IsImmersion (modelWithCornersSelf ℝ EQ) J ∞
      (MulAction.ofQuotientStabilizer G p) := by
    simpa [Function.comp_def] using!
      Manifold.IsImmersion.ex416_comp hSelfToJ hLiftQuot
  exact ⟨EQ, inferInstance, inferInstance, csQLift, manQLift, hLiftQuotJ⟩

-- Domain sampling summary: the Chapter 5 owner for this remark is `ImmersedSubmanifold`, while
-- §7.50 contributes the orbit-map vocabulary `orbit_map` and the canonical orbit subset
-- `MulAction.orbit G p`. This item stays source-facing: it asserts existence of an immersed
-- submanifold structure on that orbit subset, without introducing any new wrapper API.
-- Semantic recall: the canonical mathlib orbit/quotient API used here is
-- `MulAction.ofQuotientStabilizer` together with `MulAction.orbitEquivQuotientStabilizer`.
/-- Remark 7.50-extra-5: in the book's real-manifold setting, every orbit of a smooth Lie-group
action is a `C^∞` immersed submanifold of `M`, even when the isotropy group is nontrivial.

Correction of the original packaging: Chapter 5's `ImmersedSubmanifold` owner is written at
outer `⊤`/`ω` (analytic), while the hypotheses only supply a `C^∞` Lie group and a `C^∞` action.
The descended orbit map is therefore only a `C^∞` immersion, not an analytic one.  A concrete
counterexample to the analytic owner is the flow of a compactly supported non-analytic vector
field on `ℝ²`: the orbit through a non-equilibrium point is a `C^∞` immersed curve that is not
real-analytic.  The corrected conclusion is the same orbit-stabilizer packaging at smoothness
`∞`, which is the actual statement in Lee. -/
theorem orbit_is_immersed_submanifold
    {EG : Type uE} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace EG G]
    {EM : Type uE'} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type uH'} [TopologicalSpace HM]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
    {J : ModelWithCorners ℝ EM HM} [IsManifold J ∞ M] [J.Boundaryless]
    [MulAction G M]
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    [LieGroup (modelWithCornersSelf ℝ EG) ∞ G]
    [ContMDiffSMul (modelWithCornersSelf ℝ EG) J ∞ G M]
    (p : M) :
    ∃ (EQ : Type uQ), ∃ _ : NormedAddCommGroup EQ, ∃ _ : NormedSpace ℝ EQ,
      ∃ _ : ChartedSpace EQ (G ⧸ MulAction.stabilizer G p),
        ∃ _ : IsManifold (modelWithCornersSelf ℝ EQ) ∞
            (G ⧸ MulAction.stabilizer G p),
          IsImmersion (modelWithCornersSelf ℝ EQ) J ∞
            (MulAction.ofQuotientStabilizer G p) ∧
          Set.range (MulAction.ofQuotientStabilizer G p) = MulAction.orbit G p := by
  rcases
      (stabilizerQuotientManifoldBridge
        (EG := EG) (G := G) (EM := EM) (HM := HM) (M := M) (J := J) p) with
    ⟨EQ, instNormedAddCommGroupEQ, instNormedSpaceEQ,
      instChartedSpaceQuotient, instIsManifoldQuotient, hImm⟩
  let _ : NormedAddCommGroup EQ := instNormedAddCommGroupEQ
  let _ : NormedSpace ℝ EQ := instNormedSpaceEQ
  let _ : ChartedSpace EQ (G ⧸ MulAction.stabilizer G p) := instChartedSpaceQuotient
  let _ : IsManifold (modelWithCornersSelf ℝ EQ) ∞
      (G ⧸ MulAction.stabilizer G p) := instIsManifoldQuotient
  exact ⟨EQ, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨hImm, range_ofQuotientStabilizer_eq_orbit p⟩⟩

end OrbitSubmanifold
