import LeeSmoothLib.Ch04.Sec04_21.Exercise_4_4
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_12
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_14
import LeeSmoothLib.Ch07.Sec07_50.Definition_7_50_extra_4
import LeeSmoothLib.Ch07.Sec07_50.Theorem_7_25
import LeeSmoothLib.Verified.LevelSets.Generic

/-!
Uniquely named `C^∞` stabilizer-fiber helpers for Proposition 7.26 / Remark 7.50-extra-5.

The legacy owner `constant_rank_level_set_has_embedded_submanifold_structure` from
`Theorem_5_12` returns `IsEmbeddedSubmanifold`, whose inclusion is stored at outer `⊤`/`ω`
(analytic).  A smooth orbit map cannot supply that field: the graph of the standard flat
function `x ↦ if x ≤ 0 then 0 else exp (-1 / x)` is a `C^∞` embedded curve which is not
real-analytic.

These helpers consume the verified general real-model `C^∞` bundle
`LeeVerifiedLevelSets.Generic.constant_rank_level_set_smooth_structure`, which applies to
arbitrary finite-dimensional boundaryless real models `I`, `J` and returns a Euclidean
slice atlas of dimension `finrank E - r` together with `IsSmoothEmbedding` at regularity
`∞`, without changing the original ambient atlas.

Rank bounds are derived at the identity, which always lies on every orbit-map fiber.
The target-rank bound is not an extra hypothesis: the generic core derives it from the
nonempty identity fiber.  Only the source bound is supplied.

Trivial-isotropy immersions use the resulting fiber dimension together with rank-nullity
and Theorem 4.14's smooth criterion `is_immersion_iff_forall_injective_mfderiv`, not an
analytic stabilizer owner.
-/

open scoped ContDiff Manifold
open Manifold

noncomputable section

namespace StabilizerSmoothFiber

universe uG uM uEG uHG uEM uHM

section GenericOrbitFiber

variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {I : ModelWithCorners ℝ EG HG} [I.Boundaryless]
  [IsManifold I ∞ G] [LieGroup I ∞ G]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {J : ModelWithCorners ℝ EM HM} [J.Boundaryless] [IsManifold J ∞ M]
variable [MulAction G M] [ContMDiffSMul I J ∞ G M]

omit [I.Boundaryless] [IsManifold I ∞ G] [LieGroup I ∞ G]
  [J.Boundaryless] [IsManifold J ∞ M] [ContMDiffSMul I J ∞ G M] in
/-- The constant rank of an orbit map cannot exceed the source dimension; the identity
always lies on the fiber, so no extra nonempty hypothesis is required. -/
theorem orbitMap_rank_le_source (p : M) {r : ℕ}
    (hRank : HasConstantRank I J (orbit_map G p) r) :
    r ≤ Module.finrank ℝ EG := by
  let _ : FiniteDimensional ℝ (TangentSpace I (1 : G)) :=
    inferInstanceAs (FiniteDimensional ℝ EG)
  have hRankAt :
      rankAt I J (orbit_map G p) (1 : G) =
        Module.finrank ℝ
          ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) :=
    rankAt_eq_finrank_range_mfderiv (orbit_map G p) (1 : G)
  have hRankOne :
      Module.finrank ℝ
          ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) = r := by
    simpa [hRank.2 (1 : G)] using hRankAt.symm
  have hRangeLe :
      Module.finrank ℝ
          ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) ≤
        Module.finrank ℝ EG :=
    LinearMap.finrank_range_le
      (mfderiv I J (orbit_map G p) (1 : G)).toLinearMap
  omega

omit [I.Boundaryless] [IsManifold I ∞ G] [LieGroup I ∞ G]
  [J.Boundaryless] [IsManifold J ∞ M] [ContMDiffSMul I J ∞ G M] in
/-- The constant rank of an orbit map cannot exceed the target dimension; evaluated at the
identity, whose image is the base point `p`. -/
theorem orbitMap_rank_le_target (p : M) {r : ℕ}
    (hRank : HasConstantRank I J (orbit_map G p) r) :
    r ≤ Module.finrank ℝ EM := by
  let _ : FiniteDimensional ℝ
      (TangentSpace J (orbit_map G p (1 : G))) :=
    inferInstanceAs (FiniteDimensional ℝ EM)
  have hRankAt :
      rankAt I J (orbit_map G p) (1 : G) =
        Module.finrank ℝ
          ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) :=
    rankAt_eq_finrank_range_mfderiv (orbit_map G p) (1 : G)
  have hRankOne :
      Module.finrank ℝ
          ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) = r := by
    simpa [hRank.2 (1 : G)] using hRankAt.symm
  have hRangeLe :
      Module.finrank ℝ
          ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) ≤
        Module.finrank ℝ EM :=
    Submodule.finrank_le
      ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range)
  omega

/-- Package the orbit-map rank together with the source dimension bound derived at `1`.
The target bound is recorded as well, but the generic fiber core derives it automatically
from the nonempty identity fiber. -/
theorem orbitMap_rank_with_bounds (p : M) :
    ∃ r : ℕ, HasConstantRank I J (orbit_map G p) r ∧
      r ≤ Module.finrank ℝ EG ∧ r ≤ Module.finrank ℝ EM := by
  let F : G →[G] M :=
    { toFun := orbit_map G p
      map_smul' := by
        intro g x
        simp [orbit_map, smul_smul] }
  have hF : ContMDiff I J ∞ F := orbitMap_contMDiff p
  have hConstRank : ∃ r : ℕ, HasConstantRank I J F r :=
    @MulActionHom.hasConstantRank ℝ _
      EG inferInstance inferInstance
      HG inferInstance G inferInstance inferInstance inferInstance
      I inferInstance
      EG inferInstance inferInstance
      HG inferInstance G inferInstance inferInstance
      I inferInstance inferInstance inferInstance
      EM inferInstance inferInstance inferInstance
      HM inferInstance M inferInstance inferInstance
      J inferInstance inferInstance inferInstance inferInstance
      F hF
  rcases hConstRank with ⟨r, hRank⟩
  have hRank' : HasConstantRank I J (orbit_map G p) r := by
    simpa [F] using! hRank
  exact ⟨r, hRank', orbitMap_rank_le_source p hRank', orbitMap_rank_le_target p hRank'⟩

/-- Honest `C^∞` stabilizer bundle: the orbit-map fiber over `p` is a smoothly embedded
submanifold of `G` of codimension `r`, in the original ambient atlas.

Original invalid type (legacy Theorem 5.12):
`∃ hS : IsEmbeddedSubmanifold I K S, hS.codimension = r`
with `IsEmbeddedSubmanifold` storing an analytic (`⊤`/`ω`) inclusion from only `C^∞` input.
The corrected owner is `IsSmoothEmbedding` at regularity `∞`.

The Euclidean-model restriction of the h13 packaging is unnecessary: the verified generic
core applies to arbitrary finite-dimensional boundaryless real models `I`, `J`. -/
theorem stabilizer_has_smooth_embedded_structure
    [T2Space G] [SecondCountableTopology G] (p : M) {r : ℕ}
    (hRank : HasConstantRank I J (orbit_map G p) r) :
    let k : ℕ := Module.finrank ℝ EG - r
    let S : Set G := (MulAction.stabilizer G p : Set G)
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
      ∃ hs : IsManifold (𝓡 k) ∞ S,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
        let _ : IsManifold (𝓡 k) ∞ S := hs
        IsSmoothEmbedding (𝓡 k) I ∞ (Subtype.val : S → G) := by
  have hrm : r ≤ Module.finrank ℝ EG := orbitMap_rank_le_source p hRank
  rw [← preimage_singleton_orbit_map_eq_stabilizer p]
  exact
    LeeVerifiedLevelSets.Generic.constant_rank_level_set_smooth_structure
      (orbitMap_contMDiff p) hRank p hrm

omit [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ G] [LieGroup I ∞ G]
  [IsManifold J ∞ M] [ContMDiffSMul I J ∞ G M] in
/-- A positive-dimensional Euclidean space has no open singleton. -/
private lemma euclideanSpace_fin_not_isOpen_singleton {k : ℕ}
    (hk : k ≠ 0) (x : EuclideanSpace ℝ (Fin k)) :
    ¬ IsOpen ({x} : Set (EuclideanSpace ℝ (Fin k))) := by
  let i : Fin k := ⟨0, Nat.pos_iff_ne_zero.mpr hk⟩
  let y : EuclideanSpace ℝ (Fin k) := PiLp.single 2 i (1 : ℝ)
  have hy : y ≠ 0 := by
    intro hy0
    have hyi := congrArg (fun f : EuclideanSpace ℝ (Fin k) ↦ f i) hy0
    simp [y] at hyi
  let _ : Nontrivial (EuclideanSpace ℝ (Fin k)) := ⟨⟨0, y, by simpa using hy.symm⟩⟩
  let _ : Filter.NeBot (nhdsWithin x ({x}ᶜ)) :=
    Module.punctured_nhds_neBot ℝ (EuclideanSpace ℝ (Fin k)) x
  exact not_isOpen_singleton x

omit [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ G] [LieGroup I ∞ G]
  [IsManifold J ∞ M] [ContMDiffSMul I J ∞ G M] in
/-- A nonempty subsingleton manifold charted on `EuclideanSpace ℝ (Fin k)` must be
zero-dimensional. -/
private lemma subsingletonChartedSpace_fin_eq_zero {k : ℕ} {S : Type*}
    [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
    [Nonempty S] [Subsingleton S] :
    k = 0 := by
  by_contra hk
  let x : S := Classical.choice ‹Nonempty S›
  let z : EuclideanSpace ℝ (Fin k) := chartAt (EuclideanSpace ℝ (Fin k)) x x
  have hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin k)) x).source :=
    mem_chart_source (EuclideanSpace ℝ (Fin k)) x
  have htarget : (chartAt (EuclideanSpace ℝ (Fin k)) x).target = {z} := by
    ext y
    constructor
    · intro hy
      have hsame : (chartAt (EuclideanSpace ℝ (Fin k)) x).symm y = x := Subsingleton.elim _ _
      have : y = z := by
        calc
          y = (chartAt (EuclideanSpace ℝ (Fin k)) x)
              ((chartAt (EuclideanSpace ℝ (Fin k)) x).symm y) :=
            ((chartAt (EuclideanSpace ℝ (Fin k)) x).right_inv hy).symm
          _ = (chartAt (EuclideanSpace ℝ (Fin k)) x) x := by rw [hsame]
          _ = z := rfl
      simpa [z] using this
    · intro hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact (chartAt (EuclideanSpace ℝ (Fin k)) x).map_source hx
  have hopen : IsOpen ({z} : Set (EuclideanSpace ℝ (Fin k))) := by
    simpa [htarget] using (chartAt (EuclideanSpace ℝ (Fin k)) x).open_target
  exact euclideanSpace_fin_not_isOpen_singleton hk z hopen

/-- Trivial isotropy makes the stabilizer fiber a singleton, hence zero-dimensional. -/
theorem stabilizerModelDim_eq_zero_of_eq_bot {r : ℕ} (p : M)
    [T2Space G] [SecondCountableTopology G]
    (hRank : HasConstantRank I J (orbit_map G p) r)
    (hp : MulAction.stabilizer G p = ⊥) :
    Module.finrank ℝ EG - r = 0 := by
  let k : ℕ := Module.finrank ℝ EG - r
  have hData :=
    stabilizer_has_smooth_embedded_structure (I := I) (J := J) (G := G) (M := M) p hRank
  rcases hData with ⟨cs, hs, _hEmb⟩
  let S : Type uG := ↥((MulAction.stabilizer G p : Set G))
  let _ : TopologicalSpace S := inferInstance
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
  let _ : Nonempty S := ⟨⟨1, by simp⟩⟩
  let _ : Subsingleton S := by
    refine ⟨fun x y ↦ ?_⟩
    apply Subtype.ext
    have hx : (x : G) = 1 := by
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hp] using x.property
      simpa using hxBot
    have hy : (y : G) = 1 := by
      have hyBot : (y : G) ∈ (⊥ : Subgroup G) := by
        simpa [hp] using y.property
      simpa using hyBot
    simp [hx, hy]
  exact subsingletonChartedSpace_fin_eq_zero (k := k) (S := S)

/-- Trivial isotropy forces the orbit map to have full source rank at every point. -/
theorem orbitMapRank_eq_sourceFinrank_of_stabilizer_eq_bot (p : M)
    [T2Space G] [SecondCountableTopology G]
    (hp : MulAction.stabilizer G p = ⊥) :
    ∀ g : G, rankAt I J (orbit_map G p) g = Module.finrank ℝ EG := by
  obtain ⟨r, hRank, hrm, _⟩ :=
    orbitMap_rank_with_bounds (I := I) (J := J) (G := G) (M := M) p
  have hZero : Module.finrank ℝ EG - r = 0 :=
    stabilizerModelDim_eq_zero_of_eq_bot p hRank hp
  have hr_eq : r = Module.finrank ℝ EG := by omega
  intro g
  simpa [hr_eq] using hRank.2 g

/-- Trivial isotropy makes every manifold derivative of the orbit map injective. -/
theorem orbitMapMfderiv_injective_of_stabilizer_eq_bot (p : M)
    [T2Space G] [SecondCountableTopology G]
    (hp : MulAction.stabilizer G p = ⊥) :
    ∀ g : G, Function.Injective (mfderiv I J (orbit_map G p) g) := by
  intro g
  let _ : FiniteDimensional ℝ (TangentSpace I g) :=
    inferInstanceAs (FiniteDimensional ℝ EG)
  have hRankg :
      rankAt I J (orbit_map G p) g = Module.finrank ℝ EG :=
    orbitMapRank_eq_sourceFinrank_of_stabilizer_eq_bot p hp g
  have hRangeFinrank :
      Module.finrank ℝ ((mfderiv I J (orbit_map G p) g).toLinearMap.range) =
        Module.finrank ℝ EG := by
    have hRankAtg :
        rankAt I J (orbit_map G p) g =
          Module.finrank ℝ ((mfderiv I J (orbit_map G p) g).range) :=
      rankAt_eq_finrank_range_mfderiv (orbit_map G p) g
    simpa using hRankAtg.symm.trans hRankg
  have hNullity :=
    LinearMap.finrank_range_add_finrank_ker
      (mfderiv I J (orbit_map G p) g).toLinearMap
  change Module.finrank ℝ ((mfderiv I J (orbit_map G p) g).toLinearMap.range) +
      Module.finrank ℝ ((mfderiv I J (orbit_map G p) g).toLinearMap.ker) =
        Module.finrank ℝ EG at hNullity
  have hKerFinrank :
      Module.finrank ℝ ((mfderiv I J (orbit_map G p) g).toLinearMap.ker) = 0 := by
    rw [hRangeFinrank] at hNullity
    omega
  have hKerBot : ((mfderiv I J (orbit_map G p) g).toLinearMap.ker) = ⊥ :=
    Submodule.finrank_eq_zero.1 hKerFinrank
  exact (LinearMap.ker_eq_bot).1 hKerBot

/-- Trivial isotropy makes the orbit map an injective constant-rank map of full source rank,
hence a `C^∞` immersion.  This does not construct an analytic stabilizer owner. -/
theorem orbitMap_isImmersion_of_stabilizer_eq_bot
    [T2Space G] [SecondCountableTopology G] (p : M)
    (hp : MulAction.stabilizer G p = ⊥) :
    IsImmersion I J ∞ (orbit_map G p) := by
  have hCont : ContMDiff I J ∞ (orbit_map G p) := orbitMap_contMDiff p
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hCont).2 ?_
  intro g
  exact orbitMapMfderiv_injective_of_stabilizer_eq_bot p hp g

end GenericOrbitFiber

end StabilizerSmoothFiber

end
