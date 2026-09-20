import Mathlib
import LeeSmoothLib.Ch04.Sec04_21.Exercise_4_4
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_12
-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was fixed from the local constant-rank API in `Exercise_4_4`, the normal-form statement in
-- `Theorem_4_12`, and the local-diffeomorphism bridge in `Proposition_4_8`.

noncomputable section

open Filter
open scoped ContDiff Manifold Topology

universe uM uN

section GlobalRankTheorem

variable {m n r : ℕ}
variable {M : Type uM} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

namespace GlobalRankTheoremAux

/-- Evaluation at one Euclidean coordinate, bundled as a continuous linear map. -/
private def coordinateCLM {d : ℕ} (i : Fin d) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ where
  toFun := fun x ↦ x i
  map_add' := by simp
  map_smul' := by simp
  cont :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin d ↦ ℝ) i

/-- A coordinate hyperplane in finite-dimensional Euclidean space has empty interior. -/
private lemma coordinateHyperplane_interior_eq_empty {d : ℕ} (i : Fin d) :
    interior {x : EuclideanSpace ℝ (Fin d) | x i = 0} = ∅ := by
  let L := coordinateCLM i
  have hker : (L.ker : Set (EuclideanSpace ℝ (Fin d))) = {x | x i = 0} := by
    ext x
    simp [L, coordinateCLM]
  have hproper : L.ker ≠ ⊤ := by
    intro htop
    let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single i 1)
    have hv : v ∈ L.ker := by
      rw [htop]
      exact Submodule.mem_top
    have hv0 : v i = 0 := by
      simpa [L, coordinateCLM] using hv
    have hv1 : v i = 1 := by simp [v]
    linarith
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  apply hproper
  apply L.ker.eq_top_of_nonempty_interior'
  simpa [hker] using hne

/-- Pulling a coordinate hyperplane back through a chart still gives a set with empty interior. -/
private lemma chartCoordinateSlice_interior_eq_empty {d : ℕ} {X : Type*}
    [TopologicalSpace X] (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin d)))
    (i : Fin d) :
    interior (e.source ∩ e ⁻¹' {z : EuclideanSpace ℝ (Fin d) | z i = 0}) = ∅ := by
  let A := e.source ∩ e ⁻¹' {z : EuclideanSpace ℝ (Fin d) | z i = 0}
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hA
  have hopen : IsOpen (e '' interior A) :=
    e.isOpen_image_of_subset_source isOpen_interior <| by
      intro x hx
      exact (interior_subset hx).1
  have hnonempty : (e '' interior A).Nonempty := hA.image e
  have hsubset : e '' interior A ⊆ {z : EuclideanSpace ℝ (Fin d) | z i = 0} := by
    rintro z ⟨x, hx, rfl⟩
    exact (interior_subset hx).2
  have hhyper : (interior {z : EuclideanSpace ℝ (Fin d) | z i = 0}).Nonempty :=
    hnonempty.mono (hopen.subset_interior_iff.mpr hsubset)
  rw [coordinateHyperplane_interior_eq_empty i] at hhyper
  simpa using hhyper

/-- If `r < m`, every neighbourhood of the origin contains a nonzero vector killed by the
standard rank-`r` normal form. -/
private lemma exists_ne_zero_mem_rankNormalForm_kernel {m n r : ℕ} (hrm : r < m)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U)
    (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ U) :
    ∃ x ∈ U, x ≠ 0 ∧ rank_normal_form m n r x = 0 := by
  let i : Fin m := ⟨r, hrm⟩
  let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (Pi.single i 1)
  have hv_ne : v ≠ 0 := by
    intro hv
    have hvi := congrArg (fun z : EuclideanSpace ℝ (Fin m) ↦ z i) hv
    simpa [v] using hvi
  have htendsto :
      Tendsto (fun c : ℝ ↦ c • v) (𝓝[{c : ℝ | IsUnit c}] 0)
        (𝓝 (0 : EuclideanSpace ℝ (Fin m))) := by
    simpa using
      ((tendsto_nhdsWithin_of_tendsto_nhds (s := {c : ℝ | IsUnit c})
        (tendsto_id : Tendsto (fun c : ℝ ↦ c) (nhds 0) (nhds 0))).smul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ v) _ (𝓝 v)))
  have hpre : {c : ℝ | c • v ∈ U} ∈ 𝓝[{c : ℝ | IsUnit c}] 0 :=
    htendsto (hU.mem_nhds h0)
  obtain ⟨c, hcU, hcunit⟩ :=
    nonempty_of_mem (inter_mem hpre (self_mem_nhdsWithin : {c : ℝ | IsUnit c} ∈ _))
  have hc_ne : c ≠ 0 := hcunit.ne_zero
  refine ⟨c • v, hcU, smul_ne_zero hc_ne hv_ne, ?_⟩
  ext j
  by_cases hjr : j.1 < r
  · have hjm : j.1 < m := hjr.trans hrm
    have hji : (⟨j.1, hjm⟩ : Fin m) ≠ i := by
      intro heq
      have : j.1 = r := congrArg Fin.val heq
      omega
    simp [rank_normal_form, hjr, hjm, v, hji]
  · simp [rank_normal_form, hjr]

/-- The constant rank is bounded by the source dimension. -/
private lemma constantRank_le_source {F : M → N}
    (hFrank : Manifold.HasConstantRank I_m I_n F r) [Nonempty M] : r ≤ m := by
  let p : M := Classical.arbitrary M
  letI : FiniteDimensional ℝ (TangentSpace I_m p) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin m))
    infer_instance
  have hrange :
      Module.finrank ℝ ((mfderiv I_m I_n F p).toLinearMap.range) = r := by
    rw [← Manifold.rankAt_eq_finrank_range_mfderiv]
    exact hFrank.2 p
  have hle :
      Module.finrank ℝ ((mfderiv I_m I_n F p).toLinearMap.range) ≤ m := by
    have hdim : Module.finrank ℝ (TangentSpace I_m p) = m := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m
      exact finrank_euclideanSpace_fin
    exact (LinearMap.finrank_range_le (mfderiv I_m I_n F p).toLinearMap).trans_eq hdim
  omega

/-- The constant rank is bounded by the target dimension. -/
private lemma constantRank_le_target {F : M → N}
    (hFrank : Manifold.HasConstantRank I_m I_n F r) [Nonempty M] : r ≤ n := by
  let p : M := Classical.arbitrary M
  letI : FiniteDimensional ℝ (TangentSpace I_n (F p)) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n))
    infer_instance
  have hrange :
      Module.finrank ℝ ((mfderiv I_m I_n F p).toLinearMap.range) = r := by
    rw [← Manifold.rankAt_eq_finrank_range_mfderiv]
    exact hFrank.2 p
  have hle :
      Module.finrank ℝ ((mfderiv I_m I_n F p).toLinearMap.range) ≤ n := by
    have hdim : Module.finrank ℝ (TangentSpace I_n (F p)) = n := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
      exact finrank_euclideanSpace_fin
    exact (Submodule.finrank_le ((mfderiv I_m I_n F p).toLinearMap.range)).trans_eq hdim
  omega

end GlobalRankTheoremAux

open GlobalRankTheoremAux

/-- Theorem 4.14 (1) (Global Rank Theorem): a surjective smooth map of constant rank is a smooth
submersion. -/
-- Proof sketch: if the constant rank were strictly smaller than the target dimension, Theorem 4.12
-- would put the image locally inside coordinate slices of positive codimension; a countable cover
-- and the Baire category theorem would then rule out surjectivity.
theorem constant_rank_surjective_is_smooth_submersion {F : M → N}
    (hFsmooth : ContMDiff I_m I_n ∞ F) (hFrank : Manifold.HasConstantRank I_m I_n F r)
    (hFsurj : Function.Surjective F) :
    Manifold.IsSmoothSubmersion I_m I_n F := by
  classical
  by_cases hN : Nonempty N
  · letI : Nonempty N := hN
    have hM : Nonempty M := Function.Surjective.nonempty hFsurj
    letI : Nonempty M := hM
    have hrn : r = n := by
      have hr_le : r ≤ n := constantRank_le_target hFrank
      apply Nat.le_antisymm hr_le
      by_contra hnr
      have hr_lt : r < n := Nat.lt_of_not_ge hnr
      letI : LocallyCompactSpace M :=
        ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) M
      letI : LocallyCompactSpace N :=
        ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) N
      choose normal hnormal using fun p : M ↦
        constant_rank_local_coordinate_normal_form hFsmooth hFrank p
      choose K hKcompact hpK hKsub using fun p : M ↦
        exists_compact_subset (normal p).domChart.open_source
          (normal p).domChart_centered.1
      have hKnhds : ∀ p : M, K p ∈ 𝓝 p := fun p ↦
        mem_interior_iff_mem_nhds.mp (hpK p)
      obtain ⟨t, htcount, htcover⟩ := countable_cover_nhds hKnhds
      letI : Countable t := htcount.to_subtype
      have hcoverN : ⋃ p : t, F '' K p.1 = Set.univ := by
        apply Set.eq_univ_of_forall
        intro y
        obtain ⟨x, rfl⟩ := hFsurj y
        have hx : x ∈ ⋃ p ∈ t, K p := by
          rw [htcover]
          exact Set.mem_univ x
        rcases Set.mem_iUnion.1 hx with ⟨p, hp⟩
        rcases Set.mem_iUnion.1 hp with ⟨hpt, hxp⟩
        exact Set.mem_iUnion.2 ⟨⟨p, hpt⟩, ⟨x, hxp, rfl⟩⟩
      have hclosed : ∀ p : t, IsClosed (F '' K p.1) := fun p ↦
        ((hKcompact p.1).image hFsmooth.continuous).isClosed
      obtain ⟨p, hpint⟩ :=
        nonempty_interior_of_iUnion_of_closed hclosed hcoverN
      let i : Fin n := ⟨r, hr_lt⟩
      have himage :
          F '' K p.1 ⊆
            (normal p.1).codChart.source ∩
              (normal p.1).codChart ⁻¹'
                {z : EuclideanSpace ℝ (Fin n) | z i = 0} := by
        rintro y ⟨x, hxK, rfl⟩
        have hxdom : x ∈ (normal p.1).domChart.source := hKsub p.1 hxK
        refine ⟨(normal p.1).mapsTo hxdom, ?_⟩
        change (normal p.1).codChart (F x) i = 0
        have hxEq := (normal p.1).eqOn ((normal p.1).domChart.map_source hxdom)
        have hinv : (normal p.1).domChart.symm ((normal p.1).domChart x) = x :=
          (normal p.1).domChart.left_inv hxdom
        have hchart :
            (normal p.1).codChart (F x) =
              rank_normal_form m n r ((normal p.1).domChart x) := by
          simpa [Function.comp_def, hinv] using hxEq
        rw [hchart]
        simp [rank_normal_form, i]
      have hslicenonempty :
          (interior
            ((normal p.1).codChart.source ∩
              (normal p.1).codChart ⁻¹'
                {z : EuclideanSpace ℝ (Fin n) | z i = 0})).Nonempty :=
        hpint.mono (interior_mono himage)
      rw [chartCoordinateSlice_interior_eq_empty (normal p.1).codChart i] at hslicenonempty
      simpa using hslicenonempty
    refine ⟨hFsmooth, ?_⟩
    intro p
    letI : FiniteDimensional ℝ (TangentSpace I_n (F p)) := by
      change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      infer_instance
    apply LinearMap.range_eq_top.1
    apply Submodule.eq_top_of_finrank_eq
    have hp := hFrank.2 p
    rw [Manifold.rankAt_eq_finrank_range_mfderiv] at hp
    have hdim : Module.finrank ℝ (TangentSpace I_n (F p)) = n := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
      exact finrank_euclideanSpace_fin
    exact (hp.trans hrn).trans hdim.symm
  · letI : IsEmpty N := not_nonempty_iff.mp hN
    letI : IsEmpty M := ⟨fun x ↦ isEmptyElim (F x)⟩
    exact ⟨hFsmooth, fun p ↦ isEmptyElim p⟩

/-- Theorem 4.14 (2) (Global Rank Theorem): an injective smooth map of constant rank is a smooth
immersion. -/
-- Proof sketch: if the constant rank were strictly smaller than the source dimension, Theorem 4.12
-- would identify local coordinates in which `F` forgets at least one source coordinate, producing
-- distinct nearby points with the same image and contradicting injectivity.
theorem constant_rank_injective_is_immersion {F : M → N}
    (hFsmooth : ContMDiff I_m I_n ∞ F) (hFrank : Manifold.HasConstantRank I_m I_n F r)
    (hFinj : Function.Injective F) :
    Manifold.IsImmersion I_m I_n ∞ F := by
  classical
  apply (Manifold.is_immersion_iff_forall_injective_mfderiv hFsmooth).2
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    have hrm : r = m := by
      have hr_le : r ≤ m := constantRank_le_source hFrank
      apply Nat.le_antisymm hr_le
      by_contra hmr
      have hr_lt : r < m := Nat.lt_of_not_ge hmr
      let p : M := Classical.arbitrary M
      obtain ⟨normal, -⟩ :=
        constant_rank_local_coordinate_normal_form hFsmooth hFrank p
      obtain ⟨x, hx, hx_ne, hxker⟩ :=
        exists_ne_zero_mem_rankNormalForm_kernel hr_lt normal.domChart.open_target
          (normal.domChart_centered.2 ▸ normal.domChart.map_source normal.domChart_centered.1)
      let q : M := normal.domChart.symm x
      have hqdom : q ∈ normal.domChart.source := normal.domChart.map_target hx
      have hFqcod : F q ∈ normal.codChart.source := normal.mapsTo hqdom
      have hcoords : normal.codChart (F q) = normal.codChart (F p) := by
        have hnormalzero : rank_normal_form m n r 0 = 0 := by
          ext i
          simp [rank_normal_form]
        calc
          normal.codChart (F q) = rank_normal_form m n r x := by
            simpa [q] using normal.eqOn hx
          _ = 0 := hxker
          _ = rank_normal_form m n r 0 := hnormalzero.symm
          _ = normal.codChart (F p) := by
            have hpEq :=
              normal.eqOn (normal.domChart.map_source normal.domChart_centered.1)
            have hinv : normal.domChart.symm 0 = p := by
              calc
                normal.domChart.symm 0 =
                    normal.domChart.symm (normal.domChart p) := by
                      rw [normal.domChart_centered.2]
                _ = p := normal.domChart.left_inv normal.domChart_centered.1
            simpa [Function.comp_def, hinv, normal.domChart_centered.2] using hpEq.symm
      have hFqp : F q = F p :=
        normal.codChart.injOn hFqcod normal.codChart_centered.1 hcoords
      have hqp : q = p := hFinj hFqp
      have hx0 : x = 0 := by
        calc
          x = normal.domChart q := (normal.domChart.right_inv hx).symm
          _ = normal.domChart p := congrArg normal.domChart hqp
          _ = 0 := normal.domChart_centered.2
      exact hx_ne hx0
    intro p
    letI : FiniteDimensional ℝ (TangentSpace I_m p) := by
      change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin m))
      infer_instance
    apply LinearMap.ker_eq_bot.1
    apply Submodule.finrank_eq_zero.1
    have hp := hFrank.2 p
    rw [Manifold.rankAt_eq_finrank_range_mfderiv] at hp
    have hnullity :=
      LinearMap.finrank_range_add_finrank_ker (mfderiv I_m I_n F p).toLinearMap
    have hnullity' :
      Module.finrank ℝ ((mfderiv I_m I_n F p).toLinearMap.range) +
          Module.finrank ℝ ((mfderiv I_m I_n F p).toLinearMap.ker) = m := by
      have hdim : Module.finrank ℝ (TangentSpace I_m p) = m := by
        change Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m
        exact finrank_euclideanSpace_fin
      exact hnullity.trans hdim
    rw [hp, hrm] at hnullity'
    omega
  · letI : IsEmpty M := not_nonempty_iff.mp hM
    exact fun p ↦ isEmptyElim p

/-- Theorem 4.14 (3) (Global Rank Theorem): a bijective smooth map of constant rank is a
diffeomorphism. -/
-- Proof sketch: combine parts (1) and (2) to obtain that `F` is both a smooth submersion and a
-- smooth immersion, apply Proposition 4.8 to get a smooth local diffeomorphism, and then upgrade
-- the bijective local diffeomorphism to a global diffeomorphism.
theorem constant_rank_bijective_is_diffeomorphism {F : M → N}
    (hFsmooth : ContMDiff I_m I_n ∞ F) (hFrank : Manifold.HasConstantRank I_m I_n F r)
    (hFbij : Function.Bijective F) :
    ∃ Φ : M ≃ₘ⟮I_m, I_n⟯ N, ∀ x : M, Φ x = F x := by
  have hsubmersion :=
    constant_rank_surjective_is_smooth_submersion hFsmooth hFrank hFbij.2
  have himmersion :=
    constant_rank_injective_is_immersion hFsmooth hFrank hFbij.1
  have hlocal : IsLocalDiffeomorph I_m I_n ∞ F :=
    is_local_diffeomorph_iff_is_immersion_and_is_smooth_submersion.mpr
      ⟨himmersion, hsubmersion⟩
  let Φ := hlocal.diffeomorphOfBijective hFbij
  exact ⟨Φ, fun _ ↦ rfl⟩

end GlobalRankTheorem
