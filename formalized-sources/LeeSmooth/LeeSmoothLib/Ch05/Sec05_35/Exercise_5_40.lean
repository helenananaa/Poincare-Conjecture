import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import LeeSmoothLib.Ch04.Sec04_21.Exercise_4_4
import LeeSmoothLib.Ch04.Sec04_21.ImmersionDerivative
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_12
import LeeSmoothLib.Ch05.Sec05_35.Notation_5_35_extra_1
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_38

open scoped ContDiff Manifold Topology

section SubmanifoldLevelSetTangent

universe u𝕜 uE uE' uF uH uH' uG uM uN

open Manifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {G : Type uG} [TopologicalSpace G]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S]
variable {K : ModelWithCorners 𝕜 F G} [IsManifold K ∞ N]

omit [TopologicalSpace M] in
/-- Helper for Exercise 5.40: on a global level set `S = Φ ⁻¹' {c}`, membership in `S` is
equivalent to having the same `Φ`-value as any chosen base point of `S`. -/
theorem mem_level_set_iff_eq_basepoint {Φ : M → N} {c : N} {p q : M}
    (hlevel : S = Φ ⁻¹' {c}) (hpS : p ∈ S) :
    q ∈ S ↔ Φ q = Φ p := by
  have hpΦ : Φ p = c := by
    have hpΦmem : Φ p ∈ ({c} : Set N) := by
      change p ∈ Φ ⁻¹' ({c} : Set N)
      simpa [hlevel] using hpS
    exact Set.mem_singleton_iff.mp hpΦmem
  simp [hlevel, hpΦ]

/-- Differentiating the constant composite `Φ ∘ Subtype.val` on a global level set places the
submanifold tangent space inside `ker dΦₚ`. This inclusion is valid over an arbitrary
nontrivially normed field; it does not use a constant-rank normal form. -/
private theorem submanifoldTangentSpace_le_ker_mfderiv_of_level_set
    {Φ : M → N} {c : N} (hΦ : ContMDiff I K ∞ Φ)
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → M))
    (hlevel : S = Φ ⁻¹' {c}) (p : S) :
    T[J; p] ≤ (mfderiv I K Φ (p : M)).ker := by
  let ι : S → M := Subtype.val
  let A := mfderiv J I ι p
  let B := mfderiv I K Φ (p : M)
  have hι_mdiff : MDifferentiableAt J I ι p :=
    (hS.contMDiff.mdifferentiable (by simp)) p
  have hΦ_mdiff : MDifferentiableAt I K Φ (p : M) :=
    hΦ.mdifferentiable (by simp) (p : M)
  have hcomp : mfderiv J K (Φ ∘ ι) p = B.comp A := by
    simpa [A, B, ι] using mfderiv_comp p hΦ_mdiff hι_mdiff
  have hconst : Φ ∘ ι = fun _ : S ↦ Φ (p : M) := by
    funext q
    exact (mem_level_set_iff_eq_basepoint hlevel p.property).mp q.property
  rintro v ⟨w, rfl⟩
  change B (A w) = 0
  change (B.comp A) w = 0
  rw [← hcomp, hconst, mfderiv_const]
  rfl

/-- Exercise 5.40: if `S` is the level set `Φ ⁻¹' {c}` of a smooth map `Φ : M → N` with constant
rank, then for each `p ∈ S` the tangent space of `S` at `p`, viewed inside the ambient tangent
space, is the kernel of `dΦₚ`.

The identification uses injectivity of the inclusion derivative together with rank-nullity and
the stated codimension equation. It does not assume a local normal form. -/
theorem tangentSpace_eq_ker_mfderiv_of_level_set_of_hasConstantRank
    {r : ℕ} {Φ : M → N} {c : N} (hΦ : ContMDiff I K ∞ Φ)
    (hRank : HasConstantRank I K Φ r)
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → M))
    (hcodim : Module.finrank 𝕜 E' + r = Module.finrank 𝕜 E)
    (hlevel : S = Φ ⁻¹' {c}) (p : S) :
    T[J; p] = (mfderiv I K Φ (p : M)).ker := by
  let ι : S → M := Subtype.val
  let A := mfderiv J I ι p
  let B := mfderiv I K Φ (p : M)
  letI : FiniteDimensional 𝕜 (TangentSpace J p) := by
    change FiniteDimensional 𝕜 E'
    infer_instance
  letI : FiniteDimensional 𝕜 (TangentSpace I (p : M)) := by
    change FiniteDimensional 𝕜 E
    infer_instance
  letI : FiniteDimensional 𝕜 (TangentSpace K (Φ (p : M))) := by
    change FiniteDimensional 𝕜 F
    infer_instance
  have hrange_le : A.range ≤ B.ker := by
    simpa [A, B, ι] using
      submanifoldTangentSpace_le_ker_mfderiv_of_level_set
        (I := I) (J := J) (K := K) (S := S) hΦ hS hlevel p
  have hA_inj : Function.Injective A := by
    simpa [A, ι] using hS.isImmersion.mfderiv_injective p
  have hrangeA_finrank : Module.finrank 𝕜 A.range = Module.finrank 𝕜 E' :=
    (LinearMap.finrank_range_of_inj hA_inj).trans (by rfl)
  have hrangeB_finrank : Module.finrank 𝕜 B.range = r := by
    simpa [B, rankAt] using hRank.2 (p : M)
  have hrankNullity := B.toLinearMap.finrank_range_add_finrank_ker
  have hker_finrank : Module.finrank 𝕜 B.ker = Module.finrank 𝕜 E' := by
    have hsum : r + Module.finrank 𝕜 B.ker = Module.finrank 𝕜 E := by
      rw [← hrangeB_finrank]
      exact hrankNullity
    omega
  change A.range = B.ker
  exact Submodule.eq_of_le_of_finrank_eq hrange_le
    (hrangeA_finrank.trans hker_finrank.symm)

end SubmanifoldLevelSetTangent

/-!
The original helper
`exists_local_defining_map_on_nhds_to_fin_of_level_set_of_has_constant_rank`
claimed a constant-rank local defining map to `𝕜^r` over an arbitrary
`NontriviallyNormedField` and arbitrary models with corners. That statement is
false over `ℚ`; a concrete counterexample is recorded in `REPORT.md`.

The mathematically natural correction is the real finite-dimensional
boundaryless Euclidean setting in which the constant-rank theorem
(`constant_rank_local_coordinate_normal_form`, Theorem 4.12) actually applies.
The conclusion is unchanged: a local defining map to `ℝ^r` whose derivative
has the same kernel as `dΦₚ`. Theorem 4.12 is a named pending dependency, not
a completed proof in this module.
-/

noncomputable section

open Set Manifold

universe uM uN

section RealEuclideanConstantRankDefiningMap

variable {m n : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]
variable {S : Set M}

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

namespace Exercise540.ConstantRankDefiningMap

/-- The Euclidean rank-`r` normal form, as a continuous linear map. -/
private def rankNormalFormCLM (m n r : ℕ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun := rank_normal_form m n r
  map_add' := by
    intro x y
    ext i
    by_cases hri : i.1 < r
    · by_cases hmi : i.1 < m
      · simp [rank_normal_form, hri, hmi, PiLp.add_apply]
      · simp [rank_normal_form, hri, hmi, PiLp.add_apply]
    · simp [rank_normal_form, hri, PiLp.add_apply]
  map_smul' := by
    intro c x
    ext i
    by_cases hri : i.1 < r
    · by_cases hmi : i.1 < m
      · simp [rank_normal_form, hri, hmi, PiLp.smul_apply]
      · simp [rank_normal_form, hri, hmi, PiLp.smul_apply]
    · simp [rank_normal_form, hri, PiLp.smul_apply]
  cont := by
    have hcoord :
        Continuous fun x : EuclideanSpace ℝ (Fin m) ↦
          fun i : Fin n ↦
            if i.1 < r then
              if hmi : i.1 < m then x ⟨i.1, hmi⟩ else 0
            else 0 := by
      apply continuous_pi
      intro i
      by_cases hri : i.1 < r
      · by_cases hmi : i.1 < m
        · simpa [hri, hmi] using
            (PiLp.continuous_apply (p := 2) (β := fun _ : Fin m ↦ ℝ) ⟨i.1, hmi⟩)
        · simpa [hri, hmi] using
            (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin m) ↦ (0 : ℝ))
      · simpa [hri] using
          (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin m) ↦ (0 : ℝ))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp hcoord

/-- Projection onto the first `r` coordinates, as a map to `Fin r → ℝ`. -/
private def coordProj (n r : ℕ) (hrn : r ≤ n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin r → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin r ↦ EuclideanSpace.proj (Fin.castLE hrn i)

private theorem coordProj_apply {n r : ℕ} (hrn : r ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin r) :
    coordProj n r hrn x i = x (Fin.castLE hrn i) :=
  rfl

private theorem rankNormalForm_apply_of_lt {m n r : ℕ} {i : Fin n}
    (hri : i.1 < r) (hmi : i.1 < m) (x : EuclideanSpace ℝ (Fin m)) :
    rank_normal_form m n r x i = x ⟨i.1, hmi⟩ := by
  simp [rank_normal_form, hri, hmi]

private theorem rankNormalForm_apply_of_ge {m n r : ℕ} {i : Fin n}
    (hri : ¬ i.1 < r) (x : EuclideanSpace ℝ (Fin m)) :
    rank_normal_form m n r x i = 0 := by
  simp [rank_normal_form, hri]

private theorem coordProj_comp_rankNormalForm_apply {m n r : ℕ}
    (hrm : r ≤ m) (hrn : r ≤ n) (x : EuclideanSpace ℝ (Fin m)) (i : Fin r) :
    (coordProj n r hrn).comp (rankNormalFormCLM m n r) x i =
      x (Fin.castLE hrm i) := by
  have hri : (Fin.castLE hrn i).1 < r := by simp
  have hmi : (Fin.castLE hrn i).1 < m :=
    lt_of_lt_of_le (by simp) hrm
  have hidx : (⟨(Fin.castLE hrn i).1, hmi⟩ : Fin m) = Fin.castLE hrm i := by
    apply Fin.ext
    simp
  calc
    (coordProj n r hrn).comp (rankNormalFormCLM m n r) x i =
        rank_normal_form m n r x (Fin.castLE hrn i) := by
      simp [coordProj_apply, rankNormalFormCLM]
    _ = x ⟨(Fin.castLE hrn i).1, hmi⟩ :=
      rankNormalForm_apply_of_lt hri hmi x
    _ = x (Fin.castLE hrm i) := by rw [hidx]

private theorem coordProj_comp_rankNormalForm_surjective {m n r : ℕ}
    (hrm : r ≤ m) (hrn : r ≤ n) :
    Function.Surjective
      ((coordProj n r hrn).comp (rankNormalFormCLM m n r)) := by
  intro y
  let x : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 fun j : Fin m ↦ if h : (j : ℕ) < r then y ⟨j, h⟩ else 0
  refine ⟨x, ?_⟩
  ext i
  have hx : x (Fin.castLE hrm i) = y i := by
    change (if h : ((Fin.castLE hrm i : Fin m) : ℕ) < r then y ⟨_, h⟩ else 0) = y i
    simp
  simpa [hx] using coordProj_comp_rankNormalForm_apply hrm hrn x i

private theorem rankNormalForm_eq_iff_coordProj {m n r : ℕ}
    (hrm : r ≤ m) (hrn : r ≤ n) (a b : EuclideanSpace ℝ (Fin m)) :
    rank_normal_form m n r a = rank_normal_form m n r b ↔
      coordProj n r hrn (rank_normal_form m n r a) =
        coordProj n r hrn (rank_normal_form m n r b) := by
  constructor
  · intro h
    rw [h]
  · intro h
    ext i
    by_cases hri : i.1 < r
    · have hmi : i.1 < m := lt_of_lt_of_le hri hrm
      let j : Fin r := ⟨i.1, hri⟩
      have hcoord := congrFun h j
      have ha := coordProj_comp_rankNormalForm_apply hrm hrn a j
      have hb := coordProj_comp_rankNormalForm_apply hrm hrn b j
      have hidx : Fin.castLE hrm j = ⟨i.1, hmi⟩ := Fin.ext (by simp [j])
      have hab : a ⟨i.1, hmi⟩ = b ⟨i.1, hmi⟩ := by
        have ha' :
            coordProj n r hrn (rank_normal_form m n r a) j = a (Fin.castLE hrm j) := by
          simpa [rankNormalFormCLM] using ha
        have hb' :
            coordProj n r hrn (rank_normal_form m n r b) j = b (Fin.castLE hrm j) := by
          simpa [rankNormalFormCLM] using hb
        rw [hidx] at ha' hb'
        exact (ha'.symm.trans hcoord).trans hb'
      rw [rankNormalForm_apply_of_lt hri hmi, rankNormalForm_apply_of_lt hri hmi, hab]
    · rw [rankNormalForm_apply_of_ge hri, rankNormalForm_apply_of_ge hri]

/-- A maximal-atlas chart of a smooth Euclidean manifold is a local diffeomorphism. -/
private theorem mdifferentiable_of_mem_maximalAtlas_euclid
    {k : ℕ} {P : Type*} [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) P]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞ P]
    {e : OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin k))}
    (he : e ∈ IsManifold.maximalAtlas (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞ P) :
    e.MDifferentiable (𝓘(ℝ, EuclideanSpace ℝ (Fin k)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) :=
  ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩

end Exercise540.ConstantRankDefiningMap

open Exercise540.ConstantRankDefiningMap

/-- Corrected helper for Exercise 5.40, in the real finite-dimensional boundaryless
Euclidean setting supplied by Theorem 4.12. Near any point of a constant-rank level
set there exists a local defining map to `ℝ^r` whose derivative has the same kernel
as the original map at the base point.

Hypothesis changes relative to the original general-field statement: `𝕜` is
specialized to `ℝ`, and the source/target are finite-dimensional boundaryless
manifolds modelled on `EuclideanSpace ℝ (Fin m)` and `EuclideanSpace ℝ (Fin n)`.
The conclusion is unchanged. The original unrestricted statement is false over
`ℚ`; see `REPORT.md`.

This proof uses `constant_rank_local_coordinate_normal_form` (Theorem 4.12) as a
named pending dependency. -/
theorem exists_local_defining_map_on_nhds_to_fin_of_level_set_of_has_constant_rank
    {r : ℕ} {Φ : M → N} {c : N} (hΦ : ContMDiff I_m I_n ∞ Φ)
    (hRank : HasConstantRank I_m I_n Φ r) (hlevel : S = Φ ⁻¹' {c}) (p : S) :
    ∃ Ψ : M → Fin r → ℝ, ∃ U : Set M, (p : M) ∈ U ∧
      IsLocalDefiningMapOn I_m 𝓘(ℝ, Fin r → ℝ) S U Ψ ∧
      (mfderiv I_m 𝓘(ℝ, Fin r → ℝ) Ψ (p : M)).ker =
        (mfderiv I_m I_n Φ (p : M)).ker := by
  obtain ⟨hNF, -⟩ :=
    constant_rank_local_coordinate_normal_form (F := Φ) hΦ hRank (p : M)
  letI : FiniteDimensional ℝ (TangentSpace I_m (p : M)) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin m))
    infer_instance
  letI : FiniteDimensional ℝ (TangentSpace I_n (Φ (p : M))) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n))
    infer_instance
  have hrm : r ≤ m := by
    have hr : Module.finrank ℝ ((mfderiv I_m I_n Φ (p : M)).range) = r :=
      hRank.2 (p : M)
    have hle :=
      LinearMap.finrank_range_le (mfderiv I_m I_n Φ (p : M)).toLinearMap
    have hsrc : Module.finrank ℝ (TangentSpace I_m (p : M)) = m := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m
      exact finrank_euclideanSpace_fin
    calc
      r = Module.finrank ℝ ((mfderiv I_m I_n Φ (p : M)).range) := hr.symm
      _ ≤ Module.finrank ℝ (TangentSpace I_m (p : M)) := hle
      _ = m := hsrc
  have hrn : r ≤ n := by
    have hr : Module.finrank ℝ ((mfderiv I_m I_n Φ (p : M)).range) = r :=
      hRank.2 (p : M)
    have hle := Submodule.finrank_le (mfderiv I_m I_n Φ (p : M)).range
    have htgt : Module.finrank ℝ (TangentSpace I_n (Φ (p : M))) = n := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
      exact finrank_euclideanSpace_fin
    calc
      r = Module.finrank ℝ ((mfderiv I_m I_n Φ (p : M)).range) := hr.symm
      _ ≤ Module.finrank ℝ (TangentSpace I_n (Φ (p : M))) := hle
      _ = n := htgt
  let π := coordProj n r hrn
  let L := π.comp (rankNormalFormCLM m n r)
  let Ψ : M → Fin r → ℝ := fun q ↦ π (hNF.codChart (Φ q))
  let U : Set M := hNF.domChart.source
  have hpU : (p : M) ∈ U := hNF.domChart_centered.1
  have hUopen : IsOpen U := hNF.domChart.open_source
  have hΨ_eqOn : EqOn Ψ (L ∘ hNF.domChart) U := by
    intro q hq
    have hx := hNF.eqOn (hNF.domChart.map_source hq)
    have hinv : hNF.domChart.symm (hNF.domChart q) = q := hNF.domChart.left_inv hq
    have hchart : hNF.codChart (Φ q) = rank_normal_form m n r (hNF.domChart q) := by
      simpa [Function.comp, hinv] using hx
    simp [Ψ, L, π, hchart, rankNormalFormCLM]
  have hdomMD :=
    mdifferentiable_of_mem_maximalAtlas_euclid (k := m) hNF.domChart_mem_maximalAtlas
  have hcodMD :=
    mdifferentiable_of_mem_maximalAtlas_euclid (k := n) hNF.codChart_mem_maximalAtlas
  have hΨsmooth : ContMDiffOn I_m 𝓘(ℝ, Fin r → ℝ) ∞ Ψ U := by
    have hL : ContMDiff I_m 𝓘(ℝ, Fin r → ℝ) ∞ L := L.contMDiff
    have hdom : ContMDiffOn I_m I_m ∞ hNF.domChart U :=
      contMDiffOn_of_mem_maximalAtlas hNF.domChart_mem_maximalAtlas
    exact (hL.comp_contMDiffOn hdom).congr fun q hq ↦ hΨ_eqOn hq
  have hmem : ∀ {p' q : M}, p' ∈ S → p' ∈ U → q ∈ U → (q ∈ S ↔ Ψ q = Ψ p') := by
    intro p' q hp'S hp'U hqU
    have hΦiff : q ∈ S ↔ Φ q = Φ p' :=
      mem_level_set_iff_eq_basepoint (S := S) (Φ := Φ) (c := c) hlevel hp'S
    have hqΦ : Φ q ∈ hNF.codChart.source := hNF.mapsTo hqU
    have hp'Φ : Φ p' ∈ hNF.codChart.source := hNF.mapsTo hp'U
    have hchart_q : hNF.codChart (Φ q) =
        rank_normal_form m n r (hNF.domChart q) := by
      have hx := hNF.eqOn (hNF.domChart.map_source hqU)
      have hinv : hNF.domChart.symm (hNF.domChart q) = q :=
        hNF.domChart.left_inv hqU
      simpa [Function.comp, hinv] using hx
    have hchart_p' : hNF.codChart (Φ p') =
        rank_normal_form m n r (hNF.domChart p') := by
      have hx := hNF.eqOn (hNF.domChart.map_source hp'U)
      have hinv : hNF.domChart.symm (hNF.domChart p') = p' :=
        hNF.domChart.left_inv hp'U
      simpa [Function.comp, hinv] using hx
    constructor
    · intro hqS
      have hΦeq : Φ q = Φ p' := hΦiff.mp hqS
      simp [Ψ, hΦeq]
    · intro hΨeq
      apply hΦiff.mpr
      apply hNF.codChart.injOn hqΦ hp'Φ
      have hπeq :
          π (rank_normal_form m n r (hNF.domChart q)) =
            π (rank_normal_form m n r (hNF.domChart p')) := by
        simpa [Ψ, hchart_q, hchart_p'] using hΨeq
      have hrank :=
        (rankNormalForm_eq_iff_coordProj hrm hrn
          (hNF.domChart q) (hNF.domChart p')).2 hπeq
      simpa [hchart_q, hchart_p'] using hrank
  have hsurj : ∀ q : M, q ∈ U →
      Function.Surjective (mfderiv I_m 𝓘(ℝ, Fin r → ℝ) Ψ q) := by
    intro q hq
    have hEq : Ψ =ᶠ[𝓝 q] (L ∘ hNF.domChart) :=
      hΨ_eqOn.eventuallyEq_of_mem (hUopen.mem_nhds hq)
    have hLmd : MDifferentiableAt I_m 𝓘(ℝ, Fin r → ℝ) L (hNF.domChart q) :=
      L.mdifferentiableAt
    have hdommd : MDifferentiableAt I_m I_m hNF.domChart q :=
      hdomMD.mdifferentiableAt hq
    have hcomp :
        mfderiv I_m 𝓘(ℝ, Fin r → ℝ) (L ∘ hNF.domChart) q =
          (mfderiv I_m 𝓘(ℝ, Fin r → ℝ) L (hNF.domChart q)).comp
            (mfderiv I_m I_m hNF.domChart q) :=
      mfderiv_comp q hLmd hdommd
    have hLderiv : mfderiv I_m 𝓘(ℝ, Fin r → ℝ) L (hNF.domChart q) = L :=
      L.mfderiv_eq
    have hΨderiv :
        mfderiv I_m 𝓘(ℝ, Fin r → ℝ) Ψ q =
          L.comp (mfderiv I_m I_m hNF.domChart q) := by
      rw [hEq.mfderiv_eq, hcomp, hLderiv]
    rw [hΨderiv]
    exact (coordProj_comp_rankNormalForm_surjective hrm hrn).comp
      (hdomMD.mfderiv_surjective hq)
  refine ⟨Ψ, U, hpU, ?_, ?_⟩
  · exact
      { isOpen_source := hUopen
        smoothOn := hΨsmooth
        mem_iff_eq := hmem
        surjective_mfderiv := fun {q} hq ↦ hsurj q hq }
  · -- Kernel identity at the base point: in the rank charts, `dΨₚ = L ∘ dφₚ`
    -- and `d(codChart ∘ Φ)ₚ = rank_normal_form ∘ dφₚ`. Thus `ker dΦₚ ≤ ker dΨₚ`,
    -- and both kernels have dimension `m - r`.
    let A := mfderiv I_m 𝓘(ℝ, Fin r → ℝ) Ψ (p : M)
    let B := mfderiv I_m I_n Φ (p : M)
    letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, Fin r → ℝ) (Ψ (p : M))) := by
      change FiniteDimensional ℝ (Fin r → ℝ)
      infer_instance
    have hΦmd : MDifferentiableAt I_m I_n Φ (p : M) :=
      hΦ.mdifferentiable (by simp) (p : M)
    have hcodmd : MDifferentiableAt I_n I_n hNF.codChart (Φ (p : M)) :=
      hcodMD.mdifferentiableAt hNF.codChart_centered.1
    have hLmd : MDifferentiableAt I_m 𝓘(ℝ, Fin r → ℝ) L (hNF.domChart (p : M)) :=
      L.mdifferentiableAt
    have hdommd : MDifferentiableAt I_m I_m hNF.domChart (p : M) :=
      hdomMD.mdifferentiableAt hpU
    have hRmd : MDifferentiableAt I_m I_n (rankNormalFormCLM m n r)
        (hNF.domChart (p : M)) :=
      (rankNormalFormCLM m n r).mdifferentiableAt
    have hAderiv :
        mfderiv I_m 𝓘(ℝ, Fin r → ℝ) Ψ (p : M) =
          L.comp (mfderiv I_m I_m hNF.domChart (p : M)) := by
      have hEq : Ψ =ᶠ[𝓝 (p : M)] (L ∘ hNF.domChart) :=
        hΨ_eqOn.eventuallyEq_of_mem (hUopen.mem_nhds hpU)
      have hcomp := mfderiv_comp (p : M) hLmd hdommd
      have hLderiv : mfderiv I_m 𝓘(ℝ, Fin r → ℝ) L (hNF.domChart (p : M)) = L :=
        L.mfderiv_eq
      rw [hEq.mfderiv_eq, hcomp, hLderiv]
    have hΦchart :
        mfderiv I_m I_n (hNF.codChart ∘ Φ) (p : M) =
          (rankNormalFormCLM m n r).comp
            (mfderiv I_m I_m hNF.domChart (p : M)) := by
      have hEq : EqOn (hNF.codChart ∘ Φ)
          (⇑(rankNormalFormCLM m n r) ∘ hNF.domChart) U := by
        intro q hq
        have hx := hNF.eqOn (hNF.domChart.map_source hq)
        have hinv : hNF.domChart.symm (hNF.domChart q) = q :=
          hNF.domChart.left_inv hq
        simpa [Function.comp, hinv, rankNormalFormCLM] using hx
      have hEventually := hEq.eventuallyEq_of_mem (hUopen.mem_nhds hpU)
      have hcomp := mfderiv_comp (p : M) hRmd hdommd
      have hRderiv : mfderiv I_m I_n (rankNormalFormCLM m n r)
          (hNF.domChart (p : M)) = rankNormalFormCLM m n r :=
        (rankNormalFormCLM m n r).mfderiv_eq
      rw [hEventually.mfderiv_eq, hcomp, hRderiv]
    have hle : B.ker ≤ A.ker := by
      intro v hv
      have hBv : B v = 0 := hv
      have hcodΦ :
          (mfderiv I_m I_n (hNF.codChart ∘ Φ) (p : M)) v = 0 := by
        have hcomp := mfderiv_comp (p : M) hcodmd hΦmd
        have hcompv := congrArg (fun f => f v) hcomp
        have hrhs :
            ((mfderiv I_n I_n hNF.codChart (Φ (p : M))).comp B) v = 0 := by
          rw [ContinuousLinearMap.comp_apply, hBv, map_zero]
        exact hcompv.trans hrhs
      have hLchart :
          L.comp (mfderiv I_m I_m hNF.domChart (p : M)) =
            π.comp (mfderiv I_m I_n (hNF.codChart ∘ Φ) (p : M)) := by
        simp only [L]
        exact
          (ContinuousLinearMap.comp_assoc π (rankNormalFormCLM m n r)
              (mfderiv I_m I_m hNF.domChart (p : M))).trans
            (congrArg (ContinuousLinearMap.comp π) hΦchart.symm)
      have hAv := congrArg (fun f => f v) hAderiv
      have hLv := congrArg (fun f => f v) hLchart
      have hπ0 := congrArg (fun w => π w) hcodΦ
      change A v = 0
      dsimp [A]
      exact (hAv.trans hLv).trans (hπ0.trans (map_zero π))
    have hAsurj : Function.Surjective A := hsurj (p : M) hpU
    have hrangeA : A.range = ⊤ := LinearMap.range_eq_top.mpr hAsurj
    have hrankA := A.toLinearMap.finrank_range_add_finrank_ker
    have hfinΨ : Module.finrank ℝ (TangentSpace 𝓘(ℝ, Fin r → ℝ) (Ψ (p : M))) = r := by
      change Module.finrank ℝ (Fin r → ℝ) = r
      simp
    have hfinM : Module.finrank ℝ (TangentSpace I_m (p : M)) = m := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m
      exact finrank_euclideanSpace_fin
    have hkerA : Module.finrank ℝ A.ker = m - r := by
      have hsum_aux :
          Module.finrank ℝ (TangentSpace 𝓘(ℝ, Fin r → ℝ) (Ψ (p : M))) +
              Module.finrank ℝ A.ker =
            m := by
        have h' := hrankA
        rw [hrangeA, finrank_top] at h'
        exact h'.trans hfinM
      have hsum : r + Module.finrank ℝ A.ker = m := by
        convert hsum_aux
        exact hfinΨ.symm
      omega
    have hrangeB : Module.finrank ℝ B.range = r := by
      simpa [B, rankAt] using hRank.2 (p : M)
    have hrankB := B.toLinearMap.finrank_range_add_finrank_ker
    have hkerB : Module.finrank ℝ B.ker = m - r := by
      have hsum_aux : Module.finrank ℝ B.range + Module.finrank ℝ B.ker = m :=
        hrankB.trans hfinM
      have hsum : r + Module.finrank ℝ B.ker = m := by
        convert hsum_aux
        exact hrangeB.symm
      omega
    exact (Submodule.eq_of_le_of_finrank_eq hle (hkerB.trans hkerA.symm)).symm

end RealEuclideanConstantRankDefiningMap

end
