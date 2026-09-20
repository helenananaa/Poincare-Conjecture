import Mathlib
import LeeSmoothLib.Ch03.Sec03_14.Proposition_3_6
import LeeSmoothLib.Ch04.Sec04_21.Exercise_4_4
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_12
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16
import LeeSmoothLib.Verified.LevelSets.ModelTransport

/-!
Discrete-fiber corollary of the real rank theorem 4.12, used by Proposition 7.17
to replace the false analytic level-set owner on the identity fiber.
-/

open scoped ContDiff Manifold Topology
open Manifold Set Filter

noncomputable section

namespace LeeVerifiedLevelSets.InjectiveRank

universe uE uH uM uE' uH' uN

section RankBounds

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

omit [FiniteDimensional 𝕜 E'] in
lemma rankAt_le_sourceFinrank (f : M → N) (p : M) :
    rankAt I J f p ≤ Module.finrank 𝕜 E := by
  letI : FiniteDimensional 𝕜 (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional 𝕜 E)
  have hdim : Module.finrank 𝕜 (TangentSpace I p) = Module.finrank 𝕜 E := rfl
  simpa [rankAt] using
    (LinearMap.finrank_range_le (mfderiv I J f p).toLinearMap).trans_eq hdim

omit [FiniteDimensional 𝕜 E] in
lemma rankAt_le_targetFinrank (f : M → N) (p : M) :
    rankAt I J f p ≤ Module.finrank 𝕜 E' := by
  letI : FiniteDimensional 𝕜 (TangentSpace J (f p)) :=
    inferInstanceAs (FiniteDimensional 𝕜 E')
  have hdim : Module.finrank 𝕜 (TangentSpace J (f p)) = Module.finrank 𝕜 E' := rfl
  simpa [rankAt] using
    (Submodule.finrank_le ((mfderiv I J f p).toLinearMap.range)).trans_eq hdim

end RankBounds

section EuclideanFiber

variable {m n r : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]

local notation "I_m" => 𝓡 m
local notation "I_n" => 𝓡 n

lemma exists_ne_zero_mem_rankNormalForm_kernel (hrm : r < m)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U)
    (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ U) :
    ∃ x ∈ U, x ≠ 0 ∧ rank_normal_form m n r x = 0 := by
  let i : Fin m := ⟨r, hrm⟩
  let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (Pi.single i 1)
  have hv_ne : v ≠ 0 := by
    intro hv
    have hvi := congrArg (fun z : EuclideanSpace ℝ (Fin m) ↦ z i) hv
    simp [v] at hvi
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
    Filter.nonempty_of_mem (Filter.inter_mem hpre (self_mem_nhdsWithin : {c : ℝ | IsUnit c} ∈ _))
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

lemma rank_eq_sourceDim_of_injective_constantRank
    {F : M → N} (hFsmooth : ContMDiff I_m I_n ∞ F)
    (hFrank : HasConstantRank I_m I_n F r) (hFinj : Function.Injective F)
    (p : M) : r = m := by
  classical
  have hr_le : r ≤ m := by
    have hdimE : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
    have hrank := rankAt_le_sourceFinrank (I := I_m) (J := I_n) F p
    have : rankAt I_m I_n F p ≤ m := by simpa [hdimE] using hrank
    simpa [hFrank.2 p] using this
  apply Nat.le_antisymm hr_le
  by_contra hmr
  have hr_lt : r < m := Nat.lt_of_not_ge hmr
  obtain ⟨normal, -⟩ := constant_rank_local_coordinate_normal_form hFsmooth hFrank p
  obtain ⟨x, hx, hx_ne, hxker⟩ :=
    exists_ne_zero_mem_rankNormalForm_kernel (n := n) hr_lt normal.domChart.open_target
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

omit [IsManifold (𝓡 m) ∞ M] [IsManifold (𝓡 n) ∞ N] in
lemma injective_mfderiv_of_rank_eq_sourceDim
    {F : M → N} {p : M} (hRankp : rankAt I_m I_n F p = m) :
    Function.Injective (mfderiv I_m I_n F p) := by
  letI : FiniteDimensional ℝ (TangentSpace I_m p) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin m))
    infer_instance
  have hRangeFinrank :
      Module.finrank ℝ ((mfderiv I_m I_n F p).toLinearMap.range) = m := by
    simpa [rankAt] using hRankp
  have hNullity := LinearMap.finrank_range_add_finrank_ker (mfderiv I_m I_n F p).toLinearMap
  have hdim : Module.finrank ℝ (TangentSpace I_m p) = m := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m
    exact finrank_euclideanSpace_fin
  have hKerFinrank :
      Module.finrank ℝ ((mfderiv I_m I_n F p).toLinearMap.ker) = 0 := by
    have : Module.finrank ℝ ((mfderiv I_m I_n F p).toLinearMap.range) +
        Module.finrank ℝ ((mfderiv I_m I_n F p).toLinearMap.ker) = m :=
      hNullity.trans hdim
    omega
  have hKerBot : ((mfderiv I_m I_n F p).toLinearMap.ker) = ⊥ :=
    Submodule.finrank_eq_zero.1 hKerFinrank
  exact (LinearMap.ker_eq_bot).1 hKerBot

end EuclideanFiber

section GeneralRealModels

variable {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

open LeeVerifiedLevelSets.ModelTransport

/-- An injective constant-rank map has full source rank. This is local: no global
Hausdorff or countability hypothesis, or analytic level-set structure, is used. -/
theorem rank_eq_source_finrank_of_injective {f : M → N} {r : ℕ}
    (hf : ContMDiff I J ∞ f) (hr : HasConstantRank I J f r)
    (hinj : Function.Injective f) (p : M) : r = Module.finrank ℝ E := by
  letI := euclideanRechartChartedSpace (I := I) (M := M)
  letI := euclideanRechartChartedSpace (I := J) (M := N)
  letI := euclideanRechart_isManifold (I := I) (M := M)
  letI := euclideanRechart_isManifold (I := J) (M := N)
  have hi : Function.Injective (rechartMap f) := by
    intro x y hxy
    apply EuclideanRechart.ext
    exact hinj (congrArg EuclideanRechart.val hxy)
  exact rank_eq_sourceDim_of_injective_constantRank
    (contMDiff_rechartMap hf) (hasConstantRank_rechartMap hf hr) hi (EuclideanRechart.mk p)

end GeneralRealModels
end LeeVerifiedLevelSets.InjectiveRank
