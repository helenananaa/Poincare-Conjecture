import Mathlib
import LeeSmoothLib.Ch03.Sec03_17.Proposition_3_23
import LeeSmoothLib.Ch03.Sec03_17.Proposition_3_24
import LeeSmoothLib.Ch05.Sec05_35.Definition_5_35_extra_2
open Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

section

universe uM

variable {n : ℕ} [NeZero n]
variable {M : Type uM} [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- The distinguished boundary-coordinate component of `v` in the smooth boundary chart `e`.
In Lee's notation this is the `xⁿ`-component; in mathlib's half-space model it is indexed by `0`.
-/
def boundary_coordinate_component (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) (p : M)
    (v : TangentSpace (𝓡∂ n) p) : ℝ :=
  let w : EuclideanSpace ℝ (Fin n) := (mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p) v
  w 0

lemma smoothness_ne_zero : (∞ : ℕ∞ω) ≠ 0 := by simp

lemma atlas_mem_maximalAtlas {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) :
    e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M :=
  IsManifold.subset_maximalAtlas he

lemma mdifferentiableAt_extend {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {q : M} (hq : q ∈ e.source) :
    MDifferentiableAt (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) q :=
  (e.contMDiffAt_extend (atlas_mem_maximalAtlas he) hq).mdifferentiableAt smoothness_ne_zero

lemma mfderiv_extend_eq_id_comp_mfderiv {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {q : M} (hq : q ∈ e.source) :
    mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) q =
      (mfderiv (𝓡∂ n) (𝓡 n) (𝓡∂ n) (e q)).comp (mfderiv (𝓡∂ n) (𝓡∂ n) e q) := by
  have he_md : e.MDifferentiable (𝓡∂ n) (𝓡∂ n) := mdifferentiable_of_mem_atlas he
  have hfun : (e.extend (𝓡∂ n) : M → Eₙ) = (𝓡∂ n) ∘ e :=
    e.extend_coe (I := 𝓡∂ n)
  rw [hfun, mfderiv_comp q (𝓡∂ n).mdifferentiableAt (he_md.mdifferentiableAt hq)]

lemma mfderiv_extend_injective {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {q : M} (hq : q ∈ e.source) :
    Function.Injective (mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) q) := by
  have he_md : e.MDifferentiable (𝓡∂ n) (𝓡∂ n) := mdifferentiable_of_mem_atlas he
  have hinj_e : Function.Injective (mfderiv (𝓡∂ n) (𝓡∂ n) e q) :=
    he_md.mfderiv_injective hq
  have hinj_I : Function.Injective (mfderiv (𝓡∂ n) (𝓡 n) (𝓡∂ n) (e q)) := by
    intro w₁ w₂ hw
    have hid := (𝓡∂ n).hasMFDerivAt.mfderiv (x := e q)
    have hw' : (ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ n) (e q))) w₁ =
        (ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ n) (e q))) w₂ := by
      rw [← hid]; exact hw
    simpa using hw'
  intro v₁ v₂ hv
  apply hinj_e
  apply hinj_I
  have hcomp := mfderiv_extend_eq_id_comp_mfderiv he hq
  have hv' :
      ((mfderiv (𝓡∂ n) (𝓡 n) (𝓡∂ n) (e q)).comp (mfderiv (𝓡∂ n) (𝓡∂ n) e q)) v₁ =
        ((mfderiv (𝓡∂ n) (𝓡 n) (𝓡∂ n) (e q)).comp (mfderiv (𝓡∂ n) (𝓡∂ n) e q)) v₂ := by
    rwa [← hcomp]
  simpa [ContinuousLinearMap.comp_apply] using hv'

lemma extend_target_union_compl_range_mem_nhds
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {q : M} (hq : q ∈ e.source) :
    (e.extend (𝓡∂ n)).target ∪ (range (𝓡∂ n))ᶜ ∈ 𝓝 (e.extend (𝓡∂ n) q) := by
  rw [← nhdsWithin_univ, ← union_compl_self (range (𝓡∂ n)), nhdsWithin_union]
  exact union_mem_sup (e.extend_target_mem_nhdsWithin (I := 𝓡∂ n) hq) self_mem_nhdsWithin

lemma mem_extend_target_of_mem_safe_of_mem_range
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {y : Eₙ}
    (hy_safe : y ∈ (e.extend (𝓡∂ n)).target ∪ (range (𝓡∂ n))ᶜ)
    (hy_range : y ∈ range (𝓡∂ n)) :
    y ∈ (e.extend (𝓡∂ n)).target := by
  rcases hy_safe with hy_target | hy_out
  · exact hy_target
  · exact (hy_out hy_range).elim

lemma extend_fst_eq_zero_of_mem_boundary {p : M}
    (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source) :
    e.extend (𝓡∂ n) p 0 = 0 := by
  have hnotI : ¬ (𝓡∂ n).IsInteriorPoint p :=
    ((𝓡∂ n).isBoundaryPoint_iff_not_isInteriorPoint p).mp hp
  have htarget : e.extend (𝓡∂ n) p ∈ (e.extend (𝓡∂ n)).target :=
    (e.extend (𝓡∂ n)).map_source (by rwa [e.extend_source])
  have hrange : e.extend (𝓡∂ n) p ∈ range (𝓡∂ n) :=
    e.extend_target_subset_range (I := 𝓡∂ n) htarget
  have hnonneg : 0 ≤ (e.extend (𝓡∂ n) p) 0 := by
    rw [range_modelWithCornersEuclideanHalfSpace] at hrange
    exact hrange
  apply le_antisymm ?_ hnonneg
  by_contra hx
  have hpos : 0 < (e.extend (𝓡∂ n) p) 0 := not_le.mp hx
  have hinterior_range : e.extend (𝓡∂ n) p ∈ interior (range (𝓡∂ n)) := by
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    exact hpos
  have hinterior_target : e.extend (𝓡∂ n) p ∈ interior (e.extend (𝓡∂ n)).target :=
    e.mem_interior_extend_target (I := 𝓡∂ n) (e.map_source hpe) hinterior_range
  have hpI : (𝓡∂ n).IsInteriorPoint p :=
    (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := 𝓡∂ n) (n := ∞)
      smoothness_ne_zero he hpe).2 hinterior_target
  exact hnotI hpI

lemma mem_boundary_of_extend_fst_eq_zero {q : M}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hqe : q ∈ e.source)
    (h0 : e.extend (𝓡∂ n) q 0 = 0) :
    q ∈ (𝓡∂ n).boundary M := by
  have hnotI : ¬ (𝓡∂ n).IsInteriorPoint q := by
    intro hqI
    have hinterior_target : e.extend (𝓡∂ n) q ∈ interior (e.extend (𝓡∂ n)).target :=
      (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := 𝓡∂ n) (n := ∞)
        smoothness_ne_zero he hqe).1 hqI
    have hinterior_range : e.extend (𝓡∂ n) q ∈ interior (range (𝓡∂ n)) :=
      e.interior_extend_target_subset_interior_range (I := 𝓡∂ n) hinterior_target
    have hpos : 0 < e.extend (𝓡∂ n) q 0 := by
      rw [interior_range_modelWithCornersEuclideanHalfSpace] at hinterior_range
      exact hinterior_range
    exact (ne_of_gt hpos) h0
  exact ((𝓡∂ n).isBoundaryPoint_iff_not_isInteriorPoint q).2 hnotI

lemma affine_half_space_mapsTo_of_fst (x₀ w : Eₙ) (hx₀ : x₀ 0 = 0) {ε : ℝ} :
    (w 0 = 0 → MapsTo (fun t : ℝ ↦ x₀ + t • w) (Ioo (-ε) ε) (range (𝓡∂ n))) ∧
      (0 < w 0 → MapsTo (fun t : ℝ ↦ x₀ + t • w) (Ico 0 ε) (range (𝓡∂ n))) ∧
      (w 0 < 0 → MapsTo (fun t : ℝ ↦ x₀ + t • w) (Ioc (-ε) 0) (range (𝓡∂ n))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hw0 t _ht
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (x₀ + t • w) 0
    simpa [Pi.add_apply, Pi.smul_apply, hx₀, hw0]
  · intro hwpos t ht
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (x₀ + t • w) 0
    simpa [Pi.add_apply, Pi.smul_apply, hx₀] using mul_nonneg ht.1 hwpos.le
  · intro hwneg t ht
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (x₀ + t • w) 0
    simpa [Pi.add_apply, Pi.smul_apply, hx₀] using
      mul_nonneg_of_nonpos_of_nonpos ht.2 hwneg.le

lemma tangent_transport_mfderiv_extend_eq
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {p : M} {γ : ℝ → M}
    (hγ : γ 0 = p) (ξ : TangentSpace (𝓡∂ n) (γ 0)) :
    mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p (hγ ▸ ξ) =
      mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) (γ 0) ξ := by
  cases hγ
  rfl

lemma extend_symm_realizes_velocity
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {p : M} (hpe : p ∈ e.source)
    (v : TangentSpace (𝓡∂ n) p) {J : Set ℝ} (η : ℝ → Eₙ) (h0 : (0 : ℝ) ∈ J)
    (hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0)
    (hη0 : η 0 = e.extend (𝓡∂ n) p)
    (hη_target : MapsTo η J (e.extend (𝓡∂ n)).target)
    (hη_smooth : ContMDiffOn 𝓘(ℝ) (𝓡 n) ∞ η J)
    (hη_velocity :
      curve_velocityWithin (𝓡 n) η J 0 =
        mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v) :
    let γ : ℝ → M := (e.extend (𝓡∂ n)).symm ∘ η
    ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J ∧
      ∃ hγ : γ 0 = p, hγ ▸ curve_velocityWithin (𝓡∂ n) γ J 0 = v := by
  let γ : ℝ → M := (e.extend (𝓡∂ n)).symm ∘ η
  have hsymm :
      ContMDiffOn (𝓡 n) (𝓡∂ n) ∞ (e.extend (𝓡∂ n)).symm (e.extend (𝓡∂ n)).target := by
    have htarget : (e.extend (𝓡∂ n)).target = (𝓡∂ n) '' e.target :=
      e.extend_target' (I := 𝓡∂ n)
    rw [htarget]
    exact contMDiffOn_extend_symm (atlas_mem_maximalAtlas he)
  have hγ_smooth : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J := by
    simpa [γ, Function.comp] using hsymm.comp hη_smooth hη_target.subset_preimage
  have hγ0 : γ 0 = p := by
    dsimp [γ]
    rw [hη0]
    exact (e.extend (𝓡∂ n)).left_inv (by rwa [e.extend_source])
  have hchart_md : MDifferentiableAt (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) (γ 0) := by
    simpa [hγ0] using mdifferentiableAt_extend he hpe
  have hγ_md : MDifferentiableWithinAt 𝓘(ℝ) (𝓡∂ n) γ J 0 :=
    hγ_smooth.mdifferentiableOn smoothness_ne_zero 0 h0
  have hvelocity_after_chart :
      curve_velocityWithin (𝓡 n) ((e.extend (𝓡∂ n)) ∘ γ) J 0 =
        mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) (γ 0)
          (curve_velocityWithin (𝓡∂ n) γ J 0) :=
    composite_curve_velocity hJ hchart_md hγ_md
  have hchart_eq_eta :
      curve_velocityWithin (𝓡 n) ((e.extend (𝓡∂ n)) ∘ γ) J 0 =
        curve_velocityWithin (𝓡 n) η J 0 := by
    unfold curve_velocityWithin
    convert
      DFunLike.congr_fun
        (mfderivWithin_congr_of_mem
          (I := 𝓘(ℝ)) (I' := 𝓡 n) (s := J) (x := 0)
          (f₁ := (e.extend (𝓡∂ n)) ∘ γ) (f := η)
          (fun t ht ↦ (e.extend (𝓡∂ n)).right_inv (hη_target ht)) h0)
        (show TangentSpace (𝓘(ℝ, ℝ)) (0 : ℝ) from (1 : ℝ)) using 1 <;> rfl
  have hfixed :
      mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p
          (hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ J 0) =
        mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v := by
    exact
      (tangent_transport_mfderiv_extend_eq (e := e) (p := p) (γ := γ) hγ0
          (curve_velocityWithin (𝓡∂ n) γ J 0)).trans
        (hvelocity_after_chart.symm.trans (hchart_eq_eta.trans hη_velocity))
  exact ⟨hγ_smooth, ⟨hγ0, mfderiv_extend_injective he hpe hfixed⟩⟩

lemma one_mem_posTangentConeAt_Ico {ε : ℝ} (hε : 0 < ε) :
    (1 : ℝ) ∈ posTangentConeAt (Ico (0 : ℝ) ε) 0 := by
  rw [one_mem_posTangentConeAt_iff_mem_closure]
  have hI : Ioi (0 : ℝ) ∩ Ico 0 ε = Ioo 0 ε := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.2.2⟩
    · intro hx
      exact ⟨hx.1, ⟨hx.1.le, hx.2⟩⟩
  rw [hI, closure_Ioo (ne_of_lt hε)]
  exact ⟨le_rfl, hε.le⟩

lemma one_mem_posTangentConeAt_Ioo {ε : ℝ} (hε : 0 < ε) :
    (1 : ℝ) ∈ posTangentConeAt (Ioo (-ε) ε) 0 := by
  rw [one_mem_posTangentConeAt_iff_mem_closure]
  have hI : Ioi (0 : ℝ) ∩ Ioo (-ε) ε = Ioo 0 ε := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.2.2⟩
    · intro hx
      exact ⟨hx.1, ⟨by linarith [hx.1], hx.2⟩⟩
  rw [hI, closure_Ioo (ne_of_lt hε)]
  exact ⟨le_rfl, hε.le⟩

lemma Ioo_zero_mem_nhdsGT {ε : ℝ} (hε : 0 < ε) : Ioo (0 : ℝ) ε ∈ 𝓝[>] (0 : ℝ) := by
  have h : Ioi (0 : ℝ) ∩ Iio ε ∈ 𝓝[>] (0 : ℝ) :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hε))
  exact h

lemma neg_one_mem_posTangentConeAt_Ioc {ε : ℝ} (hε : 0 < ε) :
    (-1 : ℝ) ∈ posTangentConeAt (Ioc (-ε) (0 : ℝ)) 0 := by
  refine mem_posTangentConeAt_of_frequently_mem ?_
  exact (eventually_of_mem (Ioo_zero_mem_nhdsGT hε) (fun t ht ↦ by
    have ht' : t • (-1 : ℝ) = -t := by
      rw [smul_eq_mul, mul_neg, mul_one]
    rw [zero_add, ht']
    exact ⟨neg_lt_neg ht.2, neg_nonpos.mpr ht.1.le⟩)).frequently

lemma neg_one_mem_posTangentConeAt_Ioo {ε : ℝ} (hε : 0 < ε) :
    (-1 : ℝ) ∈ posTangentConeAt (Ioo (-ε) ε) 0 := by
  refine mem_posTangentConeAt_of_frequently_mem ?_
  exact (eventually_of_mem (Ioo_zero_mem_nhdsGT hε) (fun t ht ↦ by
    have ht' : t • (-1 : ℝ) = -t := by
      rw [smul_eq_mul, mul_neg, mul_one]
    rw [zero_add, ht']
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)).frequently

lemma isLocalMinOn_of_isMinOn {f : ℝ → ℝ} {s : Set ℝ} {a : ℝ} (h : IsMinOn f s a) :
    IsLocalMinOn f s a :=
  h.filter_mono inf_le_right

lemma hasFDerivWithinAt_coord_comp {η : ℝ → Eₙ} {J : Set ℝ}
    (hη : DifferentiableWithinAt ℝ η J 0) :
    HasFDerivWithinAt (fun t : ℝ ↦ η t 0)
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).comp (fderivWithin ℝ η J 0)) J 0 := by
  have heq : (fun t : ℝ ↦ η t 0) =
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n) : Eₙ → ℝ) ∘ η := by
    funext t
    simp [EuclideanSpace.coe_proj]
  rw [heq]
  exact HasFDerivWithinAt.comp (0 : ℝ) (t := univ)
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).hasFDerivWithinAt (x := η 0))
    hη.hasFDerivWithinAt (mapsTo_univ _ _)

lemma coord_nonneg_of_mapsTo_range {η : ℝ → Eₙ} {J : Set ℝ}
    (hη : MapsTo η J (range (𝓡∂ n))) {t : ℝ} (ht : t ∈ J) :
    0 ≤ η t 0 := by
  have : η t ∈ range (𝓡∂ n) := hη ht
  simpa [range_modelWithCornersEuclideanHalfSpace] using this

lemma boundary_coord_sign_from_model_curve {η : ℝ → Eₙ} {J : Set ℝ}
    (h0 : (0 : ℝ) ∈ J) (hη0 : η 0 0 = 0)
    (hη_range : MapsTo η J (range (𝓡∂ n)))
    (hη_diff : DifferentiableWithinAt ℝ η J 0) :
    (1 ∈ posTangentConeAt J 0 →
        0 ≤ (fderivWithin ℝ η J 0 1) 0) ∧
      ((-1 : ℝ) ∈ posTangentConeAt J 0 →
        (fderivWithin ℝ η J 0 1) 0 ≤ 0) := by
  have hmin : IsMinOn (fun t : ℝ ↦ η t 0) J 0 := by
    intro t ht
    have ht0 : 0 ≤ η t 0 := coord_nonneg_of_mapsTo_range hη_range ht
    simpa [hη0] using ht0
  have hloc : IsLocalMinOn (fun t : ℝ ↦ η t 0) J 0 := isLocalMinOn_of_isMinOn hmin
  have hfderiv := hasFDerivWithinAt_coord_comp hη_diff
  refine ⟨?_, ?_⟩
  · intro h1
    have := hloc.hasFDerivWithinAt_nonneg hfderiv h1
    simpa [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj] using this
  · intro hneg
    have := hloc.hasFDerivWithinAt_nonneg hfderiv hneg
    simpa [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj, map_neg] using this

lemma model_curve_velocity_coord (η : ℝ → Eₙ) (J : Set ℝ) :
    (show Eₙ from curve_velocityWithin (𝓡 n) η J 0) 0 =
      (fderivWithin ℝ η J 0 1) 0 := by
  unfold curve_velocityWithin
  simp [mfderivWithin_eq_fderivWithin]
  rfl

lemma contMDiffOn_extend_comp_curve
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {J : Set ℝ} {γ : ℝ → M}
    (hγ_smooth : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J)
    (hγ_source : MapsTo γ J e.source) :
    ContMDiffOn 𝓘(ℝ) (𝓡 n) ∞ ((e.extend (𝓡∂ n) : M → Eₙ) ∘ γ) J :=
  (e.contMDiffOn_extend (atlas_mem_maximalAtlas he)).comp hγ_smooth
    hγ_source.subset_preimage

lemma differentiableWithinAt_extend_comp_curve
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {J : Set ℝ} {γ : ℝ → M}
    (h0 : (0 : ℝ) ∈ J)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J)
    (hγ_source : MapsTo γ J e.source) :
    DifferentiableWithinAt ℝ ((e.extend (𝓡∂ n) : M → Eₙ) ∘ γ) J 0 := by
  have h := (contMDiffOn_extend_comp_curve he hγ_smooth hγ_source).mdifferentiableOn
    smoothness_ne_zero 0 h0
  exact mdifferentiableWithinAt_iff_differentiableWithinAt.1 h

lemma mapsTo_extend_range_of_mapsTo_source
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {J : Set ℝ} {γ : ℝ → M}
    (hγ_source : MapsTo γ J e.source) :
    MapsTo (fun t ↦ e.extend (𝓡∂ n) (γ t)) J (range (𝓡∂ n)) := by
  intro t ht
  exact e.extend_target_subset_range (I := 𝓡∂ n)
    ((e.extend (𝓡∂ n)).map_source (by
      simpa [OpenPartialHomeomorph.extend_source] using hγ_source ht))

lemma curve_velocity_after_extend
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {p : M} (hpe : p ∈ e.source)
    {J : Set ℝ} {γ : ℝ → M} (h0 : (0 : ℝ) ∈ J)
    (hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0) (hγ0 : γ 0 = p)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J)
    (hγ_source : MapsTo γ J e.source) :
    curve_velocityWithin (𝓡 n) (fun t ↦ e.extend (𝓡∂ n) (γ t)) J 0 =
      mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p
        (hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ J 0) := by
  have hchart_md : MDifferentiableAt (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) (γ 0) := by
    simpa [hγ0] using mdifferentiableAt_extend he hpe
  have hγ_md : MDifferentiableWithinAt 𝓘(ℝ) (𝓡∂ n) γ J 0 :=
    hγ_smooth.mdifferentiableOn smoothness_ne_zero 0 h0
  have hcomp :
      curve_velocityWithin (𝓡 n) ((e.extend (𝓡∂ n)) ∘ γ) J 0 =
        mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) (γ 0)
          (curve_velocityWithin (𝓡∂ n) γ J 0) :=
    composite_curve_velocity hJ hchart_md hγ_md
  have hfun : (fun t ↦ e.extend (𝓡∂ n) (γ t)) = (e.extend (𝓡∂ n)) ∘ γ := rfl
  rw [hfun, hcomp]
  exact (tangent_transport_mfderiv_extend_eq (e := e) hγ0
    (curve_velocityWithin (𝓡∂ n) γ J 0)).symm

lemma exists_Ioo_subset_preimage_source
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {p : M} (hpe : p ∈ e.source)
    {J : Set ℝ} {γ : ℝ → M} (h0 : (0 : ℝ) ∈ J) (hγ0 : γ 0 = p)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J) :
    ∃ δ : ℝ, 0 < δ ∧ MapsTo γ (J ∩ Ioo (-δ) δ) e.source := by
  have hcont : ContinuousWithinAt γ J 0 :=
    hγ_smooth.continuousOn.continuousWithinAt h0
  have hpre : γ ⁻¹' e.source ∈ 𝓝[J] 0 := by
    refine hcont.preimage_mem_nhdsWithin ?_
    simpa [hγ0] using e.open_source.mem_nhds hpe
  rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre) with ⟨u, hu, husub⟩
  rcases mem_nhds_iff_exists_Ioo_subset.mp hu with ⟨a, b, hab, hIab⟩
  have ha : a < 0 := hab.1
  have hb : 0 < b := hab.2
  let δ : ℝ := min (-a) b
  have hδ : 0 < δ := lt_min (neg_pos.mpr ha) hb
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  apply husub
  refine ⟨hIab ?_, ht.1⟩
  have htI : t ∈ Ioo (-δ) δ := ht.2
  constructor
  · have hδa : δ ≤ -a := min_le_left _ _
    have : a ≤ -δ := by linarith
    exact this.trans_lt htI.1
  · exact htI.2.trans_le (min_le_right _ _)

lemma boundary_coord_of_transported_eq
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {p : M}
    {v : TangentSpace (𝓡∂ n) p} :
    boundary_coordinate_component e p v =
      (show Eₙ from mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v) 0 :=
  rfl

/-- The distinguished coordinate of a right half-curve through a boundary point is nonnegative. -/
lemma boundary_coord_nonneg_of_Ico_curve {p : M}
    (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {ε : ℝ} (hε : 0 < ε) {γ : ℝ → M}
    (hγ_smooth : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ (Ico 0 ε))
    (hγ0 : γ 0 = p) :
    0 ≤ boundary_coordinate_component e p
      (hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ (Ico 0 ε) 0) := by
  rcases exists_Ioo_subset_preimage_source hpe (by simp [hε] : (0 : ℝ) ∈ Ico 0 ε) hγ0
      hγ_smooth with ⟨δ, hδ, hmaps⟩
  let J : Set ℝ := Ico 0 ε ∩ Ioo (-δ) δ
  have hJsub : J ⊆ Ico 0 ε := inter_subset_left
  have h0 : (0 : ℝ) ∈ J := ⟨⟨le_rfl, hε⟩, ⟨neg_lt_zero.mpr hδ, hδ⟩⟩
  have hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0 :=
    (uniqueMDiffWithinAt_Ico_zero hε).inter (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hδ, hδ⟩)
  have hγ_smoothJ : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J := hγ_smooth.mono hJsub
  have hγ_source : MapsTo γ J e.source := hmaps
  have hvel :
      curve_velocityWithin (𝓡∂ n) γ J 0 =
        curve_velocityWithin (𝓡∂ n) γ (Ico 0 ε) 0 := by
    unfold curve_velocityWithin
    change mfderivWithin 𝓘(ℝ) (𝓡∂ n) γ (Ico 0 ε ∩ Ioo (-δ) δ) 0 _ =
      mfderivWithin 𝓘(ℝ) (𝓡∂ n) γ (Ico 0 ε) 0 _
    rw [mfderivWithin_inter (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hδ, hδ⟩)]
  have hη0 : ((e.extend (𝓡∂ n) : M → Eₙ) (γ 0)) 0 = 0 := by
    simpa [hγ0] using extend_fst_eq_zero_of_mem_boundary hp he hpe
  have hdiff := differentiableWithinAt_extend_comp_curve he h0 hγ_smoothJ hγ_source
  have hrange := mapsTo_extend_range_of_mapsTo_source (e := e) hγ_source
  have h1 : (1 : ℝ) ∈ posTangentConeAt J 0 := by
    have hpos : 0 < min ε δ := lt_min hε hδ
    have hmem : (1 : ℝ) ∈ posTangentConeAt (Ico (0 : ℝ) (min ε δ)) 0 :=
      one_mem_posTangentConeAt_Ico hpos
    have hsub : Ico (0 : ℝ) (min ε δ) ⊆ J := by
      intro t ht
      refine ⟨⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩, ?_⟩
      constructor
      · exact (neg_lt_zero.mpr hδ).trans_le ht.1
      · exact ht.2.trans_le (min_le_right _ _)
    exact posTangentConeAt_mono hsub hmem
  have hsign :=
    (boundary_coord_sign_from_model_curve (η := (e.extend (𝓡∂ n) : M → Eₙ) ∘ γ)
      h0 hη0 hrange hdiff).1 h1
  have hvel_chart :=
    curve_velocity_after_extend he hpe h0 hJ hγ0 hγ_smoothJ hγ_source
  have hcast :
      hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ (Ico 0 ε) 0 =
        hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ J 0 :=
    congrArg (fun v : TangentSpace (𝓡∂ n) (γ 0) ↦ hγ0 ▸ v) hvel.symm
  have hcoord :
      boundary_coordinate_component e p
          (hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ (Ico 0 ε) 0) =
        (fderivWithin ℝ ((e.extend (𝓡∂ n) : M → Eₙ) ∘ γ) J 0 1) 0 := by
    rw [hcast, boundary_coord_of_transported_eq, ← hvel_chart,
      model_curve_velocity_coord]
    rfl
  rw [hcoord]
  exact hsign

lemma boundary_coord_nonpos_of_Ioc_curve {p : M}
    (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {ε : ℝ} (hε : 0 < ε) {γ : ℝ → M}
    (hγ_smooth : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ (Ioc (-ε) 0))
    (hγ0 : γ 0 = p) :
    boundary_coordinate_component e p
      (hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ (Ioc (-ε) 0) 0) ≤ 0 := by
  rcases exists_Ioo_subset_preimage_source hpe
      (by simp [hε] : (0 : ℝ) ∈ Ioc (-ε) 0) hγ0 hγ_smooth with ⟨δ, hδ, hmaps⟩
  let J : Set ℝ := Ioc (-ε) 0 ∩ Ioo (-δ) δ
  have hJsub : J ⊆ Ioc (-ε) 0 := inter_subset_left
  have h0 : (0 : ℝ) ∈ J := ⟨⟨neg_lt_zero.mpr hε, le_rfl⟩, ⟨neg_lt_zero.mpr hδ, hδ⟩⟩
  have hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0 :=
    (uniqueMDiffWithinAt_Ioc_zero hε).inter (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hδ, hδ⟩)
  have hγ_smoothJ : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J := hγ_smooth.mono hJsub
  have hγ_source : MapsTo γ J e.source := hmaps
  have hvel :
      curve_velocityWithin (𝓡∂ n) γ J 0 =
        curve_velocityWithin (𝓡∂ n) γ (Ioc (-ε) 0) 0 := by
    unfold curve_velocityWithin
    change mfderivWithin 𝓘(ℝ) (𝓡∂ n) γ (Ioc (-ε) 0 ∩ Ioo (-δ) δ) 0 _ =
      mfderivWithin 𝓘(ℝ) (𝓡∂ n) γ (Ioc (-ε) 0) 0 _
    rw [mfderivWithin_inter (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hδ, hδ⟩)]
  have hη0 : ((e.extend (𝓡∂ n) : M → Eₙ) (γ 0)) 0 = 0 := by
    simpa [hγ0] using extend_fst_eq_zero_of_mem_boundary hp he hpe
  have hdiff := differentiableWithinAt_extend_comp_curve he h0 hγ_smoothJ hγ_source
  have hrange := mapsTo_extend_range_of_mapsTo_source (e := e) hγ_source
  have hneg : (-1 : ℝ) ∈ posTangentConeAt J 0 := by
    have hpos : 0 < min ε δ := lt_min hε hδ
    have hmem : (-1 : ℝ) ∈ posTangentConeAt (Ioc (-min ε δ) (0 : ℝ)) 0 :=
      neg_one_mem_posTangentConeAt_Ioc hpos
    have hsub : Ioc (-min ε δ) (0 : ℝ) ⊆ J := by
      intro t ht
      refine ⟨⟨lt_of_le_of_lt (neg_le_neg (min_le_left ε δ)) ht.1, ht.2⟩, ?_⟩
      constructor
      · exact lt_of_le_of_lt (neg_le_neg (min_le_right ε δ)) ht.1
      · exact lt_of_le_of_lt ht.2 hδ
    exact posTangentConeAt_mono hsub hmem
  have hsign :=
    (boundary_coord_sign_from_model_curve (η := (e.extend (𝓡∂ n) : M → Eₙ) ∘ γ)
      h0 hη0 hrange hdiff).2 hneg
  have hvel_chart :=
    curve_velocity_after_extend he hpe h0 hJ hγ0 hγ_smoothJ hγ_source
  have hcast :
      hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ (Ioc (-ε) 0) 0 =
        hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ J 0 :=
    congrArg (fun v : TangentSpace (𝓡∂ n) (γ 0) ↦ hγ0 ▸ v) hvel.symm
  have hcoord :
      boundary_coordinate_component e p
          (hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ (Ioc (-ε) 0) 0) =
        (fderivWithin ℝ ((e.extend (𝓡∂ n) : M → Eₙ) ∘ γ) J 0 1) 0 := by
    rw [hcast, boundary_coord_of_transported_eq, ← hvel_chart,
      model_curve_velocity_coord]
    rfl
  rw [hcoord]
  exact hsign

lemma boundary_coord_eq_zero_of_Ioo_curve {p : M}
    (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {ε : ℝ} (hε : 0 < ε) {γ : ℝ → M}
    (hγ_smooth : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ (Ioo (-ε) ε))
    (hγ0 : γ 0 = p) :
    boundary_coordinate_component e p
      (hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ (Ioo (-ε) ε) 0) = 0 := by
  rcases exists_Ioo_subset_preimage_source hpe
      (⟨neg_lt_zero.mpr hε, hε⟩ : (0 : ℝ) ∈ Ioo (-ε) ε) hγ0 hγ_smooth with ⟨δ, hδ, hmaps⟩
  let J : Set ℝ := Ioo (-ε) ε ∩ Ioo (-δ) δ
  have hJsub : J ⊆ Ioo (-ε) ε := inter_subset_left
  have h0 : (0 : ℝ) ∈ J := ⟨⟨neg_lt_zero.mpr hε, hε⟩, ⟨neg_lt_zero.mpr hδ, hδ⟩⟩
  have hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0 :=
    (isOpen_Ioo.uniqueMDiffWithinAt ⟨neg_lt_zero.mpr hε, hε⟩).inter
      (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hδ, hδ⟩)
  have hγ_smoothJ : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J := hγ_smooth.mono hJsub
  have hγ_source : MapsTo γ J e.source := hmaps
  have hvel :
      curve_velocityWithin (𝓡∂ n) γ J 0 =
        curve_velocityWithin (𝓡∂ n) γ (Ioo (-ε) ε) 0 := by
    unfold curve_velocityWithin
    change mfderivWithin 𝓘(ℝ) (𝓡∂ n) γ (Ioo (-ε) ε ∩ Ioo (-δ) δ) 0 _ =
      mfderivWithin 𝓘(ℝ) (𝓡∂ n) γ (Ioo (-ε) ε) 0 _
    rw [mfderivWithin_inter (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hδ, hδ⟩)]
  have hη0 : ((e.extend (𝓡∂ n) : M → Eₙ) (γ 0)) 0 = 0 := by
    simpa [hγ0] using extend_fst_eq_zero_of_mem_boundary hp he hpe
  have hdiff := differentiableWithinAt_extend_comp_curve he h0 hγ_smoothJ hγ_source
  have hrange := mapsTo_extend_range_of_mapsTo_source (e := e) hγ_source
  have hposδ : 0 < min ε δ := lt_min hε hδ
  have hsub : Ioo (-min ε δ) (min ε δ) ⊆ J := by
    intro t ht
    refine ⟨⟨lt_of_le_of_lt (neg_le_neg (min_le_left ε δ)) ht.1,
        ht.2.trans_le (min_le_left ε δ)⟩,
      ⟨lt_of_le_of_lt (neg_le_neg (min_le_right ε δ)) ht.1,
        ht.2.trans_le (min_le_right ε δ)⟩⟩
  have h1 : (1 : ℝ) ∈ posTangentConeAt J 0 :=
    posTangentConeAt_mono hsub (one_mem_posTangentConeAt_Ioo hposδ)
  have hneg : (-1 : ℝ) ∈ posTangentConeAt J 0 :=
    posTangentConeAt_mono hsub (neg_one_mem_posTangentConeAt_Ioo hposδ)
  have hsigns :=
    boundary_coord_sign_from_model_curve (η := (e.extend (𝓡∂ n) : M → Eₙ) ∘ γ)
      h0 hη0 hrange hdiff
  have hvel_chart :=
    curve_velocity_after_extend he hpe h0 hJ hγ0 hγ_smoothJ hγ_source
  have hcast :
      hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ (Ioo (-ε) ε) 0 =
        hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ J 0 :=
    congrArg (fun v : TangentSpace (𝓡∂ n) (γ 0) ↦ hγ0 ▸ v) hvel.symm
  have hcoord :
      boundary_coordinate_component e p
          (hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ (Ioo (-ε) ε) 0) =
        (fderivWithin ℝ ((e.extend (𝓡∂ n) : M → Eₙ) ∘ γ) J 0 1) 0 := by
    rw [hcast, boundary_coord_of_transported_eq, ← hvel_chart,
      model_curve_velocity_coord]
    rfl
  apply le_antisymm
  · rw [hcoord]
    exact hsigns.2 hneg
  · rw [hcoord]
    exact hsigns.1 h1

lemma exists_affine_line_in_extend_nhds
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {p : M} (hpe : p ∈ e.source)
    (w : Eₙ) :
    ∃ ε : Set.Ioi (0 : ℝ),
      MapsTo (fun t : ℝ ↦ e.extend (𝓡∂ n) p + t • w) (Ioo (-(ε : ℝ)) ε)
        ((e.extend (𝓡∂ n)).target ∪ (range (𝓡∂ n))ᶜ) :=
  affine_line_mapsTo_symmetric_interval_of_mem_nhds _ _
    (extend_target_union_compl_range_mem_nhds hpe)

lemma exists_Ioo_boundary_curve_of_coord_eq_zero {p : M}
    (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p}
    (hv : boundary_coordinate_component e p v = 0) :
    IsBoundaryTangentVector p v := by
  let x₀ : Eₙ := e.extend (𝓡∂ n) p
  let w : Eₙ := mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v
  let η : ℝ → Eₙ := fun t ↦ x₀ + t • w
  have hx₀ : x₀ 0 = 0 := extend_fst_eq_zero_of_mem_boundary hp he hpe
  have hw0 : w 0 = 0 := hv
  rcases exists_affine_line_in_extend_nhds hpe w with ⟨ε, hη_safe⟩
  have hε : 0 < (ε : ℝ) := ε.2
  let J : Set ℝ := Ioo (-(ε : ℝ)) ε
  have h0 : (0 : ℝ) ∈ J := ⟨neg_lt_zero.mpr hε, hε⟩
  have hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0 :=
    isOpen_Ioo.uniqueMDiffWithinAt h0
  have hη0 : η 0 = e.extend (𝓡∂ n) p := by simp [η, x₀]
  have hη_smooth : ContMDiffOn 𝓘(ℝ) (𝓡 n) ∞ η J :=
    (affine_model_curve_contMDiff x₀ w).contMDiffOn
  have hη_range : MapsTo η J (range (𝓡∂ n)) :=
    (affine_half_space_mapsTo_of_fst x₀ w hx₀).1 hw0
  have hη_target : MapsTo η J (e.extend (𝓡∂ n)).target := by
    intro t ht
    exact mem_extend_target_of_mem_safe_of_mem_range (hη_safe ht) (hη_range ht)
  have hη_velocity :
      curve_velocityWithin (𝓡 n) η J 0 =
        mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v := by
    simpa [η, w] using
      affine_model_curve_velocity_within_tangent
        (x₀ := x₀) (w := mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v) hJ
  rcases extend_symm_realizes_velocity he hpe v η h0 hJ hη0 hη_target hη_smooth
      hη_velocity with ⟨hγ_smooth, hγ0, hγv⟩
  refine ⟨ε, hε, (e.extend (𝓡∂ n)).symm ∘ η, hγ_smooth, ?_, ⟨hγ0, hγv⟩⟩
  intro t ht
  have ht_target : η t ∈ (e.extend (𝓡∂ n)).target := hη_target ht
  have hsrc : ((e.extend (𝓡∂ n)).symm ∘ η) t ∈ e.source := by
    have : ((e.extend (𝓡∂ n)).symm ∘ η) t ∈ (e.extend (𝓡∂ n)).source :=
      (e.extend (𝓡∂ n)).map_target ht_target
    simpa [OpenPartialHomeomorph.extend_source] using this
  have hfst : e.extend (𝓡∂ n) (((e.extend (𝓡∂ n)).symm ∘ η) t) 0 = 0 := by
    have hright : e.extend (𝓡∂ n) (((e.extend (𝓡∂ n)).symm) (η t)) = η t :=
      (e.extend (𝓡∂ n)).right_inv ht_target
    rw [Function.comp_apply, hright]
    change (x₀ + t • w) 0 = 0
    simpa [Pi.add_apply, Pi.smul_apply, hx₀, hw0]
  exact mem_boundary_of_extend_fst_eq_zero he hsrc hfst

lemma exists_Ico_curve_of_coord_pos {p : M}
    (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p}
    (hv : 0 < boundary_coordinate_component e p v) :
    HasInwardCurveVelocity p v := by
  let x₀ : Eₙ := e.extend (𝓡∂ n) p
  let w : Eₙ := mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v
  let η : ℝ → Eₙ := fun t ↦ x₀ + t • w
  have hx₀ : x₀ 0 = 0 := extend_fst_eq_zero_of_mem_boundary hp he hpe
  have hwpos : 0 < w 0 := hv
  rcases exists_affine_line_in_extend_nhds hpe w with ⟨ε, hη_safe⟩
  have hε : 0 < (ε : ℝ) := ε.2
  let J : Set ℝ := Ico 0 (ε : ℝ)
  have h0 : (0 : ℝ) ∈ J := ⟨le_rfl, hε⟩
  have hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0 := uniqueMDiffWithinAt_Ico_zero hε
  have hη0 : η 0 = e.extend (𝓡∂ n) p := by simp [η, x₀]
  have hη_smooth : ContMDiffOn 𝓘(ℝ) (𝓡 n) ∞ η J :=
    (affine_model_curve_contMDiff x₀ w).contMDiffOn
  have hη_range : MapsTo η J (range (𝓡∂ n)) :=
    (affine_half_space_mapsTo_of_fst x₀ w hx₀).2.1 hwpos
  have hIco_sub : J ⊆ Ioo (-(ε : ℝ)) ε :=
    Ico_subset_Ioo_left (neg_lt_zero.mpr hε)
  have hη_target : MapsTo η J (e.extend (𝓡∂ n)).target := by
    intro t ht
    exact mem_extend_target_of_mem_safe_of_mem_range (hη_safe (hIco_sub ht)) (hη_range ht)
  have hη_velocity :
      curve_velocityWithin (𝓡 n) η J 0 =
        mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v := by
    simpa [η, w] using
      affine_model_curve_velocity_within_tangent
        (x₀ := x₀) (w := mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v) hJ
  rcases extend_symm_realizes_velocity he hpe v η h0 hJ hη0 hη_target hη_smooth
      hη_velocity with ⟨hγ_smooth, hγ0, hγv⟩
  exact ⟨hp, ε, hε, (e.extend (𝓡∂ n)).symm ∘ η, hγ_smooth, ⟨hγ0, hγv⟩⟩

lemma exists_Ioc_curve_of_coord_neg {p : M}
    (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p}
    (hv : boundary_coordinate_component e p v < 0) :
    HasOutwardCurveVelocity p v := by
  let x₀ : Eₙ := e.extend (𝓡∂ n) p
  let w : Eₙ := mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v
  let η : ℝ → Eₙ := fun t ↦ x₀ + t • w
  have hx₀ : x₀ 0 = 0 := extend_fst_eq_zero_of_mem_boundary hp he hpe
  have hwneg : w 0 < 0 := hv
  rcases exists_affine_line_in_extend_nhds hpe w with ⟨ε, hη_safe⟩
  have hε : 0 < (ε : ℝ) := ε.2
  let J : Set ℝ := Ioc (-(ε : ℝ)) 0
  have h0 : (0 : ℝ) ∈ J := ⟨neg_lt_zero.mpr hε, le_rfl⟩
  have hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0 := uniqueMDiffWithinAt_Ioc_zero hε
  have hη0 : η 0 = e.extend (𝓡∂ n) p := by simp [η, x₀]
  have hη_smooth : ContMDiffOn 𝓘(ℝ) (𝓡 n) ∞ η J :=
    (affine_model_curve_contMDiff x₀ w).contMDiffOn
  have hη_range : MapsTo η J (range (𝓡∂ n)) :=
    (affine_half_space_mapsTo_of_fst x₀ w hx₀).2.2 hwneg
  have hIoc_sub : J ⊆ Ioo (-(ε : ℝ)) ε :=
    Ioc_subset_Ioo_right hε
  have hη_target : MapsTo η J (e.extend (𝓡∂ n)).target := by
    intro t ht
    exact mem_extend_target_of_mem_safe_of_mem_range (hη_safe (hIoc_sub ht)) (hη_range ht)
  have hη_velocity :
      curve_velocityWithin (𝓡 n) η J 0 =
        mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v := by
    simpa [η, w] using
      affine_model_curve_velocity_within_tangent
        (x₀ := x₀) (w := mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p v) hJ
  rcases extend_symm_realizes_velocity he hpe v η h0 hJ hη0 hη_target hη_smooth
      hη_velocity with ⟨hγ_smooth, hγ0, hγv⟩
  exact ⟨hp, ε, hε, (e.extend (𝓡∂ n)).symm ∘ η, hγ_smooth, ⟨hγ0, hγv⟩⟩

lemma boundary_coordinate_component_neg
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) (p : M)
    (v : TangentSpace (𝓡∂ n) p) :
    boundary_coordinate_component e p (-v) = - boundary_coordinate_component e p v := by
  unfold boundary_coordinate_component
  have h :=
    map_neg (mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p) v
  rw [h]
  rfl

/-- Proposition 5.41: in any smooth boundary chart around a boundary point, a tangent vector is
inward-pointing exactly when the distinguished boundary-coordinate component of its chart
representation is positive. -/
theorem tangent_to_boundary_iff_boundary_coordinate_component_eq_zero
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    IsBoundaryTangentVector p v ↔
      boundary_coordinate_component e p v = 0 := by
  constructor
  · intro hv
    rcases hv with ⟨ε, hε, γ, hγ_smooth, _hγ_bd, hγ0, hγv⟩
    have := boundary_coord_eq_zero_of_Ioo_curve hp he hpe hε hγ_smooth hγ0
    rw [hγv] at this
    exact this
  · exact exists_Ioo_boundary_curve_of_coord_eq_zero hp he hpe

theorem inward_pointing_iff_boundary_coordinate_component_pos
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    IsInwardPointing p v ↔
      0 < boundary_coordinate_component e p v := by
  constructor
  · intro hv
    have hnot : ¬ IsBoundaryTangentVector p v := hv.not_isBoundaryTangentVector
    have hin : HasInwardCurveVelocity p v := hv.hasInwardCurveVelocity
    rcases hin with ⟨_hp, ε, hε, γ, hγ_smooth, hγ0, hγv⟩
    have hnonneg := boundary_coord_nonneg_of_Ico_curve hp he hpe hε hγ_smooth hγ0
    have hne : boundary_coordinate_component e p v ≠ 0 := by
      intro h0
      exact hnot ((tangent_to_boundary_iff_boundary_coordinate_component_eq_zero
        hp he hpe).2 h0)
    have hcoord := hnonneg
    rw [hγv] at hcoord
    exact lt_of_le_of_ne hcoord hne.symm
  · intro hvpos
    refine ⟨?_, exists_Ico_curve_of_coord_pos hp he hpe hvpos⟩
    intro htan
    have h0 := (tangent_to_boundary_iff_boundary_coordinate_component_eq_zero
      hp he hpe).1 htan
    exact (ne_of_gt hvpos) h0

-- Proof sketch: the same chart computation identifies outward-pointing vectors with curve germs
-- entering the interior for negative time, which corresponds to a negative distinguished
-- boundary-coordinate component.
/-- The outward-pointing vectors are exactly those whose distinguished boundary-coordinate component
is negative in any smooth boundary chart. -/
theorem outward_pointing_iff_boundary_coordinate_component_neg
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    IsOutwardPointing p v ↔
      boundary_coordinate_component e p v < 0 := by
  constructor
  · intro hv
    have hnot : ¬ IsBoundaryTangentVector p v := hv.not_isBoundaryTangentVector
    have hout : HasOutwardCurveVelocity p v := hv.hasOutwardCurveVelocity
    rcases hout with ⟨_hp, ε, hε, γ, hγ_smooth, hγ0, hγv⟩
    have hnonpos := boundary_coord_nonpos_of_Ioc_curve hp he hpe hε hγ_smooth hγ0
    have hne : boundary_coordinate_component e p v ≠ 0 := by
      intro h0
      exact hnot ((tangent_to_boundary_iff_boundary_coordinate_component_eq_zero
        hp he hpe).2 h0)
    have hcoord := hnonpos
    rw [hγv] at hcoord
    exact lt_of_le_of_ne hcoord hne
  · intro hvneg
    refine ⟨?_, exists_Ioc_curve_of_coord_neg hp he hpe hvneg⟩
    intro htan
    have h0 := (tangent_to_boundary_iff_boundary_coordinate_component_eq_zero
      hp he hpe).1 htan
    exact (ne_of_lt hvneg) h0

-- Proof sketch: combine the three sign characterizations above with the trichotomy
-- `x < 0 ∨ x = 0 ∨ 0 < x` for the distinguished boundary-coordinate component.
/-- Every tangent vector at a boundary point is tangent to the boundary, inward-pointing, or
outward-pointing. -/
theorem boundary_vector_trichotomy
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    IsBoundaryTangentVector p v ∨
      IsInwardPointing p v ∨
      IsOutwardPointing p v := by
  have htri := lt_trichotomy (boundary_coordinate_component e p v) 0
  rcases htri with hneg | h0 | hpos
  · exact Or.inr (Or.inr
      ((outward_pointing_iff_boundary_coordinate_component_neg hp he hpe).2 hneg))
  · exact Or.inl
      ((tangent_to_boundary_iff_boundary_coordinate_component_eq_zero hp he hpe).2 h0)
  · exact Or.inr (Or.inl
      ((inward_pointing_iff_boundary_coordinate_component_pos hp he hpe).2 hpos))

-- Proof sketch: use the sign descriptions of tangent and inward-pointing vectors from boundary
-- coordinates; the distinguished boundary-coordinate component cannot be both zero and positive.
/-- A tangent vector tangent to the boundary is not inward-pointing. -/
theorem tangent_to_boundary_not_inward_pointing
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    ¬ (IsBoundaryTangentVector p v ∧ IsInwardPointing p v) := by
  rintro ⟨htan, hin⟩
  have h0 := (tangent_to_boundary_iff_boundary_coordinate_component_eq_zero hp he hpe).1 htan
  have hpos := (inward_pointing_iff_boundary_coordinate_component_pos hp he hpe).1 hin
  exact (ne_of_gt hpos) h0

-- Proof sketch: use the sign descriptions of tangent and outward-pointing vectors from boundary
-- coordinates; the distinguished boundary-coordinate component cannot be both zero and negative.
/-- A tangent vector tangent to the boundary is not outward-pointing. -/
theorem tangent_to_boundary_not_outward_pointing
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    ¬ (IsBoundaryTangentVector p v ∧ IsOutwardPointing p v) := by
  rintro ⟨htan, hout⟩
  have h0 := (tangent_to_boundary_iff_boundary_coordinate_component_eq_zero hp he hpe).1 htan
  have hneg := (outward_pointing_iff_boundary_coordinate_component_neg hp he hpe).1 hout
  exact (ne_of_lt hneg) h0

-- Proof sketch: use the sign descriptions of inward- and outward-pointing vectors from boundary
-- coordinates; the distinguished boundary-coordinate component cannot be both positive and
-- negative.
/-- An inward-pointing tangent vector is not outward-pointing. -/
theorem inward_pointing_not_outward_pointing
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    ¬ (IsInwardPointing p v ∧ IsOutwardPointing p v) := by
  rintro ⟨hin, hout⟩
  have hpos := (inward_pointing_iff_boundary_coordinate_component_pos hp he hpe).1 hin
  have hneg := (outward_pointing_iff_boundary_coordinate_component_neg hp he hpe).1 hout
  exact (lt_asymm hpos) hneg

-- Proof sketch: reparameterize a witnessing curve by `t ↦ -t`; this flips the sign of the
-- tangent vector and exchanges positive-time interior germs with negative-time interior germs.
/-- A tangent vector is inward-pointing if and only if its negative is outward-pointing. -/
theorem inward_pointing_iff_neg_outward_pointing {p : M} {v : TangentSpace (𝓡∂ n) p} :
    IsInwardPointing p v ↔
      IsOutwardPointing p (-v) := by
  constructor
  · intro hv
    have hp : p ∈ (𝓡∂ n).boundary M := hv.hasInwardCurveVelocity.1
    have he : chartAt (EuclideanHalfSpace n) p ∈ atlas (EuclideanHalfSpace n) M :=
      chart_mem_atlas _ p
    have hpe : p ∈ (chartAt (EuclideanHalfSpace n) p).source := mem_chart_source _ p
    have hpos := (inward_pointing_iff_boundary_coordinate_component_pos hp he hpe).1 hv
    have hcoord := boundary_coordinate_component_neg (chartAt (EuclideanHalfSpace n) p) p v
    exact (outward_pointing_iff_boundary_coordinate_component_neg hp he hpe).2
      (by linarith)
  · intro hv
    have hp : p ∈ (𝓡∂ n).boundary M := hv.hasOutwardCurveVelocity.1
    have he : chartAt (EuclideanHalfSpace n) p ∈ atlas (EuclideanHalfSpace n) M :=
      chart_mem_atlas _ p
    have hpe : p ∈ (chartAt (EuclideanHalfSpace n) p).source := mem_chart_source _ p
    have hneg := (outward_pointing_iff_boundary_coordinate_component_neg hp he hpe).1 hv
    have hcoord := boundary_coordinate_component_neg (chartAt (EuclideanHalfSpace n) p) p v
    exact (inward_pointing_iff_boundary_coordinate_component_pos hp he hpe).2
      (by linarith)

end
