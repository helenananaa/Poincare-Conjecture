import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.C2HolderPointwiseLimit
open Filter
open scoped Topology ContDiff
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- A uniformly bounded C2-Holder sequence with a pointwise value limit retains
actual C2 derivatives and their bounds. Finite-dimensional compactness must be
proved, not replaced by an assumed derivative limit. -/
theorem contDiff_two_of_uniform_holder_pointwise_limit
    (u : ℕ → E3 → E6) (f : E3 → E6)
    (C alpha : ℝ) (hC : 0 ≤ C) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hu : ∀ n, ContDiff ℝ 2 (u n))
    (hbound : ∀ n x, ‖u n x‖ ≤ C ∧ ‖fderiv ℝ (u n) x‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (u n)) x‖ ≤ C)
    (hholder : ∀ n x y,
      ‖fderiv ℝ (fderiv ℝ (u n)) x - fderiv ℝ (fderiv ℝ (u n)) y‖ ≤
        C * ‖x - y‖ ^ alpha)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    ContDiff ℝ 2 f ∧
    (∀ x, ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) ∧
    (∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤
      C * ‖x - y‖ ^ alpha) :=
/- SWARM_PROOF_BEGIN -/
by
  let F₁ := E3 →L[ℝ] E6
  let F₂ := E3 →L[ℝ] F₁
  let J (n : ℕ) (x : E3) : E6 × (F₁ × F₂) :=
    (u n x, (fderiv ℝ (u n) x, fderiv ℝ (fderiv ℝ (u n)) x))
  have hD (n : ℕ) : ContDiff ℝ 1 (fderiv ℝ (u n)) := by
    have hn : ContDiff ℝ (1 + 1 : ℕ∞ω) (u n) := hu n
    exact (contDiff_succ_iff_fderiv.mp hn).2.2
  have hUlip (n : ℕ) : LipschitzWith C.toNNReal (u n) := by
    apply lipschitzWith_of_nnnorm_fderiv_le ((hu n).differentiable (by norm_num))
    intro x
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hC]
    simpa using (hbound n x).2.1
  have hDlip (n : ℕ) : LipschitzWith C.toNNReal (fderiv ℝ (u n)) := by
    apply lipschitzWith_of_nnnorm_fderiv_le ((hD n).differentiable (by norm_num))
    intro x
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hC]
    simpa using (hbound n x).2.2
  let m (d : ℝ) : ℝ := C * d + C * d ^ alpha
  have hm : Tendsto m (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt m 0 := by
      dsimp [m]
      exact (continuousAt_const.mul continuousAt_id).add
        (continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr ha.le)))
    simpa [m, ha.ne'] using hcont.tendsto
  have hJeq : Equicontinuous J :=
    Metric.equicontinuous_of_continuity_modulus m hm J (by
      intro x y n
      have hu' := (hUlip n).dist_le_mul x y
      have hD' := (hDlip n).dist_le_mul x y
      simp only [J, Prod.dist_eq]
      refine max_le ?_ (max_le ?_ ?_)
      · calc
          dist (u n x) (u n y) ≤ (C.toNNReal : ℝ) * dist x y := hu'
          _ = C * dist x y := by rw [Real.coe_toNNReal C hC]
          _ ≤ m (dist x y) := by
            dsimp [m]
            exact le_add_of_nonneg_right (mul_nonneg hC (Real.rpow_nonneg dist_nonneg _))
      · calc
          dist (fderiv ℝ (u n) x) (fderiv ℝ (u n) y) ≤
              (C.toNNReal : ℝ) * dist x y := hD'
          _ = C * dist x y := by rw [Real.coe_toNNReal C hC]
          _ ≤ m (dist x y) := by
            dsimp [m]
            exact le_add_of_nonneg_right (mul_nonneg hC (Real.rpow_nonneg dist_nonneg _))
      · calc
          dist (fderiv ℝ (fderiv ℝ (u n)) x) (fderiv ℝ (fderiv ℝ (u n)) y) =
              ‖fderiv ℝ (fderiv ℝ (u n)) x - fderiv ℝ (fderiv ℝ (u n)) y‖ := by
                rw [dist_eq_norm]
          _ ≤ C * ‖x - y‖ ^ alpha := hholder n x y
          _ ≤ m (dist x y) := by
            dsimp [m]
            exact le_add_of_nonneg_left (mul_nonneg hC dist_nonneg))
  have hJcont (n : ℕ) : Continuous (J n) := by
    have hDcont := (hD n).continuous
    have hHcont := (hD n).continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
    exact (hu n).continuous.prodMk (hDcont.prodMk hHcont)
  have hJbound (n : ℕ) (x : E3) :
      ‖u n x‖ ≤ C ∧ ‖fderiv ℝ (u n) x‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (u n)) x‖ ≤ C := hbound n x
  let B (x : E3) (r : ℝ) (n : ℕ) :
      BoundedContinuousFunction {z : E3 // z ∈ Metric.closedBall x r} (E6 × (F₁ × F₂)) :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun z => J n z.1, (hJcont n).comp continuous_subtype_val⟩ (2 * C) (by
        intro z w
        have hval := hbound n z.1
        have hval' := hbound n w.1
        simp only [J, Prod.dist_eq]
        refine max_le ?_ (max_le ?_ ?_)
        · calc
            dist (u n z.1) (u n w.1) ≤ ‖u n z.1‖ + ‖u n w.1‖ := dist_le_norm_add_norm _ _
            _ ≤ 2 * C := by linarith
        · calc
            dist (fderiv ℝ (u n) z.1) (fderiv ℝ (u n) w.1) ≤
                ‖fderiv ℝ (u n) z.1‖ + ‖fderiv ℝ (u n) w.1‖ := dist_le_norm_add_norm _ _
            _ ≤ 2 * C := by linarith
        · calc
            dist (fderiv ℝ (fderiv ℝ (u n)) z.1) (fderiv ℝ (fderiv ℝ (u n)) w.1) ≤
                ‖fderiv ℝ (fderiv ℝ (u n)) z.1‖ +
                  ‖fderiv ℝ (fderiv ℝ (u n)) w.1‖ := dist_le_norm_add_norm _ _
            _ ≤ 2 * C := by linarith)
  have hJlimit_data (x : E3) (r : ℝ) (hr : 0 < r) :
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ b : BoundedContinuousFunction {z : E3 // z ∈ Metric.closedBall x r}
            (E6 × (F₁ × F₂)), Tendsto (fun n => B x r (φ n)) atTop (𝓝 b) := by
    let K : Set E3 := Metric.closedBall x r
    letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall x r)
    let B' (n : ℕ) : BoundedContinuousFunction K (E6 × (F₁ × F₂)) := B x r n
    let S : Set (E6 × (F₁ × F₂)) :=
      Metric.closedBall 0 C ×ˢ (Metric.closedBall 0 C ×ˢ Metric.closedBall 0 C)
    have hScompact : IsCompact S := by
      exact (isCompact_closedBall (0 : E6) C).prod
        ((isCompact_closedBall (0 : F₁) C).prod
          (isCompact_closedBall (0 : F₂) C))
    have hBinS : ∀ (b : BoundedContinuousFunction K (E6 × (F₁ × F₂))) (z : K),
        b ∈ Set.range B' → b z ∈ S := by
      rintro b z ⟨n, rfl⟩
      change J n z.1 ∈ S
      exact ⟨Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using (hbound n z.1).1),
        ⟨Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using (hbound n z.1).2.1),
          Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using (hbound n z.1).2.2)⟩⟩
    have hBeq : Equicontinuous ((↑) : Set.range B' → K → E6 × (F₁ × F₂)) := by
      have hraw : Equicontinuous (fun (n : ℕ) (z : K) => J n z.1) := by
        convert (equicontinuous_restrict_iff J).2 (hJeq.equicontinuousOn K) using 1
        funext n z
        rfl
      let idx (q : Set.range B') : ℕ := Classical.choose (Set.mem_range.mp q.2)
      convert hraw.comp idx using 1
      funext q z
      have heq : B' (idx q) = (q : BoundedContinuousFunction K (E6 × (F₁ × F₂))) :=
        Classical.choose_spec (Set.mem_range.mp q.2)
      change (q : BoundedContinuousFunction K (E6 × (F₁ × F₂))) z = J (idx q) z.1
      rw [← heq]
      rfl
    have hcompact : IsCompact (closure (Set.range B')) :=
      BoundedContinuousFunction.arzela_ascoli S hScompact (Set.range B') hBinS hBeq
    obtain ⟨b, hb, φ, hφ, hconv⟩ :=
      hcompact.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
    change Tendsto (fun n => B x r (φ n)) atTop (𝓝 b) at hconv
    exact ⟨φ, hφ, b, hconv⟩
  have localResult (x : E3) (r : ℝ) (hr : 0 < r) :
      ∃ G : E3 → F₁, ∃ H : E3 → F₂,
        (∀ y, y ∈ Metric.ball x r → HasFDerivAt f (G y) y) ∧
        (∀ y, y ∈ Metric.ball x r → HasFDerivAt G (H y) y) ∧
        ContinuousOn H (Metric.ball x r) ∧
        (∀ y, y ∈ Metric.ball x r →
          ‖f y‖ ≤ C ∧ ‖G y‖ ≤ C ∧ ‖H y‖ ≤ C) ∧
        (∀ y z, y ∈ Metric.ball x r → z ∈ Metric.ball x r →
          ‖H y - H z‖ ≤ C * ‖y - z‖ ^ alpha) := by
    classical
    obtain ⟨φ, hφ, b, hconv⟩ := hJlimit_data x r hr
    let K : Set E3 := Metric.closedBall x r
    let G (y : E3) : F₁ :=
      if hy : y ∈ K then (b ⟨y, hy⟩).2.1 else 0
    let H (y : E3) : F₂ :=
      if hy : y ∈ K then (b ⟨y, hy⟩).2.2 else 0
    have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have hUniformProjection {γ : Type} [PseudoMetricSpace γ]
        (p : E6 × (F₁ × F₂) → γ)
        (hp : ∀ a b, dist (p a) (p b) ≤ dist a b) :
        TendstoUniformlyOn (fun n z => p (B x r (φ n) z))
          (fun z => p (b z)) atTop Set.univ := by
      rw [Metric.uniformity_basis_dist.tendstoUniformlyOn_iff_of_uniformity]
      intro ε hε
      filter_upwards [(Metric.tendsto_nhds.mp hconv ε hε)] with n hn
      intro z hz
      calc
        dist (p (b z)) (p (B x r (φ n) z)) =
            dist (p (B x r (φ n) z)) (p (b z)) := dist_comm _ _
        _ ≤ dist (B x r (φ n) z) (b z) := hp _ _
        _ ≤ dist (B x r (φ n)) b := BoundedContinuousFunction.dist_coe_le_dist z
        _ < ε := hn
    have hgradK : TendstoUniformlyOn
        (fun n z => (B x r (φ n) z).2.1) (fun z => (b z).2.1) atTop Set.univ := by
      refine hUniformProjection (γ := F₁)
        (p := fun q : E6 × (F₁ × F₂) => q.2.1) ?_
      intro a b
      change dist a.2.1 b.2.1 ≤ max (dist a.1 b.1)
        (max (dist a.2.1 b.2.1) (dist a.2.2 b.2.2))
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hhessK : TendstoUniformlyOn
        (fun n z => (B x r (φ n) z).2.2) (fun z => (b z).2.2) atTop Set.univ := by
      refine hUniformProjection (γ := F₂)
        (p := fun q : E6 × (F₁ × F₂) => q.2.2) ?_
      intro a b
      change dist a.2.2 b.2.2 ≤ max (dist a.1 b.1)
        (max (dist a.2.1 b.2.1) (dist a.2.2 b.2.2))
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    let inc (y : {z : E3 // z ∈ Metric.ball x r}) : {z : E3 // z ∈ K} :=
      ⟨y.1, Metric.ball_subset_closedBall y.2⟩
    have hgradBall : TendstoUniformlyOn
        (fun n y => fderiv ℝ (u (φ n)) y) G atTop (Metric.ball x r) := by
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      rw [← tendstoUniformlyOn_univ]
      have hcomp := hgradK.comp inc
      have heq : Set.EqOn (fun y => (b (inc y)).2.1) (fun y => G y.1) Set.univ := by
        intro y hy
        have hK : y.1 ∈ K := Metric.ball_subset_closedBall y.2
        have hK' : dist y.1 x ≤ r := Metric.mem_closedBall.mp hK
        simp [G, K, inc, hK']
      simpa [inc, B, J, Function.comp_def] using hcomp.congr_right heq
    have hhessBall : TendstoUniformlyOn
        (fun n y => fderiv ℝ (fderiv ℝ (u (φ n))) y) H atTop (Metric.ball x r) := by
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      rw [← tendstoUniformlyOn_univ]
      have hcomp := hhessK.comp inc
      have heq : Set.EqOn (fun y => (b (inc y)).2.2) (fun y => H y.1) Set.univ := by
        intro y hy
        have hK : y.1 ∈ K := Metric.ball_subset_closedBall y.2
        have hK' : dist y.1 x ≤ r := Metric.mem_closedBall.mp hK
        simp [H, K, inc, hK']
      simpa [inc, B, J, Function.comp_def] using hcomp.congr_right heq
    have hGpt (y : E3) (hy : y ∈ Metric.ball x r) :
        Tendsto (fun n => fderiv ℝ (u (φ n)) y) atTop (𝓝 (G y)) := by
      let z : {z : E3 // z ∈ K} := inc ⟨y, hy⟩
      have hz := hgradK.tendsto_at (Set.mem_univ z)
      have hK : y ∈ K := Metric.ball_subset_closedBall hy
      have hK' : dist y x ≤ r := Metric.mem_closedBall.mp hK
      have hEq : G y = (b z).2.1 := by simp [G, K, z, inc, hK']
      rw [hEq]
      simpa [z, inc, B, J] using hz
    have hHpt (y : E3) (hy : y ∈ Metric.ball x r) :
        Tendsto (fun n => fderiv ℝ (fderiv ℝ (u (φ n))) y) atTop (𝓝 (H y)) := by
      let z : {z : E3 // z ∈ K} := inc ⟨y, hy⟩
      have hz := hhessK.tendsto_at (Set.mem_univ z)
      have hK : y ∈ K := Metric.ball_subset_closedBall hy
      have hK' : dist y x ≤ r := Metric.mem_closedBall.mp hK
      have hEq : H y = (b z).2.2 := by simp [H, K, z, inc, hK']
      rw [hEq]
      simpa [z, inc, B, J] using hz
    have hDf : ∀ y, y ∈ Metric.ball x r → HasFDerivAt f (G y) y := by
      intro y hy
      apply hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hgradBall
      · intro n z hz
        exact (((hu (φ n)).differentiable (by norm_num)) z).hasFDerivAt
      · intro z hz
        exact (hlim z).comp hφtop
      · exact hy
    have hDG : ∀ y, y ∈ Metric.ball x r → HasFDerivAt G (H y) y := by
      intro y hy
      apply hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hhessBall
      · intro n z hz
        exact (((hD (φ n)).differentiable (by norm_num)) z).hasFDerivAt
      · intro z hz
        exact hGpt z hz
      · exact hy
    have hHcont : ContinuousOn H (Metric.ball x r) :=
      hhessBall.continuousOn (Frequently.of_forall fun n =>
        (hD (φ n)).continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0) |>.continuousOn)
    have hBounds : ∀ y, y ∈ Metric.ball x r →
        ‖f y‖ ≤ C ∧ ‖G y‖ ≤ C ∧ ‖H y‖ ≤ C := by
      intro y hy
      have hfv := (hlim y).comp hφtop
      have hfnorm := continuous_norm.continuousAt.tendsto.comp hfv
      have hfbound : ‖f y‖ ∈ Set.Iic C :=
        isClosed_Iic.mem_of_tendsto hfnorm (Eventually.of_forall fun n => (hbound (φ n) y).1)
      have hgnorm := continuous_norm.continuousAt.tendsto.comp (hGpt y hy)
      have hgbound : ‖G y‖ ∈ Set.Iic C :=
        isClosed_Iic.mem_of_tendsto hgnorm (Eventually.of_forall fun n => (hbound (φ n) y).2.1)
      have hhnorm := continuous_norm.continuousAt.tendsto.comp (hHpt y hy)
      have hhbound : ‖H y‖ ∈ Set.Iic C :=
        isClosed_Iic.mem_of_tendsto hhnorm (Eventually.of_forall fun n => (hbound (φ n) y).2.2)
      exact ⟨hfbound, by simpa using hgbound, by simpa using hhbound⟩
    have hHholder : ∀ y z, y ∈ Metric.ball x r → z ∈ Metric.ball x r →
        ‖H y - H z‖ ≤ C * ‖y - z‖ ^ alpha := by
      intro y z hy hz
      have hsub := (hHpt y hy).sub (hHpt z hz)
      have hnorm := continuous_norm.continuousAt.tendsto.comp hsub
      have hle : ‖H y - H z‖ ∈ Set.Iic (C * ‖y - z‖ ^ alpha) :=
        isClosed_Iic.mem_of_tendsto hnorm
          (Eventually.of_forall fun n => hholder (φ n) y z)
      simpa using hle
    exact ⟨G, H, hDf, hDG, hHcont, hBounds, hHholder⟩
  have identifyHessian (s : Set E3) (G : E3 → F₁) (H : E3 → F₂)
      (hDf : ∀ z, z ∈ s → HasFDerivAt f (G z) z)
      (hDG : ∀ z, z ∈ s → HasFDerivAt G (H z) z)
      (z : E3) (hz : z ∈ s) (hs : s ∈ 𝓝 z) :
      fderiv ℝ (fderiv ℝ f) z = H z := by
    have hev : (fun q => fderiv ℝ f q) =ᶠ[𝓝 z] G := by
      filter_upwards [hs] with q hq
      exact (hDf q hq).fderiv
    exact ((hDG z hz).congr_of_eventuallyEq hev).fderiv
  have hCD : ContDiff ℝ 2 f := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    obtain ⟨G, H, hDf, hDG, hHcont, _, _⟩ := localResult x 1 (by norm_num)
    let s : Set E3 := Metric.ball x 1
    have hGdiff : DifferentiableOn ℝ G s := by
      intro y hy
      exact (hDG y hy).differentiableAt.differentiableWithinAt
    have hGCD1 : ContDiffOn ℝ 1 G s := by
      rw [show (1 : ℕ∞ω) = 0 + 1 by norm_num,
        contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
      refine ⟨hGdiff, ?_, ?_⟩
      · intro h
        norm_num at h
      · rw [contDiffOn_zero]
        exact hHcont.congr fun y hy => (hDG y hy).fderiv
    have hfDiff : DifferentiableOn ℝ f s := by
      intro y hy
      exact (hDf y hy).differentiableAt.differentiableWithinAt
    have hfderivCD1 : ContDiffOn ℝ 1 (fderiv ℝ f) s :=
      hGCD1.congr fun y hy => (hDf y hy).fderiv
    have hfCD2 : ContDiffOn ℝ 2 f s := by
      rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num,
        contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
      refine ⟨hfDiff, ?_, hfderivCD1⟩
      intro h
      norm_num at h
    exact hfCD2.contDiffAt (Metric.ball_mem_nhds x (by norm_num))
  have hbounds (x : E3) :
      ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := by
    obtain ⟨G, H, hDf, hDG, _, hBounds, _⟩ := localResult x 1 (by norm_num)
    let s : Set E3 := Metric.ball x 1
    have hx : x ∈ s := by simp [s, Metric.mem_ball]
    obtain ⟨hf, hG, hH⟩ := hBounds x hx
    have hGeq := (hDf x hx).fderiv
    have hHeq := identifyHessian s G H hDf hDG x hx (Metric.isOpen_ball.mem_nhds hx)
    exact ⟨hf, by simpa [hGeq] using hG, by simpa [hHeq] using hH⟩
  have hHolderGlobal : ∀ x y,
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤
        C * ‖x - y‖ ^ alpha := by
    intro x y
    let r : ℝ := ‖x‖ + ‖y‖ + 1
    have hr : 0 < r := by dsimp [r]; positivity
    obtain ⟨G, H, hDf, hDG, _, _, hHholder⟩ := localResult 0 r hr
    let s : Set E3 := Metric.ball 0 r
    have hx : x ∈ s := by
      apply Metric.mem_ball.mpr
      dsimp [r]
      simpa using (show ‖x‖ < ‖x‖ + ‖y‖ + 1 by linarith [norm_nonneg y])
    have hy : y ∈ s := by
      apply Metric.mem_ball.mpr
      dsimp [r]
      simpa [add_comm ‖x‖] using (show ‖y‖ < ‖x‖ + ‖y‖ + 1 by linarith [norm_nonneg x])
    have hxeq := identifyHessian s G H hDf hDG x hx (Metric.isOpen_ball.mem_nhds hx)
    have hyeq := identifyHessian s G H hDf hDG y hy (Metric.isOpen_ball.mem_nhds hy)
    simpa [hxeq, hyeq] using hHholder x y hx hy
  exact ⟨hCD, hbounds, hHolderGlobal⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.C2HolderPointwiseLimit
