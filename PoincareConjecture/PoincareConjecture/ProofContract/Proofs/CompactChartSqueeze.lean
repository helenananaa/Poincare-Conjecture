import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.ChartSupportedHomeomorph
import PoincareConjecture.ProofContract.Proofs.EuclideanBallCompression
import PoincareConjecture.ProofContract.Proofs.BufferedRadiusProfile
import PoincareConjecture.ProofContract.Proofs.RadialHomeomorphLift
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology
theorem compact_subset_coordinate_squeeze {M : ClosedThreeManifold.{u}} (b : CoordinateBall M)
    (K : Set M) (hK : IsCompact K) (hKb : K ⊆ b.removed)
    (V : Set M) (hV : IsOpen V) (h0 : b.parametrization 0 ∈ V) :
    ∃ H : M ≃ₜ M, H '' K ⊆ V ∧ ∀ x : M, x ∉ b.removed → H x = x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hKtarget : K ⊆ b.parametrization.target := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hKb hx
    apply b.parametrization.map_source
    apply b.contains_two
    have hz' : ‖z‖ < 1 := by
      simpa [Metric.mem_ball] using hz
    simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ 2 by linarith)
  let S : Set Euclidean3 := b.parametrization.symm '' K
  have hScompact : IsCompact S := by
    dsimp [S]
    exact hK.image_of_continuousOn
      (b.parametrization.symm.continuousOn.mono hKtarget)
  have hSsubset : S ⊆ Metric.ball 0 1 := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hKb hx
    rw [b.parametrization.left_inv]
    · exact hy
    · apply b.contains_two
      have hy' : ‖y‖ < 1 := by simpa [Metric.mem_ball] using hy
      simpa [Metric.mem_closedBall] using (show ‖y‖ ≤ 2 by linarith)
  by_cases hSempty : S.Nonempty
  · obtain ⟨z, hzS, hzmax⟩ :=
      hScompact.exists_isMaxOn hSempty continuous_norm.continuousOn
    let R : ℝ := ‖z‖
    have hR0 : 0 ≤ R := by
      dsimp [R]
      exact norm_nonneg _
    have hR1 : R < 1 := by
      simpa [R, Metric.mem_ball] using hSsubset hzS
    have hKpre : b.parametrization ⁻¹' V ∈ 𝓝 (0 : Euclidean3) := by
      apply (b.parametrization.continuousAt (b.contains_two (by
        simp [Metric.mem_closedBall]))).preimage_mem_nhds
      exact hV.mem_nhds h0
    obtain ⟨δ, hδ, hδV⟩ :=
      (Metric.mem_nhds_iff (s := b.parametrization ⁻¹' V) (x := (0 : Euclidean3))).mp hKpre
    let a : ℝ := min (1 / 2) (δ / 2)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have ha1 : a < 1 := by
      have ha' : a ≤ (1 / 2 : ℝ) := min_le_left _ _
      linarith
    have haδ : a ≤ δ / 2 := min_le_right _ _
    have haR : a * R < 1 := by
      calc
        a * R < a * 1 := mul_lt_mul_of_pos_left hR1 ha
        _ = a := by ring
        _ < 1 := ha1
    have hcoef : 0 < 1 - a * R := by linarith
    have hden : 0 < 1 - R := by linarith
    let q : ℝ → ℝ := fun s =>
      if s ≤ R then a * s
      else if s ≤ 1 then a * R + (1 - a * R) * ((s - R) / (1 - R))
      else s
    let qinv : ℝ → ℝ := fun t =>
      if t ≤ a * R then t / a
      else if t ≤ 1 then R + (1 - R) * ((t - a * R) / (1 - a * R))
      else t
    have hq : StrictMono q := by
      intro x y hxy
      by_cases hx : x ≤ R
      · by_cases hy : y ≤ R
        · simp only [q, if_pos hx, if_pos hy]
          exact mul_lt_mul_of_pos_left hxy ha
        · have hyR : R < y := lt_of_not_ge hy
          by_cases hy1 : y ≤ 1
          · have hquot : 0 < (y - R) / (1 - R) := by
              exact div_pos (by linarith) hden
            rw [show q x = a * x by simp [q, hx],
              show q y = a * R + (1 - a * R) * ((y - R) / (1 - R)) by
                simp [q, not_le_of_gt hyR, hy1]]
            have hax : a * x ≤ a * R :=
              mul_le_mul_of_nonneg_left hx ha.le
            nlinarith
          · have hy1' : 1 < y := lt_of_not_ge hy1
            rw [show q x = a * x by simp [q, hx],
              show q y = y by simp [q, hy, hy1]]
            have hax : a * x ≤ a * R :=
              mul_le_mul_of_nonneg_left hx ha.le
            nlinarith
      · have hxR : R < x := lt_of_not_ge hx
        have hyR : R < y := lt_trans hxR hxy
        by_cases hx1 : x ≤ 1
        · by_cases hy1 : y ≤ 1
          · have hquot : (x - R) / (1 - R) < (y - R) / (1 - R) := by
              exact div_lt_div_of_pos_right (by linarith) hden
            have hmul := mul_lt_mul_of_pos_left hquot hcoef
            rw [show q x = a * R + (1 - a * R) * ((x - R) / (1 - R)) by
              simp [q, hx, hx1],
              show q y = a * R + (1 - a * R) * ((y - R) / (1 - R)) by
                simp [q, not_le_of_gt hyR, hy1]]
            linarith
          · have hy1' : 1 < y := lt_of_not_ge hy1
            have hquot : (x - R) / (1 - R) ≤ 1 := by
              exact (div_le_iff₀ hden).2 (by linarith)
            have hmul := mul_le_mul_of_nonneg_left hquot hcoef.le
            rw [show q x = a * R + (1 - a * R) * ((x - R) / (1 - R)) by
                simp [q, hx, hx1],
              show q y = y by simp [q, not_le_of_gt hyR, hy1]]
            nlinarith
        · have hx1' : 1 < x := lt_of_not_ge hx1
          have hy1' : 1 < y := lt_trans hx1' hxy
          rw [show q x = x by simp [q, hx, hx1],
            show q y = y by simp [q, not_le_of_gt hyR, hy1']]
          exact hxy
    have hqin : Function.RightInverse qinv q := by
      intro s
      by_cases hs : s ≤ a * R
      · have harg : s / a ≤ R := by
          apply (div_le_iff₀ ha).2
          nlinarith
        rw [show qinv s = s / a by simp [qinv, hs],
          show q (s / a) = a * (s / a) by simp [q, harg]]
        field_simp
      · have hsar : a * R < s := lt_of_not_ge hs
        by_cases hs1 : s ≤ 1
        · have hquotpos : 0 < (s - a * R) / (1 - a * R) :=
            div_pos (by linarith) hcoef
          have hquotle : (s - a * R) / (1 - a * R) ≤ 1 := by
            exact (div_le_iff₀ hcoef).2 (by linarith)
          have harg_low : R <
              R + (1 - R) * ((s - a * R) / (1 - a * R)) := by
            nlinarith
          have harg_high :
              R + (1 - R) * ((s - a * R) / (1 - a * R)) ≤ 1 := by
            nlinarith
          rw [show qinv s = R + (1 - R) * ((s - a * R) / (1 - a * R)) by
              simp [qinv, hs, hs1],
            show q (R + (1 - R) * ((s - a * R) / (1 - a * R))) =
              a * R + (1 - a * R) *
                (((R + (1 - R) * ((s - a * R) / (1 - a * R))) - R) /
                  (1 - R)) by
              simp [q, not_le_of_gt harg_low, harg_high]]
          field_simp
          ring
        · have hs1' : 1 < s := lt_of_not_ge hs1
          have hsR : R < s := lt_trans hR1 hs1'
          rw [show qinv s = s by simp [qinv, hs, hs1],
            show q s = s by simp [q, not_le_of_gt hsR, hs1']]
    let e : ℝ ≃o ℝ := StrictMono.orderIsoOfRightInverse q hq qinv hqin
    have he : (e.toHomeomorph : ℝ → ℝ) = q := by
      rfl
    have hq0 : q 0 = 0 := by
      simp [q, hR0]
    have hqsmall : ∀ s : ℝ, s ≤ R → q s = a * s := by
      intro s hs
      simp [q, hs]
    have hqfix : ∀ s : ℝ, 1 ≤ s → q s = s := by
      intro s hs
      have hsR : ¬ s ≤ R := by linarith
      by_cases hs1 : s ≤ 1
      · have hs_eq : s = 1 := le_antisymm hs1 hs
        subst s
        simp [q, hsR]
        field_simp [hden.ne']
        ring
      · have hs1' : 1 < s := lt_of_not_ge hs1
        simp [q, hsR, hs1']
    obtain ⟨H, hH0, hHrad⟩ :=
      radial_homeomorph_lift e.toHomeomorph (by rw [he]; exact hq) (by rw [he]; exact hq0)
    have hHrad' : ∀ w : Euclidean3, w ≠ 0 →
        H w = (q ‖w‖ / ‖w‖) • w := by
      intro w hw
      simpa [he] using hHrad w hw
    have hHscale : ∀ w : Euclidean3, w ∈ S → H w = a • w := by
      intro w hw
      by_cases hw0 : w = 0
      · rw [hw0, hH0]
        simp
      · rw [hHrad' w hw0, hqsmall ‖w‖ (hzmax hw)]
        field_simp [norm_ne_zero_iff.mpr hw0]
    have hHfix : ∀ w : Euclidean3, 1 ≤ ‖w‖ → H w = w := by
      intro w hw
      by_cases hw0 : w = 0
      · exfalso
        rw [hw0, norm_zero] at hw
        linarith
      · rw [hHrad' w hw0, hqfix ‖w‖ hw]
        field_simp [norm_ne_zero_iff.mpr hw0]
        simp
    obtain ⟨F, hFp, hFtarget⟩ :=
      chart_supported_homeomorph b H (fun w hw => hHfix w (by linarith))
    refine ⟨F, ?_, ?_⟩
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hKb hx
      have hwsrc : w ∈ b.parametrization.source := by
        apply b.contains_two
        have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
        simpa [Metric.mem_closedBall] using (show ‖w‖ ≤ 2 by linarith)
      have hwS : w ∈ S := by
        refine ⟨b.parametrization w, hx, ?_⟩
        rw [b.parametrization.left_inv hwsrc]
      rw [hFp w hwsrc, hHscale w hwS]
      apply hδV
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ha.le]
      have hwR : ‖w‖ ≤ R := hzmax hwS
      have hmul : a * ‖w‖ ≤ a * R :=
        mul_le_mul_of_nonneg_left hwR ha.le
      have hlt : a * R < δ := by nlinarith
      exact hmul.trans_lt hlt
    · intro x hx
      by_cases hxtarget : x ∈ b.parametrization.target
      · let w : Euclidean3 := b.parametrization.symm x
        have hwsrc : w ∈ b.parametrization.source :=
          b.parametrization.symm.map_source hxtarget
        have hxw : b.parametrization w = x :=
          b.parametrization.right_inv hxtarget
        have hw1 : 1 ≤ ‖w‖ := by
          by_contra hw
          apply hx
          refine ⟨w, ?_, hxw⟩
          simpa [Metric.mem_ball] using (lt_of_not_ge hw)
        rw [← hxw, hFp w hwsrc, hHfix w hw1, hxw]
      · exact hFtarget x hxtarget
  · have hKempty : K = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hSempty ⟨b.parametrization.symm x, ⟨x, hx, rfl⟩⟩
    obtain ⟨F, hFp, hFtarget⟩ :=
      chart_supported_homeomorph b (Homeomorph.refl Euclidean3) (by simp)
    refine ⟨F, ?_, ?_⟩
    · simp [hKempty]
    · intro x hx
      by_cases hxtarget : x ∈ b.parametrization.target
      · let w : Euclidean3 := b.parametrization.symm x
        have hwsrc : w ∈ b.parametrization.source :=
          b.parametrization.symm.map_source hxtarget
        have hxw : b.parametrization w = x :=
          b.parametrization.right_inv hxtarget
        rw [← hxw, hFp w hwsrc]
        rfl
      · exact hFtarget x hxtarget
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
