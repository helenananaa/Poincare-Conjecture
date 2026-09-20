import PoincareConjecture.ParallelMath.Core

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath
open Set Filter
open scoped Topology

/-- Blueprint `lem:forward-dini-mean-value`: a continuous scalar that increases
on `[c,d]` has a point of strictly positive upper-right slope. -/
theorem exists_pos_forwardDiff_of_increase (q : ℝ → ℝ) {c d : ℝ}
    (hcd : c < d) (hq : ContinuousOn q (Icc c d)) (hin : q c < q d) :
    ∃ s ∈ Ico c d,
      ∃ η : ℝ, 0 < η ∧ ∀ᶠ h in 𝓝[>] (0 : ℝ), η ≤ (q (s + h) - q s) / h :=
/- SWARM_PROOF_BEGIN -/
by
  have hden : 0 < d - c := sub_pos.mpr hcd
  have havg : 0 < (q d - q c) / (d - c) := div_pos (sub_pos.mpr hin) hden
  set η : ℝ := (q d - q c) / (d - c) / 2
  have hηpos : 0 < η := half_pos havg
  have hηlt : η < (q d - q c) / (d - c) := half_lt_self havg
  set φ : ℝ → ℝ := fun t => q t - η * (t - c)
  have hφcont : ContinuousOn φ (Icc c d) :=
    hq.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  obtain ⟨s, hsIcc, hsmin⟩ : ∃ s ∈ Icc c d, ∀ x ∈ Icc c d, φ s ≤ φ x :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hcd.le) hφcont
  have hφc : φ c = q c := by simp [φ]
  have hφcd : φ c < φ d := by
    have hmul : η * (d - c) < q d - q c := (lt_div_iff₀ hden).mp hηlt
    simp only [φ, hφc]
    linarith
  have hsIco : s ∈ Ico c d := by
    refine ⟨hsIcc.1, lt_of_le_of_ne hsIcc.2 ?_⟩
    intro hsd
    have hle : φ s ≤ φ c := hsmin c (left_mem_Icc.mpr hcd.le)
    rw [hsd] at hle
    exact hle.not_gt hφcd
  refine ⟨s, hsIco, η, hηpos, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hsIco.2)] with h hh
  have hsph : s + h ∈ Icc c d :=
    ⟨(le_add_of_nonneg_right hh.1.le).trans' hsIcc.1, le_of_lt (by linarith [hh.2])⟩
  have hge : η * h ≤ q (s + h) - q s := by
    have := hsmin (s + h) hsph
    simp only [φ] at this
    linarith
  exact (le_div_iff₀ hh.1).mpr hge
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath
