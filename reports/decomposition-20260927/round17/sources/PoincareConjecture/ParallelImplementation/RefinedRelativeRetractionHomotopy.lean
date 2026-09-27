import PoincareConjecture.ProofContract.Refinement20260927.RelativeApproximation
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedRelativeRetractionHomotopy
open PoincareConjecture.ProofContract.Refinement20260927
theorem relative_retraction_homotopy : RelativeRetractionHomotopyStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro N n R f
  let K : Set (ApproxAmbient n) := Set.range fun q : SweepDomain => R.embed (f q)
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_range (R.embed.continuous.comp f.continuous)
  have hK_domain : K ⊆ R.domain := by
    rintro _ ⟨q, rfl⟩
    exact R.contains (f q)
  obtain ⟨delta, hdelta, hthick⟩ :=
    hK.exists_thickening_subset_open R.open_domain hK_domain
  refine ⟨delta, hdelta, ?_⟩
  intro g hclose hends
  let segment : unitInterval × SweepDomain → ApproxAmbient n := fun z =>
    (1 - (z.1 : ℝ)) • R.embed (g z.2) + (z.1 : ℝ) • R.embed (f z.2)
  have hsegment_cont : Continuous segment := by
    dsimp [segment]
    fun_prop
  have hsegment_mem (t : unitInterval) (q : SweepDomain) : segment (t, q) ∈ R.domain := by
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨R.embed (f q), ⟨q, rfl⟩, ?_⟩
    calc
      dist (segment (t, q)) (R.embed (f q)) ≤
          dist (R.embed (g q)) (R.embed (f q)) := by
            simpa [segment, add_comm] using
              (dist_smul_add_one_sub_smul_le
                (r := (t : ℝ)) (x := R.embed (f q)) (y := R.embed (g q))
                ⟨t.2.1, t.2.2⟩)
      _ < delta := hclose q
  let segmentDomain : C(unitInterval × SweepDomain, R.domain) :=
    ⟨fun z => ⟨segment z, hsegment_mem z.1 z.2⟩,
      hsegment_cont.subtype_mk (fun z => hsegment_mem z.1 z.2)⟩
  let homotopyMap : C(unitInterval × SweepDomain, N) := R.retract.comp segmentDomain
  have hzero (q : SweepDomain) : homotopyMap (0, q) = g q := by
    simp [homotopyMap, segmentDomain, segment, R.retract_embed]
  have hone (q : SweepDomain) : homotopyMap (1, q) = f q := by
    simp [homotopyMap, segmentDomain, segment, R.retract_embed]
  refine ⟨{
    toHomotopy := {
      toFun := homotopyMap
      map_zero_left := hzero
      map_one_left := hone
    }
    prop' := ?_
  }⟩
  intro t q hq
  have hgf : g q = f q := hends hq
  have hval : (segmentDomain (t, q)).val = R.embed (g q) := by
    simp only [segmentDomain, ContinuousMap.coe_mk, segment]
    rw [hgf, ← add_smul, sub_add_cancel, one_smul]
  have hsub : segmentDomain (t, q) = ⟨R.embed (g q), R.contains (g q)⟩ :=
    Subtype.ext hval
  change R.retract (segmentDomain (t, q)) = g q
  rw [hsub]
  exact R.retract_embed (g q)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedRelativeRetractionHomotopy
