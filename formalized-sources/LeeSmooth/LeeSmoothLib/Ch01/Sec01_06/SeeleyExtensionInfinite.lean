import LeeSmoothLib.Ch01.Sec01_06.SeeleySeries
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace LeeSmooth.SeeleyExtension
universe v
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {n : ℕ} [NeZero n]

/-- Genuine local `C^∞` extension from a closed Euclidean half-space. -/
lemma contDiffOn_closedUpperHalfSpace_exists_open_extension_at
    {W : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hW : IsOpen W) {x : EuclideanSpace ℝ (Fin n)} (hxW : x ∈ W)
    (hx0 : x 0 = 0)
    (hf : ContDiffOn ℝ ∞ f (W ∩ closedUpperHalfSpace (n := n))) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧
      ∃ g : EuclideanSpace ℝ (Fin n) → F,
        ContDiffOn ℝ ∞ g V ∧
        Set.EqOn g f (V ∩ closedUpperHalfSpace (n := n)) := by
  obtain ⟨d, hd, hdW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hxW)
  let ε : ℝ := d / 8
  have hε : 0 < ε := by
    unfold ε
    linarith
  have hεd : (d / 4) ^ 2 + (2 * ε) ^ 2 ≤ d ^ 2 := by
    unfold ε
    nlinarith
  let S : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.closedBall x d ∩ closedUpperHalfSpace (n := n)
  have hSclosed : IsClosed S :=
    Metric.isClosed_closedBall.inter isClosed_closedUpperHalfSpace
  have hSupper : S ⊆ {z | 0 ≤ z 0} := inter_subset_right
  have hSunique : UniqueDiffOn ℝ S :=
    uniqueDiffOn_closedBall_inter_closedUpperHalfSpace hd hx0
  have hfS : ContDiffOn ℝ ∞ f S := hf.mono fun z hz ↦ ⟨hdW hz.1, hz.2⟩
  have hp : HasFTaylorSeriesUpToOn ∞ f (ftaylorSeriesWithin ℝ f S) S :=
    hfS.ftaylorSeriesWithin hSunique
  let T : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.closedBall x (d / 4) ∩ closedLowerHalfSpace (n := n)
  have hTclosed : IsClosed T :=
    Metric.isClosed_closedBall.inter isClosed_closedLowerHalfSpace
  have hTlower : T ⊆ {z | z 0 ≤ 0} := inter_subset_right
  obtain ⟨q, hq, hqSeam⟩ := seeleyLower_hasFTaylorSeriesUpToOn hd hε hx0 hεd hp
  let g : EuclideanSpace ℝ (Fin n) → F := seeleyExtension ε S f
  have hg : HasFTaylorSeriesUpToOn ∞ g
      (fun z m ↦ closedPiecewise S (ftaylorSeriesWithin ℝ f S · m) (q · m) z)
      (S ∪ T) := by
    apply HasFTaylorSeriesUpToOn.piecewise_of_isClosed hSclosed hTclosed hp hq
    intro m hm z hz
    have hz0 : z 0 = 0 := le_antisymm hz.2.2 hz.1.2
    exact (hqSeam z hz.2 hz0 m).symm
  have hV : Metric.ball x (d / 4) ⊆ S ∪ T := by
    intro z hz
    have hzcl : z ∈ Metric.closedBall x (d / 4) := Metric.ball_subset_closedBall hz
    by_cases hz0 : 0 ≤ z 0
    · exact Or.inl ⟨(Metric.closedBall_subset_closedBall (by linarith : d / 4 ≤ d)) hzcl, hz0⟩
    · exact Or.inr ⟨hzcl, le_of_not_ge hz0⟩
  refine ⟨Metric.ball x (d / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by linarith : 0 < d / 4),
    fun z hz ↦ hdW ((Metric.closedBall_subset_closedBall (by linarith : d / 4 ≤ d))
      (Metric.ball_subset_closedBall hz)),
    g, ?_, ?_⟩
  · exact hg.contDiffOn.mono hV
  · intro z hz
    exact seeleyExtension_eqOn_upper ε f
      ⟨(Metric.closedBall_subset_closedBall (by linarith : d / 4 ≤ d))
        (Metric.ball_subset_closedBall hz.1), hz.2⟩

#print axioms seeleyLower_hasFTaylorSeriesUpToOn
#print axioms contDiffOn_closedUpperHalfSpace_exists_open_extension_at

end LeeSmooth.SeeleyExtension
