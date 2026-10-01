import KP1Y.RankedLevelStep
import KP1Y.ConstructibleHistory

/-! 实际排名历史的合法性及载域零/后继/并集方程；坏历史默认分支在真实历史中不会触发。 -/
namespace KP1Y.ConstructibleRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking KP1Y.SetLanguage
universe u

theorem ranked_history_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {e : Env M 26} {H Γ V Q i Out : M.Domain}
    (h : KP1Y.SigmaRecursion.ValueHistory M (rankedStepMatrix.denote e) H Γ V Q)
    (hi : M.mem i Γ) (hAt : MemPair M H i Out) : ∃ P w, Prefix M P H i V ∧ RankedStep M e i P Out w := by
  obtain ⟨P,hP,hQ⟩ := h.prefixes.total i hi
  obtain ⟨hPrefix,w,_,hStep⟩ := h.obeys i hi P hP Out (h.values.bounds hM.1 hAt).2 hQ hAt
  exact ⟨P,w,hPrefix,(rankedStepMatrix_iff hM e i P Out w).mp hStep⟩

theorem ranked_history_family_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hS : FixedSyntax M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4))
    (hP : OrdinalRank M (e.bound 0) (rankContext.eval e).programs (e.bound 1)) {H Γ V Q : M.Domain}
    (h : KP1Y.SigmaRecursion.ValueHistory M (rankedStepMatrix.denote e) H Γ V Q) : RankedFamily M H Γ V := by
  refine ⟨h.values,?_⟩
  intro i Out hAt
  obtain ⟨_,_,_,hStep⟩ := ranked_history_step_d hM h (h.values.bounds hM.1 hAt).1 hAt
  exact hStep.ranked_d hM e hS hP

theorem ranked_prefix_family_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {H Γ V P i : M.Domain} (hH : RankedFamily M H Γ V) (hP : Prefix M P H i V) : RankedFamily M P i V := by
  refine ⟨hP.graph,?_⟩
  intro j p hAt
  exact hH.ranked j p ((hP.all_rows he hH.graph j (hP.graph.bounds he hAt).1 p).mp hAt)

theorem RankedStep.successor_case_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {e : Env M 26} {i j P V Out w : M.Domain} (hi : M.IsOrdinal i) (hs : M.SuccessorOf i j)
    (hGood : RankedFamily M P i V) (h : RankedStep M e i P Out w) :
    ∃ p B, MemPair M P j p ∧ Project.Formula.satisfies (((e.push p).push Out).push B) successorPacketMatrix.body := by
  obtain ⟨V',_,hGraph,hCases⟩ := h
  rcases hCases with ⟨hBad,_⟩ | ⟨_,hCases⟩
  · exact False.elim (hBad ⟨hGraph,hGood.ranked⟩)
  · rcases hCases with ⟨j',hj',p,_,B,_,hs',hAt,hOut⟩ | ⟨hNo,_,_,_⟩
    · have hjj' := Structure.SuccessorOf.predecessor_eq hM.1 (hi.mem hj') hs' hs
      subst j'
      exact ⟨p,B,hAt,hOut⟩
    · exact False.elim (hNo j hs.predecessor_mem hs)

theorem RankedStep.union_case_d {M : SetTheory.Structure.{u}} {e : Env M 26} {i P V Out w : M.Domain}
    (hNo : KP1Y.Constructible.NoPredecessor M i) (hGood : RankedFamily M P i V) (h : RankedStep M e i P Out w) :
    ∃ B, Project.Formula.satisfies ((((oneEnv i).push P).push Out).push B) rankedUnionMatrix.body := by
  obtain ⟨V',_,hGraph,hCases⟩ := h
  rcases hCases with ⟨hBad,_⟩ | ⟨_,hCases⟩
  · exact False.elim (hBad ⟨hGraph,hGood.ranked⟩)
  · rcases hCases with ⟨j,hj,_,_,_,_,hs,_,_⟩ | ⟨_,B,_,hOut⟩
    · exact False.elim (hNo j hj hs)
    · exact ⟨B,hOut⟩

theorem ranked_history_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {e : Env M 26} {H Γ V Q i j p Out : M.Domain} (hΓ : M.IsOrdinal Γ) (hGood : RankedFamily M H Γ V)
    (h : KP1Y.SigmaRecursion.ValueHistory M (rankedStepMatrix.denote e) H Γ V Q)
    (hi : M.mem i Γ) (hs : M.SuccessorOf i j) (hAt : MemPair M H i Out) (hPrev : MemPair M H j p) :
    ∃ B, Project.Formula.satisfies (((e.push p).push Out).push B) successorPacketMatrix.body := by
  obtain ⟨P,_,hPrefix,hStep⟩ := ranked_history_step_d hM h hi hAt
  obtain ⟨p',B,hPAt,hOut⟩ := hStep.successor_case_d hM (hΓ.mem hi) hs (ranked_prefix_family_d hM.1 hGood hPrefix)
  have hAt' := (hPrefix.all_rows hM.1 h.values j hs.predecessor_mem p').mp hPAt
  have hpp' := h.values.unique j p' p hAt' hPrev
  subst p'
  exact ⟨B,hOut⟩

def CarrierRangeUnion (M : SetTheory.Structure.{u}) (A H i : M.Domain) : Prop :=
  ∀ x, M.mem x A ↔ ∃ j, M.mem j i ∧ ∃ p, MemPair M H j p ∧ PacketCarrierMember M p x

theorem ranked_history_union_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {e : Env M 26} {H Γ V Q i Out A θ F : M.Domain} (hGood : RankedFamily M H Γ V)
    (h : KP1Y.SigmaRecursion.ValueHistory M (rankedStepMatrix.denote e) H Γ V Q)
    (hi : M.mem i Γ) (hNo : KP1Y.Constructible.NoPredecessor M i) (hAt : MemPair M H i Out)
    (hp : Packet M Out A θ F) : CarrierRangeUnion M A H i := by
  obtain ⟨P,_,hPrefix,hStep⟩ := ranked_history_step_d hM h hi hAt
  obtain ⟨B,hOut⟩ := hStep.union_case_d hNo (ranked_prefix_family_d hM.1 hGood hPrefix)
  obtain ⟨V',κ,hFamily,hUnion⟩ := ranked_union_carrier_d hM (oneEnv i) hp hOut
  intro x
  constructor
  · intro hx
    obtain ⟨j,hj,p,_,hPAt,hxP⟩ := (hUnion.carrier x).mp hx
    exact ⟨j,hj,p,(hPrefix.all_rows hM.1 h.values j hj p).mp hPAt,hxP⟩
  · rintro ⟨j,hj,p,hHAt,hxP⟩
    have hPAt := (hPrefix.all_rows hM.1 h.values j hj p).mpr hHAt
    exact (hUnion.carrier x).mpr ⟨j,hj,p,(hFamily.graph.bounds hM.1 hPAt).2,hPAt,hxP⟩

theorem ranked_history_empty_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {e : Env M 26} {H Γ V Q i Out A θ F : M.Domain} (hGood : RankedFamily M H Γ V)
    (h : KP1Y.SigmaRecursion.ValueHistory M (rankedStepMatrix.denote e) H Γ V Q)
    (hi : M.mem i Γ) (hEmpty : ∀ j, ¬M.mem j i) (hAt : MemPair M H i Out) (hp : Packet M Out A θ F) :
    ∀ x, ¬M.mem x A := by
  have hUnion := ranked_history_union_d hM hGood h hi (fun j hj => False.elim (hEmpty j hj)) hAt hp
  intro x hx
  obtain ⟨j,hj,_⟩ := (hUnion x).mp hx
  exact hEmpty j hj

end KP1Y.ConstructibleRank
