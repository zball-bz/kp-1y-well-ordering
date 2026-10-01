import KP1Y.SetDefComprehension
import KP1Y.ConstructibleHistory
import KP1Y.ClassBoundedTruth

/-! 传递层中所有序数构成的实际子集属于Def；用于证明Lα恰好包含α以下序数。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Bounded KP1Y.Classes KP1Y.Satisfaction KP1Y.Definability
universe u

def ordinalPredicate : Project.Delta0UnarySchema 0 where
  body := ordinalFormula (.bound 0)
  freeClosed := by simp [ordinalFormula,Project.Formula.isTransitive,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := ordinalFormula_delta0 _

theorem DefStage.ordinal_slice_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hTrans : M.TransitiveSet C.carrier) :
    ∃ S, M.mem S Def ∧ ∀ x, M.mem x S ↔ M.mem x C.carrier ∧ M.IsOrdinal x := by
  classical
  by_cases hNe : ∃ x, M.mem x C.carrier
  · have hNeCopy := hNe
    obtain ⟨a,ha⟩ := hNeCopy
    let e : Env (classModel M (fun x => M.mem x C.carrier) hNe) 0 := ⟨Fin.elim0,fun _ => ⟨a,ha⟩⟩
    obtain ⟨S,hS,hSub,hRows⟩ := h.comprehension_d hM hTrans hNe ordinalPredicate.toUnarySchema e
    have hMeaning (x : (classModel M (fun x => M.mem x C.carrier) hNe).Domain) :
        Project.Formula.satisfies (e.push x) ordinalPredicate.body ↔ M.IsOrdinal x.val :=
      (delta0_class_absolute hTrans ordinalPredicate.delta0 (e.push x)).trans
        (ordinalFormula_iff hM (forgetEnv (e.push x)) (.bound 0))
    refine ⟨S,hS,?_⟩
    intro x
    constructor
    · intro hx
      have hxC := hSub x hx
      exact ⟨hxC,(hMeaning ⟨x,hxC⟩).mp ((hRows ⟨x,hxC⟩).mp hx)⟩
    · rintro ⟨hxC,hOrd⟩
      exact (hRows ⟨x,hxC⟩).mpr ((hMeaning ⟨x,hxC⟩).mpr hOrd)
  · have hEmpty : ∀ x, ¬M.mem x C.carrier := fun x hx => hNe ⟨x,hx⟩
    exact ⟨C.carrier,empty_member_def_set_d hM h.spaces h.subsets hEmpty,
      fun x => ⟨fun hx => False.elim (hEmpty x hx),And.left⟩⟩

end KP1Y.SetLanguage

namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.SetLanguage
universe u

theorem DefLevel.member_subset_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {A T x : M.Domain} (h : DefLevel M env A T) (hx : M.mem x T) :
    M.MemberSubset x A := by
  obtain ⟨B,hB⟩ := h
  obtain ⟨W,_,hW⟩ := (defSuccessorMatrix_iff hM env A T B).mp hB
  exact (hW.stage_d hM hS).subsets.member_subset hx

theorem DefLevel.ordinal_slice_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {A T : M.Domain} (h : DefLevel M env A T) (hA : M.TransitiveSet A) :
    ∃ S, M.mem S T ∧ ∀ x, M.mem x S ↔ M.mem x A ∧ M.IsOrdinal x := by
  obtain ⟨B,hB⟩ := h
  obtain ⟨W,_,hW⟩ := (defSuccessorMatrix_iff hM env A T B).mp hB
  exact (hW.stage_d hM hS).ordinal_slice_d hM hA

end KP1Y.Constructible
