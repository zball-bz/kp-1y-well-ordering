import KP1Y.ProjectCompilation

/-! 任何普通自由闭合公式在传递载域中的带参数定义子集都实际属于Def后继。 -/
namespace KP1Y.Named
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Classes
universe u

theorem project_rows_updated_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A zero : M.Domain} (hω : M.IsOmega ω) (hZero : ∀ y, ¬M.mem y zero)
    {hNe : ∃ y, M.mem y A} {n : Nat} (φ : Project.Formula 1 (n+1))
    (e : Env (classModel M (fun y => M.mem y A) hNe) n) (a x : (classModel M (fun y => M.mem y A) hNe).Domain)
    {s t : M.Domain} (hRows : ∀ i, MemPair M s (natValue hω i.val) ((e.push a).bound i).val)
    (hU : Updated M t s (natValue hω (variableCount φ)) A zero x.val) :
    ∀ i, MemPair M t (natValue hω i.val) ((e.push x).bound i).val := by
  have hIndex (i : Fin (n+1)) : M.mem (natValue hω i.val) (natValue hω (variableCount φ)) := by
    apply natValue_lt hω
    have hi := i.isLt
    dsimp [variableCount]
    omega
  have h0 := natValue_zero_eq hM.1 hω hZero
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact (hU.rows (natValue hω 0) (hIndex 0) x.val x.property).mpr (Or.inl ⟨h0,rfl⟩)
  · have hNeName : natValue hω i.succ.val≠zero := by
      intro he
      have hNat := natValue_injective_d hM hω i.succ.val 0 (he.trans h0.symm)
      have hPositive : 0<i.succ.val := by simp
      omega
    exact (hU.rows (natValue hω i.succ.val) (hIndex i.succ) (e.bound i).val (e.bound i).property).mpr
      (Or.inr ⟨hNeName,hRows i.succ⟩)

end KP1Y.Named

namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Classes KP1Y.Named KP1Y.Satisfaction KP1Y.Definability
universe u

theorem DefStage.comprehension_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hTrans : M.TransitiveSet C.carrier)
    (hNe : ∃ y, M.mem y C.carrier) {n : Nat} (φ : Project.UnarySchema n)
    (e : Env (classModel M (fun y => M.mem y C.carrier) hNe) n) :
    ∃ S, M.mem S Def ∧ M.MemberSubset S C.carrier ∧
      ∀ x : (classModel M (fun y => M.mem y C.carrier) hNe).Domain,
        M.mem x.val S ↔ Project.Formula.satisfies (e.push x) φ.body := by
  have hNeCopy := hNe
  obtain ⟨a,ha⟩ := hNeCopy
  let a0 : (classModel M (fun y => M.mem y C.carrier) hNe).Domain := ⟨a,ha⟩
  obtain ⟨s,hS,hRows⟩ := project_assignment_exists_d hM h.spaces.omega hNe φ.body (e.push a0)
  obtain ⟨p,length,head,hP,hTruth⟩ := project_formula_program_d hM h hTrans hNe φ.body φ.freeClosed
  have hZeroBound : M.mem zero (natValue h.spaces.omega (variableCount φ.body)) := by
    have hMem := natValue_lt h.spaces.omega (i := 0) (j := variableCount φ.body) (by dsimp [variableCount]; omega)
    rw [natValue_zero_eq hM.1 h.spaces.omega h.naturals.zero_empty] at hMem
    exact hMem
  have hMeaning (x : (classModel M (fun y => M.mem y C.carrier) hNe).Domain) (t : M.Domain)
      (hU : Updated M t s (natValue h.spaces.omega (variableCount φ.body)) C.carrier zero x.val) :
      NodeTrue M C H p head t ↔ Project.Formula.satisfies (e.push x) φ.body :=
    hTruth t (e.push x) hU.graph (project_rows_updated_d hM h.spaces.omega h.naturals.zero_empty φ.body e a0 x hRows hU)
  obtain ⟨S,hSDef,hMembers⟩ := def_set_covers_program_d hM h.spaces h.raw h.typed h.subsets hP hS hZeroBound
  refine ⟨S,hSDef,h.subsets.member_subset hSDef,?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨_,t,hU,hTrue⟩ := (hMembers x.val).mp hx
    exact (hMeaning x t hU).mp hTrue
  · intro hφ
    obtain ⟨t,hU⟩ := update_exists_d hM (i := zero) hS x.property
    exact (hMembers x.val).mpr ⟨x.property,t,hU,(hMeaning x t hU).mpr hφ⟩

end KP1Y.SetLanguage
