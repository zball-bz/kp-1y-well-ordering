import KP1Y.CountableSkolemHull

/-! 全局二元枚举函数作用于有限参数元组的首项；空元组使用指定默认值。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def EnumTuple (M : SetTheory.Structure.{u}) (A EKeys e indexZero default n t x : M.Domain) : Prop :=
  (∃ a, M.mem a A ∧ MemPair M t indexZero a ∧
    ∃ key, M.mem key EKeys ∧ Codes M key a n ∧ MemPair M e key x) ∨
  ((∀ a, M.mem a A → ¬MemPair M t indexZero a) ∧ x=default)

def enumTupleFormula {d : Nat} (A EKeys e indexZero default n t x : Project.Term d) : Project.Formula 1 d :=
  .disj (Project.Formula.existsMem A
    (.conj (memPairFormula t.weaken indexZero.weaken (.bound 0))
      (Project.Formula.existsMem EKeys.weaken
        (.conj (codeFormula (.bound 0) (.bound 1) n.weaken.weaken)
          (memPairFormula e.weaken.weaken (.bound 0) x.weaken.weaken)))))
    (.conj (Project.Formula.forallMem A (.neg (memPairFormula t.weaken indexZero.weaken (.bound 0))))
      (Project.Formula.extensionalEq x default))

theorem enumTupleFormula_delta0 {d : Nat} (A EKeys e indexZero default n t x : Project.Term d) :
    (enumTupleFormula A EKeys e indexZero default n t x).IsDelta0 :=
  .disj (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.existsMem _
    (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))
    (.conj (.forallMem _ (.neg (memPairFormula_delta0 _ _ _))) (.atom _ _ _))

theorem enumTupleFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (A EKeys e indexZero default n t x : Project.Term d) :
    Project.Formula.satisfies env (enumTupleFormula A EKeys e indexZero default n t x) ↔
      EnumTuple M (A.eval env) (EKeys.eval env) (e.eval env) (indexZero.eval env)
        (default.eval env) (n.eval env) (t.eval env) (x.eval env) := by
  simp only [enumTupleFormula, Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_extensionalEq_iff_eq he,
    memPairFormula_iff he, codeFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem enum_tuple_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A EKeys e indexZero default n t : M.Domain} (hKeys : IsProduct M EKeys A ω)
    (he : Graph M e EKeys A) (hDefault : M.mem default A) (hn : M.mem n ω) :
    ∃ x, M.mem x A ∧ EnumTuple M A EKeys e indexZero default n t x := by
  classical
  by_cases hFirst : ∃ a, M.mem a A ∧ MemPair M t indexZero a
  · obtain ⟨a,ha,hAt⟩ := hFirst
    obtain ⟨key,hCode⟩ := codes_total hM a n
    have hKey := (hKeys key).mpr ⟨a,ha,n,hn,hCode⟩
    obtain ⟨x,hx,hex⟩ := he.total key hKey
    exact ⟨x,hx,Or.inl ⟨a,ha,hAt,key,hKey,hCode,hex⟩⟩
  · exact ⟨default,hDefault,Or.inr ⟨fun a ha hAt => hFirst ⟨a,ha,hAt⟩,rfl⟩⟩

theorem enum_tuple_unique {M : SetTheory.Structure.{u}} (hExt : Extensional M)
    {A EKeys e indexZero default n t length x y : M.Domain} (he : Graph M e EKeys A)
    (ht : Graph M t length A) (hx : EnumTuple M A EKeys e indexZero default n t x)
    (hy : EnumTuple M A EKeys e indexZero default n t y) : x=y := by
  rcases hx with ⟨a,ha,hAt,key,_,hCode,hex⟩ | ⟨hNone,hxDefault⟩
  · rcases hy with ⟨a',_,hAt',key',_,hCode',hey⟩ | ⟨hNone,_⟩
    · have hAs := ht.unique indexZero a a' hAt hAt'
      subst a'
      have hKeys := codes_unique hExt hCode hCode'
      subst key'
      exact he.unique key x y hex hey
    · exact False.elim (hNone a ha hAt)
  · rcases hy with ⟨a,ha,hAt,_⟩ | ⟨_,hyDefault⟩
    · exact False.elim (hNone a ha hAt)
    · exact hxDefault.trans hyDefault.symm

end KP1Y.Satisfaction
