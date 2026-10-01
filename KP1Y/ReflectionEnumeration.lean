import KP1Y.EnumerationInitialSegment

/-! 将正初段枚举规范化为κ上的总二元函数，零输入和未用输入明确返回0。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Closure
universe u

def EnumValue (M : SetTheory.Structure.{u}) (ω Keys E zero a n x : M.Domain) : Prop :=
  ((a=zero ∨ ¬M.mem n ω) ∧ x=zero) ∨
    (a≠zero ∧ M.mem n ω ∧ ∃ key, M.mem key Keys ∧ Codes M key a n ∧ MemPair M E key x)

def enumValueFormula {d : Nat} (ω Keys E zero a n x : Project.Term d) : Project.Formula 1 d :=
  .disj (.conj (.disj (Project.Formula.extensionalEq a zero) (.neg (.mem n ω))) (Project.Formula.extensionalEq x zero))
    (.conj (.neg (Project.Formula.extensionalEq a zero)) (.conj (.mem n ω)
      (Project.Formula.existsMem Keys (.conj (codeFormula (.bound 0) a.weaken n.weaken) (memPairFormula E.weaken (.bound 0) x.weaken)))))

theorem enumValueFormula_delta0 {d : Nat} (ω Keys E zero a n x : Project.Term d) :
    (enumValueFormula ω Keys E zero a n x).IsDelta0 :=
  .disj (.conj (.disj (.atom _ _ _) (.neg (.mem _ _))) (.atom _ _ _))
    (.conj (.neg (.atom _ _ _)) (.conj (.mem _ _) (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))

theorem enumValueFormula_freeClosed {d : Nat} (ω Keys E zero a n x : Project.Term d)
    (hω : ω.freeSupport=[]) (hKeys : Keys.freeSupport=[]) (hE : E.freeSupport=[]) (hZero : zero.freeSupport=[])
    (ha : a.freeSupport=[]) (hn : n.freeSupport=[]) (hx : x.freeSupport=[]) : (enumValueFormula ω Keys E zero a n x).FreeClosed := by
  simp [enumValueFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hω,hKeys,hE,hZero,ha,hn,hx]

theorem enumValueFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (ω Keys E zero a n x : Project.Term d) : Project.Formula.satisfies e (enumValueFormula ω Keys E zero a n x) ↔
      EnumValue M (ω.eval e) (Keys.eval e) (E.eval e) (zero.eval e) (a.eval e) (n.eval e) (x.eval e) := by
  simp only [enumValueFormula,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_existsMem_iff,codeFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem enum_value_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω κ Keys E zero a n : M.Domain}
    (hEnum : UniformEnumeration M ω κ Keys E) (hZero : M.mem zero κ) (ha : M.mem a κ) :
    ∃ x, M.mem x κ ∧ EnumValue M ω Keys E zero a n x := by
  classical
  by_cases ha0 : a=zero
  · exact ⟨zero,hZero,Or.inl ⟨Or.inl ha0,rfl⟩⟩
  · by_cases hn : M.mem n ω
    · obtain ⟨key,hKey⟩ := codes_total hM a n
      have hk := (hEnum.keys key).mpr ⟨a,ha,n,hn,hKey⟩
      obtain ⟨x,hx,hAt⟩ := hEnum.graph.total key hk
      exact ⟨x,hx,Or.inr ⟨ha0,hn,key,hk,hKey,hAt⟩⟩
    · exact ⟨zero,hZero,Or.inl ⟨Or.inr hn,rfl⟩⟩

theorem enum_value_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {ω κ Keys E zero a n x y : M.Domain}
    (hEnum : UniformEnumeration M ω κ Keys E) (hx : EnumValue M ω Keys E zero a n x) (hy : EnumValue M ω Keys E zero a n y) : x=y := by
  rcases hx with ⟨hDefault,hx⟩ | ⟨ha,hn,key,_,hCode,hAt⟩
  · rcases hy with ⟨_,hy⟩ | ⟨ha,hn,_⟩
    · exact hx.trans hy.symm
    · exact False.elim (hDefault.elim ha (fun h => h hn))
  · rcases hy with ⟨hDefault,_⟩ | ⟨_,_,key',_,hCode',hAt'⟩
    · exact False.elim (hDefault.elim ha (fun h => h hn))
    · have hKeys := codes_unique he hCode hCode'
      subst key'
      exact hEnum.graph.unique key x y hAt hAt'

theorem enum_value_bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {ω κ Keys E zero a n x : M.Domain}
    (hEnum : UniformEnumeration M ω κ Keys E) (hZero : M.mem zero κ) (h : EnumValue M ω Keys E zero a n x) : M.mem x κ := by
  rcases h with ⟨_,hx⟩ | ⟨_,_,_,_,_,hAt⟩
  · exact hx ▸ hZero
  · exact (hEnum.graph.bounds he hAt).2

theorem enum_value_zero {M : SetTheory.Structure.{u}} {ω Keys E zero n x : M.Domain}
    (h : EnumValue M ω Keys E zero zero n x) : x=zero := by
  rcases h with ⟨_,hx⟩ | ⟨hn,_⟩
  · exact hx
  · exact False.elim (hn rfl)

theorem enum_value_unused {M : SetTheory.Structure.{u}} {ω Keys E zero a n x : M.Domain}
    (hn : ¬M.mem n ω) (h : EnumValue M ω Keys E zero a n x) : x=zero := by
  rcases h with ⟨_,hx⟩ | ⟨_,hn',_⟩
  · exact hx
  · exact False.elim (hn hn')

theorem enum_value_positive {M : SetTheory.Structure.{u}} {ω κ Keys E zero a n x : M.Domain}
    (hEnum : UniformEnumeration M ω κ Keys E) (hZero : ∀ z, ¬M.mem z zero)
    (ha : M.mem a κ) (hPos : ∃ z, M.mem z a) (hn : M.mem n ω) (h : EnumValue M ω Keys E zero a n x) : M.mem x a := by
  rcases h with ⟨hDefault,_⟩ | ⟨_,_,key,_,hCode,hAt⟩
  · rcases hDefault with he | hNot
    · obtain ⟨z,hz⟩ := hPos
      exact False.elim (hZero z (he ▸ hz))
    · exact False.elim (hNot hn)
  · exact hEnum.positive_range a ha hPos n hn key hCode x hAt

theorem enum_value_covers {M : SetTheory.Structure.{u}} {ω κ Keys E zero a x : M.Domain}
    (hEnum : UniformEnumeration M ω κ Keys E) (hZero : ∀ z, ¬M.mem z zero) (ha : M.mem a κ) (hx : M.mem x a) :
    ∃ n, M.mem n ω ∧ EnumValue M ω Keys E zero a n x := by
  obtain ⟨n,hn,key,hk,hCode,hAt⟩ := hEnum.covers a ha x hx
  exact ⟨n,hn,Or.inr ⟨fun he => hZero x (he ▸ hx),hn,key,hk,hCode,hAt⟩⟩

end KP1Y.ReflectionModel
