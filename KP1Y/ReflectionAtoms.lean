import KP1Y.ReflectionData

/-! 有限边表与端点模板中的实际原子查询，层号覆盖完整内部ω。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking
universe u

def EdgeAt (M : SetTheory.Structure.{u}) (C : Data M.Domain) (A k q p j : M.Domain) : Prop :=
  ∃ i, M.mem i C.omega ∧ ∃ e, M.mem e C.edgeCodes ∧ MemPair M A i e ∧ Quad M C.pairs e k q p j

def NeedAt (M : SetTheory.Structure.{u}) (C : Data M.Domain) (N k q p : M.Domain) : Prop :=
  ∃ i, M.mem i C.omega ∧ ∃ e, M.mem e C.needCodes ∧ MemPair M N i e ∧ Packet M e k q p

def edgeAtFormula {n : Nat} (C : Data (Project.Term n)) (A k q p j : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.edgeCodes.weaken
    (.conj (memPairFormula A.weaken.weaken (.bound 1) (.bound 0))
      (quadFormula C.pairs.weaken.weaken (.bound 0) k.weaken.weaken q.weaken.weaken p.weaken.weaken j.weaken.weaken)))

def needAtFormula {n : Nat} (C : Data (Project.Term n)) (N k q p : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.needCodes.weaken
    (.conj (memPairFormula N.weaken.weaken (.bound 1) (.bound 0))
      (packetFormula (.bound 0) k.weaken.weaken q.weaken.weaken p.weaken.weaken)))

theorem edgeAtFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (A k q p j : Project.Term n) :
    (edgeAtFormula C A k q p j).IsDelta0 := .existsMem _ (.existsMem _
      (.conj (memPairFormula_delta0 _ _ _) (quadFormula_delta0 _ _ _ _ _ _)))

theorem needAtFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (N k q p : Project.Term n) :
    (needAtFormula C N k q p).IsDelta0 := .existsMem _ (.existsMem _
      (.conj (memPairFormula_delta0 _ _ _) (packetFormula_delta0 _ _ _ _)))

theorem edgeAtFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (A k q p j : Project.Term n)
    (hA : A.freeSupport=[]) (hk : k.freeSupport=[]) (hq : q.freeSupport=[]) (hp : p.freeSupport=[])
    (hj : j.freeSupport=[]) : (edgeAtFormula C A k q p j).FreeClosed := by
  simp [edgeAtFormula,quadFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hC.edgeCodes,hC.pairs,hA,hk,hq,hp,hj]

theorem needAtFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (N k q p : Project.Term n)
    (hN : N.freeSupport=[]) (hk : k.freeSupport=[]) (hq : q.freeSupport=[]) (hp : p.freeSupport=[]) :
    (needAtFormula C N k q p).FreeClosed := by
  simp [needAtFormula,packetFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hC.needCodes,hN,hk,hq,hp]

theorem edgeAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (C : Data (Project.Term n)) (A k q p j : Project.Term n) :
    Project.Formula.satisfies env (edgeAtFormula C A k q p j) ↔ EdgeAt M (C.eval env) (A.eval env) (k.eval env) (q.eval env) (p.eval env) (j.eval env) := by
  simp only [edgeAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,quadFormula_iff he,Term.eval_weaken]
  rfl

theorem needAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (C : Data (Project.Term n)) (N k q p : Project.Term n) :
    Project.Formula.satisfies env (needAtFormula C N k q p) ↔ NeedAt M (C.eval env) (N.eval env) (k.eval env) (q.eval env) (p.eval env) := by
  simp only [needAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,packetFormula_iff he,Term.eval_weaken]
  rfl

theorem EdgeAt.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain} (hC : C.Valid M)
    {A k q p j : M.Domain} (h : EdgeAt M C A k q p j) : M.mem k C.omega ∧ M.mem q C.omega ∧ M.mem p C.omega ∧ M.mem j C.omega := by
  obtain ⟨_,_,_,_,_,hQuad⟩ := h
  exact hQuad.bounds he hC.pairs

theorem NeedAt.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain} (hC : C.Valid M)
    {N k q p : M.Domain} (h : NeedAt M C N k q p) : M.mem k C.omega ∧ M.mem q C.omega ∧ M.mem p C.omega := by
  obtain ⟨_,_,e,heN,_,t,hE,hT⟩ := h
  obtain ⟨k',hk',t',ht',hE'⟩ := (hC.needCodes e).mp heN
  obtain ⟨hkk',htt'⟩ := codes_injective he hE hE'
  subst k'
  subst t'
  obtain ⟨q',hq',p',hp',hT'⟩ := (hC.pairs t).mp ht'
  obtain ⟨hqq',hpp'⟩ := codes_injective he hT hT'
  exact ⟨hk',hqq' ▸ hq',hpp' ▸ hp'⟩

theorem quad_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {k q p j : M.Domain} (hk : M.mem k C.omega) (hq : M.mem q C.omega) (hp : M.mem p C.omega) (hj : M.mem j C.omega) :
    ∃ e, M.mem e C.edgeCodes ∧ Quad M C.pairs e k q p j := by
  obtain ⟨u,hu⟩ := codes_total hM k q
  obtain ⟨v,hv⟩ := codes_total hM p j
  obtain ⟨e,he⟩ := codes_total hM u v
  have huP := (hC.pairs u).mpr ⟨k,hk,q,hq,hu⟩
  have hvP := (hC.pairs v).mpr ⟨p,hp,j,hj,hv⟩
  exact ⟨e,(hC.edgeCodes e).mpr ⟨u,huP,v,hvP,he⟩,u,huP,v,hvP,he,hu,hv⟩

theorem need_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {k q p : M.Domain} (hk : M.mem k C.omega) (hq : M.mem q C.omega) (hp : M.mem p C.omega) :
    ∃ e, M.mem e C.needCodes ∧ Packet M e k q p := by
  obtain ⟨t,ht⟩ := codes_total hM q p
  obtain ⟨e,he⟩ := codes_total hM k t
  exact ⟨e,(hC.needCodes e).mpr ⟨k,hk,t,(hC.pairs t).mpr ⟨q,hq,p,hp,ht⟩,he⟩,t,he,ht⟩

end KP1Y.Reflection
