import KP1Y.ReflectionShapes

/-! 有限图/模板的带位置解码，用于将每条边的层号绑定到独立参数变量。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking
universe u

theorem Quad.injective {M : SetTheory.Structure.{u}} (he : Extensional M) {Pairs e k q p j k' q' p' j' : M.Domain}
    (h : Quad M Pairs e k q p j) (h' : Quad M Pairs e k' q' p' j') : k=k' ∧ q=q' ∧ p=p' ∧ j=j' := by
  obtain ⟨u,_,v,_,hE,hU,hV⟩ := h
  obtain ⟨u',_,v',_,hE',hU',hV'⟩ := h'
  obtain ⟨hu,hv⟩ := codes_injective he hE hE'
  subst u'
  subst v'
  obtain ⟨hk,hq⟩ := codes_injective he hU hU'
  exact ⟨hk,hq,codes_injective he hV hV'⟩

theorem edge_code_decode {M : SetTheory.Structure.{u}} {C : Data M.Domain} (hC : C.Valid M) {e : M.Domain}
    (he : M.mem e C.edgeCodes) : ∃ k q p j, Quad M C.pairs e k q p j := by
  obtain ⟨u,hu,v,hv,hE⟩ := (hC.edgeCodes e).mp he
  obtain ⟨k,_,q,_,hU⟩ := (hC.pairs u).mp hu
  obtain ⟨p,_,j,_,hV⟩ := (hC.pairs v).mp hv
  exact ⟨k,q,p,j,u,hu,v,hv,hE,hU,hV⟩

theorem need_code_decode {M : SetTheory.Structure.{u}} {C : Data M.Domain} (hC : C.Valid M) {e : M.Domain}
    (he : M.mem e C.needCodes) : ∃ k q p, Packet M e k q p := by
  obtain ⟨k,_,v,hv,hE⟩ := (hC.needCodes e).mp he
  obtain ⟨q,_,p,_,hV⟩ := (hC.pairs v).mp hv
  exact ⟨k,q,p,v,hE,hV⟩

def EdgeEntry (M : SetTheory.Structure.{u}) (C : Data M.Domain) (A i k q p j : M.Domain) : Prop :=
  ∃ e, M.mem e C.edgeCodes ∧ MemPair M A i e ∧ Quad M C.pairs e k q p j

def NeedEntry (M : SetTheory.Structure.{u}) (C : Data M.Domain) (N i k q p : M.Domain) : Prop :=
  ∃ e, M.mem e C.needCodes ∧ MemPair M N i e ∧ Packet M e k q p

def edgeEntryFormula {d : Nat} (C : Data (Project.Term d)) (A i k q p j : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem C.edgeCodes (.conj (memPairFormula A.weaken i.weaken (.bound 0))
    (quadFormula C.pairs.weaken (.bound 0) k.weaken q.weaken p.weaken j.weaken))

def needEntryFormula {d : Nat} (C : Data (Project.Term d)) (N i k q p : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem C.needCodes (.conj (memPairFormula N.weaken i.weaken (.bound 0))
    (packetFormula (.bound 0) k.weaken q.weaken p.weaken))

theorem edgeEntryFormula_delta0 {d : Nat} (C : Data (Project.Term d)) (A i k q p j : Project.Term d) :
    (edgeEntryFormula C A i k q p j).IsDelta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (quadFormula_delta0 _ _ _ _ _ _))

theorem needEntryFormula_delta0 {d : Nat} (C : Data (Project.Term d)) (N i k q p : Project.Term d) :
    (needEntryFormula C N i k q p).IsDelta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (packetFormula_delta0 _ _ _ _))

theorem edgeEntryFormula_freeClosed {d : Nat} {C : Data (Project.Term d)} (hC : C.Closed) (A i k q p j : Project.Term d)
    (hA : A.freeSupport=[]) (hi : i.freeSupport=[]) (hk : k.freeSupport=[]) (hq : q.freeSupport=[])
    (hp : p.freeSupport=[]) (hj : j.freeSupport=[]) : (edgeEntryFormula C A i k q p j).FreeClosed := by
  simp [edgeEntryFormula,quadFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.edgeCodes,hC.pairs,hA,hi,hk,hq,hp,hj]

theorem needEntryFormula_freeClosed {d : Nat} {C : Data (Project.Term d)} (hC : C.Closed) (N i k q p : Project.Term d)
    (hN : N.freeSupport=[]) (hi : i.freeSupport=[]) (hk : k.freeSupport=[]) (hq : q.freeSupport=[])
    (hp : p.freeSupport=[]) : (needEntryFormula C N i k q p).FreeClosed := by
  simp [needEntryFormula,packetFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.needCodes,hN,hi,hk,hq,hp]

theorem edgeEntryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (C : Data (Project.Term d)) (A i k q p j : Project.Term d) : Project.Formula.satisfies e (edgeEntryFormula C A i k q p j) ↔
      EdgeEntry M (C.eval e) (A.eval e) (i.eval e) (k.eval e) (q.eval e) (p.eval e) (j.eval e) := by
  simp only [edgeEntryFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,quadFormula_iff he,Term.eval_weaken]
  rfl

theorem needEntryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (C : Data (Project.Term d)) (N i k q p : Project.Term d) : Project.Formula.satisfies e (needEntryFormula C N i k q p) ↔
      NeedEntry M (C.eval e) (N.eval e) (i.eval e) (k.eval e) (q.eval e) (p.eval e) := by
  simp only [needEntryFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,packetFormula_iff he,Term.eval_weaken]
  rfl

theorem EdgeEntry.occurs {M : SetTheory.Structure.{u}} {C : Data M.Domain} {A i k q p j : M.Domain}
    (hi : M.mem i C.omega) (h : EdgeEntry M C A i k q p j) : EdgeAt M C A k q p j := ⟨i,hi,h⟩

theorem NeedEntry.occurs {M : SetTheory.Structure.{u}} {C : Data M.Domain} {N i k q p : M.Domain}
    (hi : M.mem i C.omega) (h : NeedEntry M C N i k q p) : NeedAt M C N k q p := ⟨i,hi,h⟩

theorem EdgeEntry.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain} {A n i k q p j k' q' p' j' : M.Domain}
    (hA : Graph M A n C.edgeCodes) (h : EdgeEntry M C A i k q p j) (h' : EdgeEntry M C A i k' q' p' j') :
    k=k' ∧ q=q' ∧ p=p' ∧ j=j' := by
  obtain ⟨e,_,hAt,hQ⟩ := h
  obtain ⟨e',_,hAt',hQ'⟩ := h'
  have hee' := hA.unique i e e' hAt hAt'
  subst e'
  exact hQ.injective he hQ'

theorem NeedEntry.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain} {N n i k q p k' q' p' : M.Domain}
    (hN : Graph M N n C.needCodes) (h : NeedEntry M C N i k q p) (h' : NeedEntry M C N i k' q' p') : k=k' ∧ q=q' ∧ p=p' := by
  obtain ⟨e,_,hAt,hQ⟩ := h
  obtain ⟨e',_,hAt',hQ'⟩ := h'
  have hee' := hN.unique i e e' hAt hAt'
  subst e'
  exact hQ.injective he hQ'

theorem edge_entry_exists {M : SetTheory.Structure.{u}} {C : Data M.Domain} (hC : C.Valid M) {A n i : M.Domain}
    (hA : Graph M A n C.edgeCodes) (hi : M.mem i n) : ∃ k q p j, EdgeEntry M C A i k q p j := by
  obtain ⟨e,he,hAt⟩ := hA.total i hi
  obtain ⟨k,q,p,j,hQ⟩ := edge_code_decode hC he
  exact ⟨k,q,p,j,e,he,hAt,hQ⟩

theorem need_entry_exists {M : SetTheory.Structure.{u}} {C : Data M.Domain} (hC : C.Valid M) {N n i : M.Domain}
    (hN : Graph M N n C.needCodes) (hi : M.mem i n) : ∃ k q p, NeedEntry M C N i k q p := by
  obtain ⟨e,he,hAt⟩ := hN.total i hi
  obtain ⟨k,q,p,hQ⟩ := need_code_decode hC he
  exact ⟨k,q,p,e,he,hAt,hQ⟩

end KP1Y.Reflection
