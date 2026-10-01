import KP1Y.ReflectionModelBodies

/-! 固定六符号的一阶解释公式。所有解释使用同一个κ顶截面背景。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Signature
universe u

theorem six_cases (i : Fin 6) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega

def Body (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (i : Fin 6) (t : M.Domain) : Prop := match i.val with
  | 0 => BinaryBody false M C t | 1 => BinaryBody true M C t
  | 2 => RelationBody false M C t | 3 => RelationBody true M C t
  | 4 => EnumerationBody M C t | _ => ConstantBody M C t

def bodyFormula {d : Nat} (C : ArticleData (Project.Term d)) (i : Fin 6) (t : Project.Term d) : Project.Formula 1 d := match i.val with
  | 0 => binaryBodyFormula false C t | 1 => binaryBodyFormula true C t
  | 2 => relationBodyFormula false C t | 3 => relationBodyFormula true C t
  | 4 => enumerationBodyFormula C t | _ => constantBodyFormula C t

theorem bodyFormula_delta0 {d : Nat} (C : ArticleData (Project.Term d)) (i : Fin 6) (t : Project.Term d) : (bodyFormula C i t).IsDelta0 := by
  rcases six_cases i with rfl | rfl | rfl | rfl | rfl | rfl
  · exact binaryBodyFormula_delta0 false C t
  · exact binaryBodyFormula_delta0 true C t
  · exact relationBodyFormula_delta0 false C t
  · exact relationBodyFormula_delta0 true C t
  · exact enumerationBodyFormula_delta0 C t
  · exact constantBodyFormula_delta0 C t

theorem bodyFormula_freeClosed {d : Nat} {C : ArticleData (Project.Term d)} (hC : C.Closed) (i : Fin 6) (t : Project.Term d)
    (ht : t.freeSupport=[]) : (bodyFormula C i t).FreeClosed := by
  rcases six_cases i with rfl | rfl | rfl | rfl | rfl | rfl
  · exact binaryBodyFormula_freeClosed false hC t ht
  · exact binaryBodyFormula_freeClosed true hC t ht
  · exact relationBodyFormula_freeClosed false hC t ht
  · exact relationBodyFormula_freeClosed true hC t ht
  · exact enumerationBodyFormula_freeClosed hC t ht
  · exact constantBodyFormula_freeClosed hC t ht

theorem bodyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (C : ArticleData (Project.Term d)) (i : Fin 6) (t : Project.Term d) :
    Project.Formula.satisfies e (bodyFormula C i t) ↔ Body M (C.eval e) i (t.eval e) := by
  rcases six_cases i with rfl | rfl | rfl | rfl | rfl | rfl
  · exact binaryBodyFormula_iff he e false C t
  · exact binaryBodyFormula_iff he e true C t
  · exact relationBodyFormula_iff he e false C t
  · exact relationBodyFormula_iff he e true C t
  · exact enumerationBodyFormula_iff he e C t
  · exact constantBodyFormula_iff he e C t

def Meaning (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (carrier : M.Domain) (i : Fin 6) (t : M.Domain) : Prop :=
  Graph M t (C.numbers (symbolArity i)) carrier ∧ Body M C i t

def meaningFormula {d : Nat} (C : ArticleData (Project.Term d)) (carrier : Project.Term d) (i : Fin 6) (t : Project.Term d) : Project.Formula 1 d :=
  .conj (graphFormula t (C.numbers (symbolArity i)) carrier) (bodyFormula C i t)

theorem meaningFormula_delta0 {d : Nat} (C : ArticleData (Project.Term d)) (carrier : Project.Term d) (i : Fin 6) (t : Project.Term d) :
    (meaningFormula C carrier i t).IsDelta0 := .conj (graphFormula_delta0 _ _ _) (bodyFormula_delta0 _ _ _)

theorem meaningFormula_freeClosed {d : Nat} {C : ArticleData (Project.Term d)} (hC : C.Closed) (carrier : Project.Term d) (i : Fin 6) (t : Project.Term d)
    (hCarrier : carrier.freeSupport=[]) (ht : t.freeSupport=[]) : (meaningFormula C carrier i t).FreeClosed := by
  simp only [meaningFormula,Definitional.Formula.FreeClosed]
  refine ⟨?_,bodyFormula_freeClosed hC i t ht⟩
  simp [graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hC.numbers,hCarrier,ht]

theorem meaningFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (C : ArticleData (Project.Term d)) (carrier : Project.Term d) (i : Fin 6) (t : Project.Term d) :
    Project.Formula.satisfies e (meaningFormula C carrier i t) ↔ Meaning M (C.eval e) (carrier.eval e) i (t.eval e) := by
  simp only [meaningFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,bodyFormula_iff he]
  rfl

def Interprets (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (carrier r t : M.Domain) : Prop :=
  ∃ i : Fin 6, r=C.numbers i.castSucc ∧ Meaning M C carrier i t

def relationFormula {d : Nat} (C : ArticleData (Project.Term d)) (carrier r t : Project.Term d) : Project.Formula 1 d :=
  finDisjunction (fun i : Fin 6 => .conj (Project.Formula.extensionalEq r (C.numbers i.castSucc)) (meaningFormula C carrier i t))

theorem relationFormula_delta0 {d : Nat} (C : ArticleData (Project.Term d)) (carrier r t : Project.Term d) :
    (relationFormula C carrier r t).IsDelta0 := finDisjunction_delta0 _ (fun _ => .conj (.atom _ _ _) (meaningFormula_delta0 _ _ _ _))

theorem relationFormula_freeClosed {d : Nat} {C : ArticleData (Project.Term d)} (hC : C.Closed) (carrier r t : Project.Term d)
    (hCarrier : carrier.freeSupport=[]) (hr : r.freeSupport=[]) (ht : t.freeSupport=[]) : (relationFormula C carrier r t).FreeClosed := by
  apply finDisjunction_freeClosed
  intro i
  simp only [Definitional.Formula.FreeClosed]
  exact ⟨by simp [hr,hC.numbers],meaningFormula_freeClosed hC carrier i t hCarrier ht⟩

theorem relationFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (C : ArticleData (Project.Term d)) (carrier r t : Project.Term d) :
    Project.Formula.satisfies e (relationFormula C carrier r t) ↔ Interprets M (C.eval e) (carrier.eval e) (r.eval e) (t.eval e) := by
  simp only [relationFormula,finDisjunction_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,meaningFormula_iff he]
  rfl

def articleTerms : ArticleData (Project.Term 24) :=
  ⟨⟨⟨.bound 0,.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,.bound 6⟩,
      .bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12⟩,
    .bound 13,.bound 14,.bound 15,.bound 16,fun i => .bound ⟨i.val+17,by omega⟩⟩

def articleEnv {M : SetTheory.Structure.{u}} (C : ArticleData M.Domain) : Env M 24 :=
  ⟨Fin.cases C.reflection.omega (Fin.cases C.reflection.cap (Fin.cases C.reflection.middle (Fin.cases C.reflection.keys (Fin.cases C.reflection.block (Fin.cases C.reflection.bound (Fin.cases C.reflection.index (Fin.cases C.reflection.pairs (Fin.cases C.reflection.edgeCodes (Fin.cases C.reflection.needCodes (Fin.cases C.reflection.edgeLists (Fin.cases C.reflection.needLists (Fin.cases C.reflection.labels (Fin.cases C.top (Fin.cases C.table (Fin.cases C.enumKeys (Fin.cases C.enumeration (C.numbers))))))))))))))))),fun _ => C.reflection.omega⟩

theorem articleTerms_articleEnv {M : SetTheory.Structure.{u}} (C : ArticleData M.Domain) : articleTerms.eval (articleEnv C)=C := rfl

theorem articleTerms_closed : articleTerms.Closed := by
  refine ⟨?_,rfl,rfl,rfl,rfl,fun _ => rfl⟩
  constructor <;> rfl

def relationSchema : Project.Delta0BinarySchema 25 where
  body := relationFormula articleTerms.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0)
  freeClosed := relationFormula_freeClosed articleTerms_closed.weaken.weaken.weaken _ _ _ rfl rfl rfl
  delta0 := relationFormula_delta0 _ _ _ _

theorem relationSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ArticleData M.Domain) (carrier r t : M.Domain) :
    Project.Formula.satisfies ((((articleEnv C).push carrier).push r).push t) relationSchema.body ↔ Interprets M C carrier r t := by
  rw [relationSchema,relationFormula_iff he]
  simp only [ArticleData.eval_weaken,articleTerms_articleEnv]
  rfl

end KP1Y.ReflectionModel
