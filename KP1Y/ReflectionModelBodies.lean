import KP1Y.ReflectionModelData

/-! 六符号解释的具体有界真值。背景κ不随子结构载域变化，P始终读R的κ顶截面。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def queryBodyFormula {d : Nat} (C : ArticleData (Project.Term d)) (k η a b : Project.Term d) : Project.Formula 1 d :=
  KP1Y.Reflection.queryFormula C.reflection.toIndexData C.table k η a b

theorem queryBodyFormula_delta0 {d : Nat} (C : ArticleData (Project.Term d)) (k η a b : Project.Term d) :
    (queryBodyFormula C k η a b).IsDelta0 := KP1Y.Reflection.queryFormula_delta0 _ _ _ _ _ _

theorem queryBodyFormula_freeClosed {d : Nat} {C : ArticleData (Project.Term d)} (hC : C.Closed) (k η a b : Project.Term d)
    (hk : k.freeSupport=[]) (hη : η.freeSupport=[]) (ha : a.freeSupport=[]) (hb : b.freeSupport=[]) :
    (queryBodyFormula C k η a b).FreeClosed :=
  KP1Y.Reflection.queryFormula_freeClosed _ _ _ _ _ _ hC.reflection.omega hC.reflection.cap hC.reflection.keys
    hC.reflection.index hC.reflection.bound hC.table hk hη ha hb

theorem queryBodyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (C : ArticleData (Project.Term d)) (k η a b : Project.Term d) :
    Project.Formula.satisfies e (queryBodyFormula C k η a b) ↔
      KP1Y.Reflection.Query M (C.eval e).reflection.toIndexData (C.eval e).table (k.eval e) (η.eval e) (a.eval e) (b.eval e) := by
  rw [queryBodyFormula,KP1Y.Reflection.queryFormula_iff he]
  rfl

def BinaryBody (strict : Bool) (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (t : M.Domain) : Prop :=
  ∃ x, M.mem x C.top ∧ ∃ y, M.mem y C.top ∧ MemPair M t (C.numbers 0) x ∧ MemPair M t (C.numbers 1) y ∧
    if strict then M.mem x y else x=y

def binaryBodyFormula {d : Nat} (strict : Bool) (C : ArticleData (Project.Term d)) (t : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem C.top (Project.Formula.existsMem C.top.weaken
    (.conj (memPairFormula t.weaken.weaken (C.numbers 0).weaken.weaken (.bound 1))
      (.conj (memPairFormula t.weaken.weaken (C.numbers 1).weaken.weaken (.bound 0))
        (if strict then .mem (.bound 1) (.bound 0) else Project.Formula.extensionalEq (.bound 1) (.bound 0)))))

theorem binaryBodyFormula_delta0 {d : Nat} (strict : Bool) (C : ArticleData (Project.Term d)) (t : Project.Term d) :
    (binaryBodyFormula strict C t).IsDelta0 := by
  cases strict
  · exact .existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (.atom _ _ _))))
  · exact .existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (.mem _ _))))

theorem binaryBodyFormula_freeClosed {d : Nat} (strict : Bool) {C : ArticleData (Project.Term d)} (hC : C.Closed)
    (t : Project.Term d) (ht : t.freeSupport=[]) : (binaryBodyFormula strict C t).FreeClosed := by
  cases strict <;> simp [binaryBodyFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.top,hC.numbers,ht]

theorem binaryBodyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (strict : Bool) (C : ArticleData (Project.Term d)) (t : Project.Term d) :
    Project.Formula.satisfies e (binaryBodyFormula strict C t) ↔ BinaryBody strict M (C.eval e) (t.eval e) := by
  cases strict <;> simp only [binaryBodyFormula,BinaryBody,Bool.false_eq_true,↓reduceIte,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Term.eval_weaken] <;> rfl

def RelationBody (top : Bool) (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (t : M.Domain) : Prop :=
  ∃ k, M.mem k C.top ∧ ∃ η, M.mem η C.top ∧ ∃ a, M.mem a C.top ∧
    MemPair M t (C.numbers 0) k ∧ MemPair M t (C.numbers 1) η ∧ MemPair M t (C.numbers 2) a ∧
      if top then KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a C.top
      else ∃ b, M.mem b C.top ∧ MemPair M t (C.numbers 3) b ∧ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a b

def relationBodyFormula {d : Nat} (top : Bool) (C : ArticleData (Project.Term d)) (t : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem C.top (Project.Formula.existsMem C.top.weaken (Project.Formula.existsMem C.top.weaken.weaken
    (.conj (memPairFormula t.weaken.weaken.weaken (C.numbers 0).weaken.weaken.weaken (.bound 2))
      (.conj (memPairFormula t.weaken.weaken.weaken (C.numbers 1).weaken.weaken.weaken (.bound 1))
        (.conj (memPairFormula t.weaken.weaken.weaken (C.numbers 2).weaken.weaken.weaken (.bound 0))
          (if top then queryBodyFormula C.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0) C.top.weaken.weaken.weaken
          else Project.Formula.existsMem C.top.weaken.weaken.weaken
            (.conj (memPairFormula t.weaken.weaken.weaken.weaken (C.numbers 3).weaken.weaken.weaken.weaken (.bound 0))
              (queryBodyFormula C.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) (.bound 0)))))))))

theorem relationBodyFormula_delta0 {d : Nat} (top : Bool) (C : ArticleData (Project.Term d)) (t : Project.Term d) :
    (relationBodyFormula top C t).IsDelta0 := by
  cases top
  · exact .existsMem _ (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (queryBodyFormula_delta0 _ _ _ _ _))))))))
  · exact .existsMem _ (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (queryBodyFormula_delta0 _ _ _ _ _))))))

theorem relationBodyFormula_freeClosed {d : Nat} (top : Bool) {C : ArticleData (Project.Term d)} (hC : C.Closed)
    (t : Project.Term d) (ht : t.freeSupport=[]) : (relationBodyFormula top C t).FreeClosed := by
  have hR := queryBodyFormula_freeClosed hC.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl
  have hP := queryBodyFormula_freeClosed hC.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0) C.top.weaken.weaken.weaken
    rfl rfl rfl (by simpa using hC.top)
  cases top <;> simp [relationBodyFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.top,hC.numbers,ht,hR,hP]

theorem relationBodyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (top : Bool) (C : ArticleData (Project.Term d)) (t : Project.Term d) :
    Project.Formula.satisfies e (relationBodyFormula top C t) ↔ RelationBody top M (C.eval e) (t.eval e) := by
  cases top <;> simp only [relationBodyFormula,RelationBody,Bool.false_eq_true,↓reduceIte,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,queryBodyFormula_iff he,ArticleData.eval_weaken,Term.eval_weaken] <;> rfl

def EnumerationBody (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (t : M.Domain) : Prop :=
  ∃ a, M.mem a C.top ∧ ∃ n, M.mem n C.top ∧ ∃ x, M.mem x C.top ∧
    MemPair M t (C.numbers 0) a ∧ MemPair M t (C.numbers 1) n ∧ MemPair M t (C.numbers 2) x ∧
      EnumValue M C.reflection.omega C.enumKeys C.enumeration (C.numbers 0) a n x

def enumerationBodyFormula {d : Nat} (C : ArticleData (Project.Term d)) (t : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem C.top (Project.Formula.existsMem C.top.weaken (Project.Formula.existsMem C.top.weaken.weaken
    (.conj (memPairFormula t.weaken.weaken.weaken (C.numbers 0).weaken.weaken.weaken (.bound 2))
      (.conj (memPairFormula t.weaken.weaken.weaken (C.numbers 1).weaken.weaken.weaken (.bound 1))
        (.conj (memPairFormula t.weaken.weaken.weaken (C.numbers 2).weaken.weaken.weaken (.bound 0))
          (enumValueFormula C.reflection.omega.weaken.weaken.weaken C.enumKeys.weaken.weaken.weaken C.enumeration.weaken.weaken.weaken
            (C.numbers 0).weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0)))))))

theorem enumerationBodyFormula_delta0 {d : Nat} (C : ArticleData (Project.Term d)) (t : Project.Term d) :
    (enumerationBodyFormula C t).IsDelta0 := .existsMem _ (.existsMem _ (.existsMem _
      (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
        (.conj (memPairFormula_delta0 _ _ _) (enumValueFormula_delta0 _ _ _ _ _ _ _))))))

theorem enumerationBodyFormula_freeClosed {d : Nat} {C : ArticleData (Project.Term d)} (hC : C.Closed)
    (t : Project.Term d) (ht : t.freeSupport=[]) : (enumerationBodyFormula C t).FreeClosed := by
  simp [enumerationBodyFormula,enumValueFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.top,hC.numbers,hC.reflection.omega,hC.enumKeys,hC.enumeration,ht]

theorem enumerationBodyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (C : ArticleData (Project.Term d)) (t : Project.Term d) :
    Project.Formula.satisfies e (enumerationBodyFormula C t) ↔ EnumerationBody M (C.eval e) (t.eval e) := by
  simp only [enumerationBodyFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,enumValueFormula_iff he,Term.eval_weaken]
  rfl

def ConstantBody (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (t : M.Domain) : Prop :=
  MemPair M t (C.numbers 0) C.reflection.omega

def constantBodyFormula {d : Nat} (C : ArticleData (Project.Term d)) (t : Project.Term d) : Project.Formula 1 d :=
  memPairFormula t (C.numbers 0) C.reflection.omega

theorem constantBodyFormula_delta0 {d : Nat} (C : ArticleData (Project.Term d)) (t : Project.Term d) :
    (constantBodyFormula C t).IsDelta0 := memPairFormula_delta0 _ _ _

theorem constantBodyFormula_freeClosed {d : Nat} {C : ArticleData (Project.Term d)} (hC : C.Closed)
    (t : Project.Term d) (ht : t.freeSupport=[]) : (constantBodyFormula C t).FreeClosed := by
  simp [constantBodyFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hC.reflection.omega,hC.numbers,ht]

theorem constantBodyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (C : ArticleData (Project.Term d)) (t : Project.Term d) :
    Project.Formula.satisfies e (constantBodyFormula C t) ↔ ConstantBody M (C.eval e) (t.eval e) := by
  rw [constantBodyFormula,memPairFormula_iff he]
  rfl

end KP1Y.ReflectionModel
