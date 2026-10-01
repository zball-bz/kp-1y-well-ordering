import KP1Y.OneYTowerCanonSetting

/-! Lower 层输入谓词的字面对象公式，供对间隔的对象反向归纳。
主体 `InputsBody` 逐项对应 `LowerInputs` 的 prefixTop/fixed/order/select，
其中 FrameCopy 以其精确 raw 父规则 `RawCopy` 表达，伪父森林相等以伪父关系直接表达。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

/-- FrameCopy 的精确 raw 父规则（宽 n）。 -/
def RawCopy (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (n F F' : M.Domain) : Prop :=
  Forest M C.omega n F' ∧ ∀ c, M.mem c n → ∀ t, MemPair M F' c t ↔ FrameCopy.RawParent M C T A F c t

/-- 一层 lower 输入的主体（对象均已读出）。 -/
def InputsBody (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m n forests sH sP V1 Q1 newTop P1 : M.Domain) : Prop :=
  (∀ c, M.mem c A.last → ∀ v, MemPair M newTop c v ↔ MemPair M V1 c v) ∧
  (∀ s, M.mem A.root s → M.mem s A.last → (∀ q, MemPair M Q1 s q → M.mem q A.root) →
    ∀ b c v, CopyCoordinates.ParentCopy M C T A b s c → M.mem c n → MemPair M V1 s v → MemPair M newTop c v) ∧
  (∀ z c, M.mem A.root z → M.mem z c → (c=A.last ∨ M.mem c A.last) →
    (∀ p, GraphPseudoParent M C ⟨m,sH,forests,sP⟩ c p ↔ GraphPseudoParent M C ⟨m,sH,forests,sP⟩ z p) →
    ∀ vc vz, MemPair M V1 c vc → MemPair M V1 z vz → (vc=vz ∨ M.mem vc vz) →
    ∀ b cc zz tc tz, CopyCoordinates.ParentCopy M C T A b c cc → CopyCoordinates.ParentCopy M C T A b z zz →
      MemPair M newTop cc tc → MemPair M newTop zz tz → (tc=tz ∨ M.mem tc tz)) ∧
  (∀ F F', Selects true M C m F V1 Q1 → RawCopy M C T A n F F' → Selects true M C n F' newTop P1) ∧
  (∀ s b c, M.mem A.root s → M.mem s A.last → CopyCoordinates.ParentCopy M C T A b s c → M.mem c n →
    ∀ p, MemPair M P1 c p ↔ ∃ q, MemPair M Q1 s q ∧ CopyCoordinates.ParentCopy M C T A b q p)

/-- 对间隔归纳的谓词：从层号k读出源k层山形码、源k+1层行、塔在k+1处的重建行与底父图。 -/
def InputsAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m n forests Gs H Hr G k : M.Domain) : Prop :=
  ∀ k1 sCode sH sP state1 V1 Q1 newTop code1 h1 p1 P1, M.SuccessorOf k1 k → MemPair M Gs k sCode →
    Codes M sCode sH sP → MemPair M H k1 state1 → Codes M state1 V1 Q1 → MemPair M Hr k1 newTop →
    MemPair M G k1 code1 → Codes M code1 h1 p1 → MemPair M p1 C.zero P1 →
    InputsBody M C T A m n forests sH sP V1 Q1 newTop P1

section Formulas
variable {d : Nat}

def rawParentFormula (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (P child target : Project.Term d) : Project.Formula 1 d :=
  .disj (.conj (.disj (Project.Formula.extensionalEq child A.last) (.mem child A.last)) (memPairFormula P child target))
    (.conj (.mem A.last child) (Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
      (.conj (CopyCoordinates.rawDecodedFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken child.weaken.weaken (.bound 1) (.bound 0))
        (Project.Formula.existsMem A.last.weaken.weaken (.conj (memPairFormula P.weaken.weaken.weaken (.bound 2) (.bound 0))
          (CopyCoordinates.parentCopyFormula C.weaken.weaken.weaken T.weaken.weaken.weaken A.weaken.weaken.weaken
            (.bound 1) (.bound 0) target.weaken.weaken.weaken)))))))

def rawCopyFormula (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (n F F' : Project.Term d) : Project.Formula 1 d :=
  .conj (forestFormula C.omega n F') (Project.Formula.forallMem n (.forallE
    (.iff (memPairFormula F'.weaken.weaken (.bound 1) (.bound 0))
      (rawParentFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken F.weaken.weaken (.bound 1) (.bound 0)))))

def prefixFormula (A : CopyCoordinates.Context (Project.Term d)) (newTop V1 : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.forallMem A.last (.forallE (.iff (memPairFormula newTop.weaken.weaken (.bound 1) (.bound 0))
    (memPairFormula V1.weaken.weaken (.bound 1) (.bound 0))))

def fixedFormula (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (n V1 Q1 newTop : Project.Term d) : Project.Formula 1 d :=
  .forallE (.imp (.mem A.root.weaken (.bound 0)) (.imp (.mem (.bound 0) A.last.weaken)
    (.imp (.forallE (.imp (memPairFormula Q1.weaken.weaken (.bound 1) (.bound 0)) (.mem (.bound 0) A.root.weaken.weaken)))
      (.forallE (.forallE (.forallE
        (.imp (CopyCoordinates.parentCopyFormula C.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken
            A.weaken.weaken.weaken.weaken (.bound 2) (.bound 3) (.bound 1))
          (.imp (.mem (.bound 1) n.weaken.weaken.weaken.weaken)
            (.imp (memPairFormula V1.weaken.weaken.weaken.weaken (.bound 3) (.bound 0))
              (memPairFormula newTop.weaken.weaken.weaken.weaken (.bound 1) (.bound 0)))))))))))

def orderFormula (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (X : Data (Project.Term d)) (V1 newTop : Project.Term d) : Project.Formula 1 d :=
  .forallE (.forallE (.imp (.mem A.root.weaken.weaken (.bound 1)) (.imp (.mem (.bound 1) (.bound 0))
    (.imp (.disj (Project.Formula.extensionalEq (.bound 0) A.last.weaken.weaken) (.mem (.bound 0) A.last.weaken.weaken))
      (.imp (.forallE (.iff (graphPseudoParentFormula C.weaken.weaken.weaken X.weaken.weaken.weaken (.bound 1) (.bound 0))
          (graphPseudoParentFormula C.weaken.weaken.weaken X.weaken.weaken.weaken (.bound 2) (.bound 0))))
        (.forallE (.forallE (.imp (memPairFormula V1.weaken.weaken.weaken.weaken (.bound 2) (.bound 1))
          (.imp (memPairFormula V1.weaken.weaken.weaken.weaken (.bound 3) (.bound 0))
            (.imp (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0)))
              (.forallE (.forallE (.forallE (.forallE (.forallE
                (.imp (CopyCoordinates.parentCopyFormula C.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                    T.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                    A.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 7) (.bound 3))
                  (.imp (CopyCoordinates.parentCopyFormula C.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                      T.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                      A.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 8) (.bound 2))
                    (.imp (memPairFormula newTop.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
                      (.imp (memPairFormula newTop.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
                        (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0))))))))))))))))))))))

def selectFormula (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (m n V1 Q1 newTop P1 : Project.Term d) : Project.Formula 1 d :=
  .forallE (.forallE (.imp (selectsFormula true C.weaken.weaken m.weaken.weaken (.bound 1) V1.weaken.weaken Q1.weaken.weaken)
    (.imp (rawCopyFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken n.weaken.weaken (.bound 1) (.bound 0))
      (selectsFormula true C.weaken.weaken n.weaken.weaken (.bound 0) newTop.weaken.weaken P1.weaken.weaken))))

def nonrootFormula (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (n Q1 P1 : Project.Term d) : Project.Formula 1 d :=
  .forallE (.forallE (.forallE (.imp (.mem A.root.weaken.weaken.weaken (.bound 2)) (.imp (.mem (.bound 2) A.last.weaken.weaken.weaken)
    (.imp (CopyCoordinates.parentCopyFormula C.weaken.weaken.weaken T.weaken.weaken.weaken A.weaken.weaken.weaken (.bound 1) (.bound 2) (.bound 0))
      (.imp (.mem (.bound 0) n.weaken.weaken.weaken)
        (.forallE (.iff (memPairFormula P1.weaken.weaken.weaken.weaken (.bound 1) (.bound 0))
          (.existsE (.conj (memPairFormula Q1.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 0))
            (CopyCoordinates.parentCopyFormula C.weaken.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken.weaken
              A.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 0) (.bound 1))))))))))))

def inputsBodyFormula (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (m n forests sH sP V1 Q1 newTop P1 : Project.Term d) : Project.Formula 1 d :=
  .conj (prefixFormula A newTop V1) (.conj (fixedFormula C T A n V1 Q1 newTop)
    (.conj (orderFormula C T A ⟨m,sH,forests,sP⟩ V1 newTop)
      (.conj (selectFormula C T A m n V1 Q1 newTop P1) (nonrootFormula C T A n Q1 P1))))

end Formulas

section FreeClosed
variable {d : Nat} {C : ExpressionData (Project.Term d)} {T : MatrixArithmetic (Project.Term d)}
  {A : CopyCoordinates.Context (Project.Term d)}

theorem rawParentFormula_freeClosed (hC : C.Closed) (hT : CopyCoordinates.ArithmeticClosed T) (hA : A.Closed)
    (P child target : Project.Term d) (hP : P.freeSupport=[]) (hc : child.freeSupport=[]) (ht : target.freeSupport=[]) :
    (rawParentFormula C T A P child target).FreeClosed := by
  have hRaw := CopyCoordinates.rawDecodedFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken
    child.weaken.weaken (.bound 1) (.bound 0) (by simpa using hc) rfl rfl
  have hCopy := CopyCoordinates.parentCopyFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken hA.weaken.weaken.weaken
    (.bound 1) (.bound 0) target.weaken.weaken.weaken rfl rfl (by simpa using ht)
  simp [rawParentFormula,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,hC.omega,hA.last,hP,hc,ht,hRaw,hCopy]

theorem rawCopyFormula_freeClosed (hC : C.Closed) (hT : CopyCoordinates.ArithmeticClosed T) (hA : A.Closed)
    (n F F' : Project.Term d) (hn : n.freeSupport=[]) (hF : F.freeSupport=[]) (hF' : F'.freeSupport=[]) :
    (rawCopyFormula C T A n F F').FreeClosed := by
  have hForest := forestFormula_freeClosed C.omega n F' hC.omega hn hF'
  have hRaw := rawParentFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken F.weaken.weaken
    (.bound 1) (.bound 0) (by simpa using hF) rfl rfl
  simp [rawCopyFormula,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,hn,hF',hForest,hRaw]

theorem inputsBodyFormula_freeClosed (hC : C.Closed) (hT : CopyCoordinates.ArithmeticClosed T) (hA : A.Closed)
    (m n forests sH sP V1 Q1 newTop P1 : Project.Term d)
    (hm : m.freeSupport=[]) (hn : n.freeSupport=[]) (hforests : forests.freeSupport=[]) (hsH : sH.freeSupport=[])
    (hsP : sP.freeSupport=[]) (hV1 : V1.freeSupport=[]) (hQ1 : Q1.freeSupport=[]) (hTop : newTop.freeSupport=[])
    (hP1 : P1.freeSupport=[]) : (inputsBodyFormula C T A m n forests sH sP V1 Q1 newTop P1).FreeClosed := by
  have hX : (⟨m,sH,forests,sP⟩ : Data (Project.Term d)).Closed := ⟨hm,hsH,hforests,hsP⟩
  have hFixedPC := CopyCoordinates.parentCopyFormula_freeClosed hC.weaken.weaken.weaken.weaken hT.weaken.weaken.weaken.weaken
    hA.weaken.weaken.weaken.weaken (.bound 2) (.bound 3) (.bound 1) rfl rfl rfl
  have hOrdGPP1 := graphPseudoParentFormula_freeClosed hC.weaken.weaken.weaken hX.weaken.weaken.weaken (.bound 1) (.bound 0) rfl rfl
  have hOrdGPP2 := graphPseudoParentFormula_freeClosed hC.weaken.weaken.weaken hX.weaken.weaken.weaken (.bound 2) (.bound 0) rfl rfl
  have hOrdPC1 := CopyCoordinates.parentCopyFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
    hT.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken hA.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
    (.bound 4) (.bound 7) (.bound 3) rfl rfl rfl
  have hOrdPC2 := CopyCoordinates.parentCopyFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
    hT.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken hA.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
    (.bound 4) (.bound 8) (.bound 2) rfl rfl rfl
  have hSel1 := selectsFormula_freeClosed true hC.weaken.weaken m.weaken.weaken (.bound 1) V1.weaken.weaken Q1.weaken.weaken
    (by simpa using hm) rfl (by simpa using hV1) (by simpa using hQ1)
  have hSelRaw := rawCopyFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken n.weaken.weaken (.bound 1) (.bound 0)
    (by simpa using hn) rfl rfl
  have hSel2 := selectsFormula_freeClosed true hC.weaken.weaken n.weaken.weaken (.bound 0) newTop.weaken.weaken P1.weaken.weaken
    (by simpa using hn) rfl (by simpa using hTop) (by simpa using hP1)
  have hNonPC1 := CopyCoordinates.parentCopyFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken hA.weaken.weaken.weaken
    (.bound 1) (.bound 2) (.bound 0) rfl rfl rfl
  have hNonPC2 := CopyCoordinates.parentCopyFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken hT.weaken.weaken.weaken.weaken.weaken
    hA.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 0) (.bound 1) rfl rfl rfl
  simp [inputsBodyFormula,prefixFormula,fixedFormula,orderFormula,selectFormula,nonrootFormula,
    Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    hA.last,hA.root,hn,hV1,hQ1,hTop,hP1,hFixedPC,hOrdGPP1,hOrdGPP2,hOrdPC1,hOrdPC2,hSel1,hSelRaw,hSel2,hNonPC1,hNonPC2]

end FreeClosed

section Iff
variable {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
  (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d)) (A : CopyCoordinates.Context (Project.Term d))
include he

theorem rawParentFormula_iff (P child target : Project.Term d) :
    Project.Formula.satisfies e (rawParentFormula C T A P child target) ↔
      FrameCopy.RawParent M (C.eval e) (T.eval e) (A.eval e) (P.eval e) (child.eval e) (target.eval e) := by
  simp only [rawParentFormula,FrameCopy.RawParent,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,memPairFormula_iff he,
    Project.Formula.satisfies_existsMem_iff,CopyCoordinates.rawDecodedFormula_iff he,CopyCoordinates.parentCopyFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Term.eval_weaken]
  rfl

theorem rawCopyFormula_iff (n F F' : Project.Term d) :
    Project.Formula.satisfies e (rawCopyFormula C T A n F F') ↔
      RawCopy M (C.eval e) (T.eval e) (A.eval e) (n.eval e) (F.eval e) (F'.eval e) := by
  simp only [rawCopyFormula,RawCopy,Project.Formula.satisfies_conj_iff,forestFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    memPairFormula_iff he,rawParentFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Term.eval_weaken]
  rfl

theorem inputsBodyFormula_iff (m n forests sH sP V1 Q1 newTop P1 : Project.Term d) :
    Project.Formula.satisfies e (inputsBodyFormula C T A m n forests sH sP V1 Q1 newTop P1) ↔
      InputsBody M (C.eval e) (T.eval e) (A.eval e) (m.eval e) (n.eval e) (forests.eval e) (sH.eval e) (sP.eval e)
        (V1.eval e) (Q1.eval e) (newTop.eval e) (P1.eval e) := by
  simp only [inputsBodyFormula,prefixFormula,fixedFormula,orderFormula,selectFormula,nonrootFormula,InputsBody,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    memPairFormula_iff he,CopyCoordinates.parentCopyFormula_iff he,graphPseudoParentFormula_iff he,selectsFormula_iff he,
    rawCopyFormula_iff he,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,
    Data.eval_weaken,Term.eval_weaken]
  rfl

end Iff

end KP1Y.OneYFinite.TowerCanon
