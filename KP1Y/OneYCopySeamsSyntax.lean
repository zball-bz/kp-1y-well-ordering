import KP1Y.OneYCopySeamsStage

/-! 复制块不变量Stage的对象公式及满足等价；对象自然数归纳只使用这里的公式。 -/
namespace KP1Y.OneYFinite.CopySeams
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Reflection
open KP1Y.OneYFinite.CopyCoordinates
universe u

def edgesHoldFormula {n : Nat} (C : ExpressionData (Project.Term n)) (D : Reflection.Data (Project.Term n))
    (Tab Big width g : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken
    (Project.Formula.forallMem C.omega.weaken.weaken (Project.Formula.forallMem width.weaken.weaken.weaken
      (.imp (edgeAtFormula D.weaken.weaken.weaken.weaken Big.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) (.bound 0))
        (edgeTruthFormula D.weaken.weaken.weaken.weaken Tab.weaken.weaken.weaken.weaken g.weaken.weaken.weaken.weaken
          (.bound 3) (.bound 2) (.bound 1) (.bound 0))))))

theorem edgesHoldFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {D : Reflection.Data (Project.Term n)} (hD : D.Closed) (Tab Big width g : Project.Term n)
    (hTab : Tab.freeSupport=[]) (hBig : Big.freeSupport=[]) (hw : width.freeSupport=[]) (hg : g.freeSupport=[]) :
    (edgesHoldFormula C D Tab Big width g).FreeClosed := by
  have hEdge := edgeAtFormula_freeClosed hD.weaken.weaken.weaken.weaken Big.weaken.weaken.weaken.weaken
    (.bound 3) (.bound 2) (.bound 1) (.bound 0) (by simpa using hBig) rfl rfl rfl rfl
  have hTruth := edgeTruthFormula_freeClosed hD.weaken.weaken.weaken.weaken Tab.weaken.weaken.weaken.weaken
    g.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) (.bound 0) (by simpa using hTab) (by simpa using hg)
    rfl rfl rfl rfl
  simp [edgesHoldFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hw,hEdge,hTruth]

theorem edgesHoldFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (D : Reflection.Data (Project.Term n)) (Tab Big width g : Project.Term n) :
    Project.Formula.satisfies e (edgesHoldFormula C D Tab Big width g) ↔
      EdgesHold M (C.eval e) (D.eval e) (Tab.eval e) (Big.eval e) (width.eval e) (g.eval e) := by
  simp only [edgesHoldFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    edgeAtFormula_iff he,edgeTruthFormula_iff he,Data.eval_weaken,Term.eval_weaken]
  rfl

def factsHoldFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Reflection.Data (Project.Term n)) (A : Context (Project.Term n)) (Tab Original B b g : Project.Term n) :
    Project.Formula 1 n :=
  Project.Formula.forallMem B (Project.Formula.forallMem C.omega.weaken
    (Project.Formula.forallMem C.omega.weaken.weaken (Project.Formula.forallMem A.last.weaken.weaken.weaken
      (.imp (edgeAtFormula D.weaken.weaken.weaken.weaken Original.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) (.bound 0))
        (Project.Formula.forallMem C.omega.weaken.weaken.weaken.weaken
          (Project.Formula.forallMem C.omega.weaken.weaken.weaken.weaken.weaken
            (Project.Formula.forallMem C.omega.weaken.weaken.weaken.weaken.weaken.weaken
              (.imp (parentCopyFormula C.weaken.weaken.weaken.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                  A.weaken.weaken.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 2))
                (.imp (parentCopyFormula C.weaken.weaken.weaken.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                    A.weaken.weaken.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 1))
                  (.imp (parentCopyFormula C.weaken.weaken.weaken.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                      A.weaken.weaken.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 0))
                    (edgeTruthFormula D.weaken.weaken.weaken.weaken.weaken.weaken.weaken Tab.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                      g.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6) (.bound 2) (.bound 1) (.bound 0))))))))))))

theorem factsHoldFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {D : Reflection.Data (Project.Term n)} (hD : D.Closed)
    {A : Context (Project.Term n)} (hA : A.Closed) (Tab Original B b g : Project.Term n)
    (hTab : Tab.freeSupport=[]) (hOriginal : Original.freeSupport=[]) (hB : B.freeSupport=[]) (hb : b.freeSupport=[])
    (hg : g.freeSupport=[]) : (factsHoldFormula C T D A Tab Original B b g).FreeClosed := by
  have hEdge := edgeAtFormula_freeClosed hD.weaken.weaken.weaken.weaken Original.weaken.weaken.weaken.weaken
    (.bound 3) (.bound 2) (.bound 1) (.bound 0) (by simpa using hOriginal) rfl rfl rfl rfl
  have hC7 := hC.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  have hT7 := hT.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  have hA7 := hA.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  have hb7 : b.weaken.weaken.weaken.weaken.weaken.weaken.weaken.freeSupport=[] := by simpa using hb
  have hP1 := parentCopyFormula_freeClosed hC7 hT7 hA7 _ (.bound 5) (.bound 2) hb7 rfl rfl
  have hP2 := parentCopyFormula_freeClosed hC7 hT7 hA7 _ (.bound 4) (.bound 1) hb7 rfl rfl
  have hP3 := parentCopyFormula_freeClosed hC7 hT7 hA7 _ (.bound 3) (.bound 0) hb7 rfl rfl
  have hTruth := edgeTruthFormula_freeClosed hD.weaken.weaken.weaken.weaken.weaken.weaken.weaken
    Tab.weaken.weaken.weaken.weaken.weaken.weaken.weaken g.weaken.weaken.weaken.weaken.weaken.weaken.weaken
    (.bound 6) (.bound 2) (.bound 1) (.bound 0) (by simpa using hTab) (by simpa using hg) rfl rfl rfl rfl
  simp [factsHoldFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hA.last,hB,
    hEdge,hP1,hP2,hP3,hTruth]

theorem factsHoldFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (D : Reflection.Data (Project.Term n))
    (A : Context (Project.Term n)) (Tab Original B b g : Project.Term n) :
    Project.Formula.satisfies e (factsHoldFormula C T D A Tab Original B b g) ↔
      FactsHold M (C.eval e) (T.eval e) (D.eval e) (A.eval e) (Tab.eval e) (Original.eval e) (B.eval e) (b.eval e) (g.eval e) := by
  simp only [factsHoldFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    edgeAtFormula_iff he,edgeTruthFormula_iff he,parentCopyFormula_iff he,Data.eval_weaken,ExpressionData.eval_weaken,
    MatrixArithmetic.eval_weaken,Context.eval_weaken,Term.eval_weaken]
  rfl

def templatesHoldFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Reflection.Data (Project.Term n)) (A : Context (Project.Term n)) (Tab Original B b g beta : Project.Term n) :
    Project.Formula 1 n :=
  Project.Formula.forallMem B (Project.Formula.forallMem C.omega.weaken (Project.Formula.forallMem C.omega.weaken.weaken
    (.imp (edgeAtFormula D.weaken.weaken.weaken Original.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0) A.last.weaken.weaken.weaken)
      (Project.Formula.forallMem C.omega.weaken.weaken.weaken (Project.Formula.forallMem C.omega.weaken.weaken.weaken.weaken
        (.imp (parentCopyFormula C.weaken.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken.weaken
            A.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (.imp (parentCopyFormula C.weaken.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken.weaken
              A.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
            (needTruthFormula D.weaken.weaken.weaken.weaken.weaken Tab.weaken.weaken.weaken.weaken.weaken
              g.weaken.weaken.weaken.weaken.weaken beta.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 1) (.bound 0)))))))))

theorem templatesHoldFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {D : Reflection.Data (Project.Term n)} (hD : D.Closed)
    {A : Context (Project.Term n)} (hA : A.Closed) (Tab Original B b g beta : Project.Term n)
    (hTab : Tab.freeSupport=[]) (hOriginal : Original.freeSupport=[]) (hB : B.freeSupport=[]) (hb : b.freeSupport=[])
    (hg : g.freeSupport=[]) (hbeta : beta.freeSupport=[]) : (templatesHoldFormula C T D A Tab Original B b g beta).FreeClosed := by
  have hEdge := edgeAtFormula_freeClosed hD.weaken.weaken.weaken Original.weaken.weaken.weaken
    (.bound 2) (.bound 1) (.bound 0) A.last.weaken.weaken.weaken (by simpa using hOriginal) rfl rfl rfl (by simpa using hA.last)
  have hC5 := hC.weaken.weaken.weaken.weaken.weaken
  have hT5 := hT.weaken.weaken.weaken.weaken.weaken
  have hA5 := hA.weaken.weaken.weaken.weaken.weaken
  have hb5 : b.weaken.weaken.weaken.weaken.weaken.freeSupport=[] := by simpa using hb
  have hP1 := parentCopyFormula_freeClosed hC5 hT5 hA5 _ (.bound 3) (.bound 1) hb5 rfl rfl
  have hP2 := parentCopyFormula_freeClosed hC5 hT5 hA5 _ (.bound 2) (.bound 0) hb5 rfl rfl
  have hTruth := needTruthFormula_freeClosed hD.weaken.weaken.weaken.weaken.weaken Tab.weaken.weaken.weaken.weaken.weaken
    g.weaken.weaken.weaken.weaken.weaken beta.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 1) (.bound 0)
    (by simpa using hTab) (by simpa using hg) (by simpa using hbeta) rfl rfl rfl
  simp [templatesHoldFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hB,
    hEdge,hP1,hP2,hTruth]

theorem templatesHoldFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (D : Reflection.Data (Project.Term n))
    (A : Context (Project.Term n)) (Tab Original B b g beta : Project.Term n) :
    Project.Formula.satisfies e (templatesHoldFormula C T D A Tab Original B b g beta) ↔
      TemplatesHold M (C.eval e) (T.eval e) (D.eval e) (A.eval e) (Tab.eval e) (Original.eval e) (B.eval e) (b.eval e)
        (g.eval e) (beta.eval e) := by
  simp only [templatesHoldFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    edgeAtFormula_iff he,needTruthFormula_iff he,parentCopyFormula_iff he,Data.eval_weaken,ExpressionData.eval_weaken,
    MatrixArithmetic.eval_weaken,Context.eval_weaken,Term.eval_weaken]
  rfl

def controlHoldsFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Reflection.Data (Project.Term n)) (A : Context (Project.Term n)) (Tab K qControl b g beta : Project.Term n) :
    Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken
    (.imp (encodeFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken A.root.weaken.weaken b.weaken.weaken (.bound 1))
      (.imp (parentCopyFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken b.weaken.weaken qControl.weaken.weaken (.bound 0))
        (Project.Formula.forallMem D.cap.weaken.weaken (Project.Formula.forallMem D.cap.weaken.weaken.weaken
          (.imp (memPairFormula g.weaken.weaken.weaken.weaken (.bound 2) (.bound 1))
            (.imp (memPairFormula g.weaken.weaken.weaken.weaken (.bound 3) (.bound 0))
              (queryFormula D.toIndexData.weaken.weaken.weaken.weaken Tab.weaken.weaken.weaken.weaken K.weaken.weaken.weaken.weaken
                (.bound 1) (.bound 0) beta.weaken.weaken.weaken.weaken))))))))

theorem controlHoldsFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {D : Reflection.Data (Project.Term n)} (hD : D.Closed)
    {A : Context (Project.Term n)} (hA : A.Closed) (Tab K qControl b g beta : Project.Term n)
    (hTab : Tab.freeSupport=[]) (hK : K.freeSupport=[]) (hq : qControl.freeSupport=[]) (hb : b.freeSupport=[])
    (hg : g.freeSupport=[]) (hbeta : beta.freeSupport=[]) : (controlHoldsFormula C T D A Tab K qControl b g beta).FreeClosed := by
  have hEnc := encodeFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken A.root.weaken.weaken
    b.weaken.weaken (.bound 1) (by simpa using hA.root) (by simpa using hb) rfl
  have hPC := parentCopyFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken b.weaken.weaken
    qControl.weaken.weaken (.bound 0) (by simpa using hb) (by simpa using hq) rfl
  have hQuery := queryFormula_freeClosed D.toIndexData.weaken.weaken.weaken.weaken Tab.weaken.weaken.weaken.weaken
    K.weaken.weaken.weaken.weaken (.bound 1) (.bound 0) beta.weaken.weaken.weaken.weaken
    (by simpa [IndexData.weaken,IndexData.map] using hD.omega) (by simpa [IndexData.weaken,IndexData.map] using hD.cap)
    (by simpa [IndexData.weaken,IndexData.map] using hD.keys) (by simpa [IndexData.weaken,IndexData.map] using hD.index)
    (by simpa [IndexData.weaken,IndexData.map] using hD.bound) (by simpa using hTab) (by simpa using hK) rfl rfl
    (by simpa using hbeta)
  simp [controlHoldsFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.omega,hD.cap,hg,hEnc,hPC,hQuery]

theorem controlHoldsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (D : Reflection.Data (Project.Term n))
    (A : Context (Project.Term n)) (Tab K qControl b g beta : Project.Term n) :
    Project.Formula.satisfies e (controlHoldsFormula C T D A Tab K qControl b g beta) ↔
      ControlHolds M (C.eval e) (T.eval e) (D.eval e) (A.eval e) (Tab.eval e) (K.eval e) (qControl.eval e) (b.eval e)
        (g.eval e) (beta.eval e) := by
  simp only [controlHoldsFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    encodeFormula_iff he,parentCopyFormula_iff he,memPairFormula_iff he,queryFormula_iff he,IndexData.eval_weaken,
    Data.eval_index,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Context.eval_weaken,Term.eval_weaken]
  rfl

end KP1Y.OneYFinite.CopySeams
