import KP1Y.OneYCopySeamsSyntax
import KP1Y.OneYCopySeamsStep

/-! 对内部b≤N的Stage公式作对象自然数归纳；得到任意内部N处实际复制图的有界表示（Y04b）。 -/
namespace KP1Y.OneYFinite.CopySeams
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Reflection
open KP1Y.OneYFinite.CopyCoordinates
universe u

def stageFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Reflection.Data (Project.Term n)) (A : Context (Project.Term n))
    (Tab Original Big B K qControl beta b : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem D.labels.weaken
    (.conj (encodeFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken A.last.weaken.weaken b.weaken.weaken (.bound 1))
    (.conj (labelingFormula D.weaken.weaken (.bound 1) (.bound 0))
    (.conj (belowFormula D.weaken.weaken (.bound 1) (.bound 0) beta.weaken.weaken)
    (.conj (edgesHoldFormula C.weaken.weaken D.weaken.weaken Tab.weaken.weaken Big.weaken.weaken (.bound 1) (.bound 0))
    (.conj (factsHoldFormula C.weaken.weaken T.weaken.weaken D.weaken.weaken A.weaken.weaken Tab.weaken.weaken
      Original.weaken.weaken B.weaken.weaken b.weaken.weaken (.bound 0))
    (.conj (templatesHoldFormula C.weaken.weaken T.weaken.weaken D.weaken.weaken A.weaken.weaken Tab.weaken.weaken
      Original.weaken.weaken B.weaken.weaken b.weaken.weaken (.bound 0) beta.weaken.weaken)
      (controlHoldsFormula C.weaken.weaken T.weaken.weaken D.weaken.weaken A.weaken.weaken Tab.weaken.weaken
        K.weaken.weaken qControl.weaken.weaken b.weaken.weaken (.bound 0) beta.weaken.weaken))))))))

theorem stageFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {D : Reflection.Data (Project.Term n)} (hD : D.Closed)
    {A : Context (Project.Term n)} (hA : A.Closed) (Tab Original Big B K qControl beta b : Project.Term n)
    (hTab : Tab.freeSupport=[]) (hOriginal : Original.freeSupport=[]) (hBig : Big.freeSupport=[]) (hB : B.freeSupport=[])
    (hK : K.freeSupport=[]) (hq : qControl.freeSupport=[]) (hbeta : beta.freeSupport=[]) (hb : b.freeSupport=[]) :
    (stageFormula C T D A Tab Original Big B K qControl beta b).FreeClosed := by
  have hC2 := hC.weaken.weaken
  have hT2 := hT.weaken.weaken
  have hD2 := hD.weaken.weaken
  have hA2 := hA.weaken.weaken
  have hTab2 : Tab.weaken.weaken.freeSupport=[] := by simpa using hTab
  have hb2 : b.weaken.weaken.freeSupport=[] := by simpa using hb
  have hbeta2 : beta.weaken.weaken.freeSupport=[] := by simpa using hbeta
  have hEnc := encodeFormula_freeClosed hC2 hT2 hA2 A.last.weaken.weaken b.weaken.weaken (.bound 1)
    (by simpa using hA.last) hb2 rfl
  have hLab := labelingFormula_freeClosed hD2 (.bound 1) (.bound 0) rfl rfl
  have hBelow := belowFormula_freeClosed hD2 (.bound 1) (.bound 0) beta.weaken.weaken rfl rfl hbeta2
  have hEdges := edgesHoldFormula_freeClosed hC2 hD2 Tab.weaken.weaken Big.weaken.weaken (.bound 1) (.bound 0)
    hTab2 (by simpa using hBig) rfl rfl
  have hFacts := factsHoldFormula_freeClosed hC2 hT2 hD2 hA2 Tab.weaken.weaken Original.weaken.weaken B.weaken.weaken
    b.weaken.weaken (.bound 0) hTab2 (by simpa using hOriginal) (by simpa using hB) hb2 rfl
  have hTemplates := templatesHoldFormula_freeClosed hC2 hT2 hD2 hA2 Tab.weaken.weaken Original.weaken.weaken B.weaken.weaken
    b.weaken.weaken (.bound 0) beta.weaken.weaken hTab2 (by simpa using hOriginal) (by simpa using hB) hb2 rfl hbeta2
  have hControl := controlHoldsFormula_freeClosed hC2 hT2 hD2 hA2 Tab.weaken.weaken K.weaken.weaken qControl.weaken.weaken
    b.weaken.weaken (.bound 0) beta.weaken.weaken hTab2 (by simpa using hK) (by simpa using hq) hb2 rfl hbeta2
  simp [stageFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hD.labels,
    hEnc,hLab,hBelow,hEdges,hFacts,hTemplates,hControl]

theorem stageFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (D : Reflection.Data (Project.Term n))
    (A : Context (Project.Term n)) (Tab Original Big B K qControl beta b : Project.Term n) :
    Project.Formula.satisfies e (stageFormula C T D A Tab Original Big B K qControl beta b) ↔
      Stage M (C.eval e) (T.eval e) (D.eval e) (A.eval e) (Tab.eval e) (Original.eval e) (Big.eval e) (B.eval e)
        (K.eval e) (qControl.eval e) (beta.eval e) (b.eval e) := by
  simp only [stageFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    encodeFormula_iff he,labelingFormula_iff he,belowFormula_iff he,edgesHoldFormula_iff he,factsHoldFormula_iff he,
    templatesHoldFormula_iff he,controlHoldsFormula_iff he,Data.eval_weaken,ExpressionData.eval_weaken,
    MatrixArithmetic.eval_weaken,Context.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨w,hw,g,hg,h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨w,hw,g,hg,⟨h1,h2,h3,h4,h5,h6,h7⟩⟩
  · rintro ⟨w,hw,g,hg,h⟩
    exact ⟨w,hw,g,hg,h.size,h.labeling,h.below,h.edges,h.facts,h.templates,h.control⟩

private def seamC : ExpressionData (Project.Term 37) := ⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩
private def seamT : MatrixArithmetic (Project.Term 37) := ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩
private def seamA : Context (Project.Term 37) := ⟨.bound 12,.bound 11,.bound 10,.bound 9⟩
private def seamD : Reflection.Data (Project.Term 37) :=
  ⟨⟨.bound 24,.bound 25,.bound 26,.bound 27,.bound 28,.bound 29,.bound 30⟩,
    .bound 31,.bound 32,.bound 33,.bound 34,.bound 35,.bound 36⟩

/-- 归纳公式：b∈Nsucc → Stage(b)。参数为实际C/T/D/A及固定的原图、大图、坏根数据。 -/
def stageSchema : Project.UnarySchema 36 where
  body := .imp (.mem (.bound 0) (.bound 1))
    (stageFormula seamC seamT seamD seamA (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 0))
  freeClosed := by
    have h := stageFormula_freeClosed (C := seamC) ⟨rfl,rfl,rfl,rfl,rfl⟩ (T := seamT) ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (D := seamD) (by constructor <;> rfl) (A := seamA) ⟨rfl,rfl,rfl,rfl⟩
      (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 0) rfl rfl rfl rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h]

def stageEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Reflection.Data M.Domain) (A : Context M.Domain) (Tab Original Big B K qControl beta Nsucc : M.Domain) : Env M 36 :=
  (((((((((((((((((((((((dataEnv D).push C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push
    T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push
    A.last).push A.root).push A.length).push A.first).push Tab).push Original).push Big).push B).push K).push
    qControl).push beta).push Nsucc

theorem stageSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain) (D : Reflection.Data M.Domain) (A : Context M.Domain)
    (Tab Original Big B K qControl beta Nsucc b : M.Domain) :
    Project.Formula.satisfies ((stageEnv C T D A Tab Original Big B K qControl beta Nsucc).push b) stageSchema.body ↔
      (M.mem b Nsucc → Stage M C T D A Tab Original Big B K qControl beta b) := by
  simp only [stageSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,stageFormula_iff he]
  rfl

/-- 对象自然数归纳：对所有内部b≤N，第b块满足全部复制不变量。 -/
theorem stage_all_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} {Tab : M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B qControl : M.Domain}
    (hS : Scene M C T D Tab A m L V P H Original K level B qControl)
    {N BigWidth BigForests BigCodes BigG Big f beta : M.Domain} (hN : M.mem N C.omega)
    (hBigWidth : Width M C T A N BigWidth)
    (hBigTower : CopyTower.Tower M C T A m L H K level B BigWidth BigForests BigCodes BigG)
    (hBig : CopyDiagram.Enumerated M C T D ⟨B,BigWidth,BigForests,BigCodes,BigG⟩ Big)
    (hRep : Representation M D Tab m Original f) (hLast : MemPair M f A.last beta) :
    ∀ b, M.mem b C.omega → (b=N ∨ M.mem b N) → Stage M C T D A Tab Original Big B K qControl beta b := by
  have hC := hS.expression
  have he := hM.1
  have hw := omega_isOrdinal_d hM hC.omega
  have hBeta := (hRep.labeling.graph.bounds he hLast).2
  obtain ⟨Nsucc,hNsucc,hNsuccNat⟩ := hC.omega.1.2 N hN
  have hAll := natural_induction_d hM stageSchema (stageEnv C T D A Tab Original Big B K qControl beta Nsucc) hC.omega
    (by
      intro e hEmpty
      rw [stageSchema_iff he]
      intro _
      have hz := he.eq_of_same_members e C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))
      subst e
      exact stage_zero_d hM hS hBigWidth hBigTower hBig hRep hLast)
    (by
      intro p hp hIH s hs
      rw [stageSchema_iff he] at hIH ⊢
      intro hsN
      have hpN : M.mem p Nsucc := (hw.mem hNsuccNat).transitive s hsN p hs.predecessor_mem
      have hsLe : s=N ∨ M.mem s N := by
        rcases (hNsucc s).mp hsN with hlt | heq
        · exact Or.inr hlt
        · exact Or.inl (he.eq_of_same_members s N heq)
      exact stage_step_d hM hS hBigWidth hBigTower hBig hBeta hp hs hsLe (hIH hpN))
  intro b hb hbN
  have hbN' : M.mem b Nsucc := (hNsucc b).mpr (hbN.elim (fun h => Or.inr (h ▸ fun _ => Iff.rfl)) Or.inl)
  exact (stageSchema_iff he C T D A Tab Original Big B K qControl beta Nsucc b).mp (hAll b hb) hbN'

/-- Y04b出口：任意内部N∈ω，Width(N)处的实际复制图有全部标签<beta的实际表示。
唯一语义输入是实际R表（经`Table.reflect_d`的FR与`Table.root_weaken_d`）；控制根由实际Control构造。 -/
theorem copy_representation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega) {Tab : M.Domain} (hTable : Table M D Tab)
    {A : Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hOriginal : ExpressionDiagram.Enumerated M C T D m L V H Original)
    (hBad : BadAt M C m L H K level A.last A.root) (hB : M.mem B C.omega)
    {f beta N width Forests Codes G Old : M.Domain}
    (hRep : Representation M D Tab m Original f) (hLast : MemPair M f A.last beta) (hN : M.mem N C.omega)
    (hWidth : Width M C T A N width) (hTower : CopyTower.Tower M C T A m L H K level B width Forests Codes G)
    (hOld : CopyDiagram.Enumerated M C T D ⟨B,width,Forests,Codes,G⟩ Old) :
    ∃ g, M.mem g D.labels ∧ Representation M D Tab width Old g ∧ Below M D width g beta := by
  obtain ⟨qControl,hControl⟩ := CopyNeeds.control_exists_d hM hC hLayers hBad
  have hS : Scene M C T D Tab A m L V P H Original K level B qControl :=
    ⟨hC,hT,hD,hOmega,hTable,hA,hLayers,hOriginal,hBad,hB,hControl⟩
  obtain ⟨width',_,g,hg,hSt⟩ := stage_all_d hM hS hN hWidth hTower hOld hRep hLast N hN (Or.inl rfl)
  have hww := encode_unique hM.1 hT hSt.size hWidth
  subst width'
  have hDiagram := hOld.diagram_d hM hC hT hD hOmega (CopyDiagram.tower_input_valid hTower)
  refine ⟨g,hg,⟨hDiagram,hSt.labeling,?_⟩,hSt.below⟩
  intro k hk q hq p hp c _ hEdge
  obtain ⟨_,_,hcw,_,_⟩ := hDiagram.edge_columns_d hM hD hEdge
  exact hSt.edges k (hOmega ▸ hk) q (hOmega ▸ hq) p (hOmega ▸ hp) c hcw hEdge

end KP1Y.OneYFinite.CopySeams
