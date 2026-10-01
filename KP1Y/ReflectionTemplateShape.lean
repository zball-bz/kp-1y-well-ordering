import KP1Y.ReflectionShapeEntries
import KP1Y.ReflectionModelData

/-! 固定反射形状及两个实际列表长度，保留所有用于编译的索引范围证明。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Reflection
universe u v

structure TemplateShape (α : Type u) where
  width : α
  diagram : α
  template : α
  cut : α
  edgeLength : α
  needLength : α

def TemplateShape.map {α : Type u} {β : Type v} (T : TemplateShape α) (f : α → β) : TemplateShape β :=
  ⟨f T.width,f T.diagram,f T.template,f T.cut,f T.edgeLength,f T.needLength⟩

def TemplateShape.eval {M : SetTheory.Structure.{u}} {d : Nat} (T : TemplateShape (Project.Term d)) (e : Env M d) : TemplateShape M.Domain :=
  T.map (fun t => t.eval e)

def TemplateShape.weaken {d : Nat} (T : TemplateShape (Project.Term d)) : TemplateShape (Project.Term (d+1)) := T.map (fun t => t.weaken)

theorem TemplateShape.eval_weaken {M : SetTheory.Structure.{u}} {d : Nat} (e : Env M d) (x : M.Domain) (T : TemplateShape (Project.Term d)) :
    T.weaken.eval (e.push x)=T.eval e := by
  cases T
  simp [TemplateShape.weaken,TemplateShape.eval,TemplateShape.map,Term.eval_weaken]

structure TemplateShape.Closed {d : Nat} (T : TemplateShape (Project.Term d)) : Prop where
  width : T.width.freeSupport=[]
  diagram : T.diagram.freeSupport=[]
  template : T.template.freeSupport=[]
  cut : T.cut.freeSupport=[]
  edgeLength : T.edgeLength.freeSupport=[]
  needLength : T.needLength.freeSupport=[]

theorem TemplateShape.Closed.weaken {d : Nat} {T : TemplateShape (Project.Term d)} (h : T.Closed) : T.weaken.Closed := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  constructor <;> simp_all [TemplateShape.weaken,TemplateShape.map]

structure TemplateShape.Valid (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (T : TemplateShape M.Domain) : Prop where
  diagram : Diagram M C.reflection T.width T.diagram
  template : Template M C.reflection T.width T.template
  cut : M.mem T.cut T.width
  edgeLength : M.mem T.edgeLength C.reflection.omega
  needLength : M.mem T.needLength C.reflection.omega
  edges : Graph M T.diagram T.edgeLength C.reflection.edgeCodes
  needs : Graph M T.template T.needLength C.reflection.needCodes

theorem template_shape_exists {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} (hC : C.Valid M) {m A N c : M.Domain}
    (hA : Diagram M C.reflection m A) (hN : Template M C.reflection m N) (hc : M.mem c m) :
    ∃ NI NN, TemplateShape.Valid M C ⟨m,A,N,c,NI,NN⟩ := by
  obtain ⟨NI,hNI,hEdges⟩ := (hC.reflection.edgeLists A).mp hA.2.1
  obtain ⟨NN,hNN,hNeeds⟩ := (hC.reflection.needLists N).mp hN.2.1
  exact ⟨NI,NN,hA,hN,hc,hNI,hNN,hEdges,hNeeds⟩

theorem TemplateShape.Valid.edge_index {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain} {T : TemplateShape M.Domain}
    (hT : T.Valid M C) {i k q p j : M.Domain} (h : EdgeEntry M C.reflection T.diagram i k q p j) : M.mem i T.edgeLength := by
  obtain ⟨_,_,hAt,_⟩ := h
  exact (hT.edges.bounds he hAt).1

theorem TemplateShape.Valid.need_index {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain} {T : TemplateShape M.Domain}
    (hT : T.Valid M C) {i k q p : M.Domain} (h : NeedEntry M C.reflection T.template i k q p) : M.mem i T.needLength := by
  obtain ⟨_,_,hAt,_⟩ := h
  exact (hT.needs.bounds he hAt).1

theorem TemplateShape.Valid.edge_columns_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {T : TemplateShape M.Domain} (hT : T.Valid M C) {i k q p j : M.Domain}
    (h : EdgeEntry M C.reflection T.diagram i k q p j) : M.mem q T.width ∧ M.mem p T.width ∧ M.mem j T.width := by
  have hiω := (KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).transitive T.edgeLength hT.edgeLength i (hT.edge_index hM.1 h)
  have hCols := hT.diagram.edge_columns_d hM hC.reflection (h.occurs hiω)
  exact ⟨hCols.1,hCols.2.1,hCols.2.2.1⟩

theorem TemplateShape.Valid.need_columns_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {T : TemplateShape M.Domain} (hT : T.Valid M C) {i k q p : M.Domain}
    (h : NeedEntry M C.reflection T.template i k q p) : M.mem q T.width ∧ M.mem p T.width := by
  have hiω := (KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).transitive T.needLength hT.needLength i (hT.need_index hM.1 h)
  have hCols := hT.template.need_columns_d hM hC.reflection (h.occurs hiω)
  exact ⟨hCols.1,hCols.2.1⟩

end KP1Y.ReflectionModel
