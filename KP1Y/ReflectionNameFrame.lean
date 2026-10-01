import KP1Y.ReflectionVariableNames
import KP1Y.ReflectionModelData

/-! 五个实际有限变量族共用一个内部自然数作用域；输入、输出及参数名互不碰撞。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking
universe u v

theorem finite_natural_bounds_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω : M.Domain}
    (hω : M.IsOmega ω) (bounds : List M.Domain) (hBounds : ∀ b, b∈bounds → M.mem b ω) :
    ∃ B, M.mem B ω ∧ ∀ b, b∈bounds → M.MemberSubset b B := by
  induction bounds with
  | nil =>
      obtain ⟨zero,_,hZero⟩ := hω.1.1
      exact ⟨zero,hZero,fun b hb => False.elim (List.not_mem_nil hb)⟩
  | cons a rest ih =>
      obtain ⟨B,hB,hRest⟩ := ih (fun b hb => hBounds b (List.mem_cons_of_mem a hb))
      obtain ⟨D,hD,hBD,haD⟩ := KP1Y.Naturals.natural_common_bound_d hM hω hB (hBounds a (by simp))
      refine ⟨D,hD,?_⟩
      intro b hb x hx
      rcases List.mem_cons.mp hb with he | hb
      · subst b
        exact ((KP1Y.Naturals.omega_isOrdinal_d hM hω).mem hD).transitive a haD x hx
      · exact hBD x (hRest b hb x hx)

structure NamedFamily (M : SetTheory.Structure.{u}) (Pairs F tag n bound G : M.Domain) : Prop where
  graph : Graph M G n bound
  rows : ∀ i v, MemPair M G i v ↔ M.mem i n ∧ VarName M Pairs F tag i v

theorem NamedFamily.enlarge {M : SetTheory.Structure.{u}} {Pairs F tag n bound G B : M.Domain}
    (h : NamedFamily M Pairs F tag n bound G) (hSub : M.MemberSubset bound B) : NamedFamily M Pairs F tag n B G :=
  ⟨h.graph.mono_values hSub,h.rows⟩

theorem named_families_disjoint {M : SetTheory.Structure.{u}} (he : Extensional M) {ω Pairs F tag tag' n n' bound bound' G G' i j v : M.Domain}
    (hF : OrdinalRank M F Pairs ω) (h : NamedFamily M Pairs F tag n bound G)
    (h' : NamedFamily M Pairs F tag' n' bound' G') (hNe : tag≠tag') (hi : MemPair M G i v) (hj : MemPair M G' j v) : False :=
  hNe ((((h.rows i v).mp hi).2.injective he hF ((h'.rows j v).mp hj).2).1)

theorem NamedFamily.injective {M : SetTheory.Structure.{u}} (he : Extensional M) {ω Pairs F tag n bound G i j v : M.Domain}
    (hF : OrdinalRank M F Pairs ω) (h : NamedFamily M Pairs F tag n bound G) (hi : MemPair M G i v) (hj : MemPair M G j v) : i=j :=
  (((h.rows i v).mp hi).2.injective he hF ((h.rows j v).mp hj).2).2

structure NameFrame (α : Type u) where
  scope : α
  inputs : α
  outputs : α
  edgeLayers : α
  needLayers : α
  scalars : α

def NameFrame.map {α : Type u} {β : Type v} (V : NameFrame α) (f : α → β) : NameFrame β :=
  ⟨f V.scope,f V.inputs,f V.outputs,f V.edgeLayers,f V.needLayers,f V.scalars⟩

def NameFrame.eval {M : SetTheory.Structure.{u}} {d : Nat} (V : NameFrame (Project.Term d)) (e : Env M d) : NameFrame M.Domain := V.map (fun t => t.eval e)

def NameFrame.weaken {d : Nat} (V : NameFrame (Project.Term d)) : NameFrame (Project.Term (d+1)) := V.map (fun t => t.weaken)

theorem NameFrame.eval_weaken {M : SetTheory.Structure.{u}} {d : Nat} (e : Env M d) (x : M.Domain) (V : NameFrame (Project.Term d)) :
    V.weaken.eval (e.push x)=V.eval e := by
  cases V
  simp [NameFrame.weaken,NameFrame.eval,NameFrame.map,Term.eval_weaken]

structure NameFrame.Closed {d : Nat} (V : NameFrame (Project.Term d)) : Prop where
  scope : V.scope.freeSupport=[]
  inputs : V.inputs.freeSupport=[]
  outputs : V.outputs.freeSupport=[]
  edgeLayers : V.edgeLayers.freeSupport=[]
  needLayers : V.needLayers.freeSupport=[]
  scalars : V.scalars.freeSupport=[]

theorem NameFrame.Closed.weaken {d : Nat} {V : NameFrame (Project.Term d)} (h : V.Closed) : V.weaken.Closed := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  constructor <;> simp_all [NameFrame.weaken,NameFrame.map]

structure NameFrame.Valid (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (F m NI NN : M.Domain) (V : NameFrame M.Domain) : Prop where
  basis : OrdinalRank M F C.reflection.pairs C.reflection.omega
  scope : M.mem V.scope C.reflection.omega
  width : M.mem m C.reflection.omega
  edges : M.mem NI C.reflection.omega
  needs : M.mem NN C.reflection.omega
  inputs : NamedFamily M C.reflection.pairs F (C.numbers 0) m V.scope V.inputs
  outputs : NamedFamily M C.reflection.pairs F (C.numbers 1) m V.scope V.outputs
  edgeLayers : NamedFamily M C.reflection.pairs F (C.numbers 2) NI V.scope V.edgeLayers
  needLayers : NamedFamily M C.reflection.pairs F (C.numbers 3) NN V.scope V.needLayers
  scalars : NamedFamily M C.reflection.pairs F (C.numbers 4) (C.numbers 3) V.scope V.scalars

theorem name_frame_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {F m NI NN : M.Domain} (hF : OrdinalRank M F C.reflection.pairs C.reflection.omega)
    (hm : M.mem m C.reflection.omega) (hNI : M.mem NI C.reflection.omega) (hNN : M.mem NN C.reflection.omega) :
    ∃ V, NameFrame.Valid M C F m NI NN V := by
  obtain ⟨inputs,B0,hB0,hI,hIRows⟩ := name_family_bounded_d hM hC.numerals.omega hC.reflection.pairs hF.graph (hC.numerals.natural 0) hm
  obtain ⟨outputs,B1,hB1,hO,hORows⟩ := name_family_bounded_d hM hC.numerals.omega hC.reflection.pairs hF.graph (hC.numerals.natural 1) hm
  obtain ⟨edges,B2,hB2,hE,hERows⟩ := name_family_bounded_d hM hC.numerals.omega hC.reflection.pairs hF.graph (hC.numerals.natural 2) hNI
  obtain ⟨needs,B3,hB3,hN,hNRows⟩ := name_family_bounded_d hM hC.numerals.omega hC.reflection.pairs hF.graph (hC.numerals.natural 3) hNN
  obtain ⟨scalars,B4,hB4,hS,hSRows⟩ := name_family_bounded_d hM hC.numerals.omega hC.reflection.pairs hF.graph (hC.numerals.natural 4) (hC.numerals.natural 3)
  obtain ⟨bound,hBound,hSub⟩ := finite_natural_bounds_d hM hC.numerals.omega [B0,B1,B2,B3,B4] (by
    intro b hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption)
  exact ⟨⟨bound,inputs,outputs,edges,needs,scalars⟩,hF,hBound,hm,hNI,hNN,
    ⟨hI.mono_values (hSub B0 (by simp)),hIRows⟩,⟨hO.mono_values (hSub B1 (by simp)),hORows⟩,
    ⟨hE.mono_values (hSub B2 (by simp)),hERows⟩,⟨hN.mono_values (hSub B3 (by simp)),hNRows⟩,
    ⟨hS.mono_values (hSub B4 (by simp)),hSRows⟩⟩

end KP1Y.ReflectionModel
