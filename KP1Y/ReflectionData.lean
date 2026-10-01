import KP1Y.ReflectionQuery
import KP1Y.SequenceSpaces

/-! R/FR的实际集合参数：自然数原子码、全部内部有限边表/模板，以及标签序列空间。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u v

structure Data (α : Type u) extends IndexData α where
  pairs : α
  edgeCodes : α
  needCodes : α
  edgeLists : α
  needLists : α
  labels : α

def Data.map {α : Type u} {β : Type v} (C : Data α) (f : α → β) : Data β :=
  ⟨C.toIndexData.map f,f C.pairs,f C.edgeCodes,f C.needCodes,f C.edgeLists,f C.needLists,f C.labels⟩

def Data.eval {M : SetTheory.Structure.{u}} {n : Nat} (C : Data (Project.Term n)) (e : Env M n) : Data M.Domain := C.map (fun t => t.eval e)

def Data.weaken {n : Nat} (C : Data (Project.Term n)) : Data (Project.Term (n+1)) := C.map (fun t => t.weaken)

theorem Data.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n) (x : M.Domain) (C : Data (Project.Term n)) :
    C.weaken.eval (e.push x)=C.eval e := by
  rcases C with ⟨⟨ω,cap,mid,keys,L,Γ,index⟩,pairs,edges,needs,edgeLists,needLists,labels⟩
  simp [Data.weaken,Data.eval,Data.map,IndexData.map,Term.eval_weaken]

theorem Data.eval_index {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n) (C : Data (Project.Term n)) :
    C.toIndexData.eval e=(C.eval e).toIndexData := rfl

structure Data.Closed {n : Nat} (C : Data (Project.Term n)) : Prop where
  omega : C.omega.freeSupport=[]
  cap : C.cap.freeSupport=[]
  middle : C.middle.freeSupport=[]
  keys : C.keys.freeSupport=[]
  block : C.block.freeSupport=[]
  bound : C.bound.freeSupport=[]
  index : C.index.freeSupport=[]
  pairs : C.pairs.freeSupport=[]
  edgeCodes : C.edgeCodes.freeSupport=[]
  needCodes : C.needCodes.freeSupport=[]
  edgeLists : C.edgeLists.freeSupport=[]
  needLists : C.needLists.freeSupport=[]
  labels : C.labels.freeSupport=[]

theorem Data.Closed.weaken {n : Nat} {C : Data (Project.Term n)} (h : C.Closed) : C.weaken.Closed := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩
  constructor <;> simp_all [Data.weaken,Data.map,IndexData.map]

structure Data.Valid (M : SetTheory.Structure.{u}) (C : Data M.Domain) : Prop extends IndexData.Valid M C.toIndexData where
  pairs : IsProduct M C.pairs C.omega C.omega
  edgeCodes : IsProduct M C.edgeCodes C.pairs C.pairs
  needCodes : IsProduct M C.needCodes C.omega C.pairs
  edgeLists : ∀ A, M.mem A C.edgeLists ↔ ∃ n, M.mem n C.omega ∧ Graph M A n C.edgeCodes
  needLists : ∀ N, M.mem N C.needLists ↔ ∃ n, M.mem n C.omega ∧ Graph M N n C.needCodes
  labels : ∀ f, M.mem f C.labels ↔ ∃ n, M.mem n C.omega ∧ Graph M f n C.cap

theorem reflection_data_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω cap : M.Domain}
    (hω : M.IsOmega ω) (hCap : M.IsOrdinal cap) : ∃ C : Data M.Domain, C.omega=ω ∧ C.cap=cap ∧ C.Valid M := by
  obtain ⟨I,hωI,hCapI,hI⟩ := index_data_exists_d hM hω hCap
  obtain ⟨pairs,hPairs⟩ := product_exists hM I.omega I.omega
  obtain ⟨edges,hEdges⟩ := product_exists hM pairs pairs
  obtain ⟨needs,hNeeds⟩ := product_exists hM I.omega pairs
  obtain ⟨edgeLists,hEdgeLists⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hI.omega edges
  obtain ⟨needLists,hNeedLists⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hI.omega needs
  obtain ⟨labels,hLabels⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hI.omega I.cap
  exact ⟨⟨I,pairs,edges,needs,edgeLists,needLists,labels⟩,hωI,hCapI,hI,hPairs,hEdges,hNeeds,hEdgeLists,hNeedLists,hLabels⟩

def Quad (M : SetTheory.Structure.{u}) (Pairs e k q p j : M.Domain) : Prop :=
  ∃ u, M.mem u Pairs ∧ ∃ v, M.mem v Pairs ∧ Codes M e u v ∧ Codes M u k q ∧ Codes M v p j

def quadFormula {n : Nat} (Pairs e k q p j : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Pairs (Project.Formula.existsMem Pairs.weaken
    (.conj (codeFormula e.weaken.weaken (.bound 1) (.bound 0))
      (.conj (codeFormula (.bound 1) k.weaken.weaken q.weaken.weaken) (codeFormula (.bound 0) p.weaken.weaken j.weaken.weaken))))

theorem quadFormula_delta0 {n : Nat} (Pairs e k q p j : Project.Term n) : (quadFormula Pairs e k q p j).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _) (codeFormula_delta0 _ _ _))))

theorem quadFormula_freeClosed {n : Nat} (Pairs e k q p j : Project.Term n)
    (hPairs : Pairs.freeSupport=[]) (he : e.freeSupport=[]) (hk : k.freeSupport=[])
    (hq : q.freeSupport=[]) (hp : p.freeSupport=[]) (hj : j.freeSupport=[]) : (quadFormula Pairs e k q p j).FreeClosed := by
  simp [quadFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hPairs,he,hk,hq,hp,hj]

theorem quadFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (Pairs e k q p j : Project.Term n) : Project.Formula.satisfies env (quadFormula Pairs e k q p j) ↔
      Quad M (Pairs.eval env) (e.eval env) (k.eval env) (q.eval env) (p.eval env) (j.eval env) := by
  simp only [quadFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,codeFormula_iff he,Term.eval_weaken]
  rfl

theorem Quad.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {ω Pairs e k q p j : M.Domain}
    (hPairs : IsProduct M Pairs ω ω) (h : Quad M Pairs e k q p j) : M.mem k ω ∧ M.mem q ω ∧ M.mem p ω ∧ M.mem j ω := by
  obtain ⟨u,hu,v,hv,_,hU,hV⟩ := h
  obtain ⟨k',hk',q',hq',hU'⟩ := (hPairs u).mp hu
  obtain ⟨p',hp',j',hj',hV'⟩ := (hPairs v).mp hv
  obtain ⟨hkk',hqq'⟩ := codes_injective he hU hU'
  obtain ⟨hpp',hjj'⟩ := codes_injective he hV hV'
  exact ⟨hkk' ▸ hk',hqq' ▸ hq',hpp' ▸ hp',hjj' ▸ hj'⟩

end KP1Y.Reflection
