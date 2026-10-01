import KP1Y.ReflectionSignature
import KP1Y.ReflectionEnumeration
import KP1Y.ReflectionTable

/-! 一阶结构的固定背景参数。top始终是原κ，取子结构时不得改成δ。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Closure
universe u v

structure ArticleData (α : Type u) where
  reflection : KP1Y.Reflection.Data α
  top : α
  table : α
  enumKeys : α
  enumeration : α
  numbers : Numbers α

def ArticleData.map {α : Type u} {β : Type v} (C : ArticleData α) (f : α → β) : ArticleData β :=
  ⟨C.reflection.map f,f C.top,f C.table,f C.enumKeys,f C.enumeration,fun i => f (C.numbers i)⟩

def ArticleData.eval {M : SetTheory.Structure.{u}} {n : Nat} (C : ArticleData (Project.Term n)) (e : Env M n) : ArticleData M.Domain :=
  C.map (fun t => t.eval e)

def ArticleData.weaken {n : Nat} (C : ArticleData (Project.Term n)) : ArticleData (Project.Term (n+1)) := C.map (fun t => t.weaken)

theorem ArticleData.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n) (x : M.Domain)
    (C : ArticleData (Project.Term n)) : C.weaken.eval (e.push x)=C.eval e := by
  rcases C with ⟨⟨⟨ω,cap,mid,keys,L,Γ,index⟩,pairs,edges,needs,edgeLists,needLists,labels⟩,top,table,enumKeys,E,N⟩
  simp [ArticleData.weaken,ArticleData.eval,ArticleData.map,KP1Y.Reflection.Data.map,KP1Y.Reflection.IndexData.map,Term.eval_weaken]

theorem ArticleData.eval_reflection {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n) (C : ArticleData (Project.Term n)) :
    C.reflection.eval e=(C.eval e).reflection := rfl

structure ArticleData.Closed {n : Nat} (C : ArticleData (Project.Term n)) : Prop where
  reflection : C.reflection.Closed
  top : C.top.freeSupport=[]
  table : C.table.freeSupport=[]
  enumKeys : C.enumKeys.freeSupport=[]
  enumeration : C.enumeration.freeSupport=[]
  numbers : ∀ i, (C.numbers i).freeSupport=[]

theorem ArticleData.Closed.weaken {n : Nat} {C : ArticleData (Project.Term n)} (h : C.Closed) : C.weaken.Closed := by
  refine ⟨h.reflection.weaken,?_,?_,?_,?_,?_⟩
  · simpa [ArticleData.weaken,ArticleData.map] using h.top
  · simpa [ArticleData.weaken,ArticleData.map] using h.table
  · simpa [ArticleData.weaken,ArticleData.map] using h.enumKeys
  · simpa [ArticleData.weaken,ArticleData.map] using h.enumeration
  · intro i
    simpa [ArticleData.weaken,ArticleData.map] using h.numbers i

structure ArticleData.Valid (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) : Prop where
  reflection : C.reflection.Valid M
  numerals : Numerals M C.reflection.omega C.numbers
  top : M.IsOrdinal C.top
  omega_top : M.mem C.reflection.omega C.top
  cap : M.SuccessorOf C.reflection.cap C.top
  table : KP1Y.Reflection.Table M C.reflection C.table
  enumeration : UniformEnumeration M C.reflection.omega C.top C.enumKeys C.enumeration

theorem ArticleData.Valid.number_top {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} (h : C.Valid M) (i : Fin 7) :
    M.mem (C.numbers i) C.top := h.top.transitive C.reflection.omega h.omega_top (C.numbers i) (h.numerals.natural i)

theorem article_data_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω κ Keys E : M.Domain}
    (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ) (hωκ : M.mem ω κ) (hEnum : UniformEnumeration M ω κ Keys E) :
    ∃ C : ArticleData M.Domain, C.top=κ ∧ C.reflection.omega=ω ∧ C.enumKeys=Keys ∧ C.enumeration=E ∧ C.Valid M := by
  obtain ⟨cap,R,H,hCap,hRω,hRcap,hR,hTable⟩ := KP1Y.Reflection.reflection_table_for_ordinal_d hM hω hκ
  obtain ⟨N,hN⟩ := numerals_exists hR.omega
  refine ⟨⟨R,κ,H,Keys,E,N⟩,rfl,hRω,rfl,rfl,hR,hN,hκ,?_,?_,hTable,?_⟩
  · exact Eq.mpr (congrArg (fun w => M.mem w κ) hRω) hωκ
  · exact Eq.mpr (congrArg (fun c => M.SuccessorOf c κ) hRcap) hCap
  · exact Eq.mpr (congrArg (fun w => UniformEnumeration M w κ Keys E) hRω) hEnum

end KP1Y.ReflectionModel
