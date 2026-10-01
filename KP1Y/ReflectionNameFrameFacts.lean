import KP1Y.ReflectionNameFrame
import KP1Y.FrameAgreement

/-! 统一访问五个名字族，并验证量词块不能改写其他族的参数。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

def familyTag (i : Fin 5) : Fin 7 := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩

def NameFrame.family {α : Type u} (V : NameFrame α) (i : Fin 5) : α := match i.val with
  | 0 => V.inputs | 1 => V.outputs | 2 => V.edgeLayers | 3 => V.needLayers | _ => V.scalars

def familyLength {α : Type u} (C : ArticleData α) (m NI NN : α) (i : Fin 5) : α := match i.val with
  | 0 => m | 1 => m | 2 => NI | 3 => NN | _ => C.numbers 3

theorem NameFrame.Valid.family {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} {F m NI NN : M.Domain} {V : NameFrame M.Domain}
    (h : V.Valid M C F m NI NN) (i : Fin 5) :
    NamedFamily M C.reflection.pairs F (C.numbers (familyTag i)) (familyLength C m NI NN i) V.scope (V.family i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact h.inputs
  · exact h.outputs
  · exact h.edgeLayers
  · exact h.needLayers
  · exact h.scalars

theorem NameFrame.Valid.disjoint_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {F m NI NN : M.Domain} {V : NameFrame M.Domain} (h : V.Valid M C F m NI NN) {i j : Fin 5} (hij : i≠j)
    {x y v : M.Domain} (hx : MemPair M (V.family i) x v) (hy : MemPair M (V.family j) y v) : False := by
  have hTags : C.numbers (familyTag i)≠C.numbers (familyTag j) := by
    intro he
    apply hij
    exact Fin.ext (congrArg (fun a : Fin 7 => a.val) (hC.numerals.injective_d hM he))
  exact named_families_disjoint hM.1 h.basis (h.family i) (h.family j) hTags hx hy

theorem NameFrame.Valid.untouched_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {F m NI NN : M.Domain} {V : NameFrame M.Domain} (h : V.Valid M C F m NI NN) {i j : Fin 5} (hij : i≠j)
    {x v : M.Domain} (hx : MemPair M (V.family i) x v) : ¬Touched M (V.family j) (familyLength C m NI NN j) v := by
  rintro ⟨y,_,hy⟩
  exact h.disjoint_d hM hC hij hx hy

end KP1Y.ReflectionModel
