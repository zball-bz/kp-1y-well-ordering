import KP1Y.ClosureCapture

/-! 给定可数操作族和初始枚举，KPω 中实际构造一个可数且对全部内部有限参数封闭的集合。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal KP1Y.Iteration
universe u

def Closed (M : SetTheory.Structure.{u}) (C : Data M.Domain) (X : M.Domain) : Prop :=
  ∀ op, M.mem op C.operations → ∀ length, M.mem length C.omega →
    ∀ t, Graph M t length X → ∀ key, Codes M key op t → ∀ x, MemPair M C.applyOperation key x → M.mem x X

structure CountableHull (M : SetTheory.Structure.{u}) (C : Data M.Domain) (base X enumeration : M.Domain) : Prop where
  subset : M.MemberSubset X C.carrier
  onto : Onto M enumeration C.omega X
  seed : ∀ x, Reached M C.omega base x → M.mem x X
  closed : Closed M C X

theorem countable_hull_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {base : M.Domain} (hBase : Graph M base C.omega C.carrier) :
    ∃ X enumeration, CountableHull M C base X enumeration := by
  obtain ⟨R,V,hFamily⟩ := enumerator_family_exists_d hM hC hBase
  obtain ⟨X,f,hFlat⟩ := flatten_family_d hM hC hFamily
  have hSub := hFlat.subset hM.1
  refine ⟨X,f,hSub,hFlat.onto,?_,?_⟩
  · intro x hx
    exact (hFlat.members x).mpr ⟨C.zero,hC.zero_nat,base,(hFamily.graph.bounds hM.1 hFamily.initial).2,hFamily.initial,hx⟩
  · intro op hOp length hLength t hT key hCode x hAt
    obtain ⟨N,hN,E,_,hNE,hCapture⟩ := finite_tuple_captured_d hM hC hFamily hFlat hT hLength
    obtain ⟨next,hSucc,hNext⟩ := hC.omega.1.2 N hN
    obtain ⟨F,hFV,hNextF⟩ := hFamily.graph.total next hNext
    have hStep := hFamily.step N next E F hSucc hNE hNextF
    have hReach := next_enumerator_covers_operations_d hM hC (hFamily.values N hN E hNE) hStep
      hOp (hT.mono_values hSub) hLength hCapture hCode hAt
    exact (hFlat.members x).mpr ⟨next,hNext,F,hFV,hNextF,hReach⟩

end KP1Y.Closure
