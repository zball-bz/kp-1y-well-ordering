import KP1Y.ReflectionBinaryBlockTruth
import KP1Y.ReflectionGroundParameters

/-! 固定形状的四个实际原子块：输入/输出正标签、输出上界及cut等式。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

structure BasicBlocks (α : Type u) where
  omegaName : α
  pointName : α
  rootName : α
  cutName : α
  omegaSelector : α
  pointSelector : α
  cutLeft : α
  cutRight : α
  positiveInputs : α
  positiveOutputs : α
  belowOutputs : α
  atCut : α

structure BasicBlocks.Valid (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (V : NameFrame M.Domain) (B : BasicBlocks M.Domain) : Prop where
  omegaName : MemPair M V.scalars (C.numbers 0) B.omegaName
  pointName : MemPair M V.scalars (C.numbers 1) B.pointName
  rootName : MemPair M V.scalars (C.numbers 2) B.rootName
  cutName : MemPair M V.inputs T.cut B.cutName
  omegaConstant : ∀ i, M.mem i T.width → MemPair M B.omegaSelector i B.omegaName
  pointConstant : ∀ i, M.mem i T.width → MemPair M B.pointSelector i B.pointName
  cutLeftConstant : ∀ i, M.mem i (C.numbers 1) → MemPair M B.cutLeft i B.cutName
  cutRightConstant : ∀ i, M.mem i (C.numbers 1) → MemPair M B.cutRight i B.pointName
  positiveInputs : BinaryBlock M C D true V.scope T.width B.omegaSelector V.inputs B.positiveInputs
  positiveOutputs : BinaryBlock M C D true V.scope T.width B.omegaSelector V.outputs B.positiveOutputs
  belowOutputs : BinaryBlock M C D true V.scope T.width V.outputs B.pointSelector B.belowOutputs
  atCut : BinaryBlock M C D false V.scope (C.numbers 1) B.cutLeft B.cutRight B.atCut

theorem basic_blocks_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength) :
    ∃ B, BasicBlocks.Valid M C D T V B := by
  have hb : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  obtain ⟨ωv,hωv,hωRow⟩ := hV.scalars.graph.total (C.numbers 0) (hC.numerals.lt (by decide : (0:Nat)<3))
  obtain ⟨av,hav,haRow⟩ := hV.scalars.graph.total (C.numbers 1) (hC.numerals.lt (by decide : (1:Nat)<3))
  obtain ⟨θv,_,hθRow⟩ := hV.scalars.graph.total (C.numbers 2) (hC.numerals.lt (by decide : (2:Nat)<3))
  obtain ⟨cv,hcv,hcRow⟩ := hV.inputs.graph.total T.cut hT.cut
  obtain ⟨OW,hOW,hOWRows⟩ := constant_assignment_d hM T.width V.scope hωv
  obtain ⟨AW,hAW,hAWRows⟩ := constant_assignment_d hM T.width V.scope hav
  obtain ⟨CL,hCL,hCLRows⟩ := constant_assignment_d hM (C.numbers 1) V.scope hcv
  obtain ⟨CR,hCR,hCRRows⟩ := constant_assignment_d hM (C.numbers 1) V.scope hav
  obtain ⟨PI,hPI⟩ := binary_block_exists_d hM hC hD true hb hOW hV.inputs.graph
  obtain ⟨PO,hPO⟩ := binary_block_exists_d hM hC hD true hb hOW hV.outputs.graph
  obtain ⟨BO,hBO⟩ := binary_block_exists_d hM hC hD true hb hV.outputs.graph hAW
  obtain ⟨CUT,hCUT⟩ := binary_block_exists_d hM hC hD false hb hCL hCR
  exact ⟨⟨ωv,av,θv,cv,OW,AW,CL,CR,PI,PO,BO,CUT⟩,hωRow,haRow,hθRow,hcRow,hOWRows,hAWRows,hCLRows,hCRRows,hPI,hPO,hBO,hCUT⟩

theorem compare_constants_iff {M : SetTheory.Structure.{u}} {strict : Bool} {X Y n scope A s u v x y i : M.Domain}
    (hX : Graph M X n scope) (hY : Graph M Y n scope) (hS : Graph M s scope A)
    (hConstX : ∀ j, M.mem j n → MemPair M X j u) (hConstY : ∀ j, M.mem j n → MemPair M Y j v)
    (hi : M.mem i n) (hu : M.mem u scope) (hv : M.mem v scope) (hx : M.mem x A) (hy : M.mem y A)
    (hsx : MemPair M s u x) (hsy : MemPair M s v y) : CompareSelectors strict M X Y n scope A s ↔ (if strict then M.mem x y else x=y) := by
  constructor
  · intro h
    exact h i hi u hu v hv (hConstX i hi) (hConstY i hi) x hx y hy hsx hsy
  · intro h j hj u' _ v' _ hJu hJv x' _ y' _ hsx' hsy'
    have huu' := hX.unique j u' u hJu (hConstX j hj)
    have hvv' := hY.unique j v' v hJv (hConstY j hj)
    subst u'
    subst v'
    have hxx' := hS.unique u x' x hsx' hsx
    have hyy' := hS.unique v y' y hsy' hsy
    subst x'
    subst y'
    exact h

end KP1Y.ReflectionModel
