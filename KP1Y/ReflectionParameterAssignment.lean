import KP1Y.AssignmentFamilyPatch
import KP1Y.ReflectionNameFrameFacts

/-! 实际参数赋值及自由变量量词块的参数保持；没有内部有限多次元层选择。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

structure ParameterAssignment (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (V : NameFrame M.Domain)
    (NI NN LE LN SV A s : M.Domain) : Prop where
  graph : Graph M s V.scope A
  edges : TupleValue M LE V.edgeLayers s NI V.scope A
  needs : TupleValue M LN V.needLayers s NN V.scope A
  scalars : TupleValue M SV V.scalars s (C.numbers 3) V.scope A

theorem parameter_assignment_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {F m NI NN : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F m NI NN) {LE LN SV A : M.Domain}
    (hLE : Graph M LE NI A) (hLN : Graph M LN NN A) (hSV : Graph M SV (C.numbers 3) A) (hZero : M.mem (C.numbers 0) A) :
    ∃ s, ParameterAssignment M C V NI NN LE LN SV A s := by
  obtain ⟨base,hBase,_⟩ := constant_assignment_d hM V.scope A hZero
  obtain ⟨s1,hPatchS,hReadS⟩ := patch_assignment_d hM hBase hV.scalars.graph
    (fun _ _ _ hi hj => hV.scalars.injective hM.1 hV.basis hi hj) hSV
  obtain ⟨s2,hPatchE,hReadE⟩ := patch_assignment_d hM hPatchS.target hV.edgeLayers.graph
    (fun _ _ _ hi hj => hV.edgeLayers.injective hM.1 hV.basis hi hj) hLE
  have hReadS2 : TupleValue M SV V.scalars s2 (C.numbers 3) V.scope A :=
    hReadS.preserve_outside hPatchE (fun _ _ hAt => hV.untouched_d hM hC (i := 4) (j := 2) (by decide) hAt)
  obtain ⟨s3,hPatchN,hReadN⟩ := patch_assignment_d hM hPatchE.target hV.needLayers.graph
    (fun _ _ _ hi hj => hV.needLayers.injective hM.1 hV.basis hi hj) hLN
  have hReadE3 : TupleValue M LE V.edgeLayers s3 NI V.scope A :=
    hReadE.preserve_outside hPatchN (fun _ _ hAt => hV.untouched_d hM hC (i := 2) (j := 3) (by decide) hAt)
  have hReadS3 : TupleValue M SV V.scalars s3 (C.numbers 3) V.scope A :=
    hReadS2.preserve_outside hPatchN (fun _ _ hAt => hV.untouched_d hM hC (i := 4) (j := 3) (by decide) hAt)
  exact ⟨s3,hPatchN.target,hReadE3,hReadN,hReadS3⟩

theorem ParameterAssignment.preserve_inputs_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {F m NI NN : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F m NI NN) {LE LN SV A s t : M.Domain} (h : ParameterAssignment M C V NI NN LE LN SV A s)
    (hFrame : AgreeOutside M V.inputs m s t V.scope A) : ParameterAssignment M C V NI NN LE LN SV A t :=
  ⟨hFrame.target,
    h.edges.preserve_outside hFrame (fun _ _ hAt => hV.untouched_d hM hC (i := 2) (j := 0) (by decide) hAt),
    h.needs.preserve_outside hFrame (fun _ _ hAt => hV.untouched_d hM hC (i := 3) (j := 0) (by decide) hAt),
    h.scalars.preserve_outside hFrame (fun _ _ hAt => hV.untouched_d hM hC (i := 4) (j := 0) (by decide) hAt)⟩

theorem ParameterAssignment.preserve_outputs_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {F m NI NN : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F m NI NN) {LE LN SV A s t : M.Domain} (h : ParameterAssignment M C V NI NN LE LN SV A s)
    (hFrame : AgreeOutside M V.outputs m s t V.scope A) : ParameterAssignment M C V NI NN LE LN SV A t :=
  ⟨hFrame.target,
    h.edges.preserve_outside hFrame (fun _ _ hAt => hV.untouched_d hM hC (i := 2) (j := 1) (by decide) hAt),
    h.needs.preserve_outside hFrame (fun _ _ hAt => hV.untouched_d hM hC (i := 3) (j := 1) (by decide) hAt),
    h.scalars.preserve_outside hFrame (fun _ _ hAt => hV.untouched_d hM hC (i := 4) (j := 1) (by decide) hAt)⟩

end KP1Y.ReflectionModel
