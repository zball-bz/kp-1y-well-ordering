import KP1Y.ReflectionParameterAssignment
import KP1Y.ReflectionLayerParameters
import KP1Y.ReflectionTemplateShape
import KP1Y.ReflectionTupleTools

/-! 将ω/a/θ和全部边层号装入实际赋值；自由输入/输出量词块保持这些参数。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction KP1Y.Reflection
universe u

structure GroundParameters (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (T : TemplateShape M.Domain)
    (V : NameFrame M.Domain) (a θ A s : M.Domain) : Prop where
  graph : Graph M s V.scope A
  omega : ∀ v, MemPair M V.scalars (C.numbers 0) v → MemPair M s v C.reflection.omega
  point : ∀ v, MemPair M V.scalars (C.numbers 1) v → MemPair M s v a
  root : ∀ v, MemPair M V.scalars (C.numbers 2) v → MemPair M s v θ
  edges : ∀ i k q p j, EdgeEntry M C.reflection T.diagram i k q p j → ∀ v, MemPair M V.edgeLayers i v → MemPair M s v k
  needs : ∀ i k q p, NeedEntry M C.reflection T.template i k q p → ∀ v, MemPair M V.needLayers i v → MemPair M s v k

theorem ground_parameters_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {a θ A : M.Domain}
    (hA : M.IsOrdinal A) (hωA : M.mem C.reflection.omega A) (ha : M.mem a A) (hθ : M.mem θ A) :
    ∃ s, GroundParameters M C T V a θ A s := by
  obtain ⟨LE,hLE,hLERows⟩ := edge_layers_exists_d hM hC.reflection hT.edgeLength hT.edges
  obtain ⟨LN,hLN,hLNRows⟩ := need_layers_exists_d hM hC.reflection hT.needLength hT.needs
  let vals : Fin 3 → M.Domain := Fin.cases C.reflection.omega (Fin.cases a (fun _ => θ))
  obtain ⟨SV,hSV,hSVRows⟩ := fixed_tuple_exists_d hM hC.numerals ⟨3,by decide⟩ vals (Fin.cases hωA (Fin.cases ha (fun _ => hθ)))
  have hSub : M.MemberSubset C.reflection.omega A := hA.transitive C.reflection.omega hωA
  obtain ⟨s,hParams⟩ := parameter_assignment_exists_d hM hC hV (hLE.mono_values hSub) (hLN.mono_values hSub) hSV
    (hSub (C.numbers 0) (hC.numerals.natural 0))
  refine ⟨s,hParams.graph,?_,?_,?_,?_,?_⟩
  · intro v hv
    exact (hParams.scalars.rows (C.numbers 0) (hC.numerals.lt (by decide : (0:Nat)<3)) v
      (hV.scalars.graph.bounds hM.1 hv).2 C.reflection.omega hωA hv).mp (hSVRows (0 : Fin 3))
  · intro v hv
    exact (hParams.scalars.rows (C.numbers 1) (hC.numerals.lt (by decide : (1:Nat)<3)) v
      (hV.scalars.graph.bounds hM.1 hv).2 a ha hv).mp (hSVRows (1 : Fin 3))
  · intro v hv
    exact (hParams.scalars.rows (C.numbers 2) (hC.numerals.lt (by decide : (2:Nat)<3)) v
      (hV.scalars.graph.bounds hM.1 hv).2 θ hθ hv).mp (hSVRows (2 : Fin 3))
  · intro i k q p j hEntry v hv
    have hAt := hLERows i k q p j hEntry
    exact (hParams.edges.rows i (hT.edge_index hM.1 hEntry) v (hV.edgeLayers.graph.bounds hM.1 hv).2 k
      (hParams.edges.values.bounds hM.1 hAt).2 hv).mp hAt
  · intro i k q p hEntry v hv
    have hAt := hLNRows i k q p hEntry
    exact (hParams.needs.rows i (hT.need_index hM.1 hEntry) v (hV.needLayers.graph.bounds hM.1 hv).2 k
      (hParams.needs.values.bounds hM.1 hAt).2 hv).mp hAt

theorem GroundParameters.preserve_family_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {T : TemplateShape M.Domain} {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {a θ A s t : M.Domain} (h : GroundParameters M C T V a θ A s)
    (j : Fin 5) (h2 : (2:Fin 5)≠j) (h3 : (3:Fin 5)≠j) (h4 : (4:Fin 5)≠j)
    (hFrame : AgreeOutside M (V.family j) (familyLength C T.width T.edgeLength T.needLength j) s t V.scope A) :
    GroundParameters M C T V a θ A t := by
  have keep (i : Fin 5) (hij : i≠j) (k v x : M.Domain) (hName : MemPair M (V.family i) k v) (hAt : MemPair M s v x) : MemPair M t v x :=
    (hFrame.rows v ((hV.family i).graph.bounds hM.1 hName).2 (hV.untouched_d hM hC hij hName) x (h.graph.bounds hM.1 hAt).2).mp hAt
  exact ⟨hFrame.target,fun v hv => keep 4 h4 (C.numbers 0) v C.reflection.omega hv (h.omega v hv),
    fun v hv => keep 4 h4 (C.numbers 1) v a hv (h.point v hv),fun v hv => keep 4 h4 (C.numbers 2) v θ hv (h.root v hv),
    fun i k q p endCol he v hv => keep 2 h2 i v k hv (h.edges i k q p endCol he v hv),
    fun i k q p he v hv => keep 3 h3 i v k hv (h.needs i k q p he v hv)⟩

end KP1Y.ReflectionModel
