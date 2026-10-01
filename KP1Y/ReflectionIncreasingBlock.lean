import KP1Y.ReflectionBinaryBlockTruth
import KP1Y.ReflectionAdjacentLabels
import KP1Y.ReflectionTemplateShape
import KP1Y.ReflectionNameFrame
import KP1Y.BoundedNaturalInduction

/-! 相邻列比较的实际代码块。非空宽度 m 使用其内部前驱 n，恰好比较 n 条相邻边。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction KP1Y.Bounded
universe u

private def nextIndexSchema : Project.Delta0BinarySchema 0 where
  body := successorFormula (.bound 0) (.bound 1)
  freeClosed := by
    simp [successorFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := successorFormula_delta0 _ _

theorem next_index_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω n m : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) (hs : M.SuccessorOf m n) :
    ∃ J, Graph M J n m ∧ ∀ i j, MemPair M J i j ↔ M.mem i n ∧ M.mem j m ∧ M.SuccessorOf j i := by
  let e : Env M 0 := ⟨Fin.elim0,fun _ => ω⟩
  have hφ (i j : M.Domain) : Project.Formula.satisfies ((e.push i).push j) nextIndexSchema.body ↔ M.SuccessorOf j i := by
    simp only [nextIndexSchema,successorFormula_iff hM.1]
    rfl
  obtain ⟨J,hSupport,hRaw⟩ := relation_comprehension_d hM nextIndexSchema e n m
  have hRows (i j : M.Domain) : MemPair M J i j ↔ M.mem i n ∧ M.mem j m ∧ M.SuccessorOf j i := by
    simpa only [hφ] using hRaw i j
  have hOrdω := KP1Y.Naturals.omega_isOrdinal_d hM hω
  have hOrdN := hOrdω.mem hn
  refine ⟨J,⟨hSupport,?_,?_⟩,hRows⟩
  · intro i hi
    obtain ⟨j,hj,hjω⟩ := hω.1.2 i (hOrdω.transitive n hn i hi)
    have hSub : M.MemberSubset j n := by
      intro x hx
      rcases (hj x).mp hx with hxi | hSame
      · exact hOrdN.transitive i hi x hxi
      · exact (hM.1.eq_of_same_members x i hSame) ▸ hi
    have hjm : M.mem j m := by
      rcases KP1Y.Naturals.ordinal_subset_cases_d hM (hOrdω.mem hjω) hOrdN hSub with hEq | hjn
      · subst j
        exact hs.predecessor_mem
      · exact (hs j).mpr (Or.inl hjn)
    exact ⟨j,hjm,(hRows i j).mpr ⟨hi,hjm,hj⟩⟩
  · intro i j k hij hik
    exact Structure.SuccessorOf.eq hM.1 ((hRows i j).mp hij).2.2 ((hRows i k).mp hik).2.2

structure AdjacentSelectors (M : SetTheory.Structure.{u}) (names m scope n X Y : M.Domain) : Prop where
  successor : M.SuccessorOf m n
  left : Graph M X n scope
  right : Graph M Y n scope
  next : ∀ i, M.mem i n → ∃ j, M.mem j m ∧ M.SuccessorOf j i
  left_rows : ∀ i, M.mem i n → ∀ v, MemPair M X i v ↔ MemPair M names i v
  right_rows : ∀ i, M.mem i n → ∀ j, M.mem j m → M.SuccessorOf j i →
    ∀ v, MemPair M Y i v ↔ MemPair M names j v

theorem adjacent_selectors_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω n m names scope : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) (hs : M.SuccessorOf m n)
    (hNames : Graph M names m scope) : ∃ X Y, AdjacentSelectors M names m scope n X Y := by
  have hSub : M.MemberSubset n m := fun i hi => (hs i).mpr (Or.inl hi)
  obtain ⟨X,hX,hXRows⟩ := restrict_graph_d hM hNames hSub
  obtain ⟨J,hJ,hJRows⟩ := next_index_graph_d hM hω hn hs
  obtain ⟨Y,hY⟩ := tuple_value_exists_d hM hJ hNames
  refine ⟨X,Y,hs,hX,hY.values,?_,?_,?_⟩
  · intro i hi
    obtain ⟨j,hj,hAt⟩ := hJ.total i hi
    exact ⟨j,hj,((hJRows i j).mp hAt).2.2⟩
  · intro i hi v
    exact (hXRows i v).trans ⟨And.right,fun h => ⟨hi,h⟩⟩
  · intro i hi j hj hNext v
    classical
    by_cases hv : M.mem v scope
    · exact hY.rows i hi j hj v hv ((hJRows i j).mpr ⟨hi,hj,hNext⟩)
    · exact iff_of_false (fun h => hv (hY.values.bounds hM.1 h).2)
        (fun h => hv (hNames.bounds hM.1 h).2)

theorem AdjacentSelectors.compare_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {names m scope n X Y A s f : M.Domain} (h : AdjacentSelectors M names m scope n X Y)
    (hF : TupleValue M f names s m scope A) :
    CompareSelectors true M X Y n scope A s ↔ KP1Y.Reflection.AdjacentIncreasing M f m A := by
  constructor
  · intro hCompare i hi j hj hNext x hx y hy hIx hJy
    have hin : M.mem i n := by
      rcases (h.successor i).mp hi with hin | hSame
      · exact hin
      · have hin := hM.1.eq_of_same_members i n hSame
        subst i
        have hjm := Structure.SuccessorOf.eq hM.1 hNext h.successor
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) m (hjm ▸ hj))
    obtain ⟨u,hu,hIu⟩ := hF.variables.total i hi
    obtain ⟨v,hv,hJv⟩ := hF.variables.total j hj
    exact hCompare i hin u hu v hv ((h.left_rows i hin u).mpr hIu)
      ((h.right_rows i hin j hj hNext v).mpr hJv) x hx y hy
      ((hF.rows i hi u hu x hx hIu).mp hIx) ((hF.rows j hj v hv y hy hJv).mp hJy)
  · intro hAdj i hi u hu v hv hXu hYv x hx y hy hSx hSy
    obtain ⟨j,hj,hNext⟩ := h.next i hi
    have him := (h.successor i).mpr (Or.inl hi)
    have hIu := (h.left_rows i hi u).mp hXu
    have hJv := (h.right_rows i hi j hj hNext v).mp hYv
    exact hAdj i him j hj hNext x hx y hy
      ((hF.rows i him u hu x hx hIu).mpr hSx) ((hF.rows j hj v hv y hy hJv).mpr hSy)

structure IncreasingBlock (α : Type u) where
  length : α
  left : α
  right : α
  codes : α

structure IncreasingBlock.Valid (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (names m scope : M.Domain) (B : IncreasingBlock M.Domain) : Prop where
  natural : M.mem B.length C.reflection.omega
  selectors : AdjacentSelectors M names m scope B.length B.left B.right
  block : BinaryBlock M C D true scope B.length B.left B.right B.codes

theorem increasing_block_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {names m scope : M.Domain}
    (hm : M.mem m C.reflection.omega) (hNe : ∃ i, M.mem i m) (hb : M.mem scope D.omega)
    (hNames : Graph M names m scope) : ∃ B, IncreasingBlock.Valid M C D names m scope B := by
  rcases KP1Y.Naturals.natural_cases hM hC.numerals.omega hm with hEmpty | ⟨n,hn,hs⟩
  · obtain ⟨i,hi⟩ := hNe
    exact False.elim (hEmpty i hi)
  · obtain ⟨X,Y,hSel⟩ := adjacent_selectors_exists_d hM hC.numerals.omega hn hs hNames
    obtain ⟨B,hB⟩ := binary_block_exists_d hM hC hD true hb hSel.left hSel.right
    exact ⟨⟨n,X,Y,B⟩,hn,hSel,hB⟩

theorem IncreasingBlock.Valid.all_atoms_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {PC : Context M.Domain} (hAtom : AtomicTable M D PC.atomic)
    {names m scope s f : M.Domain} {B : IncreasingBlock M.Domain} (hB : B.Valid M C D names m scope)
    (hm : M.mem m C.reflection.omega) (hb : M.mem scope D.omega) (hA : M.IsOrdinal A)
    (hSub : M.MemberSubset A C.top) (hF : TupleValue M f names s m scope A) :
    AllAtoms M PC D B.codes B.length s ↔ KP1Y.Reflection.Increasing M f m A :=
  ((hB.block.all_atoms_iff_d hM hC hD hAtom hSub hb hF.source).trans
    (hB.selectors.compare_iff_d hM hF)).trans
      (KP1Y.Reflection.increasing_iff_adjacent_d hM hC.numerals.omega hm hA hF.values).symm

theorem Height.increasing_block_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {names m scope s f : M.Domain} {B : IncreasingBlock M.Domain} (hB : B.Valid M C S.relations names m scope)
    (hm : M.mem m C.reflection.omega) (hb : M.mem scope S.context.omega)
    (hF : TupleValue M f names s m scope small.carrier) :
    AllAtoms M (small.context S.context) S.relations B.codes B.length s ↔ KP1Y.Reflection.Increasing M f m small.carrier := by
  have hA : M.IsOrdinal small.carrier := Eq.mpr (congrArg M.IsOrdinal h.carrier) h.ordinal
  exact ((h.binary_block_iff_d hM hC hS hb hB.block hF.source).trans
    (hB.selectors.compare_iff_d hM hF)).trans
      (KP1Y.Reflection.increasing_iff_adjacent_d hM hC.numerals.omega hm hA hF.values).symm

theorem shape_increasing_blocks_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength) :
    ∃ BI BO, IncreasingBlock.Valid M C D V.inputs T.width V.scope BI ∧
      IncreasingBlock.Valid M C D V.outputs T.width V.scope BO := by
  have hb : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  obtain ⟨BI,hBI⟩ := increasing_block_exists_d hM hC hD hV.width ⟨T.cut,hT.cut⟩ hb hV.inputs.graph
  obtain ⟨BO,hBO⟩ := increasing_block_exists_d hM hC hD hV.width ⟨T.cut,hT.cut⟩ hb hV.outputs.graph
  exact ⟨BI,BO,hBI,hBO⟩

theorem increasing_enlarge {M : SetTheory.Structure.{u}} (he : Extensional M) {f m A B : M.Domain}
    (hF : Graph M f m A) (h : KP1Y.Reflection.Increasing M f m A) : KP1Y.Reflection.Increasing M f m B := by
  intro i hi j hj hij x _ y _ hIx hJy
  exact h i hi j hj hij x (hF.bounds he hIx).2 y (hF.bounds he hJy).2 hIx hJy

end KP1Y.ReflectionModel
