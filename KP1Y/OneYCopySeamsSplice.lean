import KP1Y.OneYCopySpliceGeometry

/-! 单个复制块的真实拼接坐标与标签：前段取反射标签，cut以后旧标签经MoveColumn移入新块。 -/
namespace KP1Y.OneYFinite.CopySeams
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Reflection
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopyInvariant KP1Y.OneYFinite.CopyGeometry
universe u

/-- 第b块到第b+1块的实际宽度与cut；均为实际Encode。 -/
structure Block (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (b next width nextWidth cut : M.Domain) : Prop where
  succ : M.SuccessorOf next b
  width : Width M C T A b width
  widthNext : Width M C T A next nextWidth
  cut : Encode M C T A A.root b cut

namespace Block

variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {A : Context M.Domain} {b next width nextWidth cut : M.Domain}

theorem width_nat (hM : M.Models KP1Y.theory) (hT : T.Valid M C)
    (h : Block M C T A b next width nextWidth cut) : M.mem width C.omega := width_natural hM.1 hT h.width

theorem widthNext_nat (hM : M.Models KP1Y.theory) (hT : T.Valid M C)
    (h : Block M C T A b next width nextWidth cut) : M.mem nextWidth C.omega := width_natural hM.1 hT h.widthNext

theorem cut_nat (hM : M.Models KP1Y.theory) (hT : T.Valid M C)
    (h : Block M C T A b next width nextWidth cut) : M.mem cut C.omega := by
  obtain ⟨_,_,_,_,_,hAdd⟩ := h.cut
  exact (hAdd.bounds hM.1 hT.add).2.2

theorem b_nat (h : Block M C T A b next width nextWidth cut) : M.mem b C.omega := h.width.2.1

theorem next_nat (hM : M.Models KP1Y.theory) (hC : C.Valid M) (h : Block M C T A b next width nextWidth cut) :
    M.mem next C.omega := natural_successor_mem_d hM hC h.b_nat h.succ

theorem cut_mem (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) (hA : A.Valid M C)
    (h : Block M C T A b next width nextWidth cut) : M.mem cut width := cut_lt_width_d hM hC hT hA h.width h.cut

theorem width_mem (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) (hA : A.Valid M C)
    (h : Block M C T A b next width nextWidth cut) : M.mem width nextWidth :=
  cut_lt_width_d hM hC hT hA h.widthNext (width_is_next_cut_d hM hC hT hA h.succ h.width)

theorem width_subset (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) (hA : A.Valid M C)
    (h : Block M C T A b next width nextWidth cut) : M.MemberSubset width nextWidth :=
  ((omega_isOrdinal_d hM hC.omega).mem (h.widthNext_nat hM hT)).transitive width (h.width_mem hM hC hT hA)

theorem difference (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) (hA : A.Valid M C)
    (h : Block M C T A b next width nextWidth cut) : TruncatedDifference M C.omega C.zero width cut A.length :=
  width_minus_cut_d hM hC hT hA h.width h.cut

theorem move_bound (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) (hA : A.Valid M C)
    (h : Block M C T A b next width nextWidth cut) {i j : M.Domain} (hi : M.mem i width)
    (hMove : MoveColumn M C T width cut i j) : M.mem j nextWidth :=
  move_column_bound_d hM hC hT (h.difference hM hC hT hA) (Or.inr (h.cut_mem hM hC hT hA))
    (width_successor_d hM hC hT hA h.succ h.width h.widthNext) hi hMove

theorem move_fixed {i j : M.Domain} (hi : M.mem i cut) (hMove : MoveColumn M C T width cut i j) : j=i := by
  rcases hMove.2.2.2 with ⟨_,he⟩ | ⟨hNot,_⟩
  · exact he
  · exact False.elim (hNot hi)

theorem move_new (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) (hA : A.Valid M C)
    (h : Block M C T A b next width nextWidth cut) {i j : M.Domain} (hi : ¬M.mem i cut)
    (hMove : MoveColumn M C T width cut i j) : ¬M.mem j width := by
  have hDiff := h.difference hM hC hT hA
  have hCutLe : cut=width ∨ M.mem cut width := Or.inr (h.cut_mem hM hC hT hA)
  have hShift := (move_as_shift_d hM hC hT hDiff hCutLe hMove.2.2.1).mp hMove
  rcases hShift with ⟨hBefore,_⟩ | ⟨_,hAdd⟩
  · exact False.elim (hi hBefore)
  · have hCutSum := truncated_difference_add_inverse_d hM hC hDiff hCutLe
    have hCutAdd : AddAt M T.addPairs T.plus cut A.length width :=
      (hT.add.add_iff_sum hM (h.cut_nat hM hT) (hA.length_nat hM.1)).mpr hCutSum
    intro hj
    exact hi ((add_same_right_lt_iff_d hM hC hT hAdd hCutAdd).mp hj)

theorem move_cut (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Block M C T A b next width nextWidth cut) : MoveColumn M C T width cut cut width :=
  move_cut_to_size_d hM hC hT (h.width_nat hM hT) (h.cut_nat hM hT)

theorem move_exists (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Block M C T A b next width nextWidth cut) {i : M.Domain} (hi : M.mem i C.omega) :
    ∃ j, M.mem j C.omega ∧ MoveColumn M C T width cut i j :=
  move_exists_d hM hC hT (h.width_nat hM hT) (h.cut_nat hM hT) hi

/-- 第b份ParentCopy再经move恰为第b+1份。 -/
theorem move_parent_copy (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) (hA : A.Valid M C)
    (h : Block M C T A b next width nextWidth cut) {p x y : M.Domain} (hOld : ParentCopy M C T A b p x) :
    MoveColumn M C T width cut x y ↔ ParentCopy M C T A next p y :=
  move_parent_copy_successor_iff_d hM hC hT hA h.succ h.width h.cut hOld

theorem move_onto (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) (hA : A.Valid M C)
    (h : Block M C T A b next width nextWidth cut) {j : M.Domain} (hj : M.mem j nextWidth) (hNot : ¬M.mem j width) :
    ∃ i, M.mem i width ∧ ¬M.mem i cut ∧ MoveColumn M C T width cut i j := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hjNat := hw.transitive nextWidth (h.widthNext_nat hM hT) j hj
  rcases hw.wellOrder.linear.compare width (h.width_nat hM hT) j hjNat with he | hlt | hgt
  · have hjw := hM.1.eq_of_same_members width j he
    subst j
    exact ⟨cut,h.cut_mem hM hC hT hA,SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) cut,h.move_cut hM hC hT⟩
  · obtain ⟨s,hRootS,hSLast,hEncode⟩ := new_nonseam_coordinates_d hM hC hT hA h.succ h.width h.widthNext hlt hj
    have hNotRoot : ¬M.mem s A.root := fun hs => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s
      ((hw.mem hEncode.1).transitive A.root hRootS s hs)
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA h.b_nat
    obtain ⟨i,_,hAt⟩ := hJ.graph.total s hEncode.1
    have hCopy := (hRows s i).mp hAt
    have hi : M.mem i width := parent_copy_below_encode_d hM hC hT hA hA.below hSLast hCopy h.width
    have hMove : MoveColumn M C T width cut i j :=
      (h.move_parent_copy hM hC hT hA hCopy).mpr ((parent_copy_bad_iff hNotRoot).mpr hEncode)
    refine ⟨i,hi,?_,hMove⟩
    intro hiCut
    have hji := move_fixed hiCut hMove
    exact hNot (hji ▸ hi)
  · exact False.elim (hNot hgt)

theorem move_injective (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) (hA : A.Valid M C)
    (h : Block M C T A b next width nextWidth cut) {i i' j : M.Domain}
    (hMove : MoveColumn M C T width cut i j) (hMove' : MoveColumn M C T width cut i' j) : i=i' := by
  obtain ⟨K,hK⟩ := move_columns_exists_d hM hC hT hA h.width h.cut
  have hw := omega_isOrdinal_d hM hC.omega
  have hKi := (hK.rows i j).mpr hMove
  have hKi' := (hK.rows i' j).mpr hMove'
  rcases hw.wellOrder.linear.compare i hMove.2.2.1 i' hMove'.2.2.1 with he | hlt | hgt
  · exact hM.1.eq_of_same_members i i' he
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) j
      (hK.embedding.strict i hMove.2.2.1 i' hMove'.2.2.1 hlt j j hKi hKi'))
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) j
      (hK.embedding.strict i' hMove'.2.2.1 i hMove.2.2.1 hgt j j hKi' hKi))

theorem move_strict (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) (hA : A.Valid M C)
    (h : Block M C T A b next width nextWidth cut) {i i' j j' : M.Domain} (hii : M.mem i i')
    (hMove : MoveColumn M C T width cut i j) (hMove' : MoveColumn M C T width cut i' j') : M.mem j j' := by
  obtain ⟨K,hK⟩ := move_columns_exists_d hM hC hT hA h.width h.cut
  exact hK.embedding.strict i hMove.2.2.1 i' hMove'.2.2.1 hii j j' ((hK.rows i j).mpr hMove) ((hK.rows i' j').mpr hMove')

end Block

private def spliceSchema : Project.Delta0BinarySchema 4 where
  body := .disj (.conj (.mem (.bound 1) (.bound 5)) (memPairFormula (.bound 4) (.bound 1) (.bound 0)))
    (.conj (.neg (.mem (.bound 1) (.bound 5))) (Project.Formula.existsMem (.bound 5)
      (.conj (memPairFormula (.bound 4) (.bound 0) (.bound 2)) (memPairFormula (.bound 3) (.bound 0) (.bound 1)))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
      Definitional.Formula.FreeClosed]
  delta0 := .disj (.conj (.mem _ _) (memPairFormula_delta0 _ _ _))
    (.conj (.neg (.mem _ _)) (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))

private theorem spliceSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (width g K f j x : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv width).push g).push K).push f).push j).push x) spliceSchema.body ↔
      (M.mem j width ∧ MemPair M g j x) ∨
        (¬M.mem j width ∧ ∃ i, M.mem i width ∧ MemPair M K i j ∧ MemPair M f i x) := by
  simp only [spliceSchema,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_existsMem_iff,
    memPairFormula_iff he]
  rfl

/-- 拼接后的新标签：旧宽度上读g，新块读f在move前的值。 -/
structure SpliceLabel (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Reflection.Data M.Domain) (width nextWidth cut f g h : M.Domain) : Prop where
  labeling : Labeling M D nextWidth h
  old : ∀ i, M.mem i width → ∀ x, MemPair M h i x ↔ MemPair M g i x
  moved : ∀ i, M.mem i width → ∀ j, MoveColumn M C T width cut i j → ∀ x, MemPair M h j x ↔ MemPair M f i x

theorem splice_label_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {A : Context M.Domain} (hA : A.Valid M C) {b next width nextWidth cut f g a : M.Domain}
    (hBlock : Block M C T A b next width nextWidth cut)
    (hf : Labeling M D width f) (hg : Labeling M D width g) (hPrefix : PrefixAgree M D f g cut)
    (hCutA : MemPair M f cut a) (hBelow : Below M D width g a) :
    ∃ h, SpliceLabel M C T D width nextWidth cut f g h := by
  have he := hM.1
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨K,hK⟩ := move_columns_exists_d hM hC hT hA hBlock.width hBlock.cut
  obtain ⟨h,hSupport,hRaw⟩ := relation_comprehension_d hM spliceSchema
    ((((oneEnv width).push g).push K).push f) nextWidth D.cap
  have hRows (j x : M.Domain) : MemPair M h j x ↔ M.mem j nextWidth ∧ M.mem x D.cap ∧
      ((M.mem j width ∧ MemPair M g j x) ∨ (¬M.mem j width ∧ ∃ i, M.mem i width ∧ MoveColumn M C T width cut i j ∧ MemPair M f i x)) := by
    rw [hRaw j x,spliceSchema_iff he]
    simp only [hK.rows]
  have hSub := hBlock.width_subset hM hC hT hA
  have hCutW := hBlock.cut_mem hM hC hT hA
  have hWidthOrd := hw.mem (hBlock.width_nat hM hT)
  -- 旧宽度上的读值
  have hOld : ∀ i, M.mem i width → ∀ x, MemPair M h i x ↔ MemPair M g i x := by
    intro i hi x
    rw [hRows i x]
    constructor
    · rintro ⟨_,_,⟨_,hgx⟩ | ⟨hNot,_⟩⟩
      · exact hgx
      · exact False.elim (hNot hi)
    · intro hgx
      exact ⟨hSub i hi,(hg.graph.bounds he hgx).2,Or.inl ⟨hi,hgx⟩⟩
  -- move后新块的读值
  have hNew : ∀ i, M.mem i width → ¬M.mem i cut → ∀ j, MoveColumn M C T width cut i j →
      ∀ x, MemPair M h j x ↔ MemPair M f i x := by
    intro i hi hNotCut j hMove x
    have hjNot := hBlock.move_new hM hC hT hA hNotCut hMove
    rw [hRows j x]
    constructor
    · rintro ⟨_,_,⟨hj,_⟩ | ⟨_,i',_,hMove',hfx⟩⟩
      · exact False.elim (hjNot hj)
      · have hii := hBlock.move_injective hM hC hT hA hMove' hMove
        exact hii ▸ hfx
    · intro hfx
      exact ⟨hBlock.move_bound hM hC hT hA hi hMove,(hf.graph.bounds he hfx).2,Or.inr ⟨hjNot,i,hi,hMove,hfx⟩⟩
  have hMoved : ∀ i, M.mem i width → ∀ j, MoveColumn M C T width cut i j → ∀ x, MemPair M h j x ↔ MemPair M f i x := by
    intro i hi j hMove x
    classical
    by_cases hiCut : M.mem i cut
    · have hji := Block.move_fixed hiCut hMove
      subst j
      rw [hOld i hi x]
      constructor
      · intro hgx
        exact (hPrefix i hiCut x (hg.graph.bounds he hgx).2).mpr hgx
      · intro hfx
        exact (hPrefix i hiCut x (hf.graph.bounds he hfx).2).mp hfx
    · exact hNew i hi hiCut j hMove x
  -- 每一新列或为旧列，或为某个cut以后旧列的move
  have hCover : ∀ j, M.mem j nextWidth → M.mem j width ∨
      ∃ i, M.mem i width ∧ ¬M.mem i cut ∧ MoveColumn M C T width cut i j := by
    intro j hj
    classical
    by_cases hjw : M.mem j width
    · exact Or.inl hjw
    · exact Or.inr (hBlock.move_onto hM hC hT hA hj hjw)
  have hGraph : Graph M h nextWidth D.cap := by
    refine ⟨hSupport,?_,?_⟩
    · intro j hj
      rcases hCover j hj with hjw | ⟨i,hi,hiCut,hMove⟩
      · obtain ⟨x,hx,hgx⟩ := hg.graph.total j hjw
        exact ⟨x,hx,(hOld j hjw x).mpr hgx⟩
      · obtain ⟨x,hx,hfx⟩ := hf.graph.total i hi
        exact ⟨x,hx,(hNew i hi hiCut j hMove x).mpr hfx⟩
    · intro j x y hx hy
      have hj := ((hRows j x).mp hx).1
      rcases hCover j hj with hjw | ⟨i,hi,hiCut,hMove⟩
      · exact hg.graph.unique j x y ((hOld j hjw x).mp hx) ((hOld j hjw y).mp hy)
      · exact hf.graph.unique i x y ((hNew i hi hiCut j hMove x).mp hx) ((hNew i hi hiCut j hMove y).mp hy)
  refine ⟨h,⟨hOmega.symm ▸ hBlock.widthNext_nat hM hT,hGraph,?_,?_⟩,hOld,hMoved⟩
  · intro j hj x hx hjx
    rcases hCover j hj with hjw | ⟨i,hi,hiCut,hMove⟩
    · exact hg.above j hjw x hx ((hOld j hjw x).mp hjx)
    · exact hf.above i hi x hx ((hNew i hi hiCut j hMove x).mp hjx)
  · intro i hi j hj hij x hx y hy hix hjy
    rcases hCover j hj with hjw | ⟨j1,hj1,hj1Cut,hMoveJ⟩
    · have hiw := hWidthOrd.transitive j hjw i hij
      exact hg.increasing i hiw j hjw hij x hx y hy ((hOld i hiw x).mp hix) ((hOld j hjw y).mp hjy)
    · have hfy := (hNew j1 hj1 hj1Cut j hMoveJ y).mp hjy
      have hyOrd := hD.cap.mem hy
      rcases hCover i hi with hiw | ⟨i1,hi1,hi1Cut,hMoveI⟩
      · have hxa := hBelow i hiw x hx ((hOld i hiw x).mp hix)
        have hCutJ1 : cut=j1 ∨ M.mem cut j1 := by
          rcases hw.wellOrder.linear.compare cut (hw.transitive width (hBlock.width_nat hM hT) cut hCutW) j1
              (hw.transitive width (hBlock.width_nat hM hT) j1 hj1) with he' | hlt | hgt
          · exact Or.inl (he.eq_of_same_members cut j1 he')
          · exact Or.inr hlt
          · exact False.elim (hj1Cut hgt)
        rcases hCutJ1 with hEq | hlt
        · subst j1
          have hay := hf.graph.unique cut a y hCutA hfy
          exact hay ▸ hxa
        · have ha := (hf.graph.bounds he hCutA).2
          have hay := hf.increasing cut hCutW j1 hj1 hlt a ha y hy hCutA hfy
          exact hyOrd.transitive a hay x hxa
      · have hfx := (hNew i1 hi1 hi1Cut i hMoveI x).mp hix
        have hi1j1 : M.mem i1 j1 := by
          rcases hw.wellOrder.linear.compare i1 hMoveI.2.2.1 j1 hMoveJ.2.2.1 with he' | hlt | hgt
          · have hEq := he.eq_of_same_members i1 j1 he'
            subst j1
            have hij' := move_unique he hT hMoveI hMoveJ
            subst j
            exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) i hij)
          · exact hlt
          · have hji := hBlock.move_strict hM hC hT hA hgt hMoveJ hMoveI
            have hjOrd := (hw.mem (hw.transitive nextWidth (hBlock.widthNext_nat hM hT) j hj))
            exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) j (hjOrd.transitive i hij j hji))
        exact hf.increasing i1 hi1 j1 hj1 hi1j1 x hx y hy hfx hfy

/-- 拼接标签下新根图的三类边：旧边读反射标签，复制边读move前旧标签（含根弱化），接缝边读端点。 -/
theorem splice_representation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {A : Context M.Domain} (hA : A.Valid M C)
    {Tab b next width nextWidth cut Old New Facts Needs f g h a : M.Domain} (hTable : Table M D Tab)
    (hBlock : Block M C T A b next width nextWidth cut)
    (hGeom : CopySplice.SpliceGeometry M C T D width nextWidth cut Old New Facts Needs)
    (hFactsDiagram : Diagram M D width Facts) (hNeedsTemplate : Template M D width Needs)
    (hf : Labeling M D width f) (hCutA : MemPair M f cut a)
    (hFacts : ∀ k q p c, EdgeAt M D Facts k q p c → EdgeTruth M D Tab f k q p c)
    (hG : Representation M D Tab width Old g) (hBelow : Below M D width g a)
    (hEnd : End M D Tab Needs g a) (hSplice : SpliceLabel M C T D width nextWidth cut f g h) :
    Representation M D Tab nextWidth New h := by
  have he := hM.1
  have hw := omega_isOrdinal_d hM hC.omega
  refine ⟨hGeom.newDiagram,hSplice.labeling,?_⟩
  intro k hk q hq p hp c hc hEdge
  rcases hGeom.classify k q p c hEdge with hOld | hCopy | hSeam
  · obtain ⟨hqw,hpw,hcw,_,_⟩ := hGeom.oldDiagram.edge_columns_d hM hD hOld
    intro η hη x hx y hy hq' hp' hc'
    exact hG.edges k hk q hq p hp c hc hOld η hη x hx y hy ((hSplice.old q hqw η).mp hq')
      ((hSplice.old p hpw x).mp hp') ((hSplice.old c hcw y).mp hc')
  · obtain ⟨q0,p0,c0,hFact,hMoveP,hMoveC,hRoot⟩ := hCopy
    obtain ⟨hq0,hp0,hc0,_,_⟩ := hFactsDiagram.edge_columns_d hM hD hFact
    have hb := hFact.bounds he hD
    intro η hη x hx y hy hq' hp' hc'
    have hfp := (hSplice.moved p0 hp0 p hMoveP x).mp hp'
    have hfc := (hSplice.moved c0 hc0 c hMoveC y).mp hc'
    rcases hRoot with hMoveQ | ⟨hqw,hCutQ⟩
    · exact hFacts k q0 p0 c0 hFact η hη x hx y hy ((hSplice.moved q0 hq0 q hMoveQ η).mp hq') hfp hfc
    · obtain ⟨η0,hη0,hfq0⟩ := hf.graph.total q0 hq0
      have hgq := (hSplice.old q hqw η).mp hq'
      have hηa := hBelow q hqw η hη hgq
      have ha := (hf.graph.bounds he hCutA).2
      have hηη0 : M.mem η η0 := by
        rcases hCutQ with hEq | hlt
        · subst q0
          exact (hf.graph.unique cut a η0 hCutA hfq0) ▸ hηa
        · exact (hD.cap.mem hη0).transitive a
            (hf.increasing cut (hBlock.cut_mem hM hC hT hA) q0 hq0 hlt a ha η0 hη0 hCutA hfq0) η hηa
      exact hTable.root_weaken_d hM hD (hFacts k q0 p0 c0 hFact η0 hη0 x hx y hy hfq0 hfp hfc) (Or.inr hηη0)
  · obtain ⟨hcw,hNeed⟩ := hSeam
    subst c
    obtain ⟨hqw,hpw,_⟩ := hNeedsTemplate.need_columns_d hM hD hNeed
    intro η hη x hx y hy hq' hp' hc'
    have hfy := (hSplice.moved cut (hBlock.cut_mem hM hC hT hA) width (hBlock.move_cut hM hC hT) y).mp hc'
    have hya := hf.graph.unique cut y a hfy hCutA
    subst y
    exact hEnd k hk q hq p hp hNeed η hη x hx ((hSplice.old q hqw η).mp hq') ((hSplice.old p hpw x).mp hp')

theorem SpliceLabel.below_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {A : Context M.Domain} (hA : A.Valid M C)
    {b next width nextWidth cut f g h a beta : M.Domain} (hBlock : Block M C T A b next width nextWidth cut)
    (hSplice : SpliceLabel M C T D width nextWidth cut f g h) (hf : Labeling M D width f)
    (hBeta : M.mem beta D.cap) (hCutA : MemPair M f cut a) (hfBeta : Below M D width f beta)
    (hgA : Below M D width g a) : Below M D nextWidth h beta := by
  intro j hj x hx hjx
  have ha := hfBeta cut (hBlock.cut_mem hM hC hT hA) a (hf.graph.bounds hM.1 hCutA).2 hCutA
  classical
  by_cases hjw : M.mem j width
  · exact (hD.cap.mem hBeta).transitive a ha x (hgA j hjw x hx ((hSplice.old j hjw x).mp hjx))
  · obtain ⟨i,hi,_,hMove⟩ := hBlock.move_onto hM hC hT hA hj hjw
    exact hfBeta i hi x hx ((hSplice.moved i hi j hMove x).mp hjx)

end KP1Y.OneYFinite.CopySeams
