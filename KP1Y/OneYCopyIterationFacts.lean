import KP1Y.OneYCopyInvariant
import KP1Y.OneYLowerRowShift

/-! 相邻复制块的实际move/ParentCopy交换，以及逐位置源事实运输的复合。 -/
namespace KP1Y.OneYFinite.CopyInvariant
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Arithmetic
open KP1Y.Reflection KP1Y.Ranking KP1Y.OneYFinite.CopyCoordinates
universe u

theorem add_associative_read_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {p off delta x nextOff y : M.Domain} (hX : AddAt M T.addPairs T.plus p off x)
    (hOff : AddAt M T.addPairs T.plus off delta nextOff) :
    AddAt M T.addPairs T.plus x delta y ↔ AddAt M T.addPairs T.plus p nextOff y := by
  have hx := hX.bounds hM.1 hT.add
  have ho := hOff.bounds hM.1 hT.add
  have hXS := (hT.add.add_iff_sum hM hx.1 hx.2.1).mp hX
  have hOS := (hT.add.add_iff_sum hM ho.1 ho.2.1).mp hOff
  constructor
  · intro hY
    obtain ⟨z,_,hZ⟩ := hT.add.add_exists_d hM hE hx.1 ho.2.2
    have he := natural_sum_assoc_d hM hE hx.2.1 ho.2.1 hXS
      ((hT.add.add_iff_sum hM hx.2.2 ho.2.1).mp hY) hOS ((hT.add.add_iff_sum hM hx.1 ho.2.2).mp hZ)
    exact he.symm ▸ hZ
  · intro hY
    obtain ⟨z,_,hZ⟩ := hT.add.add_exists_d hM hE hx.2.2 ho.2.1
    have he := natural_sum_assoc_d hM hE hx.2.1 ho.2.1 hXS
      ((hT.add.add_iff_sum hM hx.2.2 ho.2.1).mp hZ) hOS ((hT.add.add_iff_sum hM hx.1 ho.2.2).mp hY)
    exact he ▸ hZ

/-- 原move(width,cut)作用于第b份ParentCopy，恰好得到第b+1份。 -/
theorem move_parent_copy_successor_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {X : Context M.Domain} (hX : X.Valid M E) {b next width cut p x y : M.Domain}
    (hNext : M.SuccessorOf next b) (hWidth : Width M E T X b width) (hCut : Encode M E T X X.root b cut)
    (hOld : ParentCopy M E T X b p x) :
    MoveColumn M E T width cut x y ↔ ParentCopy M E T X next p y := by
  have hB := hOld.2.1
  have hP := hOld.1
  have hN := natural_successor_mem_d hM hE hB hNext
  obtain ⟨off,hOff,hMul⟩ := hT.mul.mul_exists_d hM hE hB (hX.length_nat hM.1)
  have hOldShift := (parent_copy_shift_iff hM.1 hT hB hP hOff hMul).mp hOld
  have hCutAdd : AddAt M T.addPairs T.plus X.root off cut := by
    obtain ⟨_,_,off',_,hMul',hAdd⟩ := hCut
    have he := hT.mul.mul_unique hM.1 hMul' hMul
    exact he ▸ hAdd
  have hCutNat := (hCutAdd.bounds hM.1 hT.add).2.2
  have hWidthNat := width_natural hM.1 hT hWidth
  classical
  by_cases hGood : M.mem p X.root
  · have hxp := (parent_copy_good_iff hB hP hGood).mp hOld
    subst x
    have hpc := sum_base_subset_d hM ((omega_isOrdinal_d hM hE.omega).mem hX.root)
      ((hT.add.add_iff_sum hM hX.root hOff).mp hCutAdd) p hGood
    rw [parent_copy_good_iff hN hP hGood]
    constructor
    · intro h
      exact h.2.2.2.elim And.right (fun h => False.elim (h.1 hpc))
    · intro he
      exact ⟨hWidthNat,hCutNat,hP,Or.inl ⟨hpc,he⟩⟩
  · have hXAdd : AddAt M T.addPairs T.plus p off x :=
      hOldShift.elim (fun h => False.elim (hGood h.1)) And.right
    have hx := (hXAdd.bounds hM.1 hT.add).2.2
    have hNotCut : ¬M.mem x cut := fun h => hGood ((add_same_right_lt_iff_d hM hE hT hXAdd hCutAdd).mp h)
    obtain ⟨nextOff,hNextOff,hMulNext⟩ := hT.mul.mul_exists_d hM hE hN (hX.length_nat hM.1)
    have hSumOff := natural_product_left_successor_d hM hE hB (hX.length_nat hM.1) hNext
      ((hT.mul.mul_iff_product hM hB (hX.length_nat hM.1)).mp hMul)
      ((hT.mul.mul_iff_product hM hN (hX.length_nat hM.1)).mp hMulNext)
    have hAddOff := (hT.add.add_iff_sum hM hOff (hX.length_nat hM.1)).mpr hSumOff
    rw [move_as_shift_d hM hE hT (width_minus_cut_d hM hE hT hX hWidth hCut)
      (Or.inr (cut_lt_width_d hM hE hT hX hWidth hCut)) hx,
      parent_copy_shift_iff hM.1 hT hN hP hNextOff hMulNext]
    change ((M.mem x cut ∧ y=x) ∨ (¬M.mem x cut ∧ AddAt M T.addPairs T.plus x X.length y)) ↔
      ((M.mem p X.root ∧ y=p) ∨ (¬M.mem p X.root ∧ AddAt M T.addPairs T.plus p nextOff y))
    simp only [hNotCut,hGood,false_and,not_false_eq_true,true_and,false_or]
    exact add_associative_read_iff_d hM hE hT hXAdd hAddOff

structure MoveColumns (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (width cut J : M.Domain) : Prop where
  embedding : ColumnEmbedding M E.omega E.omega J
  rows : ∀ p q, MemPair M J p q ↔ MoveColumn M E T width cut p q

theorem move_columns_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {X : Context M.Domain} (hX : X.Valid M E) {b width cut : M.Domain}
    (hWidth : Width M E T X b width) (hCut : Encode M E T X X.root b cut) : ∃ J, MoveColumns M E T width cut J := by
  have hCutNat : M.mem cut E.omega := by
    obtain ⟨_,_,_,_,_,hAdd⟩ := hCut
    exact (hAdd.bounds hM.1 hT.add).2.2
  obtain ⟨J,hJ,hRows⟩ := move_embedding_exists_d hM hE hT (width_natural hM.1 hT hWidth) hCutNat
    (Or.inr (cut_lt_width_d hM hE hT hX hWidth hCut))
  exact ⟨J,hJ,hRows⟩

theorem CopyColumns.move_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {X : Context M.Domain} (hX : X.Valid M E) {b next width cut J K L p x y : M.Domain}
    (hNext : M.SuccessorOf next b) (hWidth : Width M E T X b width) (hCut : Encode M E T X X.root b cut)
    (hJ : CopyColumns M E T X b J) (hK : MoveColumns M E T width cut K) (hL : CopyColumns M E T X next L)
    (hAt : MemPair M J p x) : MemPair M K x y ↔ MemPair M L p y := by
  rw [hK.rows,hL.rows]
  exact move_parent_copy_successor_iff_d hM hE hT hX hNext hWidth hCut ((hJ.rows p x).mp hAt)

theorem ReindexEdge.compose {M : SetTheory.Structure.{u}} (he : Extensional M) {w Pairs J K L a b c : M.Domain}
    (hCompose : ∀ p x y, MemPair M J p x → MemPair M K x y → MemPair M L p y)
    (h : ReindexEdge M w Pairs J a b) (h' : ReindexEdge M w Pairs K b c) : ReindexEdge M w Pairs L a c := by
  obtain ⟨k,hk,q,hq,p,hp,j,hj,x,_,y,_,z,_,hA,hX,hY,hZ,hB⟩ := h
  obtain ⟨k',_,x',_,y',_,z',_,u,hu,v,hv,t,ht,hB',hU,hV,hT,hC⟩ := h'
  obtain ⟨hk',hx',hy',hz'⟩ := hB.injective he hB'
  subst k'; subst x'; subst y'; subst z'
  exact ⟨k,hk,q,hq,p,hp,j,hj,u,hu,v,hv,t,ht,hA,hCompose q x u hX hU,hCompose p y v hY hV,hCompose j z t hZ hT,hC⟩

theorem ReindexNeed.compose {M : SetTheory.Structure.{u}} (he : Extensional M) {w J K L a b c : M.Domain}
    (hCompose : ∀ p x y, MemPair M J p x → MemPair M K x y → MemPair M L p y)
    (h : ReindexNeed M w J a b) (h' : ReindexNeed M w K b c) : ReindexNeed M w L a c := by
  obtain ⟨k,hk,q,hq,p,hp,x,_,y,_,hA,hX,hY,hB⟩ := h
  obtain ⟨k',_,x',_,y',_,u,hu,v,hv,hB',hU,hV,hC⟩ := h'
  obtain ⟨hk',hx',hy'⟩ := hB.injective he hB'
  subst k'; subst x'; subst y'
  exact ⟨k,hk,q,hq,p,hp,u,hu,v,hv,hA,hCompose q x u hX hU,hCompose p y v hY hV,hC⟩

theorem EdgeListTransport.compose {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : Reflection.Data M.Domain} {J K L A B C len len' : M.Domain} (hL : Graph M L D.omega D.omega)
    (hCompose : ∀ p x y, MemPair M J p x → MemPair M K x y → MemPair M L p y)
    (h : EdgeListTransport M D J len A B) (h' : EdgeListTransport M D K len' B C) : EdgeListTransport M D L len A C := by
  have hLen := graph_domain_unique he h.target h'.source
  subst len'
  refine ⟨h.natural,h.source,h'.target,?_⟩
  intro i c
  constructor
  · intro hAt
    obtain ⟨b,_,hB,hBC⟩ := (h'.rows i c).mp hAt
    obtain ⟨a,ha,hA,hAB⟩ := (h.rows i b).mp hB
    exact ⟨a,ha,hA,hAB.compose he hCompose hBC⟩
  · rintro ⟨a,_,hA,hAC⟩
    have hi := (h.source.bounds he hA).1
    obtain ⟨b,_,hB⟩ := h.target.total i hi
    obtain ⟨a',_,hA',hAB⟩ := (h.rows i b).mp hB
    have haa := h.source.unique i a' a hA' hA
    subst a'
    obtain ⟨c',_,hC⟩ := h'.target.total i hi
    obtain ⟨b',_,hB',hBC⟩ := (h'.rows i c').mp hC
    have hbb := h.target.unique i b' b hB' hB
    subst b'
    have hcc := (hAB.compose he hCompose hBC).unique he hL hAC
    exact hcc ▸ hC

theorem NeedListTransport.compose {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : Reflection.Data M.Domain} {J K L A B C len len' : M.Domain} (hL : Graph M L D.omega D.omega)
    (hCompose : ∀ p x y, MemPair M J p x → MemPair M K x y → MemPair M L p y)
    (h : NeedListTransport M D J len A B) (h' : NeedListTransport M D K len' B C) : NeedListTransport M D L len A C := by
  have hLen := graph_domain_unique he h.target h'.source
  subst len'
  refine ⟨h.natural,h.source,h'.target,?_⟩
  intro i c
  constructor
  · intro hAt
    obtain ⟨b,_,hB,hBC⟩ := (h'.rows i c).mp hAt
    obtain ⟨a,ha,hA,hAB⟩ := (h.rows i b).mp hB
    exact ⟨a,ha,hA,hAB.compose he hCompose hBC⟩
  · rintro ⟨a,_,hA,hAC⟩
    have hi := (h.source.bounds he hA).1
    obtain ⟨b,_,hB⟩ := h.target.total i hi
    obtain ⟨a',_,hA',hAB⟩ := (h.rows i b).mp hB
    have haa := h.source.unique i a' a hA' hA
    subst a'
    obtain ⟨c',_,hC⟩ := h'.target.total i hi
    obtain ⟨b',_,hB',hBC⟩ := (h'.rows i c').mp hC
    have hbb := h.target.unique i b' b hB' hB
    subst b'
    have hcc := (hAB.compose he hCompose hBC).unique he hL hAC
    exact hcc ▸ hC

theorem copied_facts_successor_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=E.omega)
    {X : Context M.Domain} (hX : X.Valid M E) {b next width cut A B : M.Domain}
    (hNext : M.SuccessorOf next b) (hWidth : Width M E T X b width) (hCut : Encode M E T X X.root b cut)
    (hOld : CopiedFacts M E T D X b A B) :
    ∃ K len C, MoveColumns M E T width cut K ∧ EdgeListTransport M D K len B C ∧ CopiedFacts M E T D X next A C := by
  obtain ⟨J,oldLen,hJ,hOld⟩ := hOld
  obtain ⟨L,hL⟩ := copy_columns_exists_d hM hE hT hX (natural_successor_mem_d hM hE hWidth.2.1 hNext)
  obtain ⟨K,hK⟩ := move_columns_exists_d hM hE hT hX hWidth hCut
  have hKD : Graph M K D.omega D.omega := by simpa only [hOmega] using hK.embedding.graph
  have hLD : Graph M L D.omega D.omega := by simpa only [hOmega] using hL.embedding.graph
  obtain ⟨len,C,hNew⟩ := edge_list_transport_exists_d hM hD hKD (hOld.list_mem hD)
  have hCompose : ∀ p x y, MemPair M J p x → MemPair M K x y → MemPair M L p y :=
    fun _ _ _ hAt hNextAt => (hJ.move_successor_d hM hE hT hX hNext hWidth hCut hK hL hAt).mp hNextAt
  exact ⟨K,len,C,hK,hNew,L,oldLen,hL,hOld.compose hM.1 hLD hCompose hNew⟩

theorem copied_templates_successor_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=E.omega)
    {X : Context M.Domain} (hX : X.Valid M E) {b next width cut A B : M.Domain}
    (hNext : M.SuccessorOf next b) (hWidth : Width M E T X b width) (hCut : Encode M E T X X.root b cut)
    (hOld : CopiedTemplates M E T D X b A B) :
    ∃ K len C, MoveColumns M E T width cut K ∧ NeedListTransport M D K len B C ∧ CopiedTemplates M E T D X next A C := by
  obtain ⟨J,oldLen,hJ,hOld⟩ := hOld
  obtain ⟨L,hL⟩ := copy_columns_exists_d hM hE hT hX (natural_successor_mem_d hM hE hWidth.2.1 hNext)
  obtain ⟨K,hK⟩ := move_columns_exists_d hM hE hT hX hWidth hCut
  have hKD : Graph M K D.omega D.omega := by simpa only [hOmega] using hK.embedding.graph
  have hLD : Graph M L D.omega D.omega := by simpa only [hOmega] using hL.embedding.graph
  obtain ⟨len,C,hNew⟩ := need_list_transport_exists_d hM hD hKD (hOld.list_mem hD)
  have hCompose : ∀ p x y, MemPair M J p x → MemPair M K x y → MemPair M L p y :=
    fun _ _ _ hAt hNextAt => (hJ.move_successor_d hM hE hT hX hNext hWidth hCut hK hL hAt).mp hNextAt
  exact ⟨K,len,C,hK,hNew,L,oldLen,hL,hOld.compose hM.1 hLD hCompose hNew⟩

theorem copied_facts_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=E.omega)
    {X : Context M.Domain} (hX : X.Valid M E) {b next width cut A B C : M.Domain}
    (hNext : M.SuccessorOf next b) (hWidth : Width M E T X b width) (hCut : Encode M E T X X.root b cut)
    (hOld : CopiedFacts M E T D X b A B) (hNew : CopiedFacts M E T D X next A C) :
    ∃ K len, MoveColumns M E T width cut K ∧ EdgeListTransport M D K len B C := by
  obtain ⟨K,len,C',hK,hMoved,hC'⟩ := copied_facts_successor_exists_d hM hE hT hD hOmega hX hNext hWidth hCut hOld
  have hCC := hC'.unique hM.1 hNew
  exact hCC ▸ ⟨K,len,hK,hMoved⟩

theorem copied_templates_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=E.omega)
    {X : Context M.Domain} (hX : X.Valid M E) {b next width cut A B C : M.Domain}
    (hNext : M.SuccessorOf next b) (hWidth : Width M E T X b width) (hCut : Encode M E T X X.root b cut)
    (hOld : CopiedTemplates M E T D X b A B) (hNew : CopiedTemplates M E T D X next A C) :
    ∃ K len, MoveColumns M E T width cut K ∧ NeedListTransport M D K len B C := by
  obtain ⟨K,len,C',hK,hMoved,hC'⟩ := copied_templates_successor_exists_d hM hE hT hD hOmega hX hNext hWidth hCut hOld
  have hCC := hC'.unique hM.1 hNew
  exact hCC ▸ ⟨K,len,hK,hMoved⟩

theorem copy_root_le_cut_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {X : Context M.Domain} (hX : X.Valid M E) {b cut q q' : M.Domain}
    (hCut : Encode M E T X X.root b cut) (hBelow : q=X.root ∨ M.mem q X.root) (hCopy : ParentCopy M E T X b q q') :
    q'=cut ∨ M.mem q' cut := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hE hT hX hCopy.2.1
  have hRootCopy : ParentCopy M E T X b X.root cut :=
    (parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mpr hCut
  have hJQ := (hRows q q').mpr hCopy
  have hJR := (hRows X.root cut).mpr hRootCopy
  rcases hBelow with he | hqr
  · subst q
    exact Or.inl (hJ.graph.unique X.root q' cut hJQ hJR)
  · exact Or.inr (hJ.strict q hCopy.1 X.root hX.root hqr q' cut hJQ hJR)

theorem root_le_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {m F c p q : M.Domain}
    (hF : Forest M E.omega m F) (hParent : MemPair M F c p) (hRoot : Root M E m F c q) : q=p ∨ M.mem q p := by
  rcases hRoot.2.2 with he | hAnc
  · subst q
    exact False.elim (hRoot.2.1 p (hF.bounds hM.1 hParent).2 hParent)
  · obtain ⟨p',hP',hTail⟩ := ancestor_parent_cases_d hM hE hF hAnc
    have hpp := hF.unique c p' p hP' hParent
    subst p'
    exact hTail.imp_right And.left

theorem control_root_le_cut_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {X : Context M.Domain} (hX : X.Valid M E) {m F b cut q control : M.Domain}
    (hF : Forest M E.omega m F) (hParent : MemPair M F X.last X.root) (hRoot : Root M E m F X.last q)
    (hCut : Encode M E T X X.root b cut) (hCopy : ParentCopy M E T X b q control) : control=cut ∨ M.mem control cut :=
  copy_root_le_cut_d hM hE hT hX hCut (root_le_parent_d hM hE hF hParent hRoot) hCopy

end KP1Y.OneYFinite.CopyInvariant
