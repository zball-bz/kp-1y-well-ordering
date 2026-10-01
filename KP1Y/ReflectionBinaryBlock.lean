import KP1Y.ReflectionBinaryCode

/-! 两个实际变量选择图逐行生成等号/小于原子代码表。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

structure BinaryBlock (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (strict : Bool) (scope n X Y B : M.Domain) : Prop where
  left : Graph M X n scope
  right : Graph M Y n scope
  graph : Graph M B n D.codes
  rows : ∀ i, M.mem i n → ∀ x, M.mem x scope → ∀ y, M.mem y scope → MemPair M X i x → MemPair M Y i y →
    ∀ a, MemPair M B i a ↔ BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope x y a

private def blockSchema (strict : Bool) : Project.Delta0BinarySchema 7 where
  body := Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 5)
    (.conj (memPairFormula (.bound 5) (.bound 3) (.bound 1)) (.conj (memPairFormula (.bound 4) (.bound 3) (.bound 0))
      (binaryCodeFormula strict (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 6) (.bound 1) (.bound 0) (.bound 2)))))
  freeClosed := by
    have hCode := binaryCodeFormula_freeClosed (d := 11) strict (.bound 7) (.bound 8) (.bound 9) (.bound 10)
      (.bound 6) (.bound 1) (.bound 0) (.bound 2) rfl rfl rfl rfl rfl rfl rfl rfl
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hCode]
  delta0 := .existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
    (binaryCodeFormula_delta0 _ _ _ _ _ _ _ _ _))))

theorem binary_block_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) (strict : Bool) {scope n X Y : M.Domain}
    (hb : M.mem scope D.omega) (hX : Graph M X n scope) (hY : Graph M Y n scope) : ∃ B, BinaryBlock M C D strict scope n X Y B := by
  let e := ((((((oneEnv D.variables).push (C.numbers 2)).push (C.numbers 1)).push (C.numbers 0)).push scope).push X).push Y
  have hφ (i a : M.Domain) : Project.Formula.satisfies ((e.push i).push a) (blockSchema strict).body ↔
      ∃ x, M.mem x scope ∧ ∃ y, M.mem y scope ∧ MemPair M X i x ∧ MemPair M Y i y ∧
        BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope x y a := by
    simp only [blockSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      memPairFormula_iff hM.1,binaryCodeFormula_iff hM.1]
    rfl
  obtain ⟨B,hSupport,hRaw⟩ := relation_comprehension_d hM (blockSchema strict) e n D.codes
  have hRows (i a : M.Domain) : MemPair M B i a ↔ M.mem i n ∧ M.mem a D.codes ∧
      ∃ x, M.mem x scope ∧ ∃ y, M.mem y scope ∧ MemPair M X i x ∧ MemPair M Y i y ∧
        BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope x y a := by
    simpa only [hφ] using hRaw i a
  have hGraph : Graph M B n D.codes := by
    refine ⟨hSupport,?_,?_⟩
    · intro i hi
      obtain ⟨x,hx,hix⟩ := hX.total i hi
      obtain ⟨y,hy,hiy⟩ := hY.total i hi
      obtain ⟨a,ha⟩ := binary_code_exists_d hM hC hD strict hb hx hy
      have haCode := ha.code_mem_d hM hC hD hb
      exact ⟨a,haCode,(hRows i a).mpr ⟨hi,haCode,x,hx,y,hy,hix,hiy,ha⟩⟩
    · intro i a b hia hib
      obtain ⟨_,_,x,_,y,_,hix,hiy,hCode⟩ := (hRows i a).mp hia
      obtain ⟨_,_,x',_,y',_,hix',hiy',hCode'⟩ := (hRows i b).mp hib
      have hxx' := hX.unique i x x' hix hix'
      have hyy' := hY.unique i y y' hiy hiy'
      subst x'
      subst y'
      exact hCode.unique_d hM hC hCode'
  refine ⟨B,hX,hY,hGraph,?_⟩
  intro i hi x hx y hy hix hiy a
  constructor
  · intro hia
    obtain ⟨_,_,x',_,y',_,hix',hiy',hCode⟩ := (hRows i a).mp hia
    have hxx' := hX.unique i x x' hix hix'
    have hyy' := hY.unique i y y' hiy hiy'
    subst x'
    subst y'
    exact hCode
  · intro hCode
    exact (hRows i a).mpr ⟨hi,hCode.code_mem_d hM hC hD hb,x,hx,y,hy,hix,hiy,hCode⟩

theorem BinaryBlock.scoped_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {strict : Bool} {scope n X Y B : M.Domain}
    (hb : M.mem scope D.omega) (h : BinaryBlock M C D strict scope n X Y B) {i a : M.Domain} (hAt : MemPair M B i a) :
    ScopedAtom M D a scope := by
  have hi := (h.graph.bounds hM.1 hAt).1
  obtain ⟨x,hx,hix⟩ := h.left.total i hi
  obtain ⟨y,hy,hiy⟩ := h.right.total i hi
  exact ((h.rows i hi x hx y hy hix hiy a).mp hAt).scoped_d hM hC hD hb

end KP1Y.ReflectionModel
