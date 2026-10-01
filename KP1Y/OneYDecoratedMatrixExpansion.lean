import KP1Y.OneYMatrixNormalization
import KP1Y.OneYOrdinaryCoordinates

/-! 独立Top值装饰的列后缀次序及完整矩阵展开保持。Top不是某个零行的伪装条目。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

/-- 后缀严格时不限制Top；只有所有后缀行相等才比较独立Top值。 -/
def DecoratedColumnLeFrom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A B : FiniteMatrix M.Domain)
    (c d start topC topD : M.Domain) : Prop :=
  ColumnLtFrom M C.omega C.zero A B c d start ∨
    (ColumnEqFrom M C.omega C.zero A B c d start ∧ (topC=topD ∨ M.mem topC topD))

/-- 实际Top读数随S见证一起给出，不用缺失读数令比较真空成立。 -/
def DecoratedRowBlocker (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (previous current start Top : M.Domain) : Prop :=
  ∀ c, M.mem c A.width → ∀ q, M.mem q A.width → ∀ p, M.mem p A.width →
    MemPair M previous c q → MemPair M current c p → p≠q →
      ∃ z, M.mem z A.width ∧ (z=q ∨ Ancestor M C A.width current z q) ∧ MemPair M current z p ∧
        ∃ topC, M.mem topC C.omega ∧ ∃ topZ, M.mem topZ C.omega ∧ MemPair M Top c topC ∧ MemPair M Top z topZ ∧
          DecoratedColumnLeFrom M C A A c z start topC topZ

def DecoratedMatrixBlockerAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (previous current start Top c : M.Domain) : Prop :=
  ∀ q, M.mem q A.width → ∀ p, M.mem p A.width → MemPair M previous c q → MemPair M current c p → p≠q →
    ∃ z, M.mem z A.width ∧ (z=q ∨ Ancestor M C A.width current z q) ∧ MemPair M current z p ∧
      ∃ topC, M.mem topC C.omega ∧ ∃ topZ, M.mem topZ C.omega ∧ MemPair M Top c topC ∧ MemPair M Top z topZ ∧
        DecoratedColumnLeFrom M C A A c z start topC topZ

def DecoratedAboveS (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (Forests Rows L base Top : M.Domain) : Prop :=
  ∀ r, M.mem r A.height → base=r ∨ M.mem base r → ∀ P, PreviousMatrixForest M C A.height Forests Rows L r P →
    ∀ Q, M.mem Q Forests → MemPair M Rows r Q → ∀ start, M.mem start C.omega → M.SuccessorOf start r →
      DecoratedRowBlocker M C A P Q start Top

theorem DecoratedColumnLeFrom.forget {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {A B : FiniteMatrix M.Domain}
    {c d start topC topD : M.Domain} (h : DecoratedColumnLeFrom M C A B c d start topC topD) : ColumnLeFrom M C.omega C.zero A B c d start := by
  rcases h with hLt | ⟨hEq,_⟩
  · exact Or.inr hLt
  · exact Or.inl hEq

theorem DecoratedRowBlocker.forget {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain}
    {previous current start Top : M.Domain} (h : DecoratedRowBlocker M C A previous current start Top) : RowBlocker M C A previous current start := by
  intro c hc q hq p hp hPrev hCur hNe
  obtain ⟨z,hz,hPath,hParent,_,_,_,_,_,_,hCompare⟩ := h c hc q hq p hp hPrev hCur hNe
  exact ⟨z,hz,hPath,hParent,hCompare.forget⟩

theorem DecoratedAboveS.forget {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain}
    {Forests Rows L base Top : M.Domain} (h : DecoratedAboveS M C A Forests Rows L base Top) : AboveS M C A Forests Rows L base :=
  fun r hr hBase P hPrev Q hQ hRow start hs hSucc => (h r hr hBase P hPrev Q hQ hRow start hs hSucc).forget

theorem decorated_column_refl {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega) (c start top : M.Domain) :
    DecoratedColumnLeFrom M C A A c c start top top :=
  Or.inr ⟨column_eq_from_refl he hA c start,Or.inl rfl⟩

theorem decorated_column_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain}
    (hA : A.Valid M C.omega) (hB : B.Valid M C.omega) (hD : D.Valid M C.omega)
    {a b d start topA topB topD : M.Domain} (hTopD : M.mem topD C.omega)
    (hAB : DecoratedColumnLeFrom M C A B a b start topA topB) (hBD : DecoratedColumnLeFrom M C B D b d start topB topD) :
    DecoratedColumnLeFrom M C A D a d start topA topD := by
  rcases hAB with hAB | ⟨hAB,hT⟩ <;> rcases hBD with hBD | ⟨hBD,hT'⟩
  · exact Or.inl (column_lt_from_trans_d hM hC hA hB hD hAB hBD)
  · exact Or.inl (column_lt_eq_from_d hM hC hB hD hAB hBD)
  · exact Or.inl (column_eq_lt_from_d hM hC hA hB hAB hBD)
  · refine Or.inr ⟨column_eq_from_trans_d hM hC hB hAB hBD,?_⟩
    rcases hT with he | hlt
    · exact he ▸ hT'
    · rcases hT' with he | hlt'
      · exact Or.inr (he ▸ hlt)
      · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hTopD).transitive topB hlt' topA hlt)


/-- 独立Top图沿普通[source0,block0]复制，不读取或改写任何矩阵行。 -/
def CopiedTopValue (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : CopyCoordinates.Context M.Domain) (Top c v : M.Domain) : Prop :=
  ∃ source, M.mem source C.omega ∧ ∃ copy, M.mem copy C.omega ∧
    OrdinaryCoordinates.Decoded M C T X c source copy ∧ MemPair M Top source v

def copiedTopValueFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (X : CopyCoordinates.Context (Project.Term n)) (Top c v : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
    (.conj (OrdinaryCoordinates.decodedFormula C.weaken.weaken T.weaken.weaken X.weaken.weaken c.weaken.weaken (.bound 1) (.bound 0))
      (memPairFormula Top.weaken.weaken (.bound 1) v.weaken.weaken)))

theorem copiedTopValueFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (X : CopyCoordinates.Context (Project.Term n)) (Top c v : Project.Term n) : (copiedTopValueFormula C T X Top c v).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (OrdinaryCoordinates.decodedFormula_delta0 _ _ _ _ _ _) (memPairFormula_delta0 _ _ _)))

theorem copiedTopValueFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T)
    {X : CopyCoordinates.Context (Project.Term n)} (hX : X.Closed) (Top c v : Project.Term n)
    (hTop : Top.freeSupport=[]) (hc : c.freeSupport=[]) (hv : v.freeSupport=[]) : (copiedTopValueFormula C T X Top c v).FreeClosed := by
  have hDec := OrdinaryCoordinates.decodedFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hX.weaken.weaken
    c.weaken.weaken (.bound 1) (.bound 0) (by simpa using hc) rfl rfl
  simp [copiedTopValueFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,hC.omega,hTop,hv,hDec]

theorem copiedTopValueFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (X : CopyCoordinates.Context (Project.Term n)) (Top c v : Project.Term n) :
    Project.Formula.satisfies e (copiedTopValueFormula C T X Top c v) ↔
      CopiedTopValue M (C.eval e) (T.eval e) (X.eval e) (Top.eval e) (c.eval e) (v.eval e) := by
  simp only [copiedTopValueFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    OrdinaryCoordinates.decodedFormula_iff he,memPairFormula_iff he,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,
    CopyCoordinates.Context.eval_weaken,Term.eval_weaken]
  rfl

structure CopiedTop (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : CopyCoordinates.Context M.Domain) (Top n NewTop : M.Domain) : Prop where
  graph : Graph M NewTop n C.omega
  rows : ∀ c v, MemPair M NewTop c v ↔ M.mem c n ∧ CopiedTopValue M C T X Top c v

private def copiedTopSchema : Project.Delta0BinarySchema 16 where
  body := copiedTopValueFormula ⟨.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩
    ⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ ⟨.bound 6,.bound 5,.bound 4,.bound 3⟩ (.bound 2) (.bound 1) (.bound 0)
  freeClosed := copiedTopValueFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ _ _ _ rfl rfl rfl
  delta0 := copiedTopValueFormula_delta0 _ _ _ _ _ _

theorem copied_top_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m n Top : M.Domain}
    (hm : M.mem m C.omega) (hn : M.mem n C.omega) (hTop : Graph M Top m C.omega) (hLast : M.mem X.last m) :
    ∃ NewTop, CopiedTop M C T X Top n NewTop := by
  let e := (((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push X.last).push X.root).push X.length).push X.first).push Top
  have hφ (c v : M.Domain) : Project.Formula.satisfies ((e.push c).push v) copiedTopSchema.body ↔ CopiedTopValue M C T X Top c v :=
    copiedTopValueFormula_iff hM.1 _ _ _ _ _ _ _
  obtain ⟨NewTop,hSupport,hRaw⟩ := relation_comprehension_d hM copiedTopSchema e n C.omega
  have hRows (c v : M.Domain) : MemPair M NewTop c v ↔ M.mem c n ∧ CopiedTopValue M C T X Top c v := by
    have hr := hRaw c v
    rw [hφ] at hr
    refine hr.trans ⟨fun h => ⟨h.1,h.2.2⟩,?_⟩
    rintro ⟨hc,hValue⟩
    have hv : M.mem v C.omega := by
      obtain ⟨_,_,_,_,_,hAt⟩ := hValue
      exact (hTop.bounds hM.1 hAt).2
    exact ⟨hc,hv,hValue⟩
  refine ⟨NewTop,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    have hw := omega_isOrdinal_d hM hC.omega
    obtain ⟨source,copy,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hX (hw.transitive n hn c hc)
    have hs := (hw.mem hm).transitive X.last hLast source (hDec.source_lt_last_d hM hC hT hX)
    obtain ⟨v,hv,hAt⟩ := hTop.total source hs
    exact ⟨v,hv,(hRows c v).mpr ⟨hc,source,hDec.2.1,copy,hDec.2.2.1,hDec,hAt⟩⟩
  · intro c v v' hAt hAt'
    obtain ⟨_,source,_,copy,_,hDec,hV⟩ := (hRows c v).mp hAt
    obtain ⟨_,source',_,copy',_,hDec',hV'⟩ := (hRows c v').mp hAt'
    have heq := (hDec.unique_d hM hC hT hX hDec').1
    subst source'
    exact hTop.unique source v v' hV hV'

theorem CopiedTop.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {T : MatrixArithmetic M.Domain} {X : CopyCoordinates.Context M.Domain} {Top n NewTop Other : M.Domain}
    (h : CopiedTop M C T X Top n NewTop) (h' : CopiedTop M C T X Top n Other) : NewTop=Other :=
  h.graph.ext he h'.graph (fun c _ v => (h.rows c v).trans (h'.rows c v).symm)

theorem CopiedTop.parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {Top n NewTop p copy c v : M.Domain}
    (h : CopiedTop M C T X Top n NewTop) (hp : M.mem p X.last) (hc : M.mem c n)
    (hCopy : CopyCoordinates.ParentCopy M C T X copy p c) : MemPair M NewTop c v ↔ MemPair M Top p v := by
  rw [h.rows c v]
  constructor
  · rintro ⟨_,source,_,block,_,hDec,hAt⟩
    have hsp := hDec.source_parent_copy_d hM hC hT hX hp hCopy
    exact hsp ▸ hAt
  · intro hAt
    obtain ⟨block,hDec⟩ := OrdinaryCoordinates.decoded_parent_copy_d hM hC hT hX hp hCopy
    exact ⟨hc,p,hDec.2.1,block,hDec.2.2.1,hDec,hAt⟩

theorem CopiedTop.prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {Top n NewTop c v : M.Domain}
    (h : CopiedTop M C T X Top n NewTop) (hc : M.mem c n) (hOld : M.mem c X.last) :
    MemPair M NewTop c v ↔ MemPair M Top c v := by
  rw [h.rows c v]
  constructor
  · rintro ⟨_,source,_,block,_,hDec,hAt⟩
    exact (hDec.original_d hM hC hT hX hOld).1 ▸ hAt
  · intro hAt
    have hDec := OrdinaryCoordinates.decoded_original_d hM hC hT hX hOld
    exact ⟨hc,c,hDec.2.1,C.zero,hC.zero_nat,hDec,hAt⟩


theorem decorated_column_congr {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {A B A' B' : FiniteMatrix M.Domain} {c d c' d' start topC topD : M.Domain}
    (hLeft : ∀ r v, PaddedEntry M C.zero A r c v ↔ PaddedEntry M C.zero A' r c' v)
    (hRight : ∀ r v, PaddedEntry M C.zero B r d v ↔ PaddedEntry M C.zero B' r d' v) :
    DecoratedColumnLeFrom M C A B c d start topC topD ↔ DecoratedColumnLeFrom M C A' B' c' d' start topC topD := by
  simp only [DecoratedColumnLeFrom,ColumnLtFrom,ColumnEqFrom,ColumnLtAt,ColumnEqAt,hLeft,hRight]

theorem decorated_column_eq_symm {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {A B : FiniteMatrix M.Domain} {c d start : M.Domain} (h : ColumnEqFrom M C.omega C.zero A B c d start) :
    ColumnEqFrom M C.omega C.zero B A d c start :=
  fun r hr hs x hx y hy hX hY => (h r hr hs y hy x hx hY hX).symm

theorem decorated_eq_transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain}
    (hA : A.Valid M C.omega) (hB : B.Valid M C.omega) (hD : D.Valid M C.omega)
    {source witness child target start topC topZ : M.Domain} (hTopZ : M.mem topZ C.omega)
    (hLeft : ColumnEqFrom M C.omega C.zero B A child source start) (hRight : ColumnEqFrom M C.omega C.zero D A target witness start)
    (hCompare : DecoratedColumnLeFrom M C A A source witness start topC topZ) :
    DecoratedColumnLeFrom M C B D child target start topC topZ :=
  decorated_column_trans_d hM hC hB hA hD hTopZ
    (decorated_column_trans_d hM hC hB hA hA hTopZ (Or.inr ⟨hLeft,Or.inl rfl⟩) hCompare)
    (Or.inr ⟨decorated_column_eq_symm hRight,Or.inl rfl⟩)

theorem column_lt_le_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain}
    (hA : A.Valid M C.omega) (hB : B.Valid M C.omega) (hD : D.Valid M C.omega)
    {a b d start : M.Domain} (hAB : ColumnLtFrom M C.omega C.zero A B a b start)
    (hBD : ColumnLeFrom M C.omega C.zero B D b d start) : ColumnLtFrom M C.omega C.zero A D a d start := by
  rcases hBD with hEq | hLt
  · exact column_lt_eq_from_d hM hC hB hD hAB hEq
  · exact column_lt_from_trans_d hM hC hA hB hD hAB hLt

/-- 承接既有lift的Eq/Lt两个强出口，保留Top只在Eq分支出现这一事实。 -/
theorem decorated_lift_realized_of_common_previous_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain}
    (hA : A.Valid M C.omega) (hB : B.Valid M C.omega) (hD : D.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {L c d start x y topC topD : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values U.forests U.rows L)
    (hc : M.mem c A.width) (hd : M.mem d A.width) (hRootC : M.mem U.root c) (hRootD : M.mem U.root d)
    (hLast : M.mem U.last A.width) (hRoot : M.mem U.root A.width) (hCopy : M.mem U.copy C.omega)
    (hPrevious : PreviousRowsEqual M C A.height U.forests U.rows L start c d)
    (hBH : B.height=A.height) (hDH : D.height=A.height) (hx : M.mem x B.width) (hy : M.mem y D.width)
    (hX : ∀ s v, MatrixEntry M B s x v ↔ LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy c s v)
    (hY : ∀ s v, MatrixEntry M D s y v ↔ LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy d s v)
    (hCompare : DecoratedColumnLeFrom M C A A c d start topC topD) : DecoratedColumnLeFrom M C B D x y start topC topD := by
  have xiff := padded_matrix_iff_lifted_d hM.1 hB hBH hx hX
  have yiff := padded_matrix_iff_lifted_d hM.1 hD hDH hy hY
  have convert (s : M.Domain) (hEq : LiftedColumnEqAt M C A T U c d s) : ColumnEqAt M C.omega C.zero B D x y s := by
    intro a ha b hb hA hB
    exact hEq a ha b hb ((xiff s a).mp hA) ((yiff s b).mp hB)
  rcases hCompare with hLt | ⟨hEq,hTop⟩
  · obtain ⟨s,hs,hStart,hEarlier,a,ha,b,hb,hAS,hBS,hab⟩ :=
      lifted_suffix_lt_of_common_previous_d hM hC hA hT hRun hc hd hRootC hRootD hLast hRoot hCopy hPrevious hLt
    exact Or.inl ⟨s,hs,hStart,fun q hq hsq => convert q (hEarlier q hq hsq),a,ha,b,hb,(xiff s a).mpr hAS,(yiff s b).mpr hBS,hab⟩
  · have hEq := lifted_suffix_eq_of_common_previous_d hM hC hA hT hRun hc hd hRootC hRootD hPrevious hEq
    exact Or.inr ⟨fun s hs hStart => convert s (hEq s hs hStart),hTop⟩

theorem decorated_lift_realized_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain}
    (hA : A.Valid M C.omega) (hB : B.Valid M C.omega) (hD : D.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {L P r c d start x y topC topD : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values U.forests U.rows L)
    (hc : M.mem c A.width) (hd : M.mem d A.width) (hRootC : M.mem U.root c) (hRootD : M.mem U.root d)
    (hLast : M.mem U.last A.width) (hRoot : M.mem U.root A.width) (hCopy : M.mem U.copy C.omega)
    (hP : MemPair M U.rows r P) (hSucc : M.SuccessorOf start r) (hSame : ParentRowsEqual M P c d)
    (hBH : B.height=A.height) (hDH : D.height=A.height) (hx : M.mem x B.width) (hy : M.mem y D.width)
    (hX : ∀ s v, MatrixEntry M B s x v ↔ LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy c s v)
    (hY : ∀ s v, MatrixEntry M D s y v ↔ LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy d s v)
    (hCompare : DecoratedColumnLeFrom M C A A c d start topC topD) : DecoratedColumnLeFrom M C B D x y start topC topD :=
  decorated_lift_realized_of_common_previous_d hM hC hA hB hD hT hRun hc hd hRootC hRootD hLast hRoot hCopy
    (previous_rows_equal_of_common_current_d hM hC hRun hP hSucc hSame) hBH hDH hx hy hX hY hCompare

/-- 矩阵、父图和独立Top共同在列前缀下运输。矩阵高度可不同，只要求padding语义相同。 -/
theorem decorated_row_blocker_transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hB : B.Valid M C.omega)
    {Prev Cur Prev' Cur' start Top NewTop : M.Domain} (hCur : Forest M C.omega A.width Cur)
    (hSub : M.MemberSubset B.width A.width) (hPrevRows : RowsAgreeOn M Prev Prev' B.width) (hCurRows : RowsAgreeOn M Cur Cur' B.width)
    (hPads : ∀ c, M.mem c B.width → ∀ r v, PaddedEntry M C.zero B r c v ↔ PaddedEntry M C.zero A r c v)
    (hTops : ∀ c, M.mem c B.width → ∀ v, MemPair M NewTop c v ↔ MemPair M Top c v)
    (hS : DecoratedRowBlocker M C A Prev Cur start Top) : DecoratedRowBlocker M C B Prev' Cur' start NewTop := by
  intro c hc q hq p hp hPrev hCurrent hNe
  have hOldPrev := (hPrevRows c hc q).mpr hPrev
  have hOldCur := (hCurRows c hc p).mpr hCurrent
  obtain ⟨z,_,hPath,hZp,topC,htc,topZ,htz,hTC,hTZ,hDecor⟩ := hS c (hSub c hc) q (hSub q hq) p (hSub p hp) hOldPrev hOldCur hNe
  have hz : M.mem z B.width := by
    rcases hPath with he | hAnc
    · exact he ▸ hq
    · exact ((omega_isOrdinal_d hM hC.omega).mem hB.width).transitive q hq z hAnc.1
  refine ⟨z,hz,?_,(hCurRows z hz p).mp hZp,topC,htc,topZ,htz,(hTops c hc topC).mpr hTC,(hTops z hz topZ).mpr hTZ,?_⟩
  · exact hPath.imp id ((ancestor_prefix_iff_d hM hC hCur hB.width hSub hq hCurRows).mp)
  · exact (decorated_column_congr (hPads c hc) (hPads z hz)).mpr hDecor


theorem decorated_blocker_at_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total F P QF Q child start Top NewTop : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega)
    (hF : Forest M C.omega A.width F) (hP : Forest M C.omega A.width P) (hQ : Forest M C.omega B.width Q)
    (hPrevRows : RowsAgreeOn M F QF X.last) (hCurRows : RowsAgreeOn M P Q X.last)
    (hTop : CopiedTop M C T X Top B.width NewTop) (hOldS : DecoratedRowBlocker M C A F P start Top)
    (hChild : M.mem child X.last) : DecoratedMatrixBlockerAt M C B QF Q start NewTop child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hSubA := (hw.mem hA.width).transitive X.last hLast
  have hSubB := hExp.prefix_width_d hM hC hIndex hX.below
  intro q _ p _ hPrev hCur hDistinct
  have hOldPrev := (hPrevRows child hChild q).mpr hPrev
  have hOldCur := (hCurRows child hChild p).mpr hCur
  obtain ⟨z,_,hPath,hZParent,topC,htc,topZ,htz,hTC,hTZ,hCompare⟩ := hOldS child (hSubA child hChild) q (hF.bounds hM.1 hOldPrev).2 p
    (hP.bounds hM.1 hOldCur).2 hOldPrev hOldCur hDistinct
  have hqLast := (hw.mem hX.last).transitive child hChild q (hF.left child q hOldPrev)
  have hzLast : M.mem z X.last := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hqLast
    · exact (hw.mem hX.last).transitive q hqLast z hAnc.1
  refine ⟨z,hSubB z hzLast,?_,(hCurRows z hzLast p).mp hZParent,topC,htc,topZ,htz,?_,?_,?_⟩
  · exact hPath.imp id ((ancestor_common_prefix_iff_d hM hC hP hQ hX.last hSubA hSubB hqLast hCurRows).mp)
  · exact (hTop.prefix_iff_d hM hC hT hX (hSubB child hChild) hChild).mpr hTC
  · exact (hTop.prefix_iff_d hM hC hT hX (hSubB z hzLast) hzLast).mpr hTZ
  · exact decorated_eq_transport_d hM hC hA hExp.matrix hExp.matrix htz
      (hExp.prefix_suffix_eq_d hM hC hA hT hLast hX.below hIndex hChild)
      (hExp.prefix_suffix_eq_d hM hC hA hT hLast hX.below hIndex hzLast) hCompare

theorem decorated_blocker_at_copy_bad_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF Q copy source child oldP start Top NewTop : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P)
    (hF : Forest M C.omega A.width F)
    (hCF : MatrixCopy.CopyForest M C T X F previous previousMax count B.width QF)
    (hCQ : MatrixCopy.CopyForest M C T X P r maximal count B.width Q)
    (hTop : CopiedTop M C T X Top B.width NewTop) (hOldS : DecoratedRowBlocker M C A F P start Top) (hs : M.SuccessorOf start r)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last)
    (hOldParent : MemPair M P source oldP) (hBad : X.root=oldP ∨ M.mem X.root oldP)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child) : DecoratedMatrixBlockerAt M C B QF Q start NewTop child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hPF := hRun.forests r P hP
  have hSourceWidth := (hw.mem hA.width).transitive X.last hLast source hSource
  have hRootWidth := (hw.mem hA.width).transitive X.last hLast X.root hX.below
  have hSourceRoot : M.mem X.root source := by
    rcases hBad with he | hlt
    · exact he.symm ▸ hPF.left source oldP hOldParent
    · exact (hw.mem (hw.transitive A.width hA.width source hSourceWidth)).transitive oldP (hPF.left source oldP hOldParent) X.root hlt
  have hNonroot : source≠X.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hSourceRoot)
  intro q _ p _ hNewPrev hNewCur hDistinct
  obtain ⟨oldQ,hOldQLast,hOldPrev,hMapQ⟩ := (hCF.source_parent_nonroot_d hM hC hT hX hF hCF.count_nat hCopy hSource hNonroot hMap q).mp hNewPrev
  obtain ⟨p',_,hOldP',hMapP⟩ := (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hCopy hSource hNonroot hMap p).mp hNewCur
  have hParentsEq := hPF.unique source p' oldP hOldP' hOldParent
  subst p'
  obtain ⟨J,hJ,hJRows⟩ := hCQ.copy_embedding_d hM hC hT hX hCopy
  have hOldPLast := (hw.mem hX.last).transitive source hSource oldP (hPF.left source oldP hOldParent)
  have hJP := (hJRows oldP p).mpr ⟨hOldPLast,hMapP⟩
  have hJQ := (hJRows oldQ q).mpr ⟨hOldQLast,hMapQ⟩
  have hOldDistinct : oldP≠oldQ := by
    intro he
    subst oldQ
    exact hDistinct (hJ.graph.unique oldP p q hJP hJQ)
  obtain ⟨z,hzWidth,hPath,hZParent,topC,htc,topZ,htz,hTC,hTZ,hCompare⟩ := hOldS source hSourceWidth oldQ (hF.bounds hM.1 hOldPrev).2 oldP
    (hPF.bounds hM.1 hOldParent).2 hOldPrev hOldParent hOldDistinct
  have hzSource : M.mem z source := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hF.left source oldQ hOldPrev
    · exact (hw.mem (hw.transitive A.width hA.width source hSourceWidth)).transitive oldQ (hF.left source oldQ hOldPrev) z hAnc.1
  have hzLast := (hw.mem hX.last).transitive source hSource z hzSource
  have hRootZ : M.mem X.root z := by
    rcases hBad with he | hlt
    · exact he.symm ▸ hPF.left z oldP hZParent
    · exact (hw.mem (hw.transitive A.width hA.width z hzWidth)).transitive oldP (hPF.left z oldP hZParent) X.root hlt
  have hzNonroot : z≠X.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hRootZ)
  obtain ⟨w,hwWidth,hJW⟩ := hJ.graph.total z hzLast
  have hMapZ := ((hJRows z w).mp hJW).2
  refine ⟨w,hwWidth,?_,?_,topC,htc,topZ,htz,?_,?_,?_⟩
  · rcases hPath with he | hAnc
    · subst z
      exact Or.inl (hJ.graph.unique oldQ w q hJW hJQ)
    · exact Or.inr ((hCQ.ancestor_bad_iff_d hM hC hT hX hPF hLast hCopy (Or.inr hRootZ) hzLast hOldQLast hMapZ hMapQ).mpr hAnc)
  · exact (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hCopy hzLast hzNonroot hMapZ p).mpr
      ⟨oldP,hOldPLast,hZParent,hMapP⟩
  · exact (hTop.parent_copy_iff_d hM hC hT hX hSource
      (hCQ.copy_value_bound_d hM hC hT hX hCopy hSource hMap) hMap).mpr hTC
  · exact (hTop.parent_copy_iff_d hM hC hT hX hzLast hwWidth hMapZ).mpr hTZ
  · have hSame : ParentRowsEqual M P source z := by
      intro t
      constructor
      · intro ht
        have he := hPF.unique source t oldP ht hOldParent
        exact he.symm ▸ hZParent
      · intro ht
        have he := hPF.unique z t oldP ht hZParent
        exact he.symm ▸ hOldParent
    exact decorated_lift_realized_d hM hC hA hExp.matrix hExp.matrix hT (U := ⟨Forests,Rows,X.last,maximal,X.root,copy⟩) hRun
      hSourceWidth hzWidth hSourceRoot hRootZ hLast hRootWidth hMap.2.1 hP hs hSame hExp.height hExp.height
      (hCQ.copy_value_bound_d hM hC hT hX hCopy hSource hMap) hwWidth
      (fun s v => hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hSource hMap)
      (fun s v => hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hzLast hMapZ) hCompare

theorem decorated_blocker_at_copy_good_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF Q copy source child oldP start Top NewTop : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P)
    (hF : Forest M C.omega A.width F)
    (hCF : MatrixCopy.CopyForest M C T X F previous previousMax count B.width QF)
    (hCQ : MatrixCopy.CopyForest M C T X P r maximal count B.width Q)
    (hTop : CopiedTop M C T X Top B.width NewTop) (hOldS : DecoratedRowBlocker M C A F P start Top) (hs : M.SuccessorOf start r) (hLow : M.mem r maximal)
    (hRootLast : Ancestor M C A.width P X.root X.last)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hNonroot : source≠X.root)
    (hOldParent : MemPair M P source oldP) (hGood : M.mem oldP X.root)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child) : DecoratedMatrixBlockerAt M C B QF Q start NewTop child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hPF := hRun.forests r P hP
  have hSourceWidth := (hw.mem hA.width).transitive X.last hLast source hSource
  intro q _ p _ hNewPrev hNewCur hDistinct
  obtain ⟨oldQ,hOldQLast,hOldPrev,hMapQ⟩ := (hCF.source_parent_nonroot_d hM hC hT hX hF hCF.count_nat hCopy hSource hNonroot hMap q).mp hNewPrev
  obtain ⟨p',_,hOldP',hMapP⟩ := (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hCopy hSource hNonroot hMap p).mp hNewCur
  have hParentsEq := hPF.unique source p' oldP hOldP' hOldParent
  subst p'
  have hTargetOld := (CopyCoordinates.parent_copy_good_iff hMapP.2.1 hMapP.1 hGood).mp hMapP
  subst p
  obtain ⟨J,hJ,hJRows⟩ := hCQ.copy_embedding_d hM hC hT hX hCopy
  have hOldPLast := (hw.mem hX.last).transitive source hSource oldP (hPF.left source oldP hOldParent)
  have hJP := (hJRows oldP oldP).mpr ⟨hOldPLast,hMapP⟩
  have hJQ := (hJRows oldQ q).mpr ⟨hOldQLast,hMapQ⟩
  have hOldDistinct : oldP≠oldQ := by
    intro he
    subst oldQ
    exact hDistinct (hJ.graph.unique oldP oldP q hJP hJQ)
  obtain ⟨z,_,hPath,hZParent,topC,htc,topZ,htz,hTC,hTZ,hCompareOld⟩ := hOldS source hSourceWidth oldQ (hF.bounds hM.1 hOldPrev).2 oldP
    (hPF.bounds hM.1 hOldParent).2 hOldPrev hOldParent hOldDistinct
  have hzSource : M.mem z source := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hF.left source oldQ hOldPrev
    · exact (hw.mem (hw.transitive A.width hA.width source hSourceWidth)).transitive oldQ (hF.left source oldQ hOldPrev) z hAnc.1
  have hzLast := (hw.mem hX.last).transitive source hSource z hzSource
  have hLeft := hExp.parent_copy_suffix_good_parent_d hM hC hA hT hX hRun hLast hIndex hCopy hSource
    (hCQ.copy_value_bound_d hM hC hT hX hCopy hSource hMap) hNonroot hMap hP hOldParent hGood hs
  have hNewTC := (hTop.parent_copy_iff_d hM hC hT hX hSource
    (hCQ.copy_value_bound_d hM hC hT hX hCopy hSource hMap) hMap).mpr hTC
  have hCompare (w : M.Domain) (hRight : ColumnEqFrom M C.omega C.zero B A w z start) :
      DecoratedColumnLeFrom M C B B child w start topC topZ :=
    decorated_eq_transport_d hM hC hA hExp.matrix hExp.matrix htz hLeft hRight hCompareOld
  classical
  by_cases hzRoot : z=X.root
  · subst z
    have hZeroCount : M.mem C.zero count := (hC.zero_mem_iff hM hCQ.count_nat).mpr
      (fun he => hC.zero_empty index (he ▸ hExp.copies.predecessor_mem))
    have hPrefix := hCQ.parent_prefix_d hM hC hT hX hPF hCQ.count_nat hZeroCount
    exact ⟨X.root,hExp.prefix_width_d hM hC hIndex hX.below X.root hX.below,
      hCQ.zero_root_path_copy_d hM hC hT hX hPF hLast hLow hRootLast hCopy hOldQLast hMapQ hPath,
      (hPrefix X.root hX.below oldP).mp hZParent,
      topC,htc,topZ,htz,hNewTC,
      (hTop.prefix_iff_d hM hC hT hX (hExp.prefix_width_d hM hC hIndex hX.below X.root hX.below) hX.below).mpr hTZ,
      hCompare X.root (hExp.prefix_suffix_eq_d hM hC hA hT hLast hX.below hIndex hX.below)⟩
  · obtain ⟨w,hwWidth,hJW⟩ := hJ.graph.total z hzLast
    have hMapZ := ((hJRows z w).mp hJW).2
    refine ⟨w,hwWidth,?_,?_,topC,htc,topZ,htz,hNewTC,?_,?_⟩
    · rcases hPath with he | hAnc
      · subst z
        exact Or.inl (hJ.graph.unique oldQ w q hJW hJQ)
      · exact Or.inr ((hCQ.ancestor_copy_iff_d hM hC hT hX hPF hLast hCopy (fun _ => hRootLast) hzLast hOldQLast hMapZ hMapQ).mpr hAnc)
    · exact (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hCopy hzLast hzRoot hMapZ oldP).mpr
        ⟨oldP,hOldPLast,hZParent,hMapP⟩
    · exact (hTop.parent_copy_iff_d hM hC hT hX hzLast hwWidth hMapZ).mpr hTZ
    · exact hCompare w (hExp.parent_copy_suffix_good_parent_d hM hC hA hT hX hRun hLast hIndex hCopy hzLast hwWidth hzRoot
        hMapZ hP hZParent hGood hs)

theorem decorated_blocker_at_copy_high_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P QF Q copy source child start Top NewTop : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P) (hF : Forest M C.omega A.width F)
    (hCQ : MatrixCopy.CopyForest M C T X P r maximal count B.width Q)
    (hTop : CopiedTop M C T X Top B.width NewTop) (hOldS : DecoratedRowBlocker M C A F P start Top) (hHigh : ¬M.mem r maximal) (hStart : maximal=start ∨ M.mem maximal start)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child)
    (hPrevRows : ∀ q, MemPair M QF child q ↔ ∃ oldQ, M.mem oldQ X.last ∧ MemPair M F source oldQ ∧ CopyCoordinates.ParentCopy M C T X copy oldQ q) :
    DecoratedMatrixBlockerAt M C B QF Q start NewTop child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hPF := hRun.forests r P hP
  have hSourceWidth := (hw.mem hA.width).transitive X.last hLast source hSource
  intro q _ p _ hPrev hCur hDistinct
  obtain ⟨oldQ,hOldQLast,hOldPrev,hMapQ⟩ := (hPrevRows q).mp hPrev
  obtain ⟨oldP,hOldPLast,hOldParent,hMapP⟩ := (hCQ.source_parent_high_d hM hC hT hX hPF hCQ.count_nat hCopy hSource hHigh hMap p).mp hCur
  obtain ⟨J,hJ,hRows⟩ := hCQ.copy_embedding_d hM hC hT hX hCopy
  have hJP := (hRows oldP p).mpr ⟨hOldPLast,hMapP⟩
  have hJQ := (hRows oldQ q).mpr ⟨hOldQLast,hMapQ⟩
  have hOldDistinct : oldP≠oldQ := by
    intro he
    subst oldQ
    exact hDistinct (hJ.graph.unique oldP p q hJP hJQ)
  obtain ⟨z,_,hPath,hZParent,topC,htc,topZ,htz,hTC,hTZ,hCompare⟩ := hOldS source hSourceWidth oldQ (hF.bounds hM.1 hOldPrev).2 oldP
    (hPF.bounds hM.1 hOldParent).2 hOldPrev hOldParent hOldDistinct
  have hzSource : M.mem z source := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hF.left source oldQ hOldPrev
    · exact (hw.mem (hw.transitive A.width hA.width source hSourceWidth)).transitive oldQ (hF.left source oldQ hOldPrev) z hAnc.1
  have hzLast := (hw.mem hX.last).transitive source hSource z hzSource
  obtain ⟨w,hwWidth,hJW⟩ := hJ.graph.total z hzLast
  have hMapZ := ((hRows z w).mp hJW).2
  refine ⟨w,hwWidth,?_,?_,topC,htc,topZ,htz,?_,?_,?_⟩
  · rcases hPath with he | hAnc
    · subst z
      exact Or.inl (hJ.graph.unique oldQ w q hJW hJQ)
    · exact Or.inr ((hCQ.ancestor_high_iff_d hM hC hT hX hPF hLast hCopy hHigh hzLast hOldQLast hMapZ hMapQ).mpr hAnc)
  · exact (hCQ.source_parent_high_d hM hC hT hX hPF hCQ.count_nat hCopy hzLast hHigh hMapZ p).mpr
      ⟨oldP,hOldPLast,hZParent,hMapP⟩
  · exact (hTop.parent_copy_iff_d hM hC hT hX hSource
      (hCQ.copy_value_bound_d hM hC hT hX hCopy hSource hMap) hMap).mpr hTC
  · exact (hTop.parent_copy_iff_d hM hC hT hX hzLast hwWidth hMapZ).mpr hTZ
  · have hLeft := hExp.parent_copy_suffix_high_d hM hC hA hT hX hLast hIndex hCopy hSource
      (hCQ.copy_value_bound_d hM hC hT hX hCopy hSource hMap) hMap hStart
    have hRight := hExp.parent_copy_suffix_high_d hM hC hA hT hX hLast hIndex hCopy hzLast hwWidth hMapZ hStart
    exact decorated_eq_transport_d hM hC hA hExp.matrix hExp.matrix htz hLeft hRight hCompare

theorem decorated_blocker_at_critical_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total F P previous previousMax QF Q prev next child start Top NewTop : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega) (hP : MemPair M Rows maximal P) (hF : Forest M C.omega A.width F)
    (hCF : MatrixCopy.CopyForest M C T X F previous previousMax count B.width QF)
    (hCQ : MatrixCopy.CopyForest M C T X P maximal maximal count B.width Q)
    (hPreviousLow : M.mem previous previousMax) (hOldTop : Graph M Top A.width C.omega) (hTop : CopiedTop M C T X Top B.width NewTop) (hOldS : DecoratedRowBlocker M C A F P start Top)
    (hStart : M.SuccessorOf start maximal) (hPrev : M.mem prev C.omega) (hs : M.SuccessorOf next prev)
    (hNext : M.mem next count) (hRootMap : CopyCoordinates.ParentCopy M C T X next X.root child) :
    DecoratedMatrixBlockerAt M C B QF Q start NewTop child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hPF := hRun.forests maximal P hP
  have hHigh : ¬M.mem maximal maximal := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) maximal
  obtain ⟨P',_,hP',hLastParent⟩ := hContext.parent
  have hPEq := hRun.graph.unique maximal P' P hP' hP
  subst P'
  have hPrevCount := (hw.mem hCQ.count_nat).transitive next hNext prev hs.predecessor_mem
  have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM X.root hC.zero_empty)
  have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hRootMap
  have hRootPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hRootMap.2.1 hRootZero).mp hEncode
  intro q _ p _ hPrevAt hCurAt _
  obtain ⟨oldQ,hOldQLast,hOldQ,hMapQ⟩ := (hCF.root_low_parent_iff_d hM hC hT hX hCF.count_nat hNext hPrev hs hPreviousLow hRootPos q).mp hPrevAt
  have hRootP := (hCQ.root_high_parent_iff_d hM hC hT hX hCQ.count_nat hNext (Or.inr hHigh) hRootPos p).mp hCurAt
  have hRootPath : X.root=oldQ ∨ Ancestor M C A.width P X.root oldQ := by
    classical
    by_cases he : X.root=oldQ
    · exact Or.inl he
    · obtain ⟨z,_,hPath,hZParent,_⟩ := hOldS X.last hLast oldQ (hF.bounds hM.1 hOldQ).2 X.root
        (hPF.bounds hM.1 hLastParent).2 hOldQ hLastParent he
      have hRootZ := ancestor_direct_d hM hC hPF hZParent
      rcases hPath with he | hPath
      · exact Or.inr (he ▸ hRootZ)
      · exact Or.inr (ancestor_trans_d hM hC hPF hRootZ hPath)
  obtain ⟨J,hJ,hRows⟩ := hCQ.copy_embedding_d hM hC hT hX hPrevCount
  obtain ⟨w,hwWidth,hJRoot⟩ := hJ.graph.total X.root hX.below
  have hPrevRootMap := ((hRows X.root w).mp hJRoot).2
  have hJQ := (hRows oldQ q).mpr ⟨hOldQLast,hMapQ⟩
  obtain ⟨top,ht,hRootTop⟩ := hOldTop.total X.root (hPF.bounds hM.1 hLastParent).2
  refine ⟨w,hwWidth,?_,?_,top,ht,top,ht,?_,?_,?_⟩
  · rcases hRootPath with he | hPath
    · subst oldQ
      exact Or.inl (hJ.graph.unique X.root w q hJRoot hJQ)
    · exact Or.inr ((hCQ.ancestor_high_iff_d hM hC hT hX hPF hLast hPrevCount hHigh hX.below hOldQLast hPrevRootMap hMapQ).mpr hPath)
  · have hPrevEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hPrevRootMap
    have hPrevPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hPrev hRootZero).mp hPrevEncode
    exact (hCQ.root_high_parent_iff_d hM hC hT hX hCQ.count_nat hPrevCount (Or.inr hHigh) hPrevPos p).mpr hRootP
  · exact (hTop.parent_copy_iff_d hM hC hT hX hX.below
      (hCQ.copy_value_bound_d hM hC hT hX hNext hX.below hRootMap) hRootMap).mpr hRootTop
  · exact (hTop.parent_copy_iff_d hM hC hT hX hX.below hwWidth hPrevRootMap).mpr hRootTop
  · have hLeft := hExp.parent_copy_suffix_high_d hM hC hA hT hX hLast hIndex hNext hX.below
      (hCQ.copy_value_bound_d hM hC hT hX hNext hX.below hRootMap) hRootMap (Or.inr hStart.predecessor_mem)
    have hRight := hExp.parent_copy_suffix_high_d hM hC hA hT hX hLast hIndex hPrevCount hX.below hwWidth hPrevRootMap (Or.inr hStart.predecessor_mem)
    exact Or.inr ⟨column_eq_from_trans_d hM hC hA hLeft (decorated_column_eq_symm hRight),Or.inl rfl⟩

theorem decorated_blocker_at_low_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF Q prev next child start Top NewTop : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P) (hF : Forest M C.omega A.width F)
    (hCF : MatrixCopy.CopyForest M C T X F previous previousMax count B.width QF)
    (hCQ : MatrixCopy.CopyForest M C T X P r maximal count B.width Q)
    (hPreviousLow : M.mem previous previousMax) (hLow : M.mem r maximal) (hTop : CopiedTop M C T X Top B.width NewTop) (hOldS : DecoratedRowBlocker M C A F P start Top)
    (hStart : M.SuccessorOf start r) (hPrev : M.mem prev C.omega) (hs : M.SuccessorOf next prev)
    (hNext : M.mem next count) (hRootMap : CopyCoordinates.ParentCopy M C T X next X.root child) :
    DecoratedMatrixBlockerAt M C B QF Q start NewTop child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hRootWidth := (hw.mem hA.width).transitive X.last hLast X.root hX.below
  have hPF := hRun.forests r P hP
  have hRootLast : Ancestor M C A.width P X.root X.last := by
    obtain ⟨_,he | ⟨P',_,hP',hAnc⟩⟩ := hContext.last_ascending_below_d hM hC hRun hLow
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hX.below))
    · exact hRun.graph.unique r P' P hP' hP ▸ hAnc
  have hPrevCount := (hw.mem hCQ.count_nat).transitive next hNext prev hs.predecessor_mem
  have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM X.root hC.zero_empty)
  have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hRootMap
  have hRootPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hRootMap.2.1 hRootZero).mp hEncode
  intro q _ p _ hPrevAt hCurAt hDistinct
  obtain ⟨oldQ,hOldQLast,hOldPrev,hMapQ⟩ := (hCF.root_low_parent_iff_d hM hC hT hX hCF.count_nat hNext hPrev hs hPreviousLow hRootPos q).mp hPrevAt
  obtain ⟨oldP,hOldPLast,hOldParent,hMapP⟩ := (hCQ.root_low_parent_iff_d hM hC hT hX hCQ.count_nat hNext hPrev hs hLow hRootPos p).mp hCurAt
  obtain ⟨J,hJ,hRows⟩ := hCQ.copy_embedding_d hM hC hT hX hPrevCount
  have hJP := (hRows oldP p).mpr ⟨hOldPLast,hMapP⟩
  have hJQ := (hRows oldQ q).mpr ⟨hOldQLast,hMapQ⟩
  have hOldDistinct : oldP≠oldQ := by
    intro he
    subst oldQ
    exact hDistinct (hJ.graph.unique oldP p q hJP hJQ)
  obtain ⟨z,hzWidth,hPath,hZParent,hLe⟩ := hOldS.forget X.last hLast oldQ (hF.bounds hM.1 hOldPrev).2 oldP
    (hPF.bounds hM.1 hOldParent).2 hOldPrev hOldParent hOldDistinct
  have hzLast : M.mem z X.last := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hOldQLast
    · exact (hw.mem hX.last).transitive oldQ hOldQLast z hAnc.1
  have hBad := ancestor_le_parent_d hM hC hPF hOldParent hRootLast
  have hRootZ : M.mem X.root z := by
    rcases hBad with he | hlt
    · exact he.symm ▸ hPF.left z oldP hZParent
    · exact (hw.mem (hw.transitive A.width hA.width z hzWidth)).transitive oldP (hPF.left z oldP hZParent) X.root hlt
  have hzNonroot : z≠X.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hRootZ)
  obtain ⟨w,hwWidth,hJW⟩ := hJ.graph.total z hzLast
  have hMapZ := ((hRows z w).mp hJW).2
  obtain ⟨topC,htc,hTC⟩ := hTop.graph.total child (hCQ.copy_value_bound_d hM hC hT hX hNext hX.below hRootMap)
  obtain ⟨topZ,htz,hTZ⟩ := hTop.graph.total w hwWidth
  refine ⟨w,hwWidth,?_,?_,topC,htc,topZ,htz,hTC,hTZ,?_⟩
  · rcases hPath with he | hAnc
    · subst z
      exact Or.inl (hJ.graph.unique oldQ w q hJW hJQ)
    · exact Or.inr ((hCQ.ancestor_bad_iff_d hM hC hT hX hPF hLast hPrevCount (Or.inr hRootZ) hzLast hOldQLast hMapZ hMapQ).mpr hAnc)
  · exact (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hPrevCount hzLast hzNonroot hMapZ p).mpr
      ⟨oldP,hOldPLast,hZParent,hMapP⟩
  · have hSame : ParentRowsEqual M P X.last z := by
      intro t
      constructor
      · intro ht
        exact (hPF.unique X.last t oldP ht hOldParent).symm ▸ hZParent
      · intro ht
        exact (hPF.unique z t oldP ht hZParent).symm ▸ hOldParent
    let U : MatrixLiftParameters M.Domain := ⟨Forests,Rows,X.last,maximal,X.root,prev⟩
    have hLift := lifted_suffix_le_of_common_parent_d hM hC hA hT (U := U) hRun hLast hzWidth hX.below hRootZ
      hLast hRootWidth hPrev hP hStart hSame hLe
    obtain ⟨G,hG⟩ := ghost_column_exists_d hM hC hA hT (U := U) hLast hRootWidth hPrev
    have hNextBound : next=index ∨ M.mem next index := by
      rcases (hExp.copies next).mp hNext with hlt | he
      · exact Or.inr hlt
      · exact Or.inl (hM.1.eq_of_same_members next index he)
    have hLeft := newroot_suffix_lt_ghost_d hM hC hA hT hRun hContext hExp hIndex hPrev hs hNextBound hRootPos hG hLow hStart
    have hRight := lifted_suffix_le_realized_d hM.1 hG.matrix hExp.matrix hG.height hExp.height
      (hG.column_bound hC) hwWidth hG.entries (fun s v => hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hPrevCount hzLast hMapZ) hLift
    exact Or.inl (column_lt_le_trans_d hM hC hExp.matrix hG.matrix hExp.matrix hLeft hRight)

theorem decorated_row_blocker_expand_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF Q start Top NewTop : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P) (hF : Forest M C.omega A.width F)
    (hCF : MatrixCopy.CopyForest M C T X F previous previousMax count B.width QF)
    (hCQ : MatrixCopy.CopyForest M C T X P r maximal count B.width Q)
    (hPreviousAbove : M.mem maximal r → ¬M.mem previous previousMax)
    (hPreviousBelow : r=maximal ∨ M.mem r maximal → M.mem previous previousMax)
    (hOldTop : Graph M Top A.width C.omega) (hTop : CopiedTop M C T X Top B.width NewTop)
    (hOldS : DecoratedRowBlocker M C A F P start Top) (hStart : M.SuccessorOf start r) : DecoratedRowBlocker M C B QF Q start NewTop := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hPF := hRun.forests r P hP
  have hrNat := hw.transitive A.height hA.height r (hRun.graph.bounds hM.1 hP).1
  have hMaxNat := hw.transitive A.height hA.height maximal hContext.row
  have hStartNat := natural_successor_mem_d hM hC hrNat hStart
  have hStartAbove (hHigh : ¬M.mem r maximal) : maximal=start ∨ M.mem maximal start := by
    apply Or.inr
    rcases hw.wellOrder.linear.compare r hrNat maximal hMaxNat with he | hlt | hgt
    · exact hM.1.eq_of_same_members r maximal he ▸ hStart.predecessor_mem
    · exact False.elim (hHigh hlt)
    · exact (hw.mem hStartNat).transitive r hStart.predecessor_mem maximal hgt
  have hRootLastBelow (hLow : M.mem r maximal) : Ancestor M C A.width P X.root X.last := by
    obtain ⟨_,he | ⟨P',_,hP',hAnc⟩⟩ := hContext.last_ascending_below_d hM hC hRun hLow
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hX.below))
    · exact hRun.graph.unique r P' P hP' hP ▸ hAnc
  have hZeroCount : M.mem C.zero count := (hC.zero_mem_iff hM hCQ.count_nat).mpr
    (fun he => hC.zero_empty index (he ▸ hExp.copies.predecessor_mem))
  have hPrevPrefix := hCF.parent_prefix_d hM hC hT hX hF hCF.count_nat hZeroCount
  have hCurPrefix := hCQ.parent_prefix_d hM hC hT hX hPF hCQ.count_nat hZeroCount
  intro child hChild
  change DecoratedMatrixBlockerAt M C B QF Q start NewTop child
  classical
  by_cases hPrefix : M.mem child X.last
  · exact decorated_blocker_at_prefix_d hM hC hA hT hX hExp hLast hIndex hF hPF hCQ.forest hPrevPrefix hCurPrefix hTop hOldS hPrefix
  · rcases hCQ.column_cases_d hM hC hT hX hChild with hGood | ⟨copy,hCopy,slot,hSlot,source,hSource,hAdd,hPos⟩
    · exact False.elim (hPrefix ((hw.mem hX.last).transitive X.root hX.below child hGood))
    · have hCopyNat := hw.transitive count hCQ.count_nat copy hCopy
      have hSlotNat := hw.transitive X.length (hX.length_nat hM.1) slot hSlot
      have hSourceNat := hw.transitive X.last hX.last source hSource
      have hAfter := ordinal_subset_cases_d hM (hw.mem hX.root) (hw.mem hSourceNat)
        (KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hX.root) ((hT.add.add_iff_sum hM hX.root hSlotNat).mp hAdd))
      have hNotGood : ¬M.mem source X.root := by
        intro hGood
        rcases hAfter with he | hlt
        · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he.symm ▸ hGood)
        · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root ((hw.mem hX.root).transitive source hGood X.root hlt)
      have hMap := (CopyCoordinates.parent_copy_bad_iff hNotGood).mpr
        ((CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hSlotNat hCopyNat hAdd).mpr hPos)
      by_cases hNonroot : source≠X.root
      · by_cases hLow : M.mem r maximal
        · intro q hq p hp hPrevAt hCurAt hDistinct
          obtain ⟨oldP,_,hOldParent,_⟩ := (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hCopy hSource hNonroot hMap p).mp hCurAt
          by_cases hGood : M.mem oldP X.root
          · exact decorated_blocker_at_copy_good_parent_d hM hC hA hT hX hRun hExp hLast hIndex hP hF hCF hCQ hTop hOldS hStart hLow (hRootLastBelow hLow)
              hCopy hSource hNonroot hOldParent hGood hMap q hq p hp hPrevAt hCurAt hDistinct
          · have hpNat := hw.transitive A.width hA.width oldP (hPF.bounds hM.1 hOldParent).2
            have hBad : X.root=oldP ∨ M.mem X.root oldP := by
              rcases hw.wellOrder.linear.compare X.root hX.root oldP hpNat with he | hlt | hgt
              · exact Or.inl (hM.1.eq_of_same_members X.root oldP he)
              · exact Or.inr hlt
              · exact False.elim (hGood hgt)
            exact decorated_blocker_at_copy_bad_parent_d hM hC hA hT hX hRun hExp hLast hIndex hP hF hCF hCQ hTop hOldS hStart
              hCopy hSource hOldParent hBad hMap q hq p hp hPrevAt hCurAt hDistinct
        · exact decorated_blocker_at_copy_high_d hM hC hA hT hX hRun hExp hLast hIndex hP hF hCQ hTop hOldS hLow (hStartAbove hLow)
            hCopy hSource hMap (hCF.source_parent_nonroot_d hM hC hT hX hF hCF.count_nat hCopy hSource hNonroot hMap)
      · have hSourceRoot : source=X.root := Classical.byContradiction hNonroot
        subst source
        have hCopyNonzero : copy≠C.zero := by
          intro he
          subst copy
          obtain ⟨J,hJ,hRows⟩ := hCQ.copy_embedding_d hM hC hT hX hCopy
          have hEq := hJ.graph.unique X.root child X.root ((hRows X.root child).mpr ⟨hX.below,hMap⟩)
            ((hRows X.root X.root).mpr ⟨hX.below,CopyCoordinates.parent_copy_zero_d hM hC hT hX hX.root⟩)
          exact hPrefix (hEq.symm ▸ hX.below)
        obtain ⟨prev,hPrev,hs⟩ : ∃ prev, M.mem prev C.omega ∧ M.SuccessorOf copy prev := by
          rcases natural_cases hM hC.omega hCopyNat with he | hSucc
          · exact False.elim (hCopyNonzero (hM.1.eq_of_same_members copy C.zero (fun t => iff_of_false (he t) (hC.zero_empty t))))
          · exact hSucc
        by_cases hLow : M.mem r maximal
        · exact decorated_blocker_at_low_root_d hM hC hA hT hX hRun hContext hExp hIndex hP hF hCF hCQ (hPreviousBelow (Or.inr hLow))
            hLow hTop hOldS hStart hPrev hs hCopy hMap
        · by_cases he : r=maximal
          · subst r
            exact decorated_blocker_at_critical_root_d hM hC hA hT hX hRun hContext hExp hIndex hP hF hCF hCQ
              (hPreviousBelow (Or.inl rfl)) hOldTop hTop hOldS hStart hPrev hs hCopy hMap
          · have hAbove : M.mem maximal r := by
              rcases hw.wellOrder.linear.compare r hrNat maximal hMaxNat with he' | hlt | hgt
              · exact False.elim (he (hM.1.eq_of_same_members r maximal he'))
              · exact False.elim (hLow hlt)
              · exact hgt
            exact decorated_blocker_at_copy_high_d hM hC hA hT hX hRun hExp hLast hIndex hP hF hCQ hTop hOldS hLow (hStartAbove hLow)
              hCopy hX.below hMap (hCF.source_parent_high_d hM hC hT hX hF hCF.count_nat hCopy hX.below (hPreviousAbove hAbove) hMap)

theorem RawMatrixExpansion.decorated_aboveS_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L OtherForests Other OtherL maximal index count total base Top NewTop : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hIndex : M.mem index C.omega) (hOldTop : Graph M Top A.width C.omega)
    (hTop : CopiedTop M C T X Top B.width NewTop) (hS : DecoratedAboveS M C A Forests Rows L base Top) :
    DecoratedAboveS M C B OtherForests Other OtherL base NewTop := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hCountNat := natural_successor_mem_d hM hC hIndex hExp.copies
  have hMaxNat := hw.transitive A.height hA.height maximal hContext.row
  intro r hrB hBase QF hPrevious Q _ hQ start hStartNat hStart
  have hr : M.mem r A.height := hExp.height ▸ hrB
  obtain ⟨P,hPMem,hP⟩ := hRun.graph.total r hr
  have hCQ := hExp.parent_copy_rows_d hM hC hA hT hX hRun hContext hOther hIndex r P Q hP hQ
  rcases hPrevious with ⟨hrZero,hQF⟩ | ⟨j,hj,hs,_,hJQF⟩
  · subst r
    subst QF
    obtain ⟨F,hCF⟩ := MatrixCopy.copy_forest_exists_d hM hC hT hX hRun.linear.1 hCountNat hExp.product hExp.width
      (row := C.zero) (maximal := C.one)
    have hLinear := hCF.linear_d hM hC hT hX hRun.linear hLast hC.one_succ.predecessor_mem
    have hEq := linear_forest_unique hM.1 hLinear hOther.linear
    subst F
    exact decorated_row_blocker_expand_d hM hC hA hT hX hRun hContext hExp hIndex hP hRun.linear.1 hCF hCQ
      (fun h => False.elim (hC.zero_empty maximal h)) (fun _ => hC.one_succ.predecessor_mem) hOldTop hTop
      (hS C.zero hr hBase L (Or.inl ⟨rfl,rfl⟩) P hPMem hP start hStartNat hStart) hStart
  · have hjA : M.mem j A.height := hExp.height ▸ hj
    obtain ⟨F,hFMem,hJF⟩ := hRun.graph.total j hjA
    have hCF := hExp.parent_copy_rows_d hM hC hA hT hX hRun hContext hOther hIndex j F QF hJF hJQF
    have hAbove : M.mem maximal r → ¬M.mem j maximal := by
      intro hMR hJM
      rcases (hs maximal).mp hMR with hMJ | he
      · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) maximal ((hw.mem hMaxNat).transitive j hJM maximal hMJ)
      · have heq := hM.1.eq_of_same_members maximal j he
        exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) maximal (heq.symm ▸ hJM)
    have hBelow : r=maximal ∨ M.mem r maximal → M.mem j maximal := by
      rintro (he | hRM)
      · exact he ▸ hs.predecessor_mem
      · exact (hw.mem hMaxNat).transitive r hRM j hs.predecessor_mem
    exact decorated_row_blocker_expand_d hM hC hA hT hX hRun hContext hExp hIndex hP (hRun.forests j F hJF) hCF hCQ hAbove hBelow hOldTop hTop
      (hS r hr hBase F (Or.inr ⟨j,hjA,hs,hFMem,hJF⟩) P hPMem hP start hStartNat hStart) hStart


theorem decorated_aboveS_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hB : B.Valid M C.omega)
    {Forests Rows L OtherForests Other OtherL base Top NewTop : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hHeight : B.height=A.height) (hSub : M.MemberSubset B.width A.width)
    (hParents : ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → RowsAgreeOn M P Q B.width)
    (hEntries : ∀ r c d, M.mem c B.width → (MatrixEntry M B r c d ↔ MatrixEntry M A r c d))
    (hTops : ∀ c, M.mem c B.width → ∀ v, MemPair M NewTop c v ↔ MemPair M Top c v)
    (hS : DecoratedAboveS M C A Forests Rows L base Top) : DecoratedAboveS M C B OtherForests Other OtherL base NewTop := by
  have hPads (c : M.Domain) (hc : M.mem c B.width) (r v : M.Domain) :
      PaddedEntry M C.zero B r c v ↔ PaddedEntry M C.zero A r c v := padded_entry_prefix_iff hHeight hSub hEntries hc
  intro r hr hBase P' hPrev Q' _ hQ' start hStart hs
  have hrA : M.mem r A.height := hHeight ▸ hr
  obtain ⟨Q,hQMem,hQ⟩ := hRun.graph.total r hrA
  have hCurRows := hParents r Q Q' hQ hQ'
  rcases hPrev with ⟨hr0,hP'⟩ | ⟨j,hj,hSucc,hP'Mem,hJ⟩
  · subst P'
    have hLinear : RowsAgreeOn M L OtherL B.width := by
      intro c hc p
      rw [hRun.linear.2 c p,hOther.linear.2 c p]
      simp only [hSub c hc,hc,true_and]
    exact decorated_row_blocker_transport_d hM hC hB (hRun.forests r Q hQ) hSub hLinear hCurRows hPads hTops
      (hS r hrA hBase L (Or.inl ⟨hr0,rfl⟩) Q hQMem hQ start hStart hs)
  · have hjA : M.mem j A.height := hHeight ▸ hj
    obtain ⟨P,hPMem,hJP⟩ := hRun.graph.total j hjA
    exact decorated_row_blocker_transport_d hM hC hB (hRun.forests r Q hQ) hSub
      (hParents j P P' hJP hJ) hCurRows hPads hTops
      (hS r hrA hBase P (Or.inr ⟨j,hjA,hSucc,hPMem,hJP⟩) Q hQMem hQ start hStart hs)

theorem TrimmedMatrix.decorated_aboveS_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L OtherForests Other OtherL base Top : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : TrimmedMatrix M C A B) (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hS : DecoratedAboveS M C A Forests Rows L base Top) : DecoratedAboveS M C B OtherForests Other OtherL base Top := by
  intro r hr hBase F hPrevious Q _ hQ start hStartNat hStart
  obtain ⟨P,hPMem,hP⟩ := hRun.graph.total r (h.trim.below r hr)
  have hEq := h.parent_rows_d hM hC hA hRun hOther r P Q hP hQ
  subst Q
  have hOldPrevious : PreviousMatrixForest M C A.height Forests Rows L r F := by
    rcases hPrevious with ⟨hz,hF⟩ | ⟨j,hj,hs,_,hF⟩
    · have hNewLinear : LinearForest M C.omega A.width OtherL := h.width ▸ hOther.linear
      have hLEq := linear_forest_unique hM.1 hRun.linear hNewLinear
      exact Or.inl ⟨hz,hF.trans hLEq.symm⟩
    · obtain ⟨P0,hP0Mem,hP0⟩ := hRun.graph.total j (h.trim.below j hj)
      have hP0F := h.parent_rows_d hM hC hA hRun hOther j P0 F hP0 hF
      exact Or.inr ⟨j,h.trim.below j hj,hs,hP0F ▸ hP0Mem,hP0F ▸ hP0⟩
  have hOldS := hS r (h.trim.below r hr) hBase F hOldPrevious P hPMem hP start hStartNat hStart
  intro c hc q hq p hp hPrev hCur hNe
  obtain ⟨z,hz,hPath,hZParent,topC,htc,topZ,htz,hTC,hTZ,hCompare⟩ := hOldS c (h.width ▸ hc) q (h.width ▸ hq) p (h.width ▸ hp) hPrev hCur hNe
  refine ⟨z,h.width.symm ▸ hz,hPath.imp id (fun ha => h.width.symm ▸ ha),hZParent,topC,htc,topZ,htz,hTC,hTZ,?_⟩
  exact (decorated_column_congr (fun r d => (h.padded_iff_d hM hC hA r c d).symm)
    (fun r d => (h.padded_iff_d hM hC hA r z d).symm)).mp hCompare

/-- Top的raw三分支：空、删除末列、按真实普通坐标复制。独立于矩阵行裁剪。 -/
def RawTopStep (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (T : MatrixArithmetic M.Domain) (Forests Rows Top : M.Domain) (R : FiniteMatrix M.Domain) (NewTop : M.Domain) : Prop :=
  (A.width=C.zero ∧ R.width=C.zero ∧ NewTop=C.zero) ∨ ∃ last, M.SuccessorOf A.width last ∧
    (((∀ r, M.mem r A.height → ¬ActiveParentRow M Forests Rows A.width last r) ∧ R.width=last ∧
      ∀ c v, MemPair M NewTop c v ↔ M.mem c last ∧ MemPair M Top c v) ∨
      ∃ maximal root, MatrixExpansionContext M C A Forests Rows last maximal root ∧ ∃ X : CopyCoordinates.Context M.Domain,
        X.last=last ∧ X.root=root ∧ X.Valid M C ∧ CopiedTop M C T X Top R.width NewTop)

def ExpandedTop (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (T : MatrixArithmetic M.Domain) (Forests Rows index Top : M.Domain) (B : FiniteMatrix M.Domain) (NewTop : M.Domain) : Prop :=
  ∃ R, R.Valid M C.omega ∧ RawMatrixStep M C A T Forests Rows index R ∧ TrimmedMatrix M C R B ∧
    RawTopStep M C A T Forests Rows Top R NewTop

theorem RawMatrixStep.decorated_aboveS_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A R : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L RawForests RawRows RawL index base Top : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hR : R.Valid M C.omega) (hRaw : RawMatrixStep M C A T Forests Rows index R)
    (hRawRun : MatrixParentRun M C R.width R.height R.cells R.values RawForests RawRows RawL)
    (hIndex : M.mem index C.omega) (hOldTop : Graph M Top A.width C.omega) (hS : DecoratedAboveS M C A Forests Rows L base Top) :
    ∃ NewTop, Graph M NewTop R.width C.omega ∧ RawTopStep M C A T Forests Rows Top R NewTop ∧
      DecoratedAboveS M C R RawForests RawRows RawL base NewTop := by
  rcases hRaw with ⟨hAW,hRH,hRW⟩ | ⟨last,hWidth,hCase⟩
  · have hGraph : Graph M C.zero R.width C.omega := hRW.symm ▸ (empty_graph hC.zero_empty : Graph M C.zero C.zero C.omega)
    exact ⟨C.zero,hGraph,Or.inl ⟨hAW,hRW,rfl⟩,fun r hr => False.elim (hC.zero_empty r (hRH ▸ hr))⟩
  · rcases hCase with ⟨hNone,hHeight,hRW,hEntries⟩ | ⟨maximal,root,count,len,total,hContext,hExp⟩
    · have hSub : M.MemberSubset R.width A.width := by
        intro c hc
        exact ((omega_isOrdinal_d hM hC.omega).mem hA.width).transitive last hWidth.predecessor_mem c (hRW ▸ hc)
      have hEntry (r c d : M.Domain) (hc : M.mem c R.width) : MatrixEntry M R r c d ↔ MatrixEntry M A r c d :=
        (hEntries r c d).trans ⟨And.right,fun h => ⟨hRW ▸ hc,h⟩⟩
      have hParents := matrix_parent_common_prefix_d hM hC hA hR hRun hRawRun hR.width hSub (fun _ hc => hc)
        (fun r c d _ _ hc => (hEntry r c d hc).symm)
      obtain ⟨NewTop,hTop,hTopRows⟩ := restrict_graph_d hM hOldTop hSub
      have hTops (c : M.Domain) (hc : M.mem c R.width) (v : M.Domain) : MemPair M NewTop c v ↔ MemPair M Top c v :=
        (hTopRows c v).trans ⟨And.right,fun h => ⟨hc,h⟩⟩
      refine ⟨NewTop,hTop,Or.inr ⟨last,hWidth,Or.inl ⟨hNone,hRW,?_⟩⟩,?_⟩
      · intro c v
        simpa only [hRW] using hTopRows c v
      · exact decorated_aboveS_prefix_d hM hC hR hRun hRawRun hHeight hSub hParents hEntry hTops hS
    · obtain ⟨first,hFirst,_⟩ := hC.omega.1.2 root hExp.difference.2.1
      let X : CopyCoordinates.Context M.Domain := ⟨last,root,len,first⟩
      have hX : X.Valid M C := ⟨hExp.difference.1,hExp.difference.2.1,hContext.root_lt_last hRun,hExp.difference,hFirst⟩
      obtain ⟨NewTop,hTop⟩ := copied_top_exists_d hM hC hT hX hA.width hR.width hOldTop hContext.width_successor.predecessor_mem
      exact ⟨NewTop,hTop.graph,Or.inr ⟨last,hWidth,Or.inr ⟨maximal,root,hContext,X,rfl,rfl,hX,hTop⟩⟩,
        hExp.decorated_aboveS_d hM hC hA hT hX hRun hContext hRawRun hIndex hOldTop hTop hS⟩

/-- 完整MatrixExpansion保持装饰S，且构造实际复制Top图，涵盖empty/delete/trim。 -/
theorem MatrixExpansion.decorated_aboveS_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L OtherForests Other OtherL index base Top : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : MatrixExpansion M C A T Forests Rows index B)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hIndex : M.mem index C.omega) (hOldTop : Graph M Top A.width C.omega) (hS : DecoratedAboveS M C A Forests Rows L base Top) :
    ∃ NewTop, Graph M NewTop B.width C.omega ∧ ExpandedTop M C A T Forests Rows index Top B NewTop ∧
      DecoratedAboveS M C B OtherForests Other OtherL base NewTop := by
  obtain ⟨R,hR,hRaw,hTrim⟩ := h
  obtain ⟨RawForests,RawRows,RawL,hRawRun⟩ := matrix_parent_run_exists_d hM hC hR
  obtain ⟨NewTop,hTop,hTopStep,hRawS⟩ := hRaw.decorated_aboveS_exists_d hM hC hA hT hRun hR hRawRun hIndex hOldTop hS
  exact ⟨NewTop,hTrim.width.symm ▸ hTop,⟨R,hR,hRaw,hTrim,hTopStep⟩,
    hTrim.decorated_aboveS_d hM hC hR hRawRun hOther hRawS⟩

theorem matrix_expansion_decorated_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L index base Top : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L) (hIndex : M.mem index C.omega)
    (hOldTop : Graph M Top A.width C.omega) (hI : MatrixDepthRegular M C A Forests Rows) (hS : DecoratedAboveS M C A Forests Rows L base Top) :
    ∃ B OtherForests Other OtherL NewTop, MatrixExpansion M C A T Forests Rows index B ∧ NormalizedMatrix M C B ∧
      MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧ MatrixDepthRegular M C B OtherForests Other ∧
      Graph M NewTop B.width C.omega ∧ ExpandedTop M C A T Forests Rows index Top B NewTop ∧
      DecoratedAboveS M C B OtherForests Other OtherL base NewTop := by
  obtain ⟨B,hB⟩ := matrix_expansion_exists_d hM hC hA hT hRun hIndex
  obtain ⟨OtherForests,Other,OtherL,hOther⟩ := matrix_parent_run_exists_d hM hC hB.matrix
  obtain ⟨NewTop,hTop,hExpanded,hDecor⟩ := hB.decorated_aboveS_exists_d hM hC hA hT hRun hOther hIndex hOldTop hS
  have hBI := (hB.relative_structural_d hM hC hA hT hRun hOther hIndex hI hS.forget).1
  exact ⟨B,OtherForests,Other,OtherL,NewTop,hB,hB.normalized,hOther,hBI,hTop,hExpanded,hDecor⟩

end KP1Y.OneYFinite
