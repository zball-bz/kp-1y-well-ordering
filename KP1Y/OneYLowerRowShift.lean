import KP1Y.OneYCopyCoordinates

/-! Lower复制的固定底行/高行反移位。全部运算读取同一实际自然数表。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open CopyCoordinates
universe u

theorem add_same_right_lt_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {a b off x y : M.Domain} (hA : AddAt M T.addPairs T.plus a off x) (hB : AddAt M T.addPairs T.plus b off y) :
    M.mem x y ↔ M.mem a b := by
  have ha := hA.bounds hM.1 hT.add
  have hb := hB.bounds hM.1 hT.add
  have hSA := (hT.add.add_iff_sum hM ha.1 ha.2.1).mp hA
  have hSB := (hT.add.add_iff_sum hM hb.1 hb.2.1).mp hB
  constructor
  · intro hxy
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare a ha.1 b hb.1 with he | hab | hba
    · have hab := hM.1.eq_of_same_members a b he
      subst b
      have hexy := hT.add.add_unique hM.1 hA hB
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) y (hexy ▸ hxy))
    · exact hab
    · have hyx := natural_sum_strict_left_d hM hC hb.1 ha.1 ha.2.1 hSB hSA hba
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) x
        (((omega_isOrdinal_d hM hC.omega).mem ha.2.2).transitive y hyx x hxy))
  · exact natural_sum_strict_left_d hM hC ha.1 hb.1 ha.2.1 hSA hSB

theorem add_same_right_eq_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {a b off x y : M.Domain} (hA : AddAt M T.addPairs T.plus a off x) (hB : AddAt M T.addPairs T.plus b off y) :
    x=y ↔ a=b := by
  constructor
  · intro he
    subst y
    have ha := hA.bounds hM.1 hT.add
    have hb := hB.bounds hM.1 hT.add
    exact natural_sum_cancel_left_d hM hC ha.2.1 ha.1 hb.1
      (natural_sum_comm_d hM hC ha.1 ha.2.1 ((hT.add.add_iff_sum hM ha.1 ha.2.1).mp hA))
      (natural_sum_comm_d hM hC hb.1 hb.2.1 ((hT.add.add_iff_sum hM hb.1 hb.2.1).mp hB))
  · intro he
    subst b
    exact hT.add.add_unique hM.1 hA hB

theorem add_same_right_le_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {a b off x y : M.Domain} (hA : AddAt M T.addPairs T.plus a off x) (hB : AddAt M T.addPairs T.plus b off y) :
    (x=y ∨ M.mem x y) ↔ (a=b ∨ M.mem a b) :=
  or_congr (add_same_right_eq_iff_d hM hC hT hA hB) (add_same_right_lt_iff_d hM hC hT hA hB)

def ShiftedRow (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (floor off r u : M.Domain) : Prop :=
  M.mem r C.omega ∧ M.mem u C.omega ∧ ∃ level, M.mem level C.omega ∧ AddAt M T.addPairs T.plus floor off level ∧
    ((M.mem r level ∧ u=floor) ∨ (¬M.mem r level ∧ DifferenceRead M T r off u))

def shiftedRowFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (floor off r u : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem r C.omega) (.conj (.mem u C.omega) (Project.Formula.existsMem C.omega
    (.conj (addAtFormula T.addPairs.weaken T.plus.weaken floor.weaken off.weaken (.bound 0))
      (.disj (.conj (.mem r.weaken (.bound 0)) (Project.Formula.extensionalEq u.weaken floor.weaken))
        (.conj (.neg (.mem r.weaken (.bound 0))) (differenceReadFormula T.weaken r.weaken off.weaken u.weaken))))))

theorem shiftedRowFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (floor off r u : Project.Term n) : (shiftedRowFormula C T floor off r u).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.existsMem _ (.conj (addAtFormula_delta0 _ _ _ _ _)
    (.disj (.conj (.mem _ _) (.atom _ _ _)) (.conj (.neg (.mem _ _)) (differenceReadFormula_delta0 _ _ _ _))))))

theorem shiftedRowFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) (floor off r u : Project.Term n)
    (hf : floor.freeSupport=[]) (ho : off.freeSupport=[]) (hr : r.freeSupport=[]) (hu : u.freeSupport=[]) :
    (shiftedRowFormula C T floor off r u).FreeClosed := by
  simp [shiftedRowFormula,differenceReadFormula,addAtFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,MatrixArithmetic.weaken,MatrixArithmetic.map,
    Definitional.Formula.FreeClosed,hC.omega,hT.addPairs,hT.plus,hT.diffPairs,hT.difference,hf,ho,hr,hu]

theorem shiftedRowFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (floor off r u : Project.Term n) :
    Project.Formula.satisfies env (shiftedRowFormula C T floor off r u) ↔
      ShiftedRow M (C.eval env) (T.eval env) (floor.eval env) (off.eval env) (r.eval env) (u.eval env) := by
  simp only [shiftedRowFormula,ShiftedRow,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,addAtFormula_iff he,differenceReadFormula_iff he,
    Term.eval_weaken,MatrixArithmetic.eval_weaken]
  rfl

theorem shifted_row_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off r : M.Domain} (hf : M.mem floor C.omega) (ho : M.mem off C.omega) (hr : M.mem r C.omega) :
    ∃ u, ShiftedRow M C T floor off r u := by
  obtain ⟨level,hl,hLevel⟩ := hT.add.add_exists_d hM hC hf ho
  classical
  by_cases hLow : M.mem r level
  · exact ⟨floor,hr,hf,level,hl,hLevel,Or.inl ⟨hLow,rfl⟩⟩
  · obtain ⟨u,hu,hU⟩ := difference_read_exists_d hM hT hr ho
    exact ⟨u,hr,hu,level,hl,hLevel,Or.inr ⟨hLow,hU⟩⟩

theorem shifted_row_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {floor off r u v : M.Domain}
    (hU : ShiftedRow M C T floor off r u) (hV : ShiftedRow M C T floor off r v) : u=v := by
  obtain ⟨_,_,level,_,hLevel,hU⟩ := hU
  obtain ⟨_,_,level',_,hLevel',hV⟩ := hV
  have hl := hT.add.add_unique he hLevel hLevel'
  subst level'
  rcases hU with ⟨hr,hu⟩ | ⟨hr,hu⟩ <;> rcases hV with ⟨hr',hv⟩ | ⟨hr',hv⟩
  · exact hu.trans hv.symm
  · exact False.elim (hr' hr)
  · exact False.elim (hr hr')
  · exact difference_read_unique he hT hu hv

theorem ShiftedRow.gap_value {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {floor off r u level : M.Domain}
    (h : ShiftedRow M C T floor off r u) (hLevel : AddAt M T.addPairs T.plus floor off level) (hr : M.mem r level) : u=floor := by
  obtain ⟨_,_,l,_,hL,hCase⟩ := h
  have hll := hT.add.add_unique he hL hLevel
  subst l
  exact hCase.elim And.right (fun h => False.elim (h.1 hr))

theorem ShiftedRow.high_sum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off r u level : M.Domain} (h : ShiftedRow M C T floor off r u)
    (hLevel : AddAt M T.addPairs T.plus floor off level) (hr : ¬M.mem r level) : AddAt M T.addPairs T.plus u off r := by
  obtain ⟨hrNat,hu,l,_,hL,hCase⟩ := h
  have hll := hT.add.add_unique hM.1 hL hLevel
  subst l
  have hDiff : DifferenceRead M T r off u := hCase.elim (fun h => False.elim (hr h.1)) And.right
  have hBounds := hLevel.bounds hM.1 hT.add
  have hw := omega_isOrdinal_d hM hC.omega
  have hOffSub : M.MemberSubset off level := sum_base_subset_d hM (hw.mem hBounds.2.1)
    (natural_sum_comm_d hM hC hBounds.1 hBounds.2.1 ((hT.add.add_iff_sum hM hBounds.1 hBounds.2.1).mp hLevel))
  have hOffR : off=r ∨ M.mem off r := by
    rcases hw.wellOrder.linear.compare off hBounds.2.1 r hrNat with he | ho | hro
    · exact Or.inl (hM.1.eq_of_same_members off r he)
    · exact Or.inr ho
    · exact False.elim (hr (hOffSub r hro))
  have hSum := truncated_difference_add_inverse_d hM hC ((difference_read_iff_d hM hT hrNat hBounds.2.1).mp hDiff) hOffR
  exact (hT.add.add_iff_sum hM hu hBounds.2.1).mpr (natural_sum_comm_d hM hC hBounds.2.1 hu hSum)

/-- 固定底行使floor≤u实际上对所有r成立，不需要额外floor≤r。 -/
theorem ShiftedRow.floor_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off r u : M.Domain} (h : ShiftedRow M C T floor off r u) : floor=u ∨ M.mem floor u := by
  have hShift := h
  obtain ⟨_,_,level,_,hLevel,hCase⟩ := h
  rcases hCase with ⟨_,he⟩ | ⟨hr,_⟩
  · exact Or.inl he.symm
  · have hSum := hShift.high_sum_d hM hC hT hLevel hr
    have hBounds := hLevel.bounds hM.1 hT.add
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare floor hBounds.1 u hShift.2.1 with he | hfu | huf
    · exact Or.inl (hM.1.eq_of_same_members floor u he)
    · exact Or.inr hfu
    · exact False.elim (hr ((add_same_right_lt_iff_d hM hC hT hSum hLevel).mpr huf))

theorem ShiftedRow.lt_height_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off r u height lifted : M.Domain} (h : ShiftedRow M C T floor off r u)
    (hf : M.mem floor height) (hHeight : AddAt M T.addPairs T.plus height off lifted) : M.mem u height ↔ M.mem r lifted := by
  have hShift := h
  obtain ⟨_,_,level,_,hLevel,hCase⟩ := h
  rcases hCase with ⟨hr,he⟩ | ⟨hr,_⟩
  · have hLL := (add_same_right_lt_iff_d hM hC hT hLevel hHeight).mpr hf
    have hRL := ((omega_isOrdinal_d hM hC.omega).mem (hHeight.bounds hM.1 hT.add).2.2).transitive level hLL r hr
    exact ⟨fun _ => hRL,fun _ => he.symm ▸ hf⟩
  · exact (add_same_right_lt_iff_d hM hC hT (hShift.high_sum_d hM hC hT hLevel hr) hHeight).symm

theorem ShiftedRow.endpoint_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off r u parentHeight lifted : M.Domain} (h : ShiftedRow M C T floor off r u)
    (hEnd : u=parentHeight ∨ M.mem u parentHeight)
    (hParent : AddAt M T.addPairs T.plus parentHeight off lifted) : r=lifted ∨ M.mem r lifted := by
  have hShift := h
  obtain ⟨_,_,level,_,hLevel,hCase⟩ := h
  rcases hCase with ⟨hr,he⟩ | ⟨hr,_⟩
  · have hFloor : floor=parentHeight ∨ M.mem floor parentHeight := he ▸ hEnd
    rcases (add_same_right_le_iff_d hM hC hT hLevel hParent).mpr hFloor with he | hLL
    · exact Or.inr (he ▸ hr)
    · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem (hParent.bounds hM.1 hT.add).2.2).transitive level hLL r hr)
  · exact (add_same_right_le_iff_d hM hC hT (hShift.high_sum_d hM hC hT hLevel hr) hParent).mpr hEnd

private def shiftedRowEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (floor off : M.Domain) : Env M 13 where
  bound i := match i.val with
    | 0 => C.omega | 1 => C.zero | 2 => C.one | 3 => C.sequences | 4 => C.expressions
    | 5 => T.addPairs | 6 => T.plus | 7 => T.mulPairs | 8 => T.times | 9 => T.diffPairs | 10 => T.difference
    | 11 => floor | _ => off
  free _ := C.zero

private def shiftedRowSchema : Project.Delta0BinarySchema 13 where
  body := shiftedRowFormula ⟨.bound 2,.bound 3,.bound 4,.bound 5,.bound 6⟩
    ⟨.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12⟩ (.bound 13) (.bound 14) (.bound 1) (.bound 0)
  freeClosed := by
    simp [shiftedRowFormula,differenceReadFormula,addAtFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,Project.Formula.forallMem,MatrixArithmetic.weaken,MatrixArithmetic.map,Definitional.Formula.FreeClosed]
  delta0 := shiftedRowFormula_delta0 _ _ _ _ _ _

theorem shifted_row_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off : M.Domain} (hf : M.mem floor C.omega) (ho : M.mem off C.omega) :
    ∃ F, Graph M F C.omega C.omega ∧ ∀ r u, MemPair M F r u ↔ ShiftedRow M C T floor off r u := by
  let env := shiftedRowEnv C T floor off
  have hφ (r u : M.Domain) : Project.Formula.satisfies ((env.push r).push u) shiftedRowSchema.body ↔ ShiftedRow M C T floor off r u := by
    rw [shiftedRowSchema,shiftedRowFormula_iff hM.1]
    rfl
  obtain ⟨F,hSupport,hRaw⟩ := relation_comprehension_d hM shiftedRowSchema env C.omega C.omega
  have hRows (r u : M.Domain) : MemPair M F r u ↔ ShiftedRow M C T floor off r u := by
    rw [hRaw r u,hφ]
    exact ⟨fun h => h.2.2,fun h => ⟨h.1,h.2.1,h⟩⟩
  refine ⟨F,⟨hSupport,?_,?_⟩,hRows⟩
  · intro r hr
    obtain ⟨u,hU⟩ := shifted_row_exists_d hM hC hT hf ho hr
    exact ⟨u,hU.2.1,(hRows r u).mpr hU⟩
  · intro r u v hu hv
    exact shifted_row_unique hM.1 hT ((hRows r u).mp hu) ((hRows r v).mp hv)

end KP1Y.OneYFinite
