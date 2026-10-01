import KP1Y.OneYLowerRowShift
import KP1Y.OneYNaturalAdditionFacts

/-! Lower行移位在实际相邻行上只会保持不变或增加一，含填充段末端。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Arithmetic
universe u

theorem add_same_right_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {a b off x y : M.Domain} (hA : AddAt M T.addPairs T.plus a off x) (hB : AddAt M T.addPairs T.plus b off y)
    (hNext : M.SuccessorOf y x) : M.SuccessorOf b a := by
  have hAB := hA.bounds hM.1 hT.add
  obtain ⟨next,hSucc,hNat⟩ := hC.omega.1.2 a hAB.1
  obtain ⟨z,_,hZ⟩ := hT.add.add_exists_d hM hC hNat hAB.2.1
  have hZX := natural_sum_left_successor_d hM hC hAB.2.1 hSucc
    ((hT.add.add_iff_sum hM hAB.1 hAB.2.1).mp hA) ((hT.add.add_iff_sum hM hNat hAB.2.1).mp hZ)
  have hZY := Structure.SuccessorOf.eq hM.1 hZX hNext
  have hNBEq := (add_same_right_eq_iff_d hM hC hT hZ hB).mp hZY
  exact hNBEq ▸ hSucc

theorem ShiftedRow.successor_of_high_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off r next u v level : M.Domain} (hU : ShiftedRow M C T floor off r u)
    (hV : ShiftedRow M C T floor off next v) (hNext : M.SuccessorOf next r)
    (hLevel : AddAt M T.addPairs T.plus floor off level) (hHigh : ¬M.mem r level) : M.SuccessorOf v u := by
  have hNotNext : ¬M.mem next level := fun h => hHigh
    (((omega_isOrdinal_d hM hC.omega).mem (hLevel.bounds hM.1 hT.add).2.2).transitive next h r hNext.predecessor_mem)
  exact add_same_right_successor_d hM hC hT (hU.high_sum_d hM hC hT hLevel hHigh)
    (hV.high_sum_d hM hC hT hLevel hNotNext) hNext

theorem ShiftedRow.successor_cases_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off r next u v : M.Domain} (hU : ShiftedRow M C T floor off r u)
    (hV : ShiftedRow M C T floor off next v) (hNext : M.SuccessorOf next r) : v=u ∨ M.SuccessorOf v u := by
  obtain ⟨level,hLevelNat,hLevel,_⟩ := hU.2.2
  classical
  by_cases hLow : M.mem r level
  · have hUF := hU.gap_value hM.1 hT hLevel hLow
    by_cases hNextLow : M.mem next level
    · exact .inl ((hV.gap_value hM.1 hT hLevel hNextLow).trans hUF.symm)
    · have hNextEq : next=level := by
        rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare next hV.1 level hLevelNat with he | hlt | hgt
        · exact hM.1.eq_of_same_members next level he
        · exact False.elim (hNextLow hlt)
        · rcases (hNext level).mp hgt with hBefore | hSame
          · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) level
              (((omega_isOrdinal_d hM hC.omega).mem hLevelNat).transitive r hLow level hBefore))
          · have hEq := hM.1.eq_of_same_members level r hSame
            exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r (hEq ▸ hLow))
      have hVSum := hV.high_sum_d hM hC hT hLevel hNextLow
      have hVF := (add_same_right_eq_iff_d hM hC hT hVSum hLevel).mp hNextEq
      exact .inl (hVF.trans hUF.symm)
  · exact .inr (hU.successor_of_high_d hM hC hT hV hNext hLevel hLow)

theorem ShiftedRow.successor_equal_floor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off r next u v : M.Domain} (hU : ShiftedRow M C T floor off r u)
    (hV : ShiftedRow M C T floor off next v) (hNext : M.SuccessorOf next r) (hEqual : v=u) : u=floor := by
  obtain ⟨level,_,hLevel,_⟩ := hU.2.2
  classical
  by_cases hLow : M.mem r level
  · exact hU.gap_value hM.1 hT hLevel hLow
  · have hSucc := hU.successor_of_high_d hM hC hT hV hNext hLevel hLow
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) u (hEqual ▸ hSucc.predecessor_mem))

theorem ShiftedRow.below_floor_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off r u : M.Domain} (hU : ShiftedRow M C T floor off r u) (hBefore : r=floor ∨ M.mem r floor) : u=floor := by
  obtain ⟨level,_,hLevel,_⟩ := hU.2.2
  classical
  by_cases hLow : M.mem r level
  · exact hU.gap_value hM.1 hT hLevel hLow
  · rcases hU.floor_le_d hM hC hT with he | hlt
    · exact he.symm
    · have hSum := hU.high_sum_d hM hC hT hLevel hLow
      have hBounds := hSum.bounds hM.1 hT.add
      have hFloorR := sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hBounds.1)
        ((hT.add.add_iff_sum hM hBounds.1 hBounds.2.1).mp hSum) floor hlt
      rcases hBefore with he | hr
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) floor (he ▸ hFloorR))
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) floor
          (((omega_isOrdinal_d hM hC.omega).mem (hLevel.bounds hM.1 hT.add).1).transitive r hr floor hFloorR))

theorem ShiftedRow.floor_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off u : M.Domain} (h : ShiftedRow M C T floor off floor u) : u=floor :=
  h.below_floor_value_d hM hC hT (.inl rfl)

end KP1Y.OneYFinite
