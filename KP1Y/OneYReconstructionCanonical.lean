import KP1Y.OneYMountainReconstruction
import KP1Y.OneYNaturalAdditionFacts

/-! 数值规范重提取的低层桥：实际重建值形成数值行与真实差图。
最近更小选择的恢复在具体复制分支另证，不由NumericRow偷偷假定。 -/
namespace KP1Y.OneYFinite.ReconstructionCanonical
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open Reconstruction MountainReconstruction
universe u

/-- 有限网格之外的内部ω行实际补零；列仍严格位于原有限width。 -/
def PaddedCell (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (H r c x : M.Domain) : Prop :=
  M.mem r D.naturals.omega ∧ M.mem c D.width ∧
    (ValidCell M D H c r x ∨ (¬M.mem r D.rows ∧ x=D.naturals.zero))

def paddedCellFormula {n : Nat} (D : GridData (Project.Term n)) (H r c x : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem r D.naturals.omega) (.conj (.mem c D.width)
    (.disj (validCellFormula D H c r x) (.conj (.neg (.mem r D.rows)) (Project.Formula.extensionalEq x D.naturals.zero))))

theorem paddedCellFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (H r c x : Project.Term n) :
    (paddedCellFormula D H r c x).IsDelta0 := .conj (.mem _ _) (.conj (.mem _ _)
      (.disj (validCellFormula_delta0 _ _ _ _ _) (.conj (.neg (.mem _ _)) (.atom _ _ _))))

theorem paddedCellFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (H r c x : Project.Term n) (hH : H.freeSupport=[]) (hr : r.freeSupport=[])
    (hc : c.freeSupport=[]) (hx : x.freeSupport=[]) : (paddedCellFormula D H r c x).FreeClosed := by
  have hV := validCellFormula_freeClosed hD H c r x hH hc hr hx
  simp [paddedCellFormula,Definitional.Formula.FreeClosed,hD.naturals.omega,hD.naturals.zero,hD.width,hD.rows,hr,hc,hx,hV]

theorem paddedCellFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (H r c x : Project.Term n) :
    Project.Formula.satisfies e (paddedCellFormula D H r c x) ↔ PaddedCell M (D.eval e) (H.eval e) (r.eval e) (c.eval e) (x.eval e) := by
  simp only [paddedCellFormula,PaddedCell,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,validCellFormula_iff he]
  rfl

theorem PaddedCell.natural {M : SetTheory.Structure.{u}} (he : Extensional M) {D : GridData M.Domain}
    (hD : D.Valid M) {H r c x : M.Domain} (h : PaddedCell M D H r c x) : M.mem x D.naturals.omega := by
  rcases h.2.2 with h | ⟨_,he⟩
  · exact (h.bounds he).2
  · exact he.symm ▸ hD.naturals.zero_nat

theorem PaddedCell.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {D : GridData M.Domain}
    {H r c x y : M.Domain} (hH : Reconstructs M D H) (hX : PaddedCell M D H r c x) (hY : PaddedCell M D H r c y) : x=y := by
  rcases hX.2.2 with hX | ⟨hr,hX⟩ <;> rcases hY.2.2 with hY | ⟨hr',hY⟩
  · exact hX.unique hH.graph hY
  · exact False.elim (hr' (hX.bounds he).1)
  · exact False.elim (hr (hY.bounds he).1)
  · exact hX.trans hY.symm

theorem padded_cell_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (_hD : D.Valid M) {H r c : M.Domain} (hH : Reconstructs M D H)
    (hr : M.mem r D.naturals.omega) (hc : M.mem c D.width) : ∃ x, PaddedCell M D H r c x := by
  classical
  by_cases hrB : M.mem r D.rows
  · obtain ⟨f,_,hCf⟩ := hH.graph.total c hc
    obtain ⟨x,_,hRX⟩ := (hH.column hM.1 hCf).graph.total r hrB
    exact ⟨x,hr,hc,Or.inl ((hH.valid_cell_iff hM.1 hCf).mpr hRX)⟩
  · exact ⟨D.naturals.zero,hr,hc,Or.inr ⟨hrB,rfl⟩⟩

theorem PaddedCell.inside {M : SetTheory.Structure.{u}} {D : GridData M.Domain} {H r c x : M.Domain}
    (h : PaddedCell M D H r c x) (hr : M.mem r D.rows) : ValidCell M D H c r x :=
  h.2.2.elim id (fun h => False.elim (h.1 hr))

structure RowValues (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (H r V : M.Domain) : Prop where
  graph : Graph M V D.width D.naturals.omega
  rows : ∀ c x, MemPair M V c x ↔ PaddedCell M D H r c x

private def rowValueEnv {M : SetTheory.Structure.{u}} (D : GridData M.Domain) (H r : M.Domain) : Env M 15 :=
  ((((((((((((((oneEnv D.naturals.omega).push D.naturals.zero).push D.naturals.one).push D.naturals.sequences).push D.naturals.expressions).push D.width).push D.rows).push D.heights).push D.forests).push D.parents).push D.tops).push D.pairs).push D.plus).push H).push r

private def rowValueSchema : Project.Delta0BinarySchema 15 where
  body := paddedCellFormula ⟨⟨.bound 16,.bound 15,.bound 14,.bound 13,.bound 12⟩,
    .bound 11,.bound 10,.bound 9,.bound 8,.bound 7,.bound 6,.bound 5,.bound 4⟩ (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := paddedCellFormula_freeClosed ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ rfl rfl rfl rfl
  delta0 := paddedCellFormula_delta0 _ _ _ _ _

theorem row_values_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H r : M.Domain} (hH : Reconstructs M D H)
    (hr : M.mem r D.naturals.omega) : ∃ V, RowValues M D H r V := by
  have hφ (c x : M.Domain) : Project.Formula.satisfies (((rowValueEnv D H r).push c).push x) rowValueSchema.body ↔
      PaddedCell M D H r c x := paddedCellFormula_iff hM.1 _ _ _ _ _ _
  obtain ⟨V,hSupport,hRaw⟩ := relation_comprehension_d hM rowValueSchema (rowValueEnv D H r) D.width D.naturals.omega
  have hRows (c x : M.Domain) : MemPair M V c x ↔ PaddedCell M D H r c x := by
    rw [hRaw c x,hφ]
    exact ⟨fun h => h.2.2,fun h => ⟨h.2.1,h.natural hM.1 hD,h⟩⟩
  refine ⟨V,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨x,hX⟩ := padded_cell_exists_d hM hD hH hr hc
    exact ⟨x,hX.natural hM.1 hD,(hRows c x).mpr hX⟩
  · intro c x y hX hY
    exact ((hRows c x).mp hX).unique hM.1 hH ((hRows c y).mp hY)

theorem PaddedCell.absent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H r c x height : M.Domain}
    (hH : Reconstructs M D H) (h : PaddedCell M D H r c x) (hHeight : MemPair M D.heights c height)
    (hAbsent : M.mem height r) : x=D.naturals.zero := by
  rcases h.2.2 with hCell | ⟨_,he⟩
  · obtain ⟨f,_,hCf,_,hRX⟩ := hCell
    exact (hH.column hM.1 hCf).absent height (hD.heights.bounds hM.1 hHeight).2 hHeight r
      ((hH.column hM.1 hCf).graph.bounds hM.1 hRX).1 x ((hH.column hM.1 hCf).graph.bounds hM.1 hRX).2 hRX hAbsent
  · exact he

theorem PaddedCell.live_positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H r c x height top : M.Domain}
    (hH : Reconstructs M D H) (h : PaddedCell M D H r c x) (hHeight : MemPair M D.heights c height)
    (hTop : MemPair M D.tops c top) (hPos : M.mem D.naturals.zero top) (hLive : r=height ∨ M.mem r height) : M.mem D.naturals.zero x := by
  have hrB : M.mem r D.rows := by
    rcases hLive with he | hlt
    · exact he.symm ▸ (hD.heights.bounds hM.1 hHeight).2
    · exact ((omega_isOrdinal_d hM hD.naturals.omega).mem hD.rows).transitive height (hD.heights.bounds hM.1 hHeight).2 r hlt
  obtain ⟨f,_,hCf,_,hRX⟩ := h.inside hrB
  obtain ⟨K,hK⟩ := contribution_graph_exists_d hM hD hH.graph c
  exact ((hH.column hM.1 hCf).to_filled_column hM hD hK hHeight hTop).live_positive_d hM hD.naturals
    hK.graph hD.addition hPos hLive hRX

theorem PaddedCell.positive_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H r c x height top : M.Domain}
    (hH : Reconstructs M D H) (h : PaddedCell M D H r c x) (hHeight : MemPair M D.heights c height)
    (hTop : MemPair M D.tops c top) (hPos : M.mem D.naturals.zero top) :
    M.mem D.naturals.zero x ↔ (r=height ∨ M.mem r height) := by
  constructor
  · intro hX
    have hh := (omega_isOrdinal_d hM hD.naturals.omega).transitive D.rows hD.rows height (hD.heights.bounds hM.1 hHeight).2
    rcases (omega_isOrdinal_d hM hD.naturals.omega).wellOrder.linear.compare r h.1 height hh with he | hlt | hgt
    · exact Or.inl (hM.1.eq_of_same_members r height he)
    · exact Or.inr hlt
    · exact False.elim (hD.naturals.zero_empty D.naturals.zero ((h.absent_d hM hD hH hHeight hgt) ▸ hX))
  · exact h.live_positive_d hM hD hH hHeight hTop hPos

private theorem successor_le_of_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r s height : M.Domain}
    (hr : M.mem r C.omega) (hh : M.mem height C.omega) (hSucc : M.SuccessorOf s r) (hLt : M.mem r height) :
    s=height ∨ M.mem s height := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hr hSucc)) (hw.mem hh)
  intro x hx
  rcases (hSucc x).mp hx with hxr | he
  · exact (hw.mem hh).transitive r hLt x hxr
  · exact (hM.1.eq_of_same_members x r he).symm ▸ hLt

theorem PaddedCell.parent_sum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H r s c p x y z : M.Domain}
    (hH : Reconstructs M D H) (hParent : Reconstruction.ParentAt M D r c p) (hSucc : M.SuccessorOf s r)
    (hX : PaddedCell M D H r c x) (hY : PaddedCell M D H s c y) (hZ : PaddedCell M D H r p z) :
    AddAt M D.pairs D.plus y z x := by
  have hBounds := hParent.bounds hM.1 hD
  obtain ⟨height,hh,hHeight⟩ := hD.heights.total c hBounds.2.1
  have hLt := (hD.live r hBounds.1 c hBounds.2.1 height hHeight).mp ⟨p,hParent⟩
  have hSH := successor_le_of_lt_d hM hD.naturals hX.1
    ((omega_isOrdinal_d hM hD.naturals.omega).transitive D.rows hD.rows height hh) hSucc hLt
  have hsB : M.mem s D.rows := by
    rcases hSH with he | hlt
    · exact he.symm ▸ hh
    · exact ((omega_isOrdinal_d hM hD.naturals.omega).mem hD.rows).transitive height hh s hlt
  obtain ⟨f,_,hCf,_,hRX⟩ := hX.inside hBounds.1
  exact hH.parent_equation_d hM hD hCf hHeight hParent hSucc hRX
    ((hH.valid_cell_iff hM.1 hCf).mp (hY.inside hsB)) (hZ.inside hBounds.1)

/-- 从真实加法重建方程得到父值严格小于子值，未使用最近更小选择。 -/
theorem PaddedCell.parent_values_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H r c p x y : M.Domain}
    (hH : Reconstructs M D H) (hTopPositive : ∀ c top, MemPair M D.tops c top → M.mem D.naturals.zero top)
    (hParent : Reconstruction.ParentAt M D r c p)
    (hP : PaddedCell M D H r p x) (hC : PaddedCell M D H r c y) : M.mem D.naturals.zero x ∧ M.mem x y := by
  obtain ⟨heightP,_,hHeightP⟩ := hD.heights.total p hP.2.1
  obtain ⟨topP,_,hTopP⟩ := hD.tops.total p hP.2.1
  have hParentPositive := hP.live_positive_d hM hD hH hHeightP hTopP (hTopPositive p topP hTopP)
    (hD.endpoint r c p hParent heightP hHeightP)
  obtain ⟨next,hSucc,hNext⟩ := hD.naturals.omega.1.2 r hC.1
  obtain ⟨v,hV⟩ := padded_cell_exists_d hM hD hH hNext hC.2.1
  obtain ⟨height,hh,hHeight⟩ := hD.heights.total c hC.2.1
  obtain ⟨top,_,hTop⟩ := hD.tops.total c hC.2.1
  have hLt := (hD.live r (hParent.bounds hM.1 hD).1 c hC.2.1 height hHeight).mp ⟨p,hParent⟩
  have hNextLe := successor_le_of_lt_d hM hD.naturals hC.1
    ((omega_isOrdinal_d hM hD.naturals.omega).transitive D.rows hD.rows height hh) hSucc hLt
  have hVPositive := hV.live_positive_d hM hD hH hHeight hTop (hTopPositive c top hTop) hNextLe
  have hSum := hC.parent_sum_d hM hD hH hParent hSucc hV hP
  have hx := hP.natural hM.1 hD
  have hv := hV.natural hM.1 hD
  have hComm := natural_sum_comm_d hM hD.naturals hv hx ((hD.addition.add_iff_sum hM hv hx).mp hSum)
  exact ⟨hParentPositive,KP1Y.Arithmetic.sum_strict_right_d hM ((omega_isOrdinal_d hM hD.naturals.omega).mem hx)
    (KP1Y.Arithmetic.sum_zero_d hM x hD.naturals.zero_empty) hComm hVPositive⟩

theorem RowValues.numeric_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H r V P : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hV : RowValues M (grid C X Top Pairs Plus B Parents) H r V) (hP : MemPair M X.parents r P) :
    NumericRow M C X.width V P := by
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  refine ⟨hV.graph,hX.forest r P hP,?_⟩
  intro c p x y hCP hPX hCY
  have hPX' := (hV.rows p x).mp hPX
  have hCY' := (hV.rows c y).mp hCY
  have hParent : CopiedMountain.ParentAt M X r c p := ⟨P,(hX.parents.bounds hM.1 hP).2,hP,hCP⟩
  exact hPX'.parent_values_d hM hD hH hPositive ((grid_parent_iff_d hM hC hX hB hParents).mpr hParent) hCY'

theorem RowValues.difference_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H r s V W P : M.Domain}
    (hTop : Graph M Top X.width C.omega)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hV : RowValues M (grid C X Top Pairs Plus B Parents) H r V)
    (hW : RowValues M (grid C X Top Pairs Plus B Parents) H s W)
    (hP : MemPair M X.parents r P) (hSucc : M.SuccessorOf s r) : DifferenceGraph M C X.width V P W := by
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  have hForest := hX.forest r P hP
  have hr := (hX.parents.bounds hM.1 hP).1
  have hw := omega_isOrdinal_d hM hC.omega
  have hAt (c v : M.Domain) (hWV : MemPair M W c v) : DifferenceAt M C X.width V P c v := by
    have hc := (hW.graph.bounds hM.1 hWV).1
    have hCellW := (hW.rows c v).mp hWV
    classical
    by_cases hSome : ∃ p, MemPair M P c p
    · obtain ⟨p,hCP⟩ := hSome
      obtain ⟨x,hx,hCX⟩ := hV.graph.total c hc
      obtain ⟨y,hy,hPY⟩ := hV.graph.total p (hForest.bounds hM.1 hCP).2
      have hOldP : CopiedMountain.ParentAt M X r c p := ⟨P,(hX.parents.bounds hM.1 hP).2,hP,hCP⟩
      have hSum := ((hV.rows c x).mp hCX).parent_sum_d hM hD hH
        ((grid_parent_iff_d hM hC hX hB hParents).mpr hOldP) hSucc hCellW ((hV.rows p y).mp hPY)
      have hv := (hW.graph.bounds hM.1 hWV).2
      have hDiff := truncated_difference_of_sum_d hM hC hy hv
        (natural_sum_comm_d hM hC hv hy ((hPlus.add_iff_sum hM hv hy).mp hSum))
      exact Or.inr ⟨p,(hForest.bounds hM.1 hCP).2,x,hx,y,hy,hCP,hCX,hPY,hDiff⟩
    · obtain ⟨height,hh,hHeight⟩ := hX.heights.total c hc
      have hNot : ¬M.mem r height := by
        intro hlt
        obtain ⟨p,F,_,hRow,hParent⟩ := (hX.source r c height hHeight).mpr hlt
        have he := hX.parents.unique r F P hRow hP
        exact hSome ⟨p,he ▸ hParent⟩
      have hHS : M.mem height s := by
        rcases hw.wellOrder.linear.compare height hh r hr with he | hlt | hgt
        · exact (hM.1.eq_of_same_members height r he).symm ▸ hSucc.predecessor_mem
        · exact (hSucc height).mpr (Or.inl hlt)
        · exact False.elim (hNot hgt)
      exact Or.inl ⟨fun p _ hP => hSome ⟨p,hP⟩,hCellW.absent_d hM hD hH hHeight hHS⟩
  refine ⟨hW.graph,fun c v => ?_⟩
  constructor
  · intro hWV
    exact ⟨(hW.graph.bounds hM.1 hWV).1,hAt c v hWV⟩
  · rintro ⟨hc,hDiff⟩
    obtain ⟨v',_,hWV⟩ := hW.graph.total c hc
    have he := difference_at_unique_d hM hC hV.graph hForest hDiff (hAt c v' hWV)
    exact he.symm ▸ hWV

/-- 差分已由实际重建解除；这里只剩明确的最近更小选择接口供复制几何证明。 -/
theorem row_next_iff_selection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H r s V W P Q : M.Domain}
    (hTop : Graph M Top X.width C.omega)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hV : RowValues M (grid C X Top Pairs Plus B Parents) H r V)
    (hW : RowValues M (grid C X Top Pairs Plus B Parents) H s W)
    (hP : MemPair M X.parents r P) (hSucc : M.SuccessorOf s r) :
    RowNext M C X.width V P W Q ↔ Selects true M C X.width P W Q :=
  ⟨fun h => h.selection,fun h => ⟨hV.difference_d hM hC hPlus hX hTop hB hParents hH hW hP hSucc,h⟩⟩

end KP1Y.OneYFinite.ReconstructionCanonical
