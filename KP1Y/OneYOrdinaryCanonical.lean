import KP1Y.OneYOrdinaryValueTransport
import KP1Y.OneYOrdinaryPseudoTransport
import KP1Y.OneYReconstructionExtraction

/-! 普通复制的真实数值恢复及提取相容。目标数值/选择从源运行推导，不作为输入假设。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Ordinary
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Naturals
open KP1Y.OneYFinite.CopyCoordinates
open KP1Y.OneYFinite.MountainReconstruction
open KP1Y.OneYFinite.ReconstructionCanonical
universe u

theorem ValueCopies.positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {V n W : M.Domain} (hn : M.mem n C.omega)
    (hCopy : ValueCopies M C T A V n C.omega W)
    (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v) : ∀c v, MemPair M W c v → M.mem C.zero v := by
  intro c v hAt
  obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA
    ((omega_isOrdinal_d hM hC.omega).transitive n hn c (hCopy.graph.bounds hM.1 hAt).1)
  exact hPositive s v ((hCopy.rows c s b hDec v).mp hAt).2

/-- 重建得到的实际底行正是源底行的普通source0复制。 -/
theorem Copies.rebuild_values_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top Top' n W : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top)
    (hTopCopy : ValueCopies M C T A Top n C.omega Top') (hRebuild : Rebuilds M C Pairs Plus Y Top' W) :
    ValueCopies M C T A V n C.omega W := by
  obtain ⟨B,Parents,H,hB,hParents,hH,hW⟩ := hRebuild
  have hRow : RowValues M (grid C Y Top' Pairs Plus B Parents) H C.zero W := by
    refine ⟨hW.graph,?_⟩
    intro c v
    rw [hW.rows c v]
    constructor
    · intro hCell
      have hSaved := hCell
      obtain ⟨f,_,hCf,_,_⟩ := hCell
      exact ⟨hC.zero_nat,(hH.graph.bounds hM.1 hCf).1,Or.inl hSaved⟩
    · intro hCell
      exact hCell.2.2.elim id (fun h => False.elim (h.1 hB.1.2.1))
  exact hCopy.row_values_copy_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hB hParents hH
    hC.zero_nat (hRun.initial_row_at_d hM) hRow


/-- 实际重建底图的真实ω行运行、高度和Top都恢复为给定普通复制山形。 -/
theorem Copies.canonical_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top Top' n W : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top)
    (hTopCopy : ValueCopies M C T A Top n C.omega Top') (hRebuild : Rebuilds M C Pairs Plus Y Top' W) :
    ∃R' : RowStateSpace M.Domain, ∃P' Run', RowRun M C Y.width R' W P' Run' ∧
      FromRun M C Y.width R' W Run' Y ∧ TopValueGraph M C Y.width R' Run' Y.heights Top' ∧
      (∀c v, MemPair M W c v → M.mem C.zero v) ∧ ValueCopies M C T A V n C.omega W := by
  have hOldTopPositive : ∀c v, MemPair M Top c v → M.mem C.zero v := by
    intro c v hAt
    obtain ⟨a,_,hA⟩ := hRun.base.values.total c (hTop.graph.bounds hM.1 hAt).1
    exact hTop.positive_d hM hC hRun hFrom.heights hA (hPositive c a hA) hAt
  have hNewTopPositive := hTopCopy.positive_d hM hC hT hA (hCopy.width ▸ hY.width) hOldTopPositive
  obtain ⟨R',P',Run',hRun',hFrom',hTop',hPositive'⟩ := ReconstructionRecovery.rebuild_run_exists_d hM hC hPlus hY
    (hCopy.width.symm ▸ hTopCopy.graph) hNewTopPositive hRebuild
    (fun _B _Parents _H hB hParents hH _r _s _W _F _Q hW hF hQ hSucc =>
      hCopy.reconstruction_selects_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hB hParents hH
        (hY.parents.bounds hM.1 hF).1 hSucc hW hF hQ)
  exact ⟨R',P',Run',hRun',hFrom',hTop',hPositive',hCopy.rebuild_values_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hRebuild⟩


/-- 恢复后的实际数值算法在每个内部ω行、保留列上仍精确读取普通source0。 -/
theorem Copies.run_value_source_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R R' : RowStateSpace M.Domain} {V P Run Top Top' n W P' Run' r c s block v : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top)
    (hTopCopy : ValueCopies M C T A Top n C.omega Top') (hRebuild : Rebuilds M C Pairs Plus Y Top' W)
    (hRun' : RowRun M C Y.width R' W P' Run') (hP' : MemPair M Y.parents C.zero P')
    (hr : M.mem r C.omega) (hc : M.mem c n) (hDec : OrdinaryCoordinates.Decoded M C T A c s block) :
    RowValue M R'.states R'.values R'.forests Run' r c v ↔ RowValue M R.states R.values R.forests Run r s v := by
  obtain ⟨B,Parents,H,hB,hParents,hH,hW⟩ := hRebuild
  have hBase : RowValues M (grid C Y Top' Pairs Plus B Parents) H C.zero W := by
    refine ⟨hW.graph,?_⟩
    intro c v
    rw [hW.rows c v]
    constructor
    · intro hCell
      have hSaved := hCell
      obtain ⟨f,_,hCf,_,_⟩ := hCell
      exact ⟨hC.zero_nat,(hH.graph.bounds hM.1 hCf).1,Or.inl hSaved⟩
    · exact fun h => h.2.2.elim id (fun h => False.elim (h.1 hB.1.2.1))
  obtain ⟨U,Q,hAt⟩ := hRun'.at_exists_d hr
  have hRow := (ReconstructionRecovery.row_run_reads_d hM hC hPlus hY (hCopy.width.symm ▸ hTopCopy.graph)
    hB hParents hH hRun' hBase hP'
    (fun _r _s _V _W _F _Q hr hSucc _ hW hF hQ =>
      hCopy.reconstruction_selects_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hB hParents hH hr hSucc hW hF hQ) hAt).1
  exact (row_value_at_iff hM.1 hRun' hAt).trans ((hRow.rows c v).trans
    (hCopy.padded_cell_source_iff_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hB hParents hH hr hc hDec))

/-- 同时实际构造复制Top、重建底图和完整数值运行。 -/
theorem Copies.canonical_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top n : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top) :
    ∃Top' W, ValueCopies M C T A Top n C.omega Top' ∧ Rebuilds M C Pairs Plus Y Top' W ∧
      ∃R' : RowStateSpace M.Domain, ∃P' Run', RowRun M C Y.width R' W P' Run' ∧
        FromRun M C Y.width R' W Run' Y ∧ TopValueGraph M C Y.width R' Run' Y.heights Top' ∧
        (∀c v, MemPair M W c v → M.mem C.zero v) ∧ ValueCopies M C T A V n C.omega W := by
  obtain ⟨Top',hTopCopy⟩ := hCopy.value_copies_exists_d hM hC hT hA hX hY (hFrom.width.symm ▸ hTop.graph)
  obtain ⟨W,hW⟩ := rebuild_exists_d hM hC hPlus hY (hCopy.width.symm ▸ hTopCopy.graph)
  exact ⟨Top',W,hTopCopy,hW,hCopy.canonical_run_exists_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hW⟩


/-- 对实际源提取结果，目标实际提取仍由同一普通复制坐标给出。 -/
theorem Copies.extraction_copy_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top Top' n W Q : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top)
    (hTopCopy : ValueCopies M C T A Top n C.omega Top') (hRebuild : Rebuilds M C Pairs Plus Y Top' W)
    (hExtraction : Extraction M C m V P Top Q) :
    ∃P' Q', MemPair M Y.parents C.zero P' ∧ Extraction M C Y.width W P' Top' Q' ∧ ForestCopies M C T A n Q Q' := by
  obtain ⟨R',P',Run',hRun',hFrom',hTop',_,_⟩ := hCopy.canonical_run_exists_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hRebuild
  obtain ⟨F,QSource,hF,hSelected,hSourceExtraction⟩ := ReconstructionExtraction.extraction_graph_exists_d hM hC hRun hX hFrom hTop
  have hQQ := (hSourceExtraction.unique_d hM hC hExtraction).2
  subst QSource
  obtain ⟨G,hG⟩ := graph_pseudo_forest_exists_d hM hC hY
  obtain ⟨Q',hQ',hCopiedQ⟩ := hCopy.pseudo_selection_exists_d hM hC hT hA hX hY hF hG hTopCopy (hFrom.width.symm ▸ hSelected)
  exact ⟨P',Q',(hFrom'.parents C.zero P').mpr ⟨W,hRun'.initial_row_at_d hM⟩,
    ReconstructionExtraction.extraction_from_graph_d hM hC hRun' hY hFrom' hTop' hG hQ',hCopiedQ⟩

/-- 任意实际运行得到的目标提取结果都满足复制公式，而非只为某个挑选的输出成立。 -/
theorem Copies.extraction_commutes_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top Top' n W Q P' ActualTop Q' : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top)
    (hTopCopy : ValueCopies M C T A Top n C.omega Top') (hRebuild : Rebuilds M C Pairs Plus Y Top' W)
    (hSource : Extraction M C m V P Top Q) (hP' : MemPair M Y.parents C.zero P')
    (hTarget : Extraction M C Y.width W P' ActualTop Q') :
    ActualTop=Top' ∧ ValueCopies M C T A Top n C.omega ActualTop ∧ ForestCopies M C T A n Q Q' := by
  obtain ⟨PNew,QNew,hPNew,hExtraction,hQCopy⟩ := hCopy.extraction_copy_exists_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hRebuild hSource
  have hPP := hY.parents.unique C.zero PNew P' hPNew hP'
  subst PNew
  obtain ⟨hTopEq,hQEq⟩ := hExtraction.unique_d hM hC hTarget
  subst QNew
  exact ⟨hTopEq.symm,hTopEq ▸ hTopCopy,hQCopy⟩

/-- 完整实际工厂：复制Top、重建底行、重新运行和提取全部实际存在并满足普通复制。 -/
theorem Copies.canonical_extraction_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top n Q : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top)
    (hSource : Extraction M C m V P Top Q) :
    ∃Top' W P' Q', ValueCopies M C T A Top n C.omega Top' ∧ Rebuilds M C Pairs Plus Y Top' W ∧
      ValueCopies M C T A V n C.omega W ∧ MemPair M Y.parents C.zero P' ∧
      Extraction M C Y.width W P' Top' Q' ∧ ForestCopies M C T A n Q Q' := by
  obtain ⟨Top',hTopCopy⟩ := hCopy.value_copies_exists_d hM hC hT hA hX hY (hFrom.width.symm ▸ hTop.graph)
  obtain ⟨W,hW⟩ := rebuild_exists_d hM hC hPlus hY (hCopy.width.symm ▸ hTopCopy.graph)
  obtain ⟨P',Q',hP',hExtraction,hQCopy⟩ := hCopy.extraction_copy_exists_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hW hSource
  exact ⟨Top',W,P',Q',hTopCopy,hW,hCopy.rebuild_values_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hW,hP',hExtraction,hQCopy⟩

end KP1Y.OneYFinite.CopiedMountain.Ordinary
