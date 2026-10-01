import KP1Y.OneYOrdinaryForestTransport
import KP1Y.OneYReconstructionCanonical

/-! 普通复制的实际值图/有限列历史，以及重建值与真实源数值行的全ω精确等价。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Ordinary
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Naturals
open KP1Y.OneYFinite.CopyCoordinates
open KP1Y.OneYFinite.MountainReconstruction
open KP1Y.OneYFinite.ReconstructionCanonical
universe u

private def valueCopyAtFormula {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : Context (Project.Term d)) (V c v : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
    (.conj (OrdinaryCoordinates.decodedFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken c.weaken.weaken (.bound 1) (.bound 0))
      (memPairFormula V.weaken.weaken (.bound 1) v.weaken.weaken)))

private def valueCopyEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (V : M.Domain) : Env M 16 :=
  (((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push V

private def valueCopySchema : Project.Delta0BinarySchema 16 where
  body := valueCopyAtFormula ⟨.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩
    ⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ ⟨.bound 6,.bound 5,.bound 4,.bound 3⟩ (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [valueCopyAtFormula,OrdinaryCoordinates.decodedFormula,copyPositionFormula,mulAtFormula,addAtFormula,
      ExpressionData.weaken,ExpressionData.map,MatrixArithmetic.weaken,MatrixArithmetic.map,Context.weaken,Context.map,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula]
  delta0 := .existsMem _ (.existsMem _ (.conj (OrdinaryCoordinates.decodedFormula_delta0 _ _ _ _ _ _) (memPairFormula_delta0 _ _ _)))

private theorem valueCopySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (V c v : M.Domain) :
    Project.Formula.satisfies (((valueCopyEnv C T A V).push c).push v) valueCopySchema.body ↔
      ∃s, M.mem s C.omega ∧ ∃b, M.mem b C.omega ∧ OrdinaryCoordinates.Decoded M C T A c s b ∧ MemPair M V s v := by
  simp only [valueCopySchema,valueCopyAtFormula,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,OrdinaryCoordinates.decodedFormula_iff he,memPairFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Context.eval_weaken,Term.eval_weaken]
  rfl

/-- 只复制所需有限列，允许Range为实际有限列历史集，不需要无限函数空间。 -/
theorem value_copies_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m V n Range : M.Domain} (hV : Graph M V m Range)
    (hn : M.mem n C.omega)
    (hBound : ∀c, M.mem c n → ∀s b, OrdinaryCoordinates.Decoded M C T A c s b → M.mem s m) :
    ∃W, ValueCopies M C T A V n Range W := by
  obtain ⟨W,hSupport,hRaw⟩ := relation_comprehension_d hM valueCopySchema (valueCopyEnv C T A V) n Range
  have hRows (c s b : M.Domain) (hDec : OrdinaryCoordinates.Decoded M C T A c s b) (v : M.Domain) :
      MemPair M W c v ↔ M.mem c n ∧ MemPair M V s v := by
    rw [hRaw c v,valueCopySchema_iff hM.1]
    constructor
    · rintro ⟨hc,_,s',_,b',_,hDec',hVAt⟩
      exact ⟨hc,(hDec'.unique_d hM hC hT hA hDec).1 ▸ hVAt⟩
    · rintro ⟨hc,hVAt⟩
      exact ⟨hc,(hV.bounds hM.1 hVAt).2,s,hDec.2.1,b,hDec.2.2.1,hDec,hVAt⟩
  refine ⟨W,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA
      ((omega_isOrdinal_d hM hC.omega).transitive n hn c hc)
    obtain ⟨v,hv,hAt⟩ := hV.total s (hBound c hc s b hDec)
    exact ⟨v,hv,(hRows c s b hDec v).mpr ⟨hc,hAt⟩⟩
  · intro c v v' hAt hAt'
    obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA
      ((omega_isOrdinal_d hM hC.omega).transitive n hn c ((hRaw c v).mp hAt).1)
    exact hV.unique s v v' ((hRows c s b hDec v).mp hAt).2 ((hRows c s b hDec v').mp hAt').2

theorem ValueCopies.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {V n Range W W' : M.Domain} (hn : M.mem n C.omega)
    (h : ValueCopies M C T A V n Range W) (h' : ValueCopies M C T A V n Range W') : W=W' := by
  apply h.graph.ext hM.1 h'.graph
  intro c hc v
  obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA
    ((omega_isOrdinal_d hM hC.omega).transitive n hn c hc)
  exact (h.rows c s b hDec v).trans (h'.rows c s b hDec v).symm

theorem Copies.source_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n c s b : M.Domain} (hCopy : Copies M C T A X n Y) (hc : M.mem c n)
    (hDec : OrdinaryCoordinates.Decoded M C T A c s b) : M.mem s X.width := by
  obtain ⟨h,_,hHeight⟩ := hY.heights.total c (hCopy.width.symm ▸ hc)
  obtain ⟨_,s',_,b',_,hDec',hOld⟩ := (hCopy.heights c h).mp hHeight
  exact (hDec'.unique_d hM hC hT hA hDec).1 ▸ (hX.heights.bounds hM.1 hOld).1

theorem Copies.value_copies_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n V Range : M.Domain} (hCopy : Copies M C T A X n Y) (hV : Graph M V X.width Range) :
    ∃W, ValueCopies M C T A V n Range W :=
  KP1Y.OneYFinite.CopiedMountain.Ordinary.value_copies_exists_d hM hC hT hA hV (hCopy.width ▸ hY.width)
    (fun _c hc _s _b hDec => hCopy.source_bound_d hM hC hT hA hX hY hc hDec)

theorem copied_grid_cell_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {A : Context M.Domain}
    {m n : M.Domain} {R : RowStateSpace M.Domain} {Run B G J : M.Domain}
    {Y : Data M.Domain} {Top Pairs Plus Parents c s block r v : M.Domain}
    (hG : Graph M G m C.sequences)
    (hColumns : ∀c f, MemPair M G c f ↔ M.mem c m ∧ OriginalColumn M C R Run B c f)
    (hJ : ValueCopies M C T A G n C.sequences J) (hc : M.mem c n)
    (hDec : OrdinaryCoordinates.Decoded M C T A c s block) :
    Reconstruction.ValidCell M (grid C Y Top Pairs Plus B Parents) J c r v ↔
      M.mem r B ∧ RowValue M R.states R.values R.forests Run r s v := by
  constructor
  · rintro ⟨f,_,hCf,_,hRv⟩
    have hSf := ((hJ.rows c s block hDec f).mp hCf).2
    exact (((hColumns s f).mp hSf).2.rows r v).mp hRv
  · intro h
    obtain ⟨f,_,hCf⟩ := hJ.graph.total c hc
    have hSf := ((hJ.rows c s block hDec f).mp hCf).2
    have hCol := ((hColumns s f).mp hSf).2
    exact ⟨f,(hG.bounds he hSf).2,hCf,hCol.graph,(hCol.rows r v).mpr h⟩

private theorem source_value_above_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P Run c height r v : M.Domain} (hRun : RowRun M C m R V P Run)
    (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hHeight : MemPair M X.heights c height) (hr : M.mem r C.omega) (hAbove : M.mem height r)
    (hValue : RowValue M R.states R.values R.forests Run r c v) : v=C.zero := by
  apply Classical.byContradiction
  intro hNot
  obtain ⟨a,_,hA⟩ := hRun.base.values.total c (hValue.bounds hM.1 hRun.space).1
  have hv := (hValue.bounds hM.1 hRun.space).2
  have hLe := (hRun.live_iff_le_height_d hM hC hA (hPositive c a hA)
    ((hFrom.heights.rows c height).mp hHeight).2 hr).mp ⟨v,hv,hValue,(hC.zero_mem_iff hM hv).mpr hNot⟩
  rcases hLe with he | hrh
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) height (he ▸ hAbove)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) height
      (((omega_isOrdinal_d hM hC.omega).mem (hX.heights.bounds hM.1 hHeight).2).transitive r hrh height hAbove)

/-- 按source0复制的真实源列历史满足目标网格的全部重建方程。 -/
theorem Copies.copied_reconstructs_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top Top' n B Parents G J : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top)
    (hTopCopy : ValueCopies M C T A Top n C.omega Top')
    (hB : SequenceBound M C Y.width Y.heights B) (hParents : Prefix M Parents Y.parents B Y.forests)
    (hG : Graph M G m C.sequences)
    (hColumns : ∀c f, MemPair M G c f ↔ M.mem c m ∧ OriginalColumn M C R Run B c f)
    (hJ : ValueCopies M C T A G n C.sequences J) :
    Reconstruction.Reconstructs M (grid C Y Top' Pairs Plus B Parents) J := by
  have hTopGraph : Graph M Top' Y.width C.omega := hCopy.width.symm ▸ hTopCopy.graph
  have hD := grid_valid_d hM hC hY hTopGraph hPlus hB hParents
  have hCells := fun c s block r v hc hDec => copied_grid_cell_iff (Y := Y) (Top := Top') (Pairs := Pairs)
    (Plus := Plus) (Parents := Parents) (r := r) (v := v) hM.1 hG hColumns hJ hc hDec (c := c) (s := s) (block := block)
  refine ⟨(show Graph M J Y.width C.sequences from hCopy.width.symm ▸ hJ.graph),?_⟩
  intro c hc f _ hCf
  have hcN : M.mem c n := hCopy.width ▸ hc
  obtain ⟨s,block,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA
    ((omega_isOrdinal_d hM hC.omega).transitive Y.width hY.width c hc)
  have hsM : M.mem s m := hFrom.width ▸ hCopy.source_bound_d hM hC hT hA hX hY hcN hDec
  have hSf := ((hJ.rows c s block hDec f).mp hCf).2
  have hCol := ((hColumns s f).mp hSf).2
  have hsLast := hDec.source_lt_last_d hM hC hT hA
  have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
  have hSourceHeight (height : M.Domain) (hHeight : MemPair M Y.heights c height) : MemPair M X.heights s height :=
    (Height.parent_copy_iff_d hM hC hT hA hsLast hMap).mp ((hCopy.heights c height).mp hHeight).2
  refine ⟨hCol.graph,?_,?_,?_⟩
  · intro height hh top _ hHeight hTopAt
    have hSourceTop := ((hTopCopy.rows c s block hDec top).mp hTopAt).2
    obtain ⟨height',_,hHeight',hValue⟩ := (hTop.rows s top).mp hSourceTop
    have he := hX.heights.unique s height' height hHeight' (hSourceHeight height hHeight)
    subst height'
    exact (hCol.rows height top).mpr ⟨hh,hValue⟩
  · intro height _ hHeight r hr v _ hRv hAbove
    exact source_value_above_height_d hM hC hRun hPositive hX hFrom (hSourceHeight height hHeight)
      ((omega_isOrdinal_d hM hC.omega).transitive B hB.1.1 r hr) hAbove ((hCol.rows r v).mp hRv).2
  · intro height hh hHeight r hr next hNext u _ v _ a _ hSucc hU hV hContrib
    have hrB := ((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive height hh r hr
    have hrω := (omega_isOrdinal_d hM hC.omega).transitive B hB.1.1 r hrB
    have hUValue := ((hCol.rows r u).mp hU).2
    have hVValue := ((hCol.rows next v).mp hV).2
    obtain ⟨pTarget,hPTarget,hAValue⟩ : ∃p, Reconstruction.ParentAt M (grid C Y Top' Pairs Plus B Parents) r c p ∧
        Reconstruction.ValidCell M (grid C Y Top' Pairs Plus B Parents) J p r a := by
      rcases hContrib with ⟨p,_,hP,hPrevious⟩ | ⟨_,hNone⟩
      · refine ⟨p,hP,?_⟩
        rcases hPrevious with hCell | ⟨_,hNoValue⟩
        · exact hCell
        · obtain ⟨fP,hfP,hPf⟩ := hJ.graph.total p (hCopy.width ▸ (hP.bounds hM.1 hD).2.2.1)
          obtain ⟨ps,pb,hPDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA
            ((omega_isOrdinal_d hM hC.omega).transitive Y.width hY.width p (hP.bounds hM.1 hD).2.2.1)
          have hPCol := ((hColumns ps fP).mp ((hJ.rows p ps pb hPDec fP).mp hPf).2).2
          obtain ⟨x,hx,hRX⟩ := hPCol.graph.total r hrB
          exact False.elim (hNoValue x hx ⟨fP,hfP,hPf,hPCol.graph,hRX⟩)
      · obtain ⟨p,hP⟩ := (hD.live r hrB c hc height hHeight).mpr hr
        exact False.elim (hNone p (hP.bounds hM.1 hD).2.2.2 hP)
    have hPY := (grid_parent_iff_d hM hC hY hB hParents).mp hPTarget
    obtain ⟨p,_,hPX,hMapP⟩ := (parent_parent_copy_iff_d hM hC hT hA hX hsLast hMap).mp ((hCopy.parents r c pTarget).mp hPY).2
    have hpLast := ((omega_isOrdinal_d hM hC.omega).mem hA.last).transitive s hsLast p (hPX.bounds hM.1 hX).2.2.2
    obtain ⟨pb,hPDec⟩ := OrdinaryCoordinates.decoded_parent_copy_d hM hC hT hA hpLast hMapP
    have hAValue' := ((hCells pTarget p pb r a (hCopy.width ▸ (hPY.bounds hM.1 hY).2.2.1) hPDec).mp hAValue).2
    obtain ⟨W,Q,hAt,hEdge⟩ := (hFrom.parent_iff hM.1 hX r s p).mp hPX
    exact row_parent_sum_d hM hC hPlus hRun hAt hEdge hSucc hUValue hVValue hAValue'


/-- 任意实际重建历史的全ω补零读取，精确等于普通source0处的真实源行值。 -/
theorem Copies.padded_cell_source_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top Top' n B Parents H r c s block v : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top)
    (hTopCopy : ValueCopies M C T A Top n C.omega Top')
    (hB : SequenceBound M C Y.width Y.heights B) (hParents : Prefix M Parents Y.parents B Y.forests)
    (hH : Reconstruction.Reconstructs M (grid C Y Top' Pairs Plus B Parents) H)
    (hr : M.mem r C.omega) (hc : M.mem c n) (hDec : OrdinaryCoordinates.Decoded M C T A c s block) :
    PaddedCell M (grid C Y Top' Pairs Plus B Parents) H r c v ↔ RowValue M R.states R.values R.forests Run r s v := by
  classical
  obtain ⟨G,hG,hColumns⟩ := original_columns_exists_d hM hC hRun hB.1.1
  obtain ⟨J,hJ⟩ := hCopy.value_copies_exists_d hM hC hT hA hX hY (hFrom.width.symm ▸ hG)
  have hReconstruct := hCopy.copied_reconstructs_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hB hParents hG hColumns hJ
  have hD := grid_valid_d hM hC hY (hCopy.width.symm ▸ hTopCopy.graph) hPlus hB hParents
  have hEq := Reconstruction.reconstruction_unique_d hM hD hH hReconstruct
  subst H
  have hCell := copied_grid_cell_iff (Y := Y) (Top := Top') (Pairs := Pairs) (Plus := Plus) (Parents := Parents)
    (r := r) (v := v) hM.1 hG hColumns hJ hc hDec
  have hcY : M.mem c Y.width := hCopy.width.symm ▸ hc
  by_cases hrB : M.mem r B
  · constructor
    · intro h
      rcases h.2.2 with hCell' | hOut
      · exact (hCell.mp hCell').2
      · exact False.elim (hOut.1 hrB)
    · intro h
      exact ⟨hr,hcY,Or.inl (hCell.mpr ⟨hrB,h⟩)⟩
  · obtain ⟨height,hh,hHeight⟩ := hY.heights.total c hcY
    have hhB := hB.1.2.2 c hcY height hh hHeight
    have hAbove : M.mem height r := by
      rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare height hh r hr with he | hlt | hlt
      · exact False.elim (hrB (hM.1.eq_of_same_members height r he ▸ hhB))
      · exact hlt
      · exact False.elim (hrB (((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive height hhB r hlt))
    have hsLast := hDec.source_lt_last_d hM hC hT hA
    have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
    have hOldHeight := (Height.parent_copy_iff_d hM hC hT hA hsLast hMap).mp ((hCopy.heights c height).mp hHeight).2
    have hsM := hFrom.width ▸ (hX.heights.bounds hM.1 hOldHeight).1
    have hZero := fun w hValue => source_value_above_height_d hM hC hRun hPositive hX hFrom hOldHeight hr hAbove hValue (v := w)
    constructor
    · intro h
      rcases h.2.2 with hCell' | ⟨_,he⟩
      · exact False.elim (hrB (hCell'.bounds hM.1).1)
      · obtain ⟨w,_,hValue⟩ := hRun.value_exists_d hM hC hr hsM
        exact (he.symm ▸ hZero w hValue) ▸ hValue
    · intro h
      exact ⟨hr,hcY,Or.inr ⟨hrB,hZero v h⟩⟩

theorem row_value_at_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run r W Q c v : M.Domain}
    (hRun : RowRun M C m R V P Run) (hAt : RowAt M R.states Run r W Q) :
    RowValue M R.states R.values R.forests Run r c v ↔ MemPair M W c v := by
  constructor
  · rintro ⟨W',_,Q',_,hAt',hValue⟩
    exact (hRun.at_unique he hAt' hAt).1 ▸ hValue
  · intro hValue
    have hSaved := hAt
    obtain ⟨state,hState,_,hCode⟩ := hAt
    obtain ⟨W',hW',Q',hQ',hCode'⟩ := (hRun.space.states state).mp hState
    obtain ⟨heW,heQ⟩ := codes_injective he hCode' hCode
    subst W'
    subst Q'
    exact ⟨W,hW',Q,hQ',hSaved,hValue⟩

theorem Copies.row_values_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top Top' n B Parents H r W Q W' : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top)
    (hTopCopy : ValueCopies M C T A Top n C.omega Top')
    (hB : SequenceBound M C Y.width Y.heights B) (hParents : Prefix M Parents Y.parents B Y.forests)
    (hH : Reconstruction.Reconstructs M (grid C Y Top' Pairs Plus B Parents) H)
    (hr : M.mem r C.omega) (hAt : RowAt M R.states Run r W Q)
    (hW' : RowValues M (grid C Y Top' Pairs Plus B Parents) H r W') : ValueCopies M C T A W n C.omega W' := by
  refine ⟨(show Graph M W' n C.omega from hCopy.width ▸ hW'.graph),?_⟩
  intro c s block hDec v
  by_cases hc : M.mem c n
  · rw [hW'.rows c v,hCopy.padded_cell_source_iff_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hB hParents hH hr hc hDec,
      row_value_at_iff hM.1 hRun hAt]
    exact ⟨fun h => ⟨hc,h⟩,And.right⟩
  · exact ⟨fun h => False.elim (hc (hCopy.width ▸ (hW'.graph.bounds hM.1 h).1)),fun h => False.elim (hc h.1)⟩

/-- 给通用恢复器的逐行选择接口；目标Selects完全由源运行计算得出。 -/
theorem Copies.reconstruction_selects_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top Top' n B Parents H r next W' F' Q' : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R V Run X)
    (hCopy : Copies M C T A X n Y) (hTop : TopValueGraph M C m R Run X.heights Top)
    (hTopCopy : ValueCopies M C T A Top n C.omega Top')
    (hB : SequenceBound M C Y.width Y.heights B) (hParents : Prefix M Parents Y.parents B Y.forests)
    (hH : Reconstruction.Reconstructs M (grid C Y Top' Pairs Plus B Parents) H)
    (hr : M.mem r C.omega) (hSucc : M.SuccessorOf next r)
    (hW' : RowValues M (grid C Y Top' Pairs Plus B Parents) H next W')
    (hF' : MemPair M Y.parents r F') (hQ' : MemPair M Y.parents next Q') : Selects true M C Y.width F' W' Q' := by
  obtain ⟨U,F,hAt⟩ := hRun.at_exists_d hr
  have hNextNat := natural_successor_mem_d hM hC hr hSucc
  obtain ⟨W,Q,hAtNext⟩ := hRun.at_exists_d hNextNat
  have hF := (hFrom.parents r F).mpr ⟨U,hAt⟩
  have hQ := (hFrom.parents next Q).mpr ⟨W,hAtNext⟩
  have hValues := hCopy.row_values_copy_d hM hC hT hA hPlus hRun hPositive hX hY hFrom hTop hTopCopy hB hParents hH hNextNat hAtNext hW'
  have hSelect : Selects true M C X.width F W Q := hFrom.width.symm ▸ (hRun.at_next hM.1 hSucc hAt hAtNext).selection
  exact hCopy.selects_d hM true hC hT hA hX hY hF hF' hQ hQ' hValues hSelect

end KP1Y.OneYFinite.CopiedMountain.Ordinary
