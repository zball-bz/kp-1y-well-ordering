import KP1Y.OneYLowerBottomZero

/-! Lower底行的实际恢复（原 `restrictedParent_bottom_numeric`）：目标第0行父图恰为在继承帧
FrameCopy F 上对实际重建底值的最右较小选择。三种列：原列、无源父复制列（底值为1）、有源父复制列（阻挡）。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
open KP1Y.OneYFinite.MountainReconstruction KP1Y.OneYFinite.ReconstructionCanonical
universe u

/-- 原列 c<last：目标底行父项与帧复制选择都逐字等于源的帧选择。 -/
theorem bottom_original_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    (hCopy : Copies M C T D Y.width Y) (hKept : M.MemberSubset D.coordinates.last Y.width)
    {m : M.Domain} {R : RowStateSpace M.Domain} {W Q J : M.Domain}
    (hRun : RowRun M C m R W Q J) (hFrom : FromRun M C m R W J D.mountain)
    {Bottom F N F' P0 : M.Domain} (hBotW : RowsAgreeOn M Bottom W D.coordinates.last)
    (hSel : Selects true M C m F W Q) (hFC : FrameCopy.Copies M C T D.coordinates F N Y.width F')
    (hP0 : MemPair M Y.parents C.zero P0) {c : M.Domain} (hcLast : M.mem c D.coordinates.last) (p : M.Domain) :
    MemPair M P0 c p ↔ RestrictedParent true M C Y.width F' Bottom c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hQ0 : MemPair M D.mountain.parents C.zero Q := (hFrom.parents C.zero Q).mpr ⟨W,hRun.initial_row_at_d hM⟩
  have hLastM : M.mem D.coordinates.last m := hFrom.width ▸ hD.last
  have hLastSub : M.MemberSubset D.coordinates.last m := fun a ha => (hw.mem hRun.space.width).transitive _ hLastM a ha
  have hF'F : RowsAgreeOn M F' F D.coordinates.last := fun a ha t =>
    FrameCopy.Copies.original_parent_iff_d hM hC hT hD.coordinates hSel.inherited hFC (Or.inr ha) (hKept a ha) t
  exact (canon_row_parent_iff hM.1 hY hP0).symm.trans
    ((hCopy.original_parents_d hM hC hD (hKept c hcLast) (Or.inr hcLast)).trans
      ((canon_row_parent_iff hM.1 hD.mountain hQ0).trans ((hSel.parents c p).trans
        ((restricted_parent_prefix_iff_d hM true hC hSel.inherited hD.coordinates.last hLastSub hcLast
          (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)).trans
          (restricted_parent_prefix_iff_d hM true hC hFC.forest hD.coordinates.last hKept hcLast hF'F hBotW).symm))))

/-- 源第0行无父的复制列：底值为1（RootsOne与上层fixed），因此既无目标父项也无帧选择。 -/
theorem bottom_encoded_none_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    (hCopy : Copies M C T D Y.width Y) (hKept : M.MemberSubset D.coordinates.last Y.width)
    {m : M.Domain} {R : RowStateSpace M.Domain} {W Q J : M.Domain}
    (hRun : RowRun M C m R W Q J) (hRooted : RootedRow M C m W Q) (hFrom : FromRun M C m R W J D.mountain)
    {oldTop Qnext newTop Bottom : M.Domain}
    (hExtraction : Extraction M C m W Q oldTop Qnext) (hNewTop : Graph M newTop Y.width C.omega)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last) (hFixed : UpperFixed M C T D oldTop Qnext Y.width newTop)
    (hRebuild : Rebuilds M C T.addPairs T.plus Y newTop Bottom) {F' P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) {c s0 b : M.Domain} (hSource : Source M D.coordinates s0)
    (hEnc : Encode M C T D.coordinates s0 b c) (hc : M.mem c Y.width) (hNone : ∀ p0, ¬MemPair M Q s0 p0) :
    (∀ p, ¬MemPair M P0 c p) ∧ ∀ p, ¬RestrictedParent true M C Y.width F' Bottom c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hQ0 : MemPair M D.mountain.parents C.zero Q := (hFrom.parents C.zero Q).mpr ⟨W,hRun.initial_row_at_d hM⟩
  have hNotGood : ¬M.mem s0 D.coordinates.root := fun h =>
    nat_irrefl hM _ ((hw.mem hD.coordinates.root).transitive s0 h _ hSource.1)
  have hMap : ParentCopy M C T D.coordinates b s0 c := (parent_copy_bad_iff hNotGood).mpr hEnc
  constructor
  · intro p hp
    obtain ⟨q,hq,_⟩ := (zero_parent_copy_iff_d hM hC hT hD hCopy hSource hMap hc).mp
      ((canon_row_parent_iff hM.1 hY hP0).mpr hp)
    exact hNone q ((canon_row_parent_iff hM.1 hD.mountain hQ0).mp hq)
  · intro p hRP
    have hs0Last : M.mem s0 D.coordinates.last := by
      rcases hSource.2 with he | hlt
      · exfalso
        have hRootLast := source_root_ancestor_last_d hM hC hD hRun hFrom hQ0 (zero_le_d hM hC (hD.floor_nat hM.1))
        obtain ⟨q,hq,_⟩ := ancestor_parent_cases_d hM hC (hD.mountain.forest C.zero Q hQ0) hRootLast
        exact hNone q (he ▸ hq)
      · exact hlt
    have hs0m : M.mem s0 m := hFrom.width ▸ ((hw.mem hD.mountain.width).transitive D.coordinates.last hD.last s0 hs0Last)
    obtain ⟨w,_,hWs⟩ := hRooted.row.values.total s0 hs0m
    have hw1 : w=C.one := hRooted.rootsOne s0 w hWs (fun q _ hq => hNone q hq)
    have hBot := (good_bottom_value_d hM hC hT hD hY hCopy hKept hRun hRooted.positive hFrom hExtraction hNewTop
      hPrefixTop hFixed hRebuild hSource.1 hs0Last (fun q hq => False.elim (hNone q hq)) hMap hc).mpr hWs
    obtain ⟨_,x,_,y,_,_,hCY,hXY,hPos⟩ := hRP.1
    have hy1 : y=C.one := (hRebuild.graph.unique c y w hCY hBot).trans hw1
    subst hy1
    have hPos' : M.mem C.zero x := by simpa [PositiveValue] using hPos
    rcases (hC.one_succ x).mp hXY with hx0 | hx0
    · exact hC.zero_empty x hx0
    · exact nat_irrefl hM C.zero ((hM.1.eq_of_same_members x C.zero hx0) ▸ hPos')

/-- 源第0行有父 p0 的复制列：目标父项 ParentCopy b p0 正是帧复制上的最右较小选择（阻挡由源帧选择运输）。 -/
theorem bottom_encoded_some_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    (hCopy : Copies M C T D Y.width Y)
    {m : M.Domain} {R : RowStateSpace M.Domain} {W Q J : M.Domain}
    (hRun : RowRun M C m R W Q J) (hPositive : ∀ c a, MemPair M W c a → M.mem C.zero a)
    (hFrom : FromRun M C m R W J D.mountain) {oldTop Qnext newTop : M.Domain}
    (hExtraction : Extraction M C m W Q oldTop Qnext) (hNewTop : Graph M newTop Y.width C.omega)
    (hNewPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last) (hFixed : UpperFixed M C T D oldTop Qnext Y.width newTop)
    (hOrder : ∀ Pseudo, GraphPseudoForest M C D.mountain Pseudo → UpperOrder M C T D Pseudo oldTop newTop)
    {B Parents H Bottom : M.Domain} (hB : SequenceBound M C Y.width Y.heights B)
    (hP : Prefix M Parents Y.parents B Y.forests)
    (hH : Reconstruction.Reconstructs M (grid C Y newTop T.addPairs T.plus B Parents) H)
    (hRow0 : RowValues M (grid C Y newTop T.addPairs T.plus B Parents) H C.zero Bottom)
    (hCanon : ∀ r s V W' F0 Q0, M.mem r C.omega → (C.zero=r ∨ M.mem C.zero r) → M.SuccessorOf s r →
      RowValues M (grid C Y newTop T.addPairs T.plus B Parents) H r V →
      RowValues M (grid C Y newTop T.addPairs T.plus B Parents) H s W' →
      MemPair M Y.parents r F0 → MemPair M Y.parents s Q0 → Selects true M C Y.width F0 W' Q0)
    (hBotPos : ∀ c v, MemPair M Bottom c v → M.mem C.zero v)
    {F N F' P0 : M.Domain} (hSel : Selects true M C m F W Q) (hFC : FrameCopy.Copies M C T D.coordinates F N Y.width F')
    (hP0 : MemPair M Y.parents C.zero P0) {c s0 b p0 : M.Domain} (hSource : Source M D.coordinates s0)
    (hEnc : Encode M C T D.coordinates s0 b c) (hc : M.mem c Y.width) (hQs0 : MemPair M Q s0 p0)
    (hPrefix : ∀ i, M.mem i c → ∀ a, MemPair M P0 i a ↔ RestrictedParent true M C Y.width F' Bottom i a) :
    ∃ p, ParentCopy M C T D.coordinates b p0 p ∧ MemPair M P0 c p ∧ RestrictedParent true M C Y.width F' Bottom c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hTopOld := Expansion.extraction_top_for_source_d hM hC hRun hFrom hExtraction
  have hQ0 : MemPair M D.mountain.parents C.zero Q := (hFrom.parents C.zero Q).mpr ⟨W,hRun.initial_row_at_d hM⟩
  have hNotGood : ¬M.mem s0 D.coordinates.root := fun h =>
    nat_irrefl hM _ ((hw.mem hD.coordinates.root).transitive s0 h _ hSource.1)
  have hMap : ParentCopy M C T D.coordinates b s0 c := (parent_copy_bad_iff hNotGood).mpr hEnc
  have hb := hEnc.2.1
  obtain ⟨Jc,hJc,hRowsJ⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hb
  have hp0m := (hRun.base.forest.bounds hM.1 hQs0).2
  have hp0ω := hw.transitive m hRun.space.width p0 hp0m
  obtain ⟨pp,_,hJp⟩ := hJc.graph.total p0 hp0ω
  have hMapP := (hRowsJ p0 pp).mp hJp
  have hPX : ParentAt M D.mountain C.zero s0 p0 := (canon_row_parent_iff hM.1 hD.mountain hQ0).mpr hQs0
  have hP0c : MemPair M P0 c pp := (canon_row_parent_iff hM.1 hY hP0).mp
    ((zero_parent_copy_iff_d hM hC hT hD hCopy hSource hMap hc).mpr ⟨p0,hPX,hMapP⟩)
  refine ⟨pp,hMapP,hP0c,?_⟩
  have hAncF := ((hSel.parents s0 p0).mp hQs0).1.1
  obtain ⟨q0,hFq0,hq0case⟩ := ancestor_parent_cases_d hM hC hSel.inherited hAncF
  have hq0s : M.mem q0 s0 := hSel.inherited.left s0 q0 hFq0
  have hp0s : M.mem p0 s0 := hRun.base.forest.left s0 p0 hQs0
  have hq0Last := nat_lt_of_lt_of_le hM hC hD.coordinates.last hq0s hSource.2
  have hp0Last := nat_lt_of_lt_of_le hM hC hD.coordinates.last hp0s hSource.2
  have hq0ω := hw.transitive D.coordinates.last hD.coordinates.last q0 hq0Last
  obtain ⟨q',_,hJq⟩ := hJc.graph.total q0 hq0ω
  have hMapQ' := (hRowsJ q0 q').mp hJq
  have hF'c : MemPair M F' c q' := (FrameCopy.Copies.encoded_parent_iff_d hM hC hT hD.coordinates hSel.inherited hFC
    hSource hEnc hc q').mpr ⟨q0,hq0Last,hFq0,hMapQ'⟩
  have hFF := hFC.forest
  have hNum0 := hRow0.numeric_d hM hC hT.add hY hNewTop hNewPos hB hP hH hP0
  have hLastM : M.mem D.coordinates.last m := hFrom.width ▸ hD.last
  have hRootLastQ := source_root_ancestor_last_d hM hC hD hRun hFrom hQ0 (zero_le_d hM hC (hD.floor_nat hM.1))
  have hRootLastF : Ancestor M C m F D.coordinates.root D.coordinates.last :=
    hSel.ancestor_inherited_d hM hC (hFrom.width ▸ hRootLastQ)
  have hAfterP0 : s0=D.coordinates.last → (D.coordinates.root=p0 ∨ M.mem D.coordinates.root p0) := by
    intro he
    subst he
    exact ancestor_le_parent_d hM hC (hD.mountain.forest C.zero Q hQ0) hQs0 hRootLastQ
  have hAncF' := frame_copy_ancestor_d hM hC hT hD.coordinates hSel.inherited hFC hLastM hRootLastF hSource hEnc hc
    hp0Last hAfterP0 hMapP hAncF
  rcases hq0case with he | hAncPQ
  · subst he
    have hqq := parent_copy_unique_d hM hC hT hD.coordinates hMapQ' hMapP
    subst hqq
    exact ReconstructionSelection.restricted_parent_of_direct_d hM hC hNum0 hFF hP0c hF'c
  have hNe : p0≠q0 := fun he => nat_irrefl hM p0 (he ▸ hAncPQ.1)
  obtain ⟨z0,_,hPath0,hZ0P,tc,htc,tz,htz,hTC,hTZ,hKey0⟩ :=
    source_bottom_blocker_d hM hC hRun hPositive hD.mountain hFrom hTopOld hSel hFq0 hQs0 hNe
  have hq'Y : M.mem q' Y.width := (hFF.bounds hM.1 hF'c).2
  have hBlk : BlockerAt M C Y newTop P0 c q' pp C.one := by
    classical
    by_cases hGood : M.mem p0 D.coordinates.root
    · have hpp : pp=p0 := (parent_copy_good_iff hb hp0ω hGood).mp hMapP
      subst hpp
      exact good_blocker_of_source_d hM hC hT hD hY hCopy hRun hFrom hExtraction hPrefixTop hFixed hC.one_succ hQ0 hP0
        hQs0 hGood hSource.1 hSource.2 hMap hc hMapQ' hq0s hPath0 hZ0P htc htz hTC hTZ hKey0
    · refine bad_blocker_of_source_d hM hC hT hD hY hCopy hNewTop hQ0 hq0s hQs0 hGood hPath0 hZ0P hTC hTZ hKey0
        hMap hc hMapQ' ?_ ?_ ?_
      · intro a x hAP _ hAnc hMapA _
        exact zero_ancestor_copy_d hM hC hT hD hY hCopy hRun hFrom hQ0 hP0 hSource hQs0 hAP hGood hAnc hq0s
          hMapA hMapQ' hq'Y
      · intro a x hAP hRootA has hMapA hxY
        have haLast := nat_lt_of_lt_of_le hM hC hD.coordinates.last has hSource.2
        exact (canon_row_parent_iff hM.1 hY hP0).mp
          ((zero_parent_copy_iff_d hM hC hT hD hCopy ⟨hRootA,Or.inr haLast⟩ hMapA hxY).mpr
            ⟨p0,(canon_row_parent_iff hM.1 hD.mountain hQ0).mpr hAP,hMapP⟩)
      · intro a x tc ta tc' ta' hAP hRootA has hMapA _ hTC hTA hTC' hTA' hKey
        exact zero_key_transport_d hM hC hT hD hY hCopy hRun hFrom hOrder hQ0 hQs0 hAP hRootA has hSource.2
          hMap hMapA hc hTC hTA hTC' hTA' hKey
  obtain ⟨z',_,hPathY,hZ'P,tc',_,tz',_,hTC',hTZ',hKeyY⟩ := hBlk
  have hUpper := key_value_le_d hM hC hT.add hY hNewTop hNewPos hB hP hH hCanon hC.zero_nat (Or.inl rfl) hC.one_succ
    hRow0 hP0 hP0c hZ'P hTC' hTZ' hKeyY
  have hZeros : NumericOrder.ZerosAtRoots M Y.width F' Bottom C.zero :=
    fun a _ hZero => False.elim (nat_irrefl hM C.zero (hBotPos a C.zero hZero))
  exact ReconstructionSelection.restricted_parent_of_blocker_d hM hC hNum0 hFF hZeros hF'c hP0c hAncF' hPrefix
    hPathY hZ'P hUpper

end KP1Y.OneYFinite.LowerBlock
