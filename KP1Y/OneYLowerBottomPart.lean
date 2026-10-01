import KP1Y.OneYLowerBottomSelect

/-! Lower底行恢复的汇合（原 `restrictedParent_bottom_numeric`）：对内部列号作对象归纳，
解除严格左前缀；给出 `LowerLayer.BottomPart` 字段形状的实际定理。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
open KP1Y.OneYFinite.MountainReconstruction KP1Y.OneYFinite.ReconstructionCanonical
universe u

private def bottomEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m F V Q : M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push F).push V).push Q

private def bottomSchema : Project.UnarySchema 9 where
  body := .forallE (.iff (memPairFormula (.bound 2) (.bound 1) (.bound 0))
    (restrictedParentFormula true ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 0)))
  freeClosed := by
    have hRestricted := restrictedParentFormula_freeClosed true
      (show (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hRestricted,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem]

private theorem bottomSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m F V Q c : M.Domain) :
    Project.Formula.satisfies ((bottomEnv C m F V Q).push c) bottomSchema.body ↔
      ∀ p, MemPair M Q c p ↔ RestrictedParent true M C m F V c p := by
  simp only [bottomSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    memPairFormula_iff he,restrictedParentFormula_iff he]
  rfl

/-- 输出宽度保留原末列以前的全部列。 -/
theorem width_kept_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {N n : M.Domain} (hN : Width M C T A N n) :
    M.MemberSubset A.last n := by
  obtain ⟨_,_,off,hOff,_,hAdd⟩ := hN
  exact sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hA.last) ((hT.add.add_iff_sum hM hA.last hOff).mp hAdd)

/-- 原 `restrictedParent_bottom_numeric`：目标第0行父图恰为帧复制 F' 上对实际重建底值的选择。
输入：源实际运行与帧选择、上层 `prefixTop/fixed/order`、本层 `PseudoTopBound`。 -/
theorem bottom_select_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) (hKept : M.MemberSubset D.coordinates.last n)
    {m : M.Domain} {R : RowStateSpace M.Domain} {W Q J : M.Domain}
    (hRun : RowRun M C m R W Q J) (hRooted : RootedRow M C m W Q) (hFrom : FromRun M C m R W J D.mountain)
    {oldTop Qnext newTop Bottom : M.Domain}
    (hExtraction : Extraction M C m W Q oldTop Qnext) (hNewTop : Graph M newTop n C.omega)
    (hNewPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last) (hFixed : UpperFixed M C T D oldTop Qnext n newTop)
    (hOrder : ∀ Pseudo, GraphPseudoForest M C D.mountain Pseudo → UpperOrder M C T D Pseudo oldTop newTop)
    (hBound : ReconstructionSelection.PseudoTopBound M C Y newTop)
    (hRebuild : Rebuilds M C T.addPairs T.plus Y newTop Bottom)
    {F N F' P0 : M.Domain} (hSel : Selects true M C m F W Q) (hFC : FrameCopy.Copies M C T D.coordinates F N n F')
    (hP0 : MemPair M Y.parents C.zero P0) : Selects true M C n F' Bottom P0 := by
  have hn := hCopy.width
  subst hn
  have hw := omega_isOrdinal_d hM hC.omega
  have hPositive := hRooted.positive
  have hTopOld := Expansion.extraction_top_for_source_d hM hC hRun hFrom hExtraction
  have hBlockers := lower_decorated_blockers_d hM hC hT hD hY hCopy hRun hPositive hFrom hExtraction hNewTop
    hPrefixTop hFixed hOrder
  have hNested := hCopy.nested_d hM hC hT hD hY hRun hFrom
  obtain ⟨_,_,_,_,_,_,hBotPos⟩ := ReconstructionRecovery.structural_rebuild_run_exists_d hM hC hT.add hY hNewTop hNewPos
    hRebuild hNested hBound hBlockers
  have hBotW := hCopy.rebuild_prefix_d hM hC hT.add hD hY hRun hPositive hFrom hTopOld hNewTop hKept hPrefixTop hRebuild
  obtain ⟨B,Parents,H,hB,hP,hH,hBot⟩ := id hRebuild
  have hRow0 : RowValues M (grid C Y newTop T.addPairs T.plus B Parents) H C.zero Bottom := by
    refine ⟨hBot.graph,?_⟩
    intro c v
    rw [hBot.rows c v]
    constructor
    · intro hCell
      have hSaved := hCell
      obtain ⟨f,_,hCf,_,_⟩ := hCell
      exact ⟨hC.zero_nat,(hH.graph.bounds hM.1 hCf).1,Or.inl hSaved⟩
    · intro hCell
      exact hCell.2.2.elim id (fun h => False.elim (h.1 hB.1.2.1))
  have hCanon : ∀ r s V W' F0 Q0, M.mem r C.omega → (C.zero=r ∨ M.mem C.zero r) → M.SuccessorOf s r →
      RowValues M (grid C Y newTop T.addPairs T.plus B Parents) H r V →
      RowValues M (grid C Y newTop T.addPairs T.plus B Parents) H s W' →
      MemPair M Y.parents r F0 → MemPair M Y.parents s Q0 → Selects true M C Y.width F0 W' Q0 :=
    fun _ _ _ _ _ _ _ _ hSucc _ hW' hF0 hQ0 => ReconstructionRecovery.structural_reconstruction_selects_d hM hC hT.add hY
      hNewTop hNewPos hB hP hH hNested hBound hBlockers hW' hF0 hQ0 hSucc
  have hFF := hFC.forest
  have hAll := KP1Y.induction_d hM bottomSchema (bottomEnv C Y.width F' Bottom P0) (by
    intro c ih
    apply (bottomSchema_iff hM.1 C Y.width F' Bottom P0 c).mpr
    have hPrefix := fun i hi => (bottomSchema_iff hM.1 C Y.width F' Bottom P0 i).mp (ih i hi)
    intro p
    classical
    by_cases hc : M.mem c Y.width
    · by_cases hcLast : M.mem c D.coordinates.last
      · exact bottom_original_iff_d hM hC hT hD hY hCopy hKept hRun hFrom hBotW hSel hFC hP0 hcLast p
      have hcω := hw.transitive Y.width hY.width c hc
      have hLastLe := nat_le_of_not_lt hM hC hcω hD.coordinates.last hcLast
      have hRootC : M.mem D.coordinates.root c := nat_lt_of_lt_of_le hM hC hcω hD.coordinates.below hLastLe
      obtain ⟨s0,b,hRaw⟩ := raw_decode_exists_d hM hC hT hD.coordinates hcω
      obtain ⟨hSource,hEnc⟩ := (raw_decoded_active_iff hRootC).mp hRaw
      by_cases hSome : ∃ p0, MemPair M Q s0 p0
      · obtain ⟨p0,hQs0⟩ := hSome
        obtain ⟨pp,_,hP0c,hRP⟩ := bottom_encoded_some_d hM hC hT hD hY hCopy hRun hPositive hFrom hExtraction hNewTop
          hNewPos hPrefixTop hFixed hOrder hB hP hH hRow0 hCanon hBotPos hSel hFC hP0 hSource hEnc hc hQs0 hPrefix
        constructor
        · intro hp
          have he := (hY.forest C.zero P0 hP0).unique c p pp hp hP0c
          subst he
          exact hRP
        · intro hp
          have he := restricted_parent_unique_d hM true hC hFF hp hRP
          subst he
          exact hP0c
      · obtain ⟨h1,h2⟩ := bottom_encoded_none_d hM hC hT hD hY hCopy hKept hRun hRooted hFrom hExtraction hNewTop
          hPrefixTop hFixed hRebuild hP0 hSource hEnc hc (fun p0 h => hSome ⟨p0,h⟩)
        exact iff_of_false (h1 p) (h2 p)
    · exact iff_of_false (fun h => hc ((hY.forest C.zero P0 hP0).bounds hM.1 h).1) (fun h => hc (h.1.1.bounds hM.1).2))
  exact ⟨hFF,hRebuild.graph,hY.forest C.zero P0 hP0,fun c => (bottomSchema_iff hM.1 C Y.width F' Bottom P0 c).mp (hAll c)⟩

/-- `LowerLayer.BottomPart` 字段（LANE-B `OneYLowerLayerStep.lean`）的实际证明，类型与其定义体相同。
`hLayers` 只用于源第k行的 RootedRow；`hN` 只用于 last⊆n。 -/
theorem bottom_part_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K k N n : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hN : CopyCoordinates.Width M C T A N n) :
    ∀ {W Q J oldTop Qnext newTop Pnext Bottom F F' P0 : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
      TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
      Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
      TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
      ReconstructionSelection.PseudoTopBound M C Y newTop →
      MountainReconstruction.Rebuilds M C T.addPairs T.plus Y newTop Bottom →
      Selects true M C m F W Q → FrameCopy.Copies M C T A F N n F' → MemPair M Y.parents C.zero P0 →
      Selects true M C n F' Bottom P0 := by
  intro W Q J oldTop Qnext newTop Pnext Bottom F F' P0 D Y hData hNew hPos hInputs hBound hRebuild hSel hFC hP0
  have hA := hData.coordinates
  subst hA
  exact bottom_select_d hM hC hT hData.context hData.target hData.copies
    (width_kept_d hM hC hT hData.context.coordinates hN) hData.run (hLayers.at_rooted hM.1 hData.layer) hData.from_run
    hData.extraction hNew hPos hInputs.prefixTop hInputs.fixed hInputs.order hBound hRebuild hSel hFC hP0

end KP1Y.OneYFinite.LowerBlock
