import KP1Y.OneYTowerCanonLowerFormula
import KP1Y.OneYTowerCanonExits
import KP1Y.OneYTerminalBaseTopForest

/-! Lower 输入谓词 `InputsAt` 的一元对象模式及其与 `LowerInputs` 的精确换算；
塔中各层实际数据的统一读出；Terminal 重建行的原前缀保持。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

private def schemaC : ExpressionData (Project.Term 35) := ⟨.bound 34,.bound 33,.bound 32,.bound 31,.bound 30⟩
private def schemaT : MatrixArithmetic (Project.Term 35) := ⟨.bound 29,.bound 28,.bound 27,.bound 26,.bound 25,.bound 24⟩
private def schemaA : CopyCoordinates.Context (Project.Term 35) := ⟨.bound 23,.bound 22,.bound 21,.bound 20⟩

def inputsSchema : Project.UnarySchema 22 where
  body := .forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (successorFormula (.bound 11) (.bound 12)) (.imp (memPairFormula (.bound 16) (.bound 12) (.bound 10))
      (.imp (codeFormula (.bound 10) (.bound 9) (.bound 8)) (.imp (memPairFormula (.bound 15) (.bound 11) (.bound 7))
        (.imp (codeFormula (.bound 7) (.bound 6) (.bound 5)) (.imp (memPairFormula (.bound 14) (.bound 11) (.bound 4))
          (.imp (memPairFormula (.bound 13) (.bound 11) (.bound 3)) (.imp (codeFormula (.bound 3) (.bound 2) (.bound 1))
            (.imp (memPairFormula (.bound 1) (.bound 33) (.bound 0))
              (inputsBodyFormula schemaC schemaT schemaA (.bound 19) (.bound 18) (.bound 17) (.bound 9) (.bound 8)
                (.bound 6) (.bound 5) (.bound 4) (.bound 0))))))))))))))))))))))
  freeClosed := by
    have hBody := inputsBodyFormula_freeClosed (C := schemaC) (T := schemaT) (A := schemaA)
      ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩
      (.bound 19) (.bound 18) (.bound 17) (.bound 9) (.bound 8) (.bound 6) (.bound 5) (.bound 4) (.bound 0)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,successorFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,hBody]

def inputsEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m n forests Gs H Hr G : M.Domain) : Env M 22 :=
  (((((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push m).push n).push forests).push Gs).push H).push Hr).push G

theorem inputsSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain) (A : CopyCoordinates.Context M.Domain) (m n forests Gs H Hr G k : M.Domain) :
    Project.Formula.satisfies ((inputsEnv C T A m n forests Gs H Hr G).push k) inputsSchema.body ↔
      InputsAt M C T A m n forests Gs H Hr G k := by
  simp only [inputsSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    successorFormula_iff he,memPairFormula_iff he,codeFormula_iff he,inputsBodyFormula_iff he]
  rfl

/-- RawCopy 与实际 FrameCopy 互推。 -/
theorem raw_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {m F index n F' : M.Domain}
    (hF : Forest M C.omega m F) (hWidth : CopyCoordinates.Width M C T A index n) :
    RawCopy M C T A n F F' ↔ FrameCopy.Copies M C T A F index n F' := by
  constructor
  · rintro ⟨hF',hRows⟩
    obtain ⟨F'',hF''⟩ := FrameCopy.copies_exists_d hM hC hT hA hF hWidth
    have he : F''=F' := hF''.forest.ext hM.1 hF' (fun c t => by
      constructor
      · intro hAt
        have hc := (hF''.forest.bounds hM.1 hAt).1
        exact (hRows c hc t).mpr ((hF''.raw_parent_iff_d hM hC hT hA hF hc).mp hAt)
      · intro hAt
        have hc := (hF'.bounds hM.1 hAt).1
        exact (hF''.raw_parent_iff_d hM hC hT hA hF hc).mpr ((hRows c hc t).mp hAt))
    exact he ▸ hF''
  · intro h
    exact ⟨h.forest,fun c hc t => h.raw_parent_iff_d hM hC hT hA hF hc⟩

/-- 主体 → 实际 `LowerInputs`。 -/
theorem InputsBody.lower_inputs_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {D : Lower.Context M.Domain}
    {m N n forests sH sP V1 Q1 newTop P1 : M.Domain} (hDA : D.coordinates=A) (hDX : D.mountain=⟨m,sH,forests,sP⟩)
    (hWidth : CopyCoordinates.Width M C T A N n)
    (h : InputsBody M C T A m n forests sH sP V1 Q1 newTop P1) : LowerInputs M C T D m N n V1 Q1 newTop P1 := by
  obtain ⟨hPrefix,hFixed,hOrder,hSelect,hNonroot⟩ := h
  subst hDA
  refine ⟨hPrefix,hFixed,?_,⟨?_,hNonroot⟩⟩
  · intro Pseudo hPseudo z c hz hzc hc hSame
    apply hOrder z c hz hzc hc
    intro p
    rw [hDX] at hPseudo
    exact (hPseudo.rows c p).symm.trans ((hSame p).trans (hPseudo.rows z p))
  · intro F F' hSel hCopy
    exact hSelect F F' hSel ((raw_copy_iff_d hM hC hT hA hSel.inherited hWidth).mpr hCopy)

/-- 由四项实际出口组装主体。 -/
theorem inputs_body_of_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {D : Lower.Context M.Domain}
    {m N n forests sH sP V1 Q1 newTop P1 : M.Domain} (hDA : D.coordinates=A) (hDX : D.mountain=⟨m,sH,forests,sP⟩)
    (hX : D.mountain.Valid M C) (hWidth : CopyCoordinates.Width M C T A N n)
    (hPrefix : RowsAgreeOn M newTop V1 A.last) (hFixed : Lower.UpperFixed M C T D V1 Q1 n newTop)
    (hOrder : ∀ Pseudo, GraphPseudoForest M C D.mountain Pseudo → Lower.UpperOrder M C T D Pseudo V1 newTop)
    (hSelect : ∀ F F', Selects true M C m F V1 Q1 → FrameCopy.Copies M C T A F N n F' → Selects true M C n F' newTop P1)
    (hNonroot : ∀ s b c, M.mem A.root s → M.mem s A.last → CopyCoordinates.ParentCopy M C T A b s c → M.mem c n →
      ∀ p, MemPair M P1 c p ↔ ∃ q, MemPair M Q1 s q ∧ CopyCoordinates.ParentCopy M C T A b q p) :
    InputsBody M C T A m n forests sH sP V1 Q1 newTop P1 := by
  subst hDA
  refine ⟨hPrefix,hFixed,?_,?_,hNonroot⟩
  · obtain ⟨Pseudo,hPseudo⟩ := graph_pseudo_forest_exists_d hM hC hX
    intro z c hz hzc hc hSame
    apply hOrder Pseudo hPseudo z c hz hzc hc
    intro p
    rw [hPseudo.rows c p,hPseudo.rows z p]
    rw [hDX] at hPseudo ⊢
    exact hSame p
  · intro F F' hSel hRaw
    exact hSelect F F' hSel ((raw_copy_iff_d hM hC hT hA hSel.inherited hWidth).mp hRaw)

variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
  {V P H K level B strict N n Forests CodeSpace G Nr Top Hr : M.Domain}

/-- 塔重建的每一行都合法，因而值全为正。 -/
theorem Setting.row_positive_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {i F : M.Domain} (hAt : MemPair M Hr i F) : ∀ c v, MemPair M F c v → M.mem C.zero v := by
  have hLegal := h.run.legal_d hM hC hT.add h.tower.width h.tower.bound h.tower.graph h.valid_codes
    (h.top.legal_d hM hC h.tower.width) i F hAt
  exact fun c v hV => legal_values_positive hM.1 hLegal hV

/-- 宽度不小于原末列：last ⊆ n。 -/
theorem Setting.last_subset_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) : M.MemberSubset A.last n := by
  obtain ⟨_,_,off,hoff,_,hAdd⟩ := h.width
  exact KP1Y.Arithmetic.sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem h.coordinates.last)
    ((hT.add.add_iff_sum hM h.coordinates.last hoff).mp hAdd)

/-- Terminal 重建行保持原末列以前的全部底值。 -/
theorem terminal_rebuild_prefix_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (hA : A.Valid M C) {R : RowStateSpace M.Domain} {W Q J OldTop level NewTop Bottom : M.Domain} {X Y : Data M.Domain}
    (hRun : RowRun M C m R W Q J) (hPositive : ∀ c v, MemPair M W c v → M.mem C.zero v)
    (hX : X.Valid M C) (hY : Y.Valid M C) (hFrom : FromRun M C m R W J X) (hOldTop : TopValueGraph M C m R J X.heights OldTop)
    (hCopy : Terminal.Copies M C T A X level n Y) (hTop : CopiedTop M C T A OldTop Y.width NewTop)
    (hRebuild : MountainReconstruction.Rebuilds M C T.addPairs T.plus Y NewTop Bottom)
    (hLastX : M.mem A.last X.width) (hKept : M.MemberSubset A.last Y.width) : RowsAgreeOn M Bottom W A.last := by
  have hOldGraph : Graph M OldTop X.width C.omega := hFrom.width.symm ▸ hOldTop.graph
  have hOldRebuild := MountainReconstruction.rebuild_original_d hM hC hT.add hRun hPositive hX hFrom hOldTop
  have hOldKept : M.MemberSubset A.last X.width :=
    fun c hc => ((omega_isOrdinal_d hM hC.omega).mem hX.width).transitive A.last hLastX c hc
  exact hRebuild.prefix_d hM hC hT.add hY hX hTop.graph hOldGraph hA.last hKept hOldKept
    (fun c hc v => hCopy.original_heights_d hM hC hT hA (hCopy.width ▸ hKept c hc) hc)
    (fun c hc v => hTop.prefix_iff_d hM hC hT hA (hKept c hc) hc)
    (fun c hc r _ p => hCopy.original_parents_d hM hC hA (hCopy.width ▸ hKept c hc) hc) hOldRebuild

end KP1Y.OneYFinite.TowerCanon
