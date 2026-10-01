import KP1Y.OneYCanonHelperSelectCases

/-! H1：Terminal底行在外部继承帧F的实际复制F'上，按目标底值恰选出目标第0行父图P0。
对目标列作对象集合归纳（谓词为显式Δ₀公式），每列归入前缀/非root副本/高或低seam/无父。 -/
namespace KP1Y.OneYFinite.TerminalBase
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open ReconstructionCanonical Reconstruction MountainReconstruction ReconstructionRecovery
universe u

private def columnEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m F V Q : M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push F).push V).push Q

private def columnSchema : Project.UnarySchema 9 where
  body := .forallE (.iff (memPairFormula (.bound 2) (.bound 1) (.bound 0))
    (restrictedParentFormula true ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 0)))
  freeClosed := by
    have hRestricted := restrictedParentFormula_freeClosed true
      (show (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hRestricted,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem]

private theorem columnSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m F V Q c : M.Domain) :
    Project.Formula.satisfies ((columnEnv C m F V Q).push c) columnSchema.body ↔
      ∀ p, MemPair M Q c p ↔ RestrictedParent true M C m F V c p := by
  simp only [columnSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    memPairFormula_iff he,restrictedParentFormula_iff he]
  rfl

section
variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
  {X Y : CopiedMountain.Data M.Domain} {A : CopyCoordinates.Context M.Domain}

/-- 无目标第0行父项的列底值为1，故无任何受限父候选。 -/
theorem Base.no_parent_restricted_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F' P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) {c : M.Domain} (hc : M.mem c n)
    (hNone : ∀ p, ¬MemPair M P0 c p) (p : M.Domain) : ¬RestrictedParent true M C n F' Bottom c p := by
  rintro ⟨⟨_,xp,_,y,_,hXP,hY,hxy,hPos⟩,_⟩
  have hcY : M.mem c Y.width := h.width_eq ▸ hc
  have hNoY : ∀ q, ¬CopiedMountain.ParentAt M Y C.zero c q := fun q hq => hNone q ((h.target_zero_iff hM hP0 c q).mp hq)
  have hy1 := h.no_parent_one_d hM hC hT hNoY hY
  subst hy1
  have hPos' : M.mem C.zero xp := by simpa [PositiveValue] using hPos
  rcases (hC.one_succ xp).mp hxy with h0 | he
  · exact hC.zero_empty xp h0
  · exact hC.zero_empty C.zero ((hM.1.eq_of_same_members xp C.zero he) ▸ hPos')

/-- 单列：由严格左前缀的选择相等推出本列选择相等。 -/
theorem Base.select_column_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' P0 : M.Domain}
    (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) {c : M.Domain}
    (hPrefix : ∀ i, M.mem i c → ∀ a, MemPair M P0 i a ↔ RestrictedParent true M C n F' Bottom i a) (p : M.Domain) :
    MemPair M P0 c p ↔ RestrictedParent true M C n F' Bottom c p := by
  have hForest0 : Forest M C.omega n P0 := h.width_eq ▸ h.target.forest C.zero P0 hP0
  classical
  by_cases hc : M.mem c n
  · have hForward : ∀ q, MemPair M P0 c q → RestrictedParent true M C n F' Bottom c q := by
      intro q hCQ
      by_cases hcl : M.mem c A.last
      · exact (h.select_prefix_d hM hC hT hF hF' hP0 hcl q).mp hCQ
      · obtain ⟨s,b,hSource,hEncode,hMap⟩ := h.decode_d hM hC hT hc hcl
        rcases hSource.2 with hsl | hs
        · have hEnc : CopyCoordinates.Encode M C T A A.last b c := hsl ▸ hEncode
          rcases h.zero_le_level hM hC with hZ | hLow
          · exact h.select_seam_high_d hM hC hT hF hF' hP0 hZ.symm hEnc hc hPrefix hCQ
          · exact h.select_seam_low_d hM hC hT hF hF' hP0 hLow hEnc hc hPrefix hCQ
        · exact h.select_nonroot_d hM hC hT hF hF' hP0 hSource.1 hs hMap hc hPrefix hCQ
    constructor
    · exact hForward p
    · intro hRP
      by_cases hSome : ∃ q, MemPair M P0 c q
      · obtain ⟨q,hCQ⟩ := hSome
        have he := restricted_parent_unique_d hM true hC hF'.forest (hForward q hCQ) hRP
        exact he ▸ hCQ
      · exact False.elim (h.no_parent_restricted_d hM hC hT hP0 hc (fun q hq => hSome ⟨q,hq⟩) p hRP)
  · exact iff_of_false (fun hp => hc (hForest0.bounds hM.1 hp).1) (fun hp => hc (hp.1.1.bounds hM.1).2)

theorem Base.select_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' P0 : M.Domain}
    (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) : Selects true M C n F' Bottom P0 := by
  have hAll := KP1Y.induction_d hM columnSchema (columnEnv C n F' Bottom P0) (by
    intro c ih
    apply (columnSchema_iff hM.1 C n F' Bottom P0 c).mpr
    exact h.select_column_d hM hC hT hF hF' hP0 (fun i hi => (columnSchema_iff hM.1 C n F' Bottom P0 i).mp (ih i hi)))
  exact ⟨hF'.forest,h.width_eq ▸ h.bottom_graph,h.width_eq ▸ h.target.forest C.zero P0 hP0,
    fun c => (columnSchema_iff hM.1 C n F' Bottom P0 c).mp (hAll c)⟩

end

/-- H1：原 badAtTerminalBase_select_external / badAtTerminal_restrictedParent_external。 -/
theorem terminal_base_select_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hBase : RootedRow M C m V P)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    (hOldTop : TopValueGraph M C m R H X.heights OldTop)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) (hWidth : M.SuccessorOf m A.last)
    (hBad : RowBadAt M C R H level A.last A.root) (hIndex : M.mem index C.omega)
    (hN : CopyCoordinates.Width M C T A index n) (hY : Y.Valid M C)
    (hCopy : CopiedMountain.Terminal.Copies M C T A X level n Y)
    (hTop : CopiedTop M C T A OldTop Y.width NewTop)
    (hRebuild : Rebuilds M C T.addPairs T.plus Y NewTop Bottom)
    {F F' P0 : M.Domain} (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) : Selects true M C n F' Bottom P0 :=
  (Base.mk hRun hBase hX hFrom hOldTop hA hWidth hBad hIndex hN hY hCopy hTop hRebuild).select_d hM hC hT hF hF' hP0

end KP1Y.OneYFinite.TerminalBase
