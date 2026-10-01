import KP1Y.OneYLowerCopyNesting
import KP1Y.OneYMountainReconstruction

/-! Lower实际重建值与上层值输入。oldTop是源提取值，newTop是相邻层实际重建底值。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open MountainReconstruction
universe u

/-- 原提取父good或无父的非root坏部列，复制顶部值与原提取值相等。 -/
def UpperFixed (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Context M.Domain) (oldTop upperParents width newTop : M.Domain) : Prop :=
  ∀s, M.mem D.coordinates.root s → M.mem s D.coordinates.last →
    (∀q, MemPair M upperParents s q → M.mem q D.coordinates.root) →
    ∀b c v, CopyCoordinates.ParentCopy M C T D.coordinates b s c → M.mem c width →
      MemPair M oldTop s v → MemPair M newTop c v

/-- 原Pseudo共同父窗口上的旧顶部弱序由实际相邻上层复制值保持。 -/
def UpperOrder (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Context M.Domain) (Pseudo oldTop newTop : M.Domain) : Prop :=
  ∀z c, M.mem D.coordinates.root z → M.mem z c → (c=D.coordinates.last ∨ M.mem c D.coordinates.last) →
    ParentRowsEqual M Pseudo c z → ∀vc vz, MemPair M oldTop c vc → MemPair M oldTop z vz →
      (vc=vz ∨ M.mem vc vz) → ∀b cc zz tc tz,
      CopyCoordinates.ParentCopy M C T D.coordinates b c cc → CopyCoordinates.ParentCopy M C T D.coordinates b z zz →
      MemPair M newTop cc tc → MemPair M newTop zz tz → tc=tz ∨ M.mem tc tz

theorem UpperFixed.rows_iff_d {M : SetTheory.Structure.{u}} (_he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Context M.Domain}
    {oldTop upperParents width newTop : M.Domain} (hOld : Graph M oldTop D.mountain.width C.omega)
    (hNew : Graph M newTop width C.omega) (hFixed : UpperFixed M C T D oldTop upperParents width newTop)
    {s b c : M.Domain} (hs : M.mem s D.mountain.width) (hRoot : M.mem D.coordinates.root s)
    (hLast : M.mem s D.coordinates.last) (hGood : ∀q, MemPair M upperParents s q → M.mem q D.coordinates.root)
    (hMap : CopyCoordinates.ParentCopy M C T D.coordinates b s c) (hc : M.mem c width) (v : M.Domain) :
    MemPair M newTop c v ↔ MemPair M oldTop s v := by
  constructor
  · intro hAt
    obtain ⟨w,_,hW⟩ := hOld.total s hs
    have hNewW := hFixed s hRoot hLast hGood b c w hMap hc hW
    exact hNew.unique c w v hNewW hAt ▸ hW
  · exact hFixed s hRoot hLast hGood b c v hMap hc

/-- 实际重建保留旧末列以前的全部数值；不依赖当前层的最近更小恢复。 -/
theorem Copies.rebuild_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {T : MatrixArithmetic M.Domain} {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run oldTop n newTop Bottom : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    (hFrom : FromRun M C m R V Run D.mountain) (hOldTop : TopValueGraph M C m R Run D.mountain.heights oldTop)
    (hCopy : Copies M C T D n Y) (hNewTop : Graph M newTop Y.width C.omega)
    (hKept : M.MemberSubset D.coordinates.last Y.width) (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last)
    (hRebuild : Rebuilds M C Pairs Plus Y newTop Bottom) : RowsAgreeOn M Bottom V D.coordinates.last := by
  have hOldGraph : Graph M oldTop D.mountain.width C.omega := hFrom.width.symm ▸ hOldTop.graph
  have hOldRebuild := rebuild_original_d hM hC hPlus hRun hPositive hD.mountain hFrom hOldTop
  have hOldKept : M.MemberSubset D.coordinates.last D.mountain.width :=
    fun c hc => ((omega_isOrdinal_d hM hC.omega).mem hD.mountain.width).transitive D.coordinates.last hD.last c hc
  exact hRebuild.prefix_d hM hC hPlus hY hD.mountain hNewTop hOldGraph hD.coordinates.last hKept hOldKept
    (fun c hc v => hCopy.original_heights_d hM hC hD (hCopy.width ▸ hKept c hc) (Or.inr hc)) hPrefixTop
    (fun c hc r _ p => hCopy.original_parents_d hM hC hD (hCopy.width ▸ hKept c hc) (Or.inr hc)) hOldRebuild

end KP1Y.OneYFinite.CopiedMountain.Lower
