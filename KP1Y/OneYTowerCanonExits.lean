import KP1Y.OneYTowerCanonInterface
import KP1Y.OneYDecoratedMatrixExpansion

/-! Terminal 底行(k=K)给下层的四个出口 H1–H4 的精确命题（由助手车道在
`OneYCanonHelper*` 中证明；此处只陈述，供汇合模块作为显式前提直到其落地）。
前提包与 `ExpansionCanonical.terminal_rebuild_rows_d` 完全相同。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

/-- Terminal 层的全部实际前提（不含 `hM`）。V,P 为源第K层底行/父图，NewTop=Hr(K+1)，Bottom=Hr(K)。 -/
def TerminalBaseContext (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (m V P H level index n OldTop NewTop Bottom : M.Domain) (R : RowStateSpace M.Domain)
    (X Y : Data M.Domain) (A : CopyCoordinates.Context M.Domain) : Prop :=
  C.Valid M ∧ T.Valid M C ∧ RowRun M C m R V P H ∧ RootedRow M C m V P ∧ X.Valid M C ∧
  FromRun M C m R V H X ∧ TopValueGraph M C m R H X.heights OldTop ∧ A.Valid M C ∧
  M.SuccessorOf m A.last ∧ RowBadAt M C R H level A.last A.root ∧ M.mem index C.omega ∧
  CopyCoordinates.Width M C T A index n ∧ Y.Valid M C ∧ Terminal.Copies M C T A X level n Y ∧
  CopiedTop M C T A OldTop Y.width NewTop ∧ MountainReconstruction.Rebuilds M C T.addPairs T.plus Y NewTop Bottom

/-- H1–H4（见 tracker/handoff/LANE-C.md "Available for helper"）。 -/
structure TerminalExits (M : SetTheory.Structure.{u}) : Prop where
  select : ∀ {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
      {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
      {X Y : Data M.Domain} {A : CopyCoordinates.Context M.Domain} {F F' P0 : M.Domain},
    TerminalBaseContext M C T m V P H level index n OldTop NewTop Bottom R X Y A →
    Selects true M C m F V P → FrameCopy.Copies M C T A F index n F' → MemPair M Y.parents C.zero P0 →
    Selects true M C n F' Bottom P0
  nonroot : ∀ {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
      {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
      {X Y : Data M.Domain} {A : CopyCoordinates.Context M.Domain} {P0 s b c p : M.Domain},
    TerminalBaseContext M C T m V P H level index n OldTop NewTop Bottom R X Y A →
    MemPair M Y.parents C.zero P0 → M.mem A.root s → M.mem s A.last →
    CopyCoordinates.ParentCopy M C T A b s c → M.mem c n →
    (MemPair M P0 c p ↔ ∃ q, MemPair M P s q ∧ CopyCoordinates.ParentCopy M C T A b q p)
  fixed : ∀ {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
      {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
      {X Y : Data M.Domain} {A : CopyCoordinates.Context M.Domain} {D : Lower.Context M.Domain},
    TerminalBaseContext M C T m V P H level index n OldTop NewTop Bottom R X Y A →
    D.coordinates=A → Lower.UpperFixed M C T D V P n Bottom
  order : ∀ {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
      {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
      {X Y : Data M.Domain} {A : CopyCoordinates.Context M.Domain} {D : Lower.Context M.Domain} {F : M.Domain},
    TerminalBaseContext M C T m V P H level index n OldTop NewTop Bottom R X Y A →
    D.coordinates=A → Selects true M C m F V P → Lower.UpperOrder M C T D F V Bottom

end KP1Y.OneYFinite.TowerCanon
