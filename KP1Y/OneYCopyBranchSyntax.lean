import KP1Y.OneYOrdinaryCopy
import KP1Y.OneYTerminalCopy
import KP1Y.OneYLowerCopy
import KP1Y.OneYCopiedMountainSyntax

/-! 三种复制的有界行规格。固定输出宽度和森林载体，由实际图的界恢复完整Copies。 -/
namespace KP1Y.OneYFinite.CopiedMountain
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

def BoundedCopyRows (M : SetTheory.Structure.{u}) (w n : M.Domain) (Y : Data M.Domain)
    (H : M.Domain → M.Domain → Prop) (P : M.Domain → M.Domain → M.Domain → Prop) : Prop :=
  (∀ c, M.mem c n → ∀ h, M.mem h w → (MemPair M Y.heights c h ↔ H c h)) ∧
  (∀ r, M.mem r w → ∀ c, M.mem c n → ∀ p, M.mem p n → (ParentAt M Y r c p ↔ P r c p))

def boundedCopyFormula {d : Nat} (w n : Project.Term d) (Y : Data (Project.Term d))
    (H : Project.Formula 1 (d+2)) (P : Project.Formula 1 (d+3)) : Project.Formula 1 d :=
  .conj (Project.Formula.forallMem n (Project.Formula.forallMem w.weaken
    (.iff (memPairFormula Y.heights.weaken.weaken (.bound 1) (.bound 0)) H)))
    (Project.Formula.forallMem w (Project.Formula.forallMem n.weaken (Project.Formula.forallMem n.weaken.weaken
      (.iff (parentAtFormula Y.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0)) P))))

theorem boundedCopyFormula_delta0 {d : Nat} (w n : Project.Term d) (Y : Data (Project.Term d))
    {H : Project.Formula 1 (d+2)} {P : Project.Formula 1 (d+3)} (hH : H.IsDelta0) (hP : P.IsDelta0) :
    (boundedCopyFormula w n Y H P).IsDelta0 :=
  .conj (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _) hH)))
    (.forallMem _ (.forallMem _ (.forallMem _ (.iff (parentAtFormula_delta0 _ _ _ _) hP))))

theorem boundedCopyFormula_freeClosed {d : Nat} {w n : Project.Term d} (hw : w.freeSupport=[]) (hn : n.freeSupport=[])
    {Y : Data (Project.Term d)} (hY : Y.Closed) {H : Project.Formula 1 (d+2)} {P : Project.Formula 1 (d+3)}
    (hH : H.FreeClosed) (hP : P.FreeClosed) : (boundedCopyFormula w n Y H P).FreeClosed := by
  have hp := parentAtFormula_freeClosed hY.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl
  simp [boundedCopyFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,hw,hn,hY.heights,hH,hP,hp]

theorem boundedCopyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (w n : Project.Term d) (Y : Data (Project.Term d)) (H : Project.Formula 1 (d+2)) (P : Project.Formula 1 (d+3)) :
    Project.Formula.satisfies e (boundedCopyFormula w n Y H P) ↔
      BoundedCopyRows M (w.eval e) (n.eval e) (Y.eval e)
        (fun c h => Project.Formula.satisfies ((e.push c).push h) H)
        (fun r c p => Project.Formula.satisfies (((e.push r).push c).push p) P) := by
  simp only [boundedCopyFormula,BoundedCopyRows,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff he,parentAtFormula_iff he,Term.eval_weaken,Data.eval_weaken]
  rfl

theorem bounded_copy_rows_full_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {n : M.Domain} {Y : Data M.Domain} (hY : Y.Valid M C) (hWidth : Y.width=n)
    {H : M.Domain → M.Domain → Prop} {P : M.Domain → M.Domain → M.Domain → Prop}
    (hH : ∀ c h, H c h → M.mem h C.omega) (hP : ∀ r c p, P r c p → M.mem r C.omega ∧ M.mem p c) :
    BoundedCopyRows M C.omega n Y H P ↔
      (∀ c h, MemPair M Y.heights c h ↔ M.mem c n ∧ H c h) ∧
      (∀ r c p, ParentAt M Y r c p ↔ M.mem c n ∧ P r c p) := by
  constructor
  · rintro ⟨hHeight,hParent⟩
    constructor
    · intro c h
      constructor
      · intro hAt
        have hc := hWidth ▸ (hY.heights.bounds hM.1 hAt).1
        exact ⟨hc,(hHeight c hc h (hY.heights.bounds hM.1 hAt).2).mp hAt⟩
      · rintro ⟨hc,hSpec⟩
        exact (hHeight c hc h (hH c h hSpec)).mpr hSpec
    · intro r c p
      constructor
      · intro hAt
        have hb := hAt.bounds hM.1 hY
        have hc := hWidth ▸ hb.2.1
        exact ⟨hc,(hParent r hb.1 c hc p (hWidth ▸ hb.2.2.1)).mp hAt⟩
      · rintro ⟨hc,hSpec⟩
        have hb := hP r c p hSpec
        have hn := hWidth ▸ hY.width
        have hp := ((omega_isOrdinal_d hM hC.omega).mem hn).transitive c hc p hb.2
        exact (hParent r hb.1 c hc p hp).mpr hSpec
  · rintro ⟨hHeight,hParent⟩
    exact ⟨fun c hc h _ => (hHeight c h).trans ⟨And.right,fun h => ⟨hc,h⟩⟩,
      fun r _ c hc p _ => (hParent r c p).trans ⟨And.right,fun h => ⟨hc,h⟩⟩⟩

def ordinaryCopiesFormula {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (X : Data (Project.Term d)) (n : Project.Term d) (Y : Data (Project.Term d)) : Project.Formula 1 d :=
  boundedCopyFormula C.omega n Y
    (Ordinary.heightFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken X.weaken.weaken (.bound 1) (.bound 0))
    (Ordinary.parentFormula C.weaken.weaken.weaken T.weaken.weaken.weaken A.weaken.weaken.weaken X.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))

def terminalCopiesFormula {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (X : Data (Project.Term d)) (level n : Project.Term d) (Y : Data (Project.Term d)) : Project.Formula 1 d :=
  boundedCopyFormula C.omega n Y
    (Ordinary.heightFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken X.weaken.weaken (.bound 1) (.bound 0))
    (Terminal.parentFormula C.weaken.weaken.weaken T.weaken.weaken.weaken A.weaken.weaken.weaken X.weaken.weaken.weaken
      level.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))

def lowerCopiesFormula {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (D : Lower.Context (Project.Term d)) (n : Project.Term d) (Y : Data (Project.Term d)) : Project.Formula 1 d :=
  boundedCopyFormula C.omega n Y
    (Lower.heightFormula C.weaken.weaken T.weaken.weaken D.weaken.weaken (.bound 1) (.bound 0))
    (Lower.parentFormula C.weaken.weaken.weaken T.weaken.weaken.weaken D.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))

theorem ordinaryCopiesFormula_delta0 {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (X : Data (Project.Term d)) (n : Project.Term d) (Y : Data (Project.Term d)) :
    (ordinaryCopiesFormula C T A X n Y).IsDelta0 :=
  boundedCopyFormula_delta0 _ _ _ (Ordinary.heightFormula_delta0 _ _ _ _ _ _) (Ordinary.parentFormula_delta0 _ _ _ _ _ _ _)

theorem terminalCopiesFormula_delta0 {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (X : Data (Project.Term d)) (level n : Project.Term d) (Y : Data (Project.Term d)) :
    (terminalCopiesFormula C T A X level n Y).IsDelta0 :=
  boundedCopyFormula_delta0 _ _ _ (Ordinary.heightFormula_delta0 _ _ _ _ _ _) (Terminal.parentFormula_delta0 _ _ _ _ _ _ _ _)

theorem lowerCopiesFormula_delta0 {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (D : Lower.Context (Project.Term d)) (n : Project.Term d) (Y : Data (Project.Term d)) : (lowerCopiesFormula C T D n Y).IsDelta0 :=
  boundedCopyFormula_delta0 _ _ _ (Lower.heightFormula_delta0 _ _ _ _ _) (Lower.parentFormula_delta0 _ _ _ _ _ _)

theorem ordinaryCopiesFormula_freeClosed {d : Nat} {C : ExpressionData (Project.Term d)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term d)} (hT : CopyCoordinates.ArithmeticClosed T)
    {A : CopyCoordinates.Context (Project.Term d)} (hA : A.Closed) {X Y : Data (Project.Term d)} (hX : X.Closed) (hY : Y.Closed)
    (n : Project.Term d) (hn : n.freeSupport=[]) : (ordinaryCopiesFormula C T A X n Y).FreeClosed :=
  boundedCopyFormula_freeClosed hC.omega hn hY
    (Ordinary.heightFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken hX.weaken.weaken _ _ rfl rfl)
    (Ordinary.parentFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken hA.weaken.weaken.weaken hX.weaken.weaken.weaken _ _ _ rfl rfl rfl)

theorem terminalCopiesFormula_freeClosed {d : Nat} {C : ExpressionData (Project.Term d)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term d)} (hT : CopyCoordinates.ArithmeticClosed T)
    {A : CopyCoordinates.Context (Project.Term d)} (hA : A.Closed) {X Y : Data (Project.Term d)} (hX : X.Closed) (hY : Y.Closed)
    (level n : Project.Term d) (hl : level.freeSupport=[]) (hn : n.freeSupport=[]) : (terminalCopiesFormula C T A X level n Y).FreeClosed :=
  boundedCopyFormula_freeClosed hC.omega hn hY
    (Ordinary.heightFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken hX.weaken.weaken _ _ rfl rfl)
    (Terminal.parentFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken hA.weaken.weaken.weaken hX.weaken.weaken.weaken
      _ _ _ _ (by simpa using hl) rfl rfl rfl)

theorem lowerCopiesFormula_freeClosed {d : Nat} {C : ExpressionData (Project.Term d)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term d)} (hT : CopyCoordinates.ArithmeticClosed T)
    {D : Lower.Context (Project.Term d)} (hD : D.Closed) {Y : Data (Project.Term d)} (hY : Y.Closed)
    (n : Project.Term d) (hn : n.freeSupport=[]) : (lowerCopiesFormula C T D n Y).FreeClosed :=
  boundedCopyFormula_freeClosed hC.omega hn hY
    (Lower.heightFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hD.weaken.weaken _ _ rfl rfl)
    (Lower.parentFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken hD.weaken.weaken.weaken _ _ _ rfl rfl rfl)

private theorem ordinary_height_natural {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {T : MatrixArithmetic M.Domain} {A : CopyCoordinates.Context M.Domain} {X : Data M.Domain} (hX : X.Valid M C)
    {c h : M.Domain} (hHeight : Ordinary.Height M C T A X c h) : M.mem h C.omega := by
  obtain ⟨_,_,_,_,_,hAt⟩ := hHeight
  exact (hX.heights.bounds he hAt).2

theorem ordinaryCopiesFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {d : Nat} (e : Env M d)
    (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d)) (A : CopyCoordinates.Context (Project.Term d))
    (X : Data (Project.Term d)) (n : Project.Term d) (Y : Data (Project.Term d))
    (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e)) (hA : (A.eval e).Valid M (C.eval e))
    (hX : (X.eval e).Valid M (C.eval e)) (hY : (Y.eval e).Valid M (C.eval e)) (hWidth : (Y.eval e).width=n.eval e)
    (hForests : ∀ F, M.mem F (Y.eval e).forests ↔ Forest M (C.eval e).omega (n.eval e) F) :
    Project.Formula.satisfies e (ordinaryCopiesFormula C T A X n Y) ↔ Ordinary.Copies M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (n.eval e) (Y.eval e) := by
  rw [ordinaryCopiesFormula,boundedCopyFormula_iff hM.1]
  simp only [Ordinary.heightFormula_iff hM.1,Ordinary.parentFormula_iff hM.1,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Data.eval_weaken]
  change BoundedCopyRows M (C.eval e).omega (n.eval e) (Y.eval e)
    (Ordinary.Height M (C.eval e) (T.eval e) (A.eval e) (X.eval e))
    (Ordinary.Parent M (C.eval e) (T.eval e) (A.eval e) (X.eval e)) ↔ _
  have hBounds (r c p : M.Domain) (h : Ordinary.Parent M (C.eval e) (T.eval e) (A.eval e) (X.eval e) r c p) :
      M.mem r (C.eval e).omega ∧ M.mem p c := by
    have hLeft := h.left_d hM hC hT hA hX
    obtain ⟨_,_,_,_,_,_,_,hAt,_⟩ := h
    exact ⟨(hAt.bounds hM.1 hX).1,hLeft⟩
  rw [bounded_copy_rows_full_iff_d hM hC hY hWidth
    (H := Ordinary.Height M (C.eval e) (T.eval e) (A.eval e) (X.eval e))
    (P := Ordinary.Parent M (C.eval e) (T.eval e) (A.eval e) (X.eval e))
    (fun _ _ h => ordinary_height_natural hM.1 hX h) hBounds]
  exact ⟨fun h => ⟨hWidth,hForests,h.1,h.2⟩,fun h => ⟨h.heights,h.parents⟩⟩

theorem terminalCopiesFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {d : Nat} (e : Env M d)
    (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d)) (A : CopyCoordinates.Context (Project.Term d))
    (X : Data (Project.Term d)) (level n : Project.Term d) (Y : Data (Project.Term d))
    (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e)) (hA : (A.eval e).Valid M (C.eval e))
    (hX : (X.eval e).Valid M (C.eval e)) (hY : (Y.eval e).Valid M (C.eval e)) (hWidth : (Y.eval e).width=n.eval e)
    (hForests : ∀ F, M.mem F (Y.eval e).forests ↔ Forest M (C.eval e).omega (n.eval e) F) :
    Project.Formula.satisfies e (terminalCopiesFormula C T A X level n Y) ↔ Terminal.Copies M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (level.eval e) (n.eval e) (Y.eval e) := by
  rw [terminalCopiesFormula,boundedCopyFormula_iff hM.1]
  simp only [Ordinary.heightFormula_iff hM.1,Terminal.parentFormula_iff hM.1,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  change BoundedCopyRows M (C.eval e).omega (n.eval e) (Y.eval e)
    (Ordinary.Height M (C.eval e) (T.eval e) (A.eval e) (X.eval e))
    (Terminal.Parent M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (level.eval e)) ↔ _
  rw [bounded_copy_rows_full_iff_d hM hC hY hWidth
    (H := Ordinary.Height M (C.eval e) (T.eval e) (A.eval e) (X.eval e))
    (P := Terminal.Parent M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (level.eval e))
    (fun _ _ h => ordinary_height_natural hM.1 hX h)
    (fun _ _ _ h => ⟨h.row_natural hM.1 hX,h.left_d hM hC hT hA hX⟩)]
  exact ⟨fun h => ⟨hWidth,hForests,h.1,h.2⟩,fun h => ⟨h.heights,h.parents⟩⟩

theorem lowerCopiesFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {d : Nat} (e : Env M d)
    (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d)) (D : Lower.Context (Project.Term d))
    (n : Project.Term d) (Y : Data (Project.Term d)) (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e))
    (hD : (D.eval e).Valid M (C.eval e)) (hY : (Y.eval e).Valid M (C.eval e)) (hWidth : (Y.eval e).width=n.eval e)
    (hForests : ∀ F, M.mem F (Y.eval e).forests ↔ Forest M (C.eval e).omega (n.eval e) F) :
    Project.Formula.satisfies e (lowerCopiesFormula C T D n Y) ↔ Lower.Copies M (C.eval e) (T.eval e) (D.eval e) (n.eval e) (Y.eval e) := by
  rw [lowerCopiesFormula,boundedCopyFormula_iff hM.1]
  simp only [Lower.heightFormula_iff hM.1,Lower.parentFormula_iff hM.1,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Lower.Context.eval_weaken]
  change BoundedCopyRows M (C.eval e).omega (n.eval e) (Y.eval e)
    (Lower.Height M (C.eval e) (T.eval e) (D.eval e))
    (Lower.Parent M (C.eval e) (T.eval e) (D.eval e)) ↔ _
  rw [bounded_copy_rows_full_iff_d hM hC hY hWidth
    (H := Lower.Height M (C.eval e) (T.eval e) (D.eval e))
    (P := Lower.Parent M (C.eval e) (T.eval e) (D.eval e))
    (fun _ _ h => h.natural hM.1 hT hD)
    (fun _ _ _ h => ⟨h.1,h.left_d hM hC hT hD⟩)]
  exact ⟨fun h => ⟨hWidth,hForests,h.1,h.2⟩,fun h => ⟨h.heights,h.parents⟩⟩

end KP1Y.OneYFinite.CopiedMountain
