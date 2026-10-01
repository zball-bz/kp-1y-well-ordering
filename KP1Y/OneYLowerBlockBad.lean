import KP1Y.OneYLowerBlockGood

/-! Lower阻挡：坏部父（父项不在root左侧）一支的核心构造。源阻挡 z0 映为 ParentCopy b z0；
路径与父项运输按目标行对应给出；KeyLE运输以 `KeyTransport`（原 `keyLE_succ_rowCopy`）精确列出。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
universe u

/-- 源行 v→w 在目标中的位置（原 `rowCopy b s0 v`）：锥内且 floor≤v 时整体上移 b·rise，否则不动。
这里只记录较高行 w 的目标行 sY。 -/
def LiftedRow (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Lower.Context M.Domain) (s0 b v w sY : M.Domain) : Prop :=
  (¬(InCone M C D s0 ∧ (D.floor=v ∨ M.mem D.floor v)) ∧ sY=w) ∨
    ((InCone M C D s0 ∧ (D.floor=v ∨ M.mem D.floor v)) ∧ ∃ off, M.mem off C.omega ∧
      MulAt M T.mulPairs T.times b D.rise off ∧ AddAt M T.addPairs T.plus w off sY)

/-- 坏部父分支唯一的KeyLE输入（原 `keyLE_succ_rowCopy`）：源行w上 s0,a 有共同坏部父 p0，
源KeyLE（起点succ w）运输为目标KeyLE（起点succ sY），Top为实际旧/新Top读数。 -/
def KeyTransport (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Lower.Context M.Domain) (Y : Data M.Domain) (oldTop newTop : M.Domain) : Prop :=
  ∀ v w sY t t' Q0 s0 a p0 b c x tc ta tc' ta',
    M.SuccessorOf w v → MemPair M D.mountain.parents w Q0 → MemPair M Q0 s0 p0 → MemPair M Q0 a p0 →
    ¬M.mem p0 D.coordinates.root → M.mem a s0 → (s0=D.coordinates.last ∨ M.mem s0 D.coordinates.last) →
    LiftedRow M C T D s0 b v w sY → M.SuccessorOf t w → M.SuccessorOf t' sY →
    ParentCopy M C T D.coordinates b s0 c → ParentCopy M C T D.coordinates b a x →
    M.mem c Y.width → M.mem x Y.width →
    MemPair M oldTop s0 tc → MemPair M oldTop a ta → MemPair M newTop c tc' → MemPair M newTop x ta' →
    ForestOrder.KeyLE M C D.mountain s0 a t tc ta → ForestOrder.KeyLE M C Y c x t' tc' ta'

/-- 坏部父核心（给定源阻挡 z）：路径、父项、KeyLE三项运输作为对目标行的显式局部条件。 -/
theorem bad_blocker_of_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {oldTop newTop : M.Domain} (hNewTop : Graph M newTop n C.omega)
    {w t t' Q0 Q s0 q0 p0 b c q p z tc tz : M.Domain} (hQ0 : MemPair M D.mountain.parents w Q0)
    (hq0s : M.mem q0 s0) (hNew : MemPair M Q0 s0 p0) (hBad : ¬M.mem p0 D.coordinates.root)
    (hPath : z=q0 ∨ Ancestor M C D.mountain.width Q0 z q0) (hZP : MemPair M Q0 z p0)
    (hTC : MemPair M oldTop s0 tc) (hTZ : MemPair M oldTop z tz) (hKey : ForestOrder.KeyLE M C D.mountain s0 z t tc tz)
    (hMap : ParentCopy M C T D.coordinates b s0 c) (hc : M.mem c n) (hMapQ : ParentCopy M C T D.coordinates b q0 q)
    (hPathT : ∀ a x, MemPair M Q0 a p0 → M.mem D.coordinates.root a → Ancestor M C D.mountain.width Q0 a q0 →
      ParentCopy M C T D.coordinates b a x → M.mem x Y.width → Ancestor M C Y.width Q x q)
    (hParentT : ∀ a x, MemPair M Q0 a p0 → M.mem D.coordinates.root a → M.mem a s0 →
      ParentCopy M C T D.coordinates b a x → M.mem x Y.width → MemPair M Q x p)
    (hKeyT : ∀ a x tc ta tc' ta', MemPair M Q0 a p0 → M.mem D.coordinates.root a → M.mem a s0 →
      ParentCopy M C T D.coordinates b a x → M.mem x Y.width →
      MemPair M oldTop s0 tc → MemPair M oldTop a ta → MemPair M newTop c tc' → MemPair M newTop x ta' →
      ForestOrder.KeyLE M C D.mountain s0 a t tc ta → ForestOrder.KeyLE M C Y c x t' tc' ta') :
    BlockerAt M C Y newTop Q c q p t' := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hb : M.mem b C.omega := hMap.2.1
  have hs0ω : M.mem s0 C.omega := hMap.1
  have hp0ω := hw.transitive D.mountain.width hD.mountain.width p0 ((hD.mountain.forest w Q0 hQ0).bounds hM.1 hNew).2
  have hRootP0 := nat_le_of_not_lt hM hC hp0ω hD.coordinates.root hBad
  have hp0s : M.mem p0 s0 := (hD.mountain.forest w Q0 hQ0).left s0 p0 hNew
  have hRootS : M.mem D.coordinates.root s0 := nat_lt_of_le_of_lt hM hC hs0ω hRootP0 hp0s
  have hzs : M.mem z s0 := hPath.elim (fun he => he ▸ hq0s) (fun h => (hw.mem hs0ω).transitive q0 hq0s z h.1)
  have hzω := hw.transitive s0 hs0ω z hzs
  have hp0z : M.mem p0 z := (hD.mountain.forest w Q0 hQ0).left z p0 hZP
  have hRootZ : M.mem D.coordinates.root z := nat_lt_of_le_of_lt hM hC hzω hRootP0 hp0z
  have hNotGood : ¬M.mem s0 D.coordinates.root := fun h =>
    nat_irrefl hM D.coordinates.root ((hw.mem hD.coordinates.root).transitive s0 h D.coordinates.root hRootS)
  have hEnc : Encode M C T D.coordinates s0 b c := (parent_copy_bad_iff hNotGood).mp hMap
  have hcY : M.mem c Y.width := hCopy.width.symm ▸ hc
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hb
  obtain ⟨z',_,hJz⟩ := hJ.graph.total z hzω
  have hMapZ := (hRows z z').mp hJz
  have hzY : M.mem z' Y.width :=
    (hw.mem hY.width).transitive c hcY z' (parent_copy_below_encode_d hM hC hT hD.coordinates hRootS hzs hMapZ hEnc)
  obtain ⟨tc',htc',hTC'⟩ := hNewTop.total c hc
  obtain ⟨tz',htz',hTZ'⟩ := hNewTop.total z' (hCopy.width ▸ hzY)
  refine ⟨z',hzY,?_,hParentT z z' hZP hRootZ hzs hMapZ hzY,tc',htc',tz',htz',hTC',hTZ',
    hKeyT z z' tc tz tc' tz' hZP hRootZ hzs hMapZ hzY hTC hTZ hTC' hTZ' hKey⟩
  rcases hPath with he | hAnc
  · subst z
    exact Or.inl (parent_copy_unique_d hM hC hT hD.coordinates hMapZ hMapQ)
  · exact Or.inr (hPathT z z' hZP hRootZ hAnc hMapZ hzY)

/-- 坏部父核心：路径、父项、KeyLE三项运输作为对目标行的显式局部条件，阻挡本身由源实际阻挡构造。 -/
theorem bad_blocker_core_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    (hFrom : FromRun M C m R V H D.mountain) {oldTop newTop : M.Domain}
    (hTopOld : TopValueGraph M C m R H D.mountain.heights oldTop) (hNewTop : Graph M newTop n C.omega)
    {v w t t' F0 Q0 Q s0 q0 p0 b c q p : M.Domain} (hSucc : M.SuccessorOf w v) (hNext : M.SuccessorOf t w)
    (hF0 : MemPair M D.mountain.parents v F0) (hQ0 : MemPair M D.mountain.parents w Q0)
    (hOld : MemPair M F0 s0 q0) (hNew : MemPair M Q0 s0 p0) (hNe : p0≠q0) (hBad : ¬M.mem p0 D.coordinates.root)
    (hMap : ParentCopy M C T D.coordinates b s0 c) (hc : M.mem c n) (hMapQ : ParentCopy M C T D.coordinates b q0 q)
    (hPathT : ∀ a x, MemPair M Q0 a p0 → M.mem D.coordinates.root a → Ancestor M C D.mountain.width Q0 a q0 →
      ParentCopy M C T D.coordinates b a x → M.mem x Y.width → Ancestor M C Y.width Q x q)
    (hParentT : ∀ a x, MemPair M Q0 a p0 → M.mem D.coordinates.root a → M.mem a s0 →
      ParentCopy M C T D.coordinates b a x → M.mem x Y.width → MemPair M Q x p)
    (hKeyT : ∀ a x tc ta tc' ta', MemPair M Q0 a p0 → M.mem D.coordinates.root a → M.mem a s0 →
      ParentCopy M C T D.coordinates b a x → M.mem x Y.width →
      MemPair M oldTop s0 tc → MemPair M oldTop a ta → MemPair M newTop c tc' → MemPair M newTop x ta' →
      ForestOrder.KeyLE M C D.mountain s0 a t tc ta → ForestOrder.KeyLE M C Y c x t' tc' ta') :
    BlockerAt M C Y newTop Q c q p t' := by
  obtain ⟨z,_,hPath,hZP,tc,_,tz,_,hTC,hTZ,hKey⟩ :=
    source_row_blocker_d hM hC hRun hPositive hD.mountain hFrom hTopOld hSucc hNext hF0 hQ0 hOld hNew hNe
  exact bad_blocker_of_source_d hM hC hT hD hY hCopy hNewTop hQ0 ((hD.mountain.forest v F0 hF0).left s0 q0 hOld) hNew hBad
    hPath hZP hTC hTZ hKey hMap hc hMapQ hPathT hParentT hKeyT

end KP1Y.OneYFinite.LowerBlock
