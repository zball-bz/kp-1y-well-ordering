import KP1Y.OneYOrdinaryCopy
import KP1Y.OneYActiveGeometry
import KP1Y.OneYLowerRowShift

/-! 较低层复制：所有根/高度条件来自真实坏根与数值行运行。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u v

def RootAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : Data M.Domain) (r c q : M.Domain) : Prop :=
  ∃ F, M.mem F X.forests ∧ MemPair M X.parents r F ∧ Root M C X.width F c q

def rootAtFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) (r c q : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem X.forests (.conj (memPairFormula X.parents.weaken r.weaken (.bound 0))
    (rootFormula C.weaken X.width.weaken (.bound 0) c.weaken q.weaken))

theorem rootAtFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) (r c q : Project.Term n) :
    (rootAtFormula C X r c q).IsDelta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (rootFormula_delta0 _ _ _ _ _))

theorem rootAtFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) (r c q : Project.Term n)
    (hr : r.freeSupport=[]) (hc : c.freeSupport=[]) (hq : q.freeSupport=[]) : (rootAtFormula C X r c q).FreeClosed := by
  have hRoot := rootFormula_freeClosed hC.weaken X.width.weaken (.bound 0) c.weaken q.weaken
    (by simpa using hX.width) rfl (by simpa using hc) (by simpa using hq)
  simp [rootAtFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,hX.forests,hX.parents,hr,hRoot]

theorem rootAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) (r c q : Project.Term n) :
    Project.Formula.satisfies e (rootAtFormula C X r c q) ↔ RootAt M (C.eval e) (X.eval e) (r.eval e) (c.eval e) (q.eval e) := by
  simp only [rootAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,rootFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

theorem RootAt.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {X : Data M.Domain} (hX : X.Valid M C) {r c q : M.Domain} (h : RootAt M C X r c q) :
    M.mem r C.omega ∧ M.mem q X.width ∧ M.mem c X.width ∧ (q=c ∨ M.mem q c) := by
  obtain ⟨F,_,hRow,hRoot⟩ := h
  refine ⟨(hX.parents.bounds he hRow).1,hRoot.1,?_,hRoot.2.2.imp_right And.left⟩
  rcases hRoot.2.2 with heq | hAnc
  · exact heq ▸ hRoot.1
  · exact (hAnc.bounds he).2

theorem RootAt.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C) {r c q q' : M.Domain}
    (h : RootAt M C X r c q) (h' : RootAt M C X r c q') : q=q' := by
  obtain ⟨F,_,hRow,hRoot⟩ := h
  obtain ⟨F',_,hRow',hRoot'⟩ := h'
  have hFF := hX.parents.unique r F F' hRow hRow'
  subst F'
  exact root_unique_d hM hC (hX.forest r F hRow) hRoot hRoot'

theorem root_at_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C) {r c : M.Domain}
    (hr : M.mem r C.omega) (hc : M.mem c X.width) : ∃ q, RootAt M C X r c q := by
  obtain ⟨F,hF,hRow⟩ := hX.parents.total r hr
  obtain ⟨q,hRoot⟩ := root_exists_d hM hC (hX.forest r F hRow) hc
  exact ⟨q,F,hF,hRow,hRoot⟩

theorem top_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {X : Data M.Domain} (hX : X.Valid M C) {c h : M.Domain}
    (hHeight : MemPair M X.heights c h) : RootAt M C X h c c := by
  obtain ⟨F,hF,hRow⟩ := hX.parents.total h (hX.heights.bounds hM.1 hHeight).2
  refine ⟨F,hF,hRow,(hX.heights.bounds hM.1 hHeight).1,?_,Or.inl rfl⟩
  intro p _ hParent
  have hSelf := (hX.source h c h hHeight).mp ⟨p,F,hF,hRow,hParent⟩
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) h hSelf

/-- 高行父边在任一低行保持连通根，来自源 RowRun 的已证明逐行细化。 -/
def Coherent (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : Data M.Domain) : Prop :=
  ∀ r u c p q, M.mem r C.omega → (r=u ∨ M.mem r u) → ParentAt M X u c p →
    (RootAt M C X r c q ↔ RootAt M C X r p q)

theorem from_run_coherent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    {X : Data M.Domain} (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X) : Coherent M C X := by
  intro r u c p q _ hLe hParent
  obtain ⟨G,_,hG,hCP⟩ := hParent
  obtain ⟨UG,hRowG⟩ := (hFrom.parents u G).mp hG
  have hAncestor := ancestor_direct_d hM hC (hRun.at_numeric_d hM hC hRowG).forest hCP
  have transfer (c0 p0 : M.Domain) (hBase : ∀ F, MemPair M X.parents r F →
      (Root M C X.width F c0 q ↔ Root M C X.width F p0 q)) : RootAt M C X r c0 q → RootAt M C X r p0 q := by
    rintro ⟨F,hF,hRow,hRoot⟩
    exact ⟨F,hF,hRow,(hBase F hRow).mp hRoot⟩
  have hLow (F : M.Domain) (hF : MemPair M X.parents r F) : Root M C X.width F c q ↔ Root M C X.width F p q := by
    obtain ⟨UF,hRowF⟩ := (hFrom.parents r F).mp hF
    have hAnc := hRun.ancestor_lower_d hM hC hRowF hRowG hLe hAncestor
    rw [hFrom.width]
    exact root_ancestor_iff_d hM hC (hRun.at_numeric_d hM hC hRowF).forest hAnc
  exact ⟨transfer c p hLow,transfer p c (fun F hF => (hLow F hF).symm)⟩

structure Context (α : Type u) where
  coordinates : CopyCoordinates.Context α
  mountain : Data α
  floor : α
  rise : α

structure Context.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (D : Context M.Domain) : Prop where
  coordinates : D.coordinates.Valid M C
  mountain : D.mountain.Valid M C
  last : M.mem D.coordinates.last D.mountain.width
  floor : MemPair M D.mountain.heights D.coordinates.root D.floor
  rise : ∃ h, M.mem h C.omega ∧ MemPair M D.mountain.heights D.coordinates.last h ∧ M.mem D.floor h ∧
    TruncatedDifference M C.omega C.zero h D.floor D.rise
  last_root : RootAt M C D.mountain D.floor D.coordinates.last D.coordinates.root
  coherent : Coherent M C D.mountain

theorem context_from_bad_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K d k W Q : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K d A.last A.root) (hLayer : RowAt M L.states H k W Q) (hk : M.mem k K)
    {R : RowStateSpace M.Domain} {J : M.Domain} (hRows : RowRun M C m R W Q J)
    {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R W J X) :
    ∃ D : Context M.Domain, D.coordinates=A ∧ D.mountain=X ∧ D.Valid M C := by
  have hLast : M.mem A.last m := by
    obtain ⟨WK,_,PK,_,_,JK,hRK,U,_,F,_,hRow,hParent,_⟩ := hBad
    exact ((hRK.at_numeric_d hM hC hRow).forest.bounds hM.1 hParent).1
  have hRoot : M.mem A.root m := ((omega_isOrdinal_d hM hC.omega).mem hRows.space.width).transitive A.last hLast A.root hA.below
  obtain ⟨floor,hFloor,hHY⟩ := hFrom.heights.graph.total A.root hRoot
  obtain ⟨height,hHeight,hHX⟩ := hFrom.heights.graph.total A.last hLast
  obtain ⟨U,F,hRow⟩ := hRows.at_exists_d hFloor
  obtain ⟨hHigher,hRootF⟩ := hLayers.bad_root_lower_root_d hM hC hBad hLayer hk hRows hFrom.heights hHY hHX hRow
  obtain ⟨rise,_,hDiff⟩ := truncated_difference_exists_d hM hC hHeight hFloor
  have hParentRow := (hFrom.parents floor F).mpr ⟨U,hRow⟩
  have hLastX : M.mem A.last X.width := hFrom.width.symm ▸ hLast
  have hRootX : Root M C X.width F A.last A.root := hFrom.width.symm ▸ hRootF
  exact ⟨⟨A,X,floor,rise⟩,rfl,rfl,⟨hA,hX,hLastX,hHY,⟨height,hHeight,hHX,hHigher,hDiff⟩,
    ⟨F,(hX.parents.bounds hM.1 hParentRow).2,hParentRow,hRootX⟩,from_run_coherent_d hM hC hRows hFrom⟩⟩


theorem Context.Valid.floor_nat {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {D : Context M.Domain} (hD : D.Valid M C) : M.mem D.floor C.omega := (hD.mountain.heights.bounds he hD.floor).2

theorem Context.Valid.rise_nat {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {D : Context M.Domain} (hD : D.Valid M C) : M.mem D.rise C.omega := by
  obtain ⟨_,_,_,_,hDiff⟩ := hD.rise
  exact truncated_difference_natural he hDiff

theorem Context.Valid.rise_positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C) : M.mem C.zero D.rise := by
  obtain ⟨_,_,_,hHigher,hDiff⟩ := hD.rise
  exact (truncated_difference_positive_iff_d hM hC hDiff).mpr hHigher

theorem Context.Valid.last_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C) {height : M.Domain}
    (hHeight : MemPair M D.mountain.heights D.coordinates.last height) : KP1Y.Arithmetic.Sum M D.floor D.rise height := by
  obtain ⟨h,_,hAt,hHigher,hDiff⟩ := hD.rise
  have hh := hD.mountain.heights.unique D.coordinates.last h height hAt hHeight
  exact hh ▸ truncated_difference_add_inverse_d hM hC hDiff (Or.inr hHigher)

def InCone (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (D : Context M.Domain) (c : M.Domain) : Prop :=
  ∃ h, M.mem h C.omega ∧ MemPair M D.mountain.heights c h ∧ (D.floor=h ∨ M.mem D.floor h) ∧
    RootAt M C D.mountain D.floor c D.coordinates.root

theorem in_cone_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {D : Context M.Domain} (hD : D.Valid M C) : InCone M C D D.coordinates.root :=
  ⟨D.floor,hD.floor_nat hM.1,hD.floor,Or.inl rfl,top_root_d hM hD.mountain hD.floor⟩

theorem in_cone_last {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {D : Context M.Domain}
    (hD : D.Valid M C) : InCone M C D D.coordinates.last := by
  obtain ⟨h,hh,hAt,hHigher,_⟩ := hD.rise
  exact ⟨h,hh,hAt,Or.inr hHigher,hD.last_root⟩

theorem InCone.root_le {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {D : Context M.Domain} (hD : D.Valid M C) {c : M.Domain} (h : InCone M C D c) :
    D.coordinates.root=c ∨ M.mem D.coordinates.root c := by
  obtain ⟨_,_,_,_,hRoot⟩ := h
  exact (hRoot.bounds he hD.mountain).2.2.2

theorem InCone.height_strict_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C) {c height : M.Domain}
    (h : InCone M C D c) (hAfter : M.mem D.coordinates.root c) (hHeight : MemPair M D.mountain.heights c height) : M.mem D.floor height := by
  obtain ⟨h,_,hAt,hLe,hRoot⟩ := h
  have hhh := hD.mountain.heights.unique c h height hAt hHeight
  subst h
  rcases hLe with he | hLess
  · have hTop := top_root_d hM hD.mountain hHeight
    have hRoot' : RootAt M C D.mountain height c D.coordinates.root := he ▸ hRoot
    have hRootC := hRoot'.unique_d hM hC hD.mountain hTop
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c (hRootC ▸ hAfter))
  · exact hLess

private theorem nat_le_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain} (hc : M.mem c C.omega)
    (hab : a=b ∨ M.mem a b) (hbc : b=c ∨ M.mem b c) : a=c ∨ M.mem a c := by
  rcases hab with he | hab
  · exact he ▸ hbc
  · rcases hbc with he | hbc
    · exact Or.inr (he ▸ hab)
    · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hc).transitive b hbc a hab)

theorem InCone.high_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C) {c p r : M.Domain}
    (h : InCone M C D c) (hHigh : D.floor=r ∨ M.mem D.floor r) (hParent : ParentAt M D.mountain r c p) : InCone M C D p := by
  obtain ⟨_,_,_,_,hRoot⟩ := h
  obtain ⟨height,hh,hAt⟩ := hD.mountain.heights.total p (hParent.bounds hM.1 hD.mountain).2.2.1
  have hLe := nat_le_trans_d hM hC hh hHigh (hD.mountain.endpoint r c p height hParent hAt)
  exact ⟨height,hh,hAt,hLe,(hD.coherent D.floor r c p D.coordinates.root (hD.floor_nat hM.1) hHigh hParent).mp hRoot⟩


def Context.map {α : Type u} {β : Type v} (D : Context α) (f : α → β) : Context β :=
  ⟨D.coordinates.map f,D.mountain.map f,f D.floor,f D.rise⟩

def Context.eval {M : SetTheory.Structure.{u}} {n : Nat} (D : Context (Project.Term n)) (e : Env M n) : Context M.Domain := D.map (fun t => t.eval e)
def Context.weaken {n : Nat} (D : Context (Project.Term n)) : Context (Project.Term (n+1)) := D.map (fun t => t.weaken)

theorem Context.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat} (D : Context (Project.Term n)) (e : Env M n) (x : M.Domain) :
    D.weaken.eval (e.push x)=D.eval e := by
  rcases D with ⟨A,X,floor,rise⟩
  cases A
  cases X
  simp [Context.eval,Context.weaken,Context.map,CopyCoordinates.Context.map,Data.map,Term.eval_weaken]

structure Context.Closed {n : Nat} (D : Context (Project.Term n)) : Prop where
  coordinates : D.coordinates.Closed
  mountain : D.mountain.Closed
  floor : D.floor.freeSupport=[]
  rise : D.rise.freeSupport=[]

theorem Context.Closed.weaken {n : Nat} {D : Context (Project.Term n)} (h : D.Closed) : D.weaken.Closed := by
  exact ⟨h.coordinates.weaken,h.mountain.weaken,by simpa [Context.weaken,Context.map] using h.floor,
    by simpa [Context.weaken,Context.map] using h.rise⟩

def inConeFormula {n : Nat} (C : ExpressionData (Project.Term n)) (D : Context (Project.Term n)) (c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (.conj (memPairFormula D.mountain.heights.weaken c.weaken (.bound 0))
    (.conj (.disj (Project.Formula.extensionalEq D.floor.weaken (.bound 0)) (.mem D.floor.weaken (.bound 0)))
      (rootAtFormula C.weaken D.mountain.weaken D.floor.weaken c.weaken D.coordinates.root.weaken)))

theorem inConeFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (D : Context (Project.Term n)) (c : Project.Term n) :
    (inConeFormula C D c).IsDelta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _)
      (.conj (.disj (.atom _ _ _) (.mem _ _)) (rootAtFormula_delta0 _ _ _ _ _)))

theorem inConeFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {D : Context (Project.Term n)} (hD : D.Closed) (c : Project.Term n) (hc : c.freeSupport=[]) : (inConeFormula C D c).FreeClosed := by
  have hRoot := rootAtFormula_freeClosed hC.weaken hD.mountain.weaken D.floor.weaken c.weaken D.coordinates.root.weaken
    (by simpa using hD.floor) (by simpa using hc) (by simpa using hD.coordinates.root)
  simp [inConeFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,hC.omega,hD.mountain.heights,hD.floor,hc,hRoot]

theorem inConeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (D : Context (Project.Term n)) (c : Project.Term n) :
    Project.Formula.satisfies e (inConeFormula C D c) ↔ InCone M (C.eval e) (D.eval e) (c.eval e) := by
  simp only [inConeFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,
    memPairFormula_iff he,rootAtFormula_iff he,ExpressionData.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  rfl

/-- 较低层原始 c≤last 逐字保留，之后在锥内按 block*rise 增加高度。 -/
def Height (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Context M.Domain) (c h : M.Domain) : Prop := M.mem c C.omega ∧
  (((c=D.coordinates.last ∨ M.mem c D.coordinates.last) ∧ MemPair M D.mountain.heights c h) ∨
    (M.mem D.coordinates.last c ∧ ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧
      CopyCoordinates.RawDecoded M C T D.coordinates c s b ∧ ∃ a, M.mem a C.omega ∧ MemPair M D.mountain.heights s a ∧
        ((InCone M C D s ∧ ∃ off, M.mem off C.omega ∧ MulAt M T.mulPairs T.times b D.rise off ∧ AddAt M T.addPairs T.plus a off h) ∨
          (¬InCone M C D s ∧ h=a))))

def heightFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Context (Project.Term n)) (c h : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem c C.omega) (.disj
    (.conj (.disj (Project.Formula.extensionalEq c D.coordinates.last) (.mem c D.coordinates.last)) (memPairFormula D.mountain.heights c h))
    (.conj (.mem D.coordinates.last c) (Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
      (.conj (CopyCoordinates.rawDecodedFormula C.weaken.weaken T.weaken.weaken D.coordinates.weaken.weaken c.weaken.weaken (.bound 1) (.bound 0))
        (Project.Formula.existsMem C.omega.weaken.weaken (.conj (memPairFormula D.mountain.heights.weaken.weaken.weaken (.bound 2) (.bound 0))
          (.disj (.conj (inConeFormula C.weaken.weaken.weaken D.weaken.weaken.weaken (.bound 2))
            (Project.Formula.existsMem C.omega.weaken.weaken.weaken
              (.conj (mulAtFormula T.mulPairs.weaken.weaken.weaken.weaken T.times.weaken.weaken.weaken.weaken
                (.bound 2) D.rise.weaken.weaken.weaken.weaken (.bound 0))
                (addAtFormula T.addPairs.weaken.weaken.weaken.weaken T.plus.weaken.weaken.weaken.weaken (.bound 1) (.bound 0) h.weaken.weaken.weaken.weaken))))
            (.conj (.neg (inConeFormula C.weaken.weaken.weaken D.weaken.weaken.weaken (.bound 2)))
              (Project.Formula.extensionalEq h.weaken.weaken.weaken (.bound 0)))))))))))

theorem heightFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Context (Project.Term n)) (c h : Project.Term n) : (heightFormula C T D c h).IsDelta0 :=
  .conj (.mem _ _) (.disj (.conj (.disj (.atom _ _ _) (.mem _ _)) (memPairFormula_delta0 _ _ _))
    (.conj (.mem _ _) (.existsMem _ (.existsMem _ (.conj (CopyCoordinates.rawDecodedFormula_delta0 _ _ _ _ _ _)
      (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.disj
        (.conj (inConeFormula_delta0 _ _ _) (.existsMem _ (.conj (mulAtFormula_delta0 _ _ _ _ _) (addAtFormula_delta0 _ _ _ _ _))))
        (.conj (.neg (inConeFormula_delta0 _ _ _)) (.atom _ _ _))))))))))

theorem heightFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T)
    {D : Context (Project.Term n)} (hD : D.Closed) (c h : Project.Term n) (hc : c.freeSupport=[]) (hh : h.freeSupport=[]) :
    (heightFormula C T D c h).FreeClosed := by
  have hRaw := CopyCoordinates.rawDecodedFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hD.coordinates.weaken.weaken
    c.weaken.weaken (.bound 1) (.bound 0) (by simpa using hc) rfl rfl
  have hCone := inConeFormula_freeClosed hC.weaken.weaken.weaken hD.weaken.weaken.weaken (Project.Term.bound (depth := n+3) 2) rfl
  simp [heightFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    mulAtFormula,addAtFormula,Project.Formula.forallMem,hC.omega,hD.coordinates.last,hD.mountain.heights,hD.rise,
    hT.mulPairs,hT.times,hT.addPairs,hT.plus,hc,hh,hRaw,hCone]

theorem heightFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (D : Context (Project.Term n)) (c h : Project.Term n) :
    Project.Formula.satisfies e (heightFormula C T D c h) ↔ Height M (C.eval e) (T.eval e) (D.eval e) (c.eval e) (h.eval e) := by
  simp only [heightFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_neg_iff,
    memPairFormula_iff he,CopyCoordinates.rawDecodedFormula_iff he,inConeFormula_iff he,mulAtFormula_iff he,addAtFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Context.eval_weaken,Term.eval_weaken]
  rfl


private theorem old_new_disjoint_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {c last : M.Domain} (hc : M.mem c C.omega)
    (hOld : c=last ∨ M.mem c last) (hNew : M.mem last c) : False := by
  rcases hOld with he | hlt
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c (he.symm ▸ hNew)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c
      (((omega_isOrdinal_d hM hC.omega).mem hc).transitive last hNew c hlt)

theorem height_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {c : M.Domain} (hc : M.mem c C.omega) :
    ∃ h, M.mem h C.omega ∧ Height M C T D c h := by
  classical
  have hw := omega_isOrdinal_d hM hC.omega
  by_cases hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last
  · have hcM : M.mem c D.mountain.width := by
      rcases hOld with he | hlt
      · exact he.symm ▸ hD.last
      · exact (hw.mem hD.mountain.width).transitive D.coordinates.last hD.last c hlt
    obtain ⟨h,hh,hAt⟩ := hD.mountain.heights.total c hcM
    exact ⟨h,hh,hc,Or.inl ⟨hOld,hAt⟩⟩
  · have hNew : M.mem D.coordinates.last c := by
      rcases hw.wellOrder.linear.compare c hc D.coordinates.last hD.coordinates.last with he | hlt | hgt
      · exact False.elim (hOld (Or.inl (hM.1.eq_of_same_members _ _ he)))
      · exact False.elim (hOld (Or.inr hlt))
      · exact hgt
    obtain ⟨s,b,hRaw⟩ := CopyCoordinates.raw_decode_exists_d hM hC hT hD.coordinates hc
    have hSource := CopyCoordinates.raw_decoded_source_bounds_d hM hC hD.coordinates hRaw
    have hsM : M.mem s D.mountain.width := by
      rcases hSource.2 with he | hlt
      · exact he.symm ▸ hD.last
      · exact (hw.mem hD.mountain.width).transitive D.coordinates.last hD.last s hlt
    obtain ⟨a,ha,hAt⟩ := hD.mountain.heights.total s hsM
    by_cases hCone : InCone M C D s
    · obtain ⟨off,hOff,hMul⟩ := hT.mul.mul_exists_d hM hC hRaw.2.1 (hD.rise_nat hM.1)
      obtain ⟨h,hh,hAdd⟩ := hT.add.add_exists_d hM hC ha hOff
      exact ⟨h,hh,hc,Or.inr ⟨hNew,s,hRaw.1,b,hRaw.2.1,hRaw,a,ha,hAt,Or.inl ⟨hCone,off,hOff,hMul,hAdd⟩⟩⟩
    · exact ⟨a,ha,hc,Or.inr ⟨hNew,s,hRaw.1,b,hRaw.2.1,hRaw,a,ha,hAt,Or.inr ⟨hCone,rfl⟩⟩⟩

theorem Height.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {c h h' : M.Domain} (hH : Height M C T D c h) (hH' : Height M C T D c h') : h=h' := by
  rcases hH.2 with ⟨hOld,hAt⟩ | ⟨hNew,s,_,b,_,hRaw,a,_,hAt,hLift⟩ <;>
    rcases hH'.2 with ⟨hOld',hAt'⟩ | ⟨hNew',s',_,b',_,hRaw',a',_,hAt',hLift'⟩
  · exact hD.mountain.heights.unique c h h' hAt hAt'
  · exact False.elim (old_new_disjoint_d hM hC hH.1 hOld hNew')
  · exact False.elim (old_new_disjoint_d hM hC hH.1 hOld' hNew)
  · obtain ⟨hss,hbb⟩ := CopyCoordinates.raw_decode_unique_d hM hC hT hD.coordinates hRaw hRaw'
    subst s'
    subst b'
    have haa := hD.mountain.heights.unique s a a' hAt hAt'
    subst a'
    rcases hLift with ⟨hCone,off,_,hMul,hAdd⟩ | ⟨hNot,hh⟩ <;>
      rcases hLift' with ⟨hCone',off',_,hMul',hAdd'⟩ | ⟨hNot',hh'⟩
    · have hoo := hT.mul.mul_unique hM.1 hMul hMul'
      subst off'
      exact hT.add.add_unique hM.1 hAdd hAdd'
    · exact False.elim (hNot' hCone)
    · exact False.elim (hNot hCone')
    · exact hh.trans hh'.symm

theorem Height.natural {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {c h : M.Domain} (hH : Height M C T D c h) : M.mem h C.omega := by
  rcases hH.2 with ⟨_,hAt⟩ | ⟨_,_,_,_,_,_,a,ha,_,hLift⟩
  · exact (hD.mountain.heights.bounds he hAt).2
  · rcases hLift with ⟨_,_,_,_,hAdd⟩ | ⟨_,hh⟩
    · exact (hAdd.bounds he hT.add).2.2
    · exact hh.symm ▸ ha


/-- 高度方向的 a+b*rise，由已构造乘法/加法表读取。 -/
def Lifted (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Context M.Domain) (a b h : M.Domain) : Prop :=
  M.mem a C.omega ∧ M.mem b C.omega ∧ ∃ off, M.mem off C.omega ∧ MulAt M T.mulPairs T.times b D.rise off ∧ AddAt M T.addPairs T.plus a off h

theorem lifted_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {a b : M.Domain} (ha : M.mem a C.omega) (hb : M.mem b C.omega) :
    ∃ h, M.mem h C.omega ∧ Lifted M C T D a b h := by
  obtain ⟨off,hOff,hMul⟩ := hT.mul.mul_exists_d hM hC hb (hD.rise_nat hM.1)
  obtain ⟨h,hh,hAdd⟩ := hT.add.add_exists_d hM hC ha hOff
  exact ⟨h,hh,ha,hb,off,hOff,hMul,hAdd⟩

theorem Lifted.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} {a b h h' : M.Domain} (hH : Lifted M C T D a b h) (hH' : Lifted M C T D a b h') : h=h' := by
  obtain ⟨_,_,off,_,hMul,hAdd⟩ := hH
  obtain ⟨_,_,off',_,hMul',hAdd'⟩ := hH'
  have heq := hT.mul.mul_unique he hMul hMul'
  subst off'
  exact hT.add.add_unique he hAdd hAdd'

theorem lifted_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {a : M.Domain} (ha : M.mem a C.omega) : Lifted M C T D a C.zero a := by
  obtain ⟨off,_,hMul⟩ := hT.mul.mul_exists_d hM hC hC.zero_nat (hD.rise_nat hM.1)
  have ho := natural_product_zero_left_d hM hC (hD.rise_nat hM.1) ((hT.mul.mul_iff_product hM hC.zero_nat (hD.rise_nat hM.1)).mp hMul)
  subst off
  exact ⟨ha,hC.zero_nat,C.zero,hC.zero_nat,hMul,(hT.add.add_iff_sum hM ha hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM a hC.zero_empty)⟩

/-- 一次 seam 换号：先加一个rise再复制b块，等于从低底值复制b+1块。 -/
theorem Lifted.successor_base_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {a a' b next h : M.Domain}
    (ha : M.mem a C.omega) (hBase : KP1Y.Arithmetic.Sum M a D.rise a') (hSucc : M.SuccessorOf next b)
    (hH : Lifted M C T D a' b h) : Lifted M C T D a next h := by
  obtain ⟨ha',hb,off,hOff,hMul,hAdd⟩ := hH
  have hn := natural_successor_mem_d hM hC hb hSucc
  obtain ⟨nextOff,hNextOff,hNextMul⟩ := hT.mul.mul_exists_d hM hC hn (hD.rise_nat hM.1)
  have hOldProd := (hT.mul.mul_iff_product hM hb (hD.rise_nat hM.1)).mp hMul
  have hNewProd := (hT.mul.mul_iff_product hM hn (hD.rise_nat hM.1)).mp hNextMul
  have hOffRise := natural_product_left_successor_d hM hC hb (hD.rise_nat hM.1) hSucc hOldProd hNewProd
  have hRiseOff := natural_sum_comm_d hM hC hOff (hD.rise_nat hM.1) hOffRise
  obtain ⟨target,_,hTarget⟩ := hT.add.add_exists_d hM hC ha hNextOff
  have heq := natural_sum_assoc_d hM hC (hD.rise_nat hM.1) hOff hBase
    ((hT.add.add_iff_sum hM ha' hOff).mp hAdd) hRiseOff ((hT.add.add_iff_sum hM ha hNextOff).mp hTarget)
  exact ⟨ha,hn,nextOff,hNextOff,hNextMul,heq.symm ▸ hTarget⟩

/-- 同一高度的普通坐标正规形；root seam的后一块计数在这里显式体现。 -/
def UniformHeight (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Context M.Domain) (c h : M.Domain) : Prop :=
  ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧ OrdinaryCoordinates.Decoded M C T D.coordinates c s b ∧
    ∃ a, M.mem a C.omega ∧ MemPair M D.mountain.heights s a ∧
      ((InCone M C D s ∧ Lifted M C T D a b h) ∨ (¬InCone M C D s ∧ h=a))

theorem UniformHeight.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {c h h' : M.Domain}
    (hH : UniformHeight M C T D c h) (hH' : UniformHeight M C T D c h') : h=h' := by
  obtain ⟨s,_,b,_,hDec,a,_,hAt,hLift⟩ := hH
  obtain ⟨s',_,b',_,hDec',a',_,hAt',hLift'⟩ := hH'
  obtain ⟨hss,hbb⟩ := hDec.unique_d hM hC hT hD.coordinates hDec'
  subst s'
  subst b'
  have haa := hD.mountain.heights.unique s a a' hAt hAt'
  subst a'
  rcases hLift with ⟨hCone,hLift⟩ | ⟨hNot,hh⟩ <;> rcases hLift' with ⟨hCone',hLift'⟩ | ⟨hNot',hh'⟩
  · exact hLift.unique hM.1 hT hLift'
  · exact False.elim (hNot' hCone)
  · exact False.elim (hNot hCone')
  · exact hh.trans hh'.symm

theorem Height.uniform_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {c h : M.Domain} (hH : Height M C T D c h) : UniformHeight M C T D c h := by
  classical
  have hw := omega_isOrdinal_d hM hC.omega
  rcases hH.2 with ⟨hOld,hAt⟩ | ⟨hNew,s,hs,b,hb,hRaw,a,ha,hAt,hLift⟩
  · rcases hOld with he | hOld
    · subst c
      have hRaw := CopyCoordinates.raw_original_coordinates_d hM hC hT hD.coordinates ⟨hD.coordinates.below,Or.inl rfl⟩
      obtain ⟨next,hSucc,hDec⟩ := OrdinaryCoordinates.raw_seam_decoded_d hM hC hT hD.coordinates hD.coordinates.last hD.coordinates.below hRaw
      have hLift : Lifted M C T D D.floor next h :=
        (lifted_zero_d hM hC hT hD (hD.mountain.heights.bounds hM.1 hAt).2).successor_base_d hM hC hT hD
          (hD.floor_nat hM.1) (hD.last_height_d hM hC hAt) hSucc
      exact ⟨D.coordinates.root,hD.coordinates.root,next,hDec.2.2.1,hDec,D.floor,hD.floor_nat hM.1,hD.floor,
        Or.inl ⟨in_cone_root_d hM hD,hLift⟩⟩
    · have hDec := OrdinaryCoordinates.decoded_original_d hM hC hT hD.coordinates hOld
      refine ⟨c,hDec.2.1,C.zero,hC.zero_nat,hDec,h,(hD.mountain.heights.bounds hM.1 hAt).2,hAt,?_⟩
      by_cases hCone : InCone M C D c
      · exact Or.inl ⟨hCone,lifted_zero_d hM hC hT hD (hD.mountain.heights.bounds hM.1 hAt).2⟩
      · exact Or.inr ⟨hCone,rfl⟩
  · have hAfter := (hw.mem hH.1).transitive D.coordinates.last hNew D.coordinates.root hD.coordinates.below
    rcases (CopyCoordinates.raw_decoded_source_bounds_d hM hC hD.coordinates hRaw).2 with he | hSmall
    · subst s
      obtain ⟨next,hSucc,hDec⟩ := OrdinaryCoordinates.raw_seam_decoded_d hM hC hT hD.coordinates hH.1 hAfter hRaw
      have hLastCone := in_cone_last hD
      rcases hLift with ⟨_,off,hOff,hMul,hAdd⟩ | ⟨hNot,_⟩
      · have hHeightLift : Lifted M C T D a b h := ⟨ha,hb,off,hOff,hMul,hAdd⟩
        have hNewLift := hHeightLift.successor_base_d hM hC hT hD (hD.floor_nat hM.1) (hD.last_height_d hM hC hAt) hSucc
        exact ⟨D.coordinates.root,hD.coordinates.root,next,hDec.2.2.1,hDec,D.floor,hD.floor_nat hM.1,hD.floor,
          Or.inl ⟨in_cone_root_d hM hD,hNewLift⟩⟩
      · exact False.elim (hNot hLastCone)
    · have hDec := OrdinaryCoordinates.raw_nonseam_decoded_d hM hC hT hD.coordinates hH.1 hAfter hRaw hSmall
      refine ⟨s,hs,b,hb,hDec,a,ha,hAt,?_⟩
      rcases hLift with ⟨hCone,off,hOff,hMul,hAdd⟩ | hNot
      · exact Or.inl ⟨hCone,ha,hb,off,hOff,hMul,hAdd⟩
      · exact Or.inr hNot

theorem height_iff_uniform_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {c h : M.Domain} : Height M C T D c h ↔ UniformHeight M C T D c h := by
  constructor
  · exact fun h => h.uniform_d hM hC hT hD
  · intro hUniform
    have hc : M.mem c C.omega := by
      obtain ⟨_,_,_,_,hDec,_⟩ := hUniform
      exact hDec.1
    obtain ⟨h',_,hHeight⟩ := height_exists_d hM hC hT hD hc
    have heq := hUniform.unique_d hM hC hT hD (hHeight.uniform_d hM hC hT hD)
    exact heq.symm ▸ hHeight


theorem InCone.not_good_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C) {p : M.Domain}
    (h : InCone M C D p) : ¬M.mem p D.coordinates.root := by
  intro hp
  rcases h.root_le hM.1 hD with he | hRoot
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (he ▸ hp)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root
      (((omega_isOrdinal_d hM hC.omega).mem hD.coordinates.root).transitive p hp D.coordinates.root hRoot)

theorem height_parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {p b c a h : M.Domain}
    (hp : M.mem p D.coordinates.last) (hCopy : CopyCoordinates.ParentCopy M C T D.coordinates b p c)
    (hBase : MemPair M D.mountain.heights p a) :
    Height M C T D c h ↔ ((InCone M C D p ∧ Lifted M C T D a b h) ∨ (¬InCone M C D p ∧ h=a)) := by
  have hExact (hCone : InCone M C D p) : OrdinaryCoordinates.Decoded M C T D.coordinates c p b := by
    rcases hCopy.2.2 with ⟨hGood,_⟩ | ⟨hNot,hEncode⟩
    · exact False.elim (hCone.not_good_d hM hC hD hGood)
    · exact OrdinaryCoordinates.decoded_encode_d hM hC hT hD.coordinates hp hNot hEncode
  rw [height_iff_uniform_d hM hC hT hD]
  constructor
  · rintro ⟨s,_,block,_,hDec,a',_,hAt,hLift⟩
    have hsp := hDec.source_parent_copy_d hM hC hT hD.coordinates hp hCopy
    subst s
    have haa := hD.mountain.heights.unique p a' a hAt hBase
    subst a'
    rcases hLift with ⟨hCone,hLift⟩ | hNot
    · have hbb := (hDec.unique_d hM hC hT hD.coordinates (hExact hCone)).2
      subst block
      exact Or.inl ⟨hCone,hLift⟩
    · exact Or.inr hNot
  · rintro (⟨hCone,hLift⟩ | ⟨hNot,hh⟩)
    · exact ⟨p,hCopy.1,b,hCopy.2.1,hExact hCone,a,(hD.mountain.heights.bounds hM.1 hBase).2,hBase,Or.inl ⟨hCone,hLift⟩⟩
    · obtain ⟨block,hDec⟩ := OrdinaryCoordinates.decoded_parent_copy_d hM hC hT hD.coordinates hp hCopy
      exact ⟨p,hCopy.1,block,hDec.2.2.1,hDec,a,(hD.mountain.heights.bounds hM.1 hBase).2,hBase,Or.inr ⟨hNot,hh⟩⟩

theorem Lifted.base_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} {a b h : M.Domain} (hH : Lifted M C T D a b h) : a=h ∨ M.mem a h := by
  obtain ⟨ha,_,off,hOff,_,hAdd⟩ := hH
  have hh := (hAdd.bounds hM.1 hT.add).2.2
  have hSum := (hT.add.add_iff_sum hM ha hOff).mp hAdd
  exact ordinal_subset_cases_d hM ((omega_isOrdinal_d hM hC.omega).mem ha) ((omega_isOrdinal_d hM hC.omega).mem hh)
    (KP1Y.Arithmetic.sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem ha) hSum)

theorem Height.parent_copy_ge_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {p b c a h : M.Domain}
    (hp : M.mem p D.coordinates.last) (hCopy : CopyCoordinates.ParentCopy M C T D.coordinates b p c)
    (hBase : MemPair M D.mountain.heights p a) (hHeight : Height M C T D c h) : a=h ∨ M.mem a h := by
  rcases (height_parent_copy_iff_d hM hC hT hD hp hCopy hBase).mp hHeight with ⟨_,hLift⟩ | ⟨_,hh⟩
  · exact hLift.base_le_d hM hC hT
  · exact Or.inl hh.symm

theorem height_original_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {D : Context M.Domain} (hD : D.Valid M C)
    {c h : M.Domain} (hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last) : Height M C T D c h ↔ MemPair M D.mountain.heights c h := by
  constructor
  · intro hH
    rcases hH.2 with ⟨_,hAt⟩ | ⟨hNew,_⟩
    · exact hAt
    · exact False.elim (old_new_disjoint_d hM hC hH.1 hOld hNew)
  · intro hAt
    have hc := (omega_isOrdinal_d hM hC.omega).transitive D.mountain.width hD.mountain.width c (hD.mountain.heights.bounds hM.1 hAt).1
    exact ⟨hc,Or.inl ⟨hOld,hAt⟩⟩


private def copyEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Context M.Domain) : Env M 21 :=
  (((((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push D.coordinates.last).push D.coordinates.root).push D.coordinates.length).push D.coordinates.first).push D.mountain.width).push D.mountain.heights).push D.mountain.forests).push D.mountain.parents).push D.floor).push D.rise)

private def heightSchema : Project.Delta0BinarySchema 21 where
  body := heightFormula ⟨.bound 22,.bound 21,.bound 20,.bound 19,.bound 18⟩ ⟨.bound 17,.bound 16,.bound 15,.bound 14,.bound 13,.bound 12⟩
    ⟨⟨.bound 11,.bound 10,.bound 9,.bound 8⟩,⟨.bound 7,.bound 6,.bound 5,.bound 4⟩,.bound 3,.bound 2⟩ (.bound 1) (.bound 0)
  freeClosed := heightFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    ⟨⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩ _ _ rfl rfl
  delta0 := heightFormula_delta0 _ _ _ _ _

private theorem heightSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (D : Context M.Domain) (c h : M.Domain) :
    Project.Formula.satisfies (((copyEnv C T D).push c).push h) heightSchema.body ↔ Height M C T D c h :=
  heightFormula_iff he _ _ _ _ _ _

theorem height_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {n : M.Domain} (hn : M.mem n C.omega) :
    ∃ Heights, Graph M Heights n C.omega ∧ ∀ c h, MemPair M Heights c h ↔ M.mem c n ∧ Height M C T D c h := by
  obtain ⟨Heights,hSupport,hRaw⟩ := relation_comprehension_d hM heightSchema (copyEnv C T D) n C.omega
  have hRows (c h : M.Domain) : MemPair M Heights c h ↔ M.mem c n ∧ Height M C T D c h := by
    have hr := hRaw c h
    rw [heightSchema_iff hM.1] at hr
    exact hr.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.natural hM.1 hT hD,h.2⟩⟩
  refine ⟨Heights,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨h,hh,hHeight⟩ := height_exists_d hM hC hT hD ((omega_isOrdinal_d hM hC.omega).transitive n hn c hc)
    exact ⟨h,hh,(hRows c h).mpr ⟨hc,hHeight⟩⟩
  · intro c h h' hAt hAt'
    exact ((hRows c h).mp hAt).2.unique_d hM hC hT hD ((hRows c h').mp hAt').2


def MovedParent (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Context M.Domain) (r s b q : M.Domain) : Prop :=
  ∃ off, M.mem off C.omega ∧ MulAt M T.mulPairs T.times b D.rise off ∧ ∃ u, M.mem u C.omega ∧
    ShiftedRow M C T D.floor off r u ∧ ∃ p, M.mem p C.omega ∧ ParentAt M D.mountain u s p ∧
      CopyCoordinates.Encode M C T D.coordinates p b q

/-- 精确旧段 / gap或高行纯平移 / 未移动行ParentCopy 三分支。 -/
def Parent (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Context M.Domain) (r c q : M.Domain) : Prop := M.mem r C.omega ∧ M.mem c C.omega ∧
  (((c=D.coordinates.last ∨ M.mem c D.coordinates.last) ∧ ParentAt M D.mountain r c q) ∨
    (M.mem D.coordinates.last c ∧ ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧
      CopyCoordinates.RawDecoded M C T D.coordinates c s b ∧
      (((InCone M C D s ∧ (D.floor=r ∨ M.mem D.floor r)) ∧ MovedParent M C T D r s b q) ∨
        (¬(InCone M C D s ∧ (D.floor=r ∨ M.mem D.floor r)) ∧ ∃ p, M.mem p C.omega ∧
          ParentAt M D.mountain r s p ∧ CopyCoordinates.ParentCopy M C T D.coordinates b p q))))

def movedParentFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Context (Project.Term n)) (r s b q : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (.conj (mulAtFormula T.mulPairs.weaken T.times.weaken b.weaken D.rise.weaken (.bound 0))
    (Project.Formula.existsMem C.omega.weaken (.conj
      (shiftedRowFormula C.weaken.weaken T.weaken.weaken D.floor.weaken.weaken (.bound 1) r.weaken.weaken (.bound 0))
      (Project.Formula.existsMem C.omega.weaken.weaken (.conj
        (parentAtFormula D.mountain.weaken.weaken.weaken (.bound 1) s.weaken.weaken.weaken (.bound 0))
        (CopyCoordinates.encodeFormula C.weaken.weaken.weaken T.weaken.weaken.weaken D.coordinates.weaken.weaken.weaken
          (.bound 0) b.weaken.weaken.weaken q.weaken.weaken.weaken))))))

theorem movedParentFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Context (Project.Term n)) (r s b q : Project.Term n) : (movedParentFormula C T D r s b q).IsDelta0 :=
  .existsMem _ (.conj (mulAtFormula_delta0 _ _ _ _ _) (.existsMem _ (.conj (shiftedRowFormula_delta0 _ _ _ _ _ _)
    (.existsMem _ (.conj (parentAtFormula_delta0 _ _ _ _) (CopyCoordinates.encodeFormula_delta0 _ _ _ _ _ _))))))

theorem movedParentFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (D : Context (Project.Term n)) (r s b q : Project.Term n) :
    Project.Formula.satisfies e (movedParentFormula C T D r s b q) ↔
      MovedParent M (C.eval e) (T.eval e) (D.eval e) (r.eval e) (s.eval e) (b.eval e) (q.eval e) := by
  simp only [movedParentFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    mulAtFormula_iff he,shiftedRowFormula_iff he,parentAtFormula_iff he,CopyCoordinates.encodeFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  rfl

def movesFormula {n : Nat} (C : ExpressionData (Project.Term n)) (D : Context (Project.Term n)) (r s : Project.Term n) : Project.Formula 1 n :=
  .conj (inConeFormula C D s) (.disj (Project.Formula.extensionalEq D.floor r) (.mem D.floor r))

theorem movesFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (D : Context (Project.Term n)) (r s : Project.Term n) :
    (movesFormula C D r s).IsDelta0 := .conj (inConeFormula_delta0 _ _ _) (.disj (.atom _ _ _) (.mem _ _))

def parentFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Context (Project.Term n)) (r c q : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem r C.omega) (.conj (.mem c C.omega) (.disj
    (.conj (.disj (Project.Formula.extensionalEq c D.coordinates.last) (.mem c D.coordinates.last)) (parentAtFormula D.mountain r c q))
    (.conj (.mem D.coordinates.last c) (Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
      (.conj (CopyCoordinates.rawDecodedFormula C.weaken.weaken T.weaken.weaken D.coordinates.weaken.weaken c.weaken.weaken (.bound 1) (.bound 0))
        (.disj (.conj (movesFormula C.weaken.weaken D.weaken.weaken r.weaken.weaken (.bound 1))
          (movedParentFormula C.weaken.weaken T.weaken.weaken D.weaken.weaken r.weaken.weaken (.bound 1) (.bound 0) q.weaken.weaken))
          (.conj (.neg (movesFormula C.weaken.weaken D.weaken.weaken r.weaken.weaken (.bound 1)))
            (Project.Formula.existsMem C.omega.weaken.weaken (.conj
              (parentAtFormula D.mountain.weaken.weaken.weaken r.weaken.weaken.weaken (.bound 2) (.bound 0))
              (CopyCoordinates.parentCopyFormula C.weaken.weaken.weaken T.weaken.weaken.weaken D.coordinates.weaken.weaken.weaken
                (.bound 1) (.bound 0) q.weaken.weaken.weaken)))))))))))

theorem parentFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Context (Project.Term n)) (r c q : Project.Term n) : (parentFormula C T D r c q).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.disj (.conj (.disj (.atom _ _ _) (.mem _ _)) (parentAtFormula_delta0 _ _ _ _))
    (.conj (.mem _ _) (.existsMem _ (.existsMem _ (.conj (CopyCoordinates.rawDecodedFormula_delta0 _ _ _ _ _ _)
      (.disj (.conj (movesFormula_delta0 _ _ _ _) (movedParentFormula_delta0 _ _ _ _ _ _ _))
        (.conj (.neg (movesFormula_delta0 _ _ _ _)) (.existsMem _
          (.conj (parentAtFormula_delta0 _ _ _ _) (CopyCoordinates.parentCopyFormula_delta0 _ _ _ _ _ _)))))))))))

theorem parentFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (D : Context (Project.Term n)) (r c q : Project.Term n) :
    Project.Formula.satisfies e (parentFormula C T D r c q) ↔ Parent M (C.eval e) (T.eval e) (D.eval e) (r.eval e) (c.eval e) (q.eval e) := by
  simp only [parentFormula,movesFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_existsMem_iff,parentAtFormula_iff he,CopyCoordinates.rawDecodedFormula_iff he,
    inConeFormula_iff he,movedParentFormula_iff he,CopyCoordinates.parentCopyFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Context.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  simp only [Context.weaken,Context.map,Term.eval_weaken]
  rfl


theorem movedParentFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {D : Context (Project.Term n)} (hD : D.Closed)
    (r s b q : Project.Term n) (hr : r.freeSupport=[]) (hs : s.freeSupport=[]) (hb : b.freeSupport=[]) (hq : q.freeSupport=[]) :
    (movedParentFormula C T D r s b q).FreeClosed := by
  have hShift := shiftedRowFormula_freeClosed hC.weaken.weaken hT.weaken.weaken D.floor.weaken.weaken (.bound 1) r.weaken.weaken (.bound 0)
    (by simpa using hD.floor) rfl (by simpa using hr) rfl
  have hParent := parentAtFormula_freeClosed hD.mountain.weaken.weaken.weaken (.bound 1) s.weaken.weaken.weaken (.bound 0)
    rfl (by simpa using hs) rfl
  have hEncode := CopyCoordinates.encodeFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken hD.coordinates.weaken.weaken.weaken
    (.bound 0) b.weaken.weaken.weaken q.weaken.weaken.weaken rfl (by simpa using hb) (by simpa using hq)
  simp [movedParentFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,mulAtFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,hC.omega,hT.mulPairs,hT.times,hD.rise,hb,hShift,hParent,hEncode]

theorem movesFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {D : Context (Project.Term n)} (hD : D.Closed) (r s : Project.Term n) (hr : r.freeSupport=[]) (hs : s.freeSupport=[]) :
    (movesFormula C D r s).FreeClosed := by
  have hCone := inConeFormula_freeClosed hC hD s hs
  simp [movesFormula,Definitional.Formula.FreeClosed,hCone,hD.floor,hr]

theorem parentFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {D : Context (Project.Term n)} (hD : D.Closed)
    (r c q : Project.Term n) (hr : r.freeSupport=[]) (hc : c.freeSupport=[]) (hq : q.freeSupport=[]) :
    (parentFormula C T D r c q).FreeClosed := by
  have hOld := parentAtFormula_freeClosed hD.mountain r c q hr hc hq
  have hRaw := CopyCoordinates.rawDecodedFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hD.coordinates.weaken.weaken
    c.weaken.weaken (.bound 1) (.bound 0) (by simpa using hc) rfl rfl
  have hMove := movesFormula_freeClosed hC.weaken.weaken hD.weaken.weaken r.weaken.weaken (.bound 1) (by simpa using hr) rfl
  have hMoved := movedParentFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hD.weaken.weaken
    r.weaken.weaken (.bound 1) (.bound 0) q.weaken.weaken (by simpa using hr) rfl rfl (by simpa using hq)
  have hParent := parentAtFormula_freeClosed hD.mountain.weaken.weaken.weaken r.weaken.weaken.weaken (.bound 2) (.bound 0)
    (by simpa using hr) rfl rfl
  have hCopy := CopyCoordinates.parentCopyFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken hD.coordinates.weaken.weaken.weaken
    (.bound 1) (.bound 0) q.weaken.weaken.weaken rfl rfl (by simpa using hq)
  simp [parentFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hD.coordinates.last,hr,hc,hOld,hRaw,hMove,hMoved,hParent,hCopy]

theorem MovedParent.unique_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r s b q q' : M.Domain}
    (h : MovedParent M C T D r s b q) (h' : MovedParent M C T D r s b q') : q=q' := by
  obtain ⟨off,_,hMul,u,_,hShift,p,_,hParent,hEncode⟩ := h
  obtain ⟨off',_,hMul',u',_,hShift',p',_,hParent',hEncode'⟩ := h'
  have hoo := hT.mul.mul_unique he hMul hMul'
  subst off'
  have huu := shifted_row_unique he hT hShift hShift'
  subst u'
  have hpp := hParent.unique hD.mountain hParent'
  subst p'
  exact CopyCoordinates.encode_unique he hT hEncode hEncode'

private theorem encode_strict_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {p s b q c : M.Domain} (hLeft : M.mem p s)
    (hP : CopyCoordinates.Encode M C T A p b q) (hS : CopyCoordinates.Encode M C T A s b c) : M.mem q c := by
  obtain ⟨hp,_,off,hOff,hMul,hAdd⟩ := hP
  obtain ⟨hs,_,off',_,hMul',hAdd'⟩ := hS
  have hoo := hT.mul.mul_unique hM.1 hMul hMul'
  subst off'
  exact natural_sum_strict_left_d hM hC hp hs hOff ((hT.add.add_iff_sum hM hp hOff).mp hAdd)
    ((hT.add.add_iff_sum hM hs hOff).mp hAdd') hLeft

theorem Parent.left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r c q : M.Domain} (h : Parent M C T D r c q) : M.mem q c := by
  rcases h.2.2 with ⟨_,hParent⟩ | ⟨hNew,s,_,b,_,hRaw,hCase⟩
  · exact (hParent.bounds hM.1 hD.mountain).2.2.2
  · have hAfter := ((omega_isOrdinal_d hM hC.omega).mem h.2.1).transitive D.coordinates.last hNew D.coordinates.root hD.coordinates.below
    have hSource := (CopyCoordinates.raw_decoded_active_iff hAfter).mp hRaw
    rcases hCase with ⟨_,off,_,_,u,_,_,p,_,hParent,hEncode⟩ | ⟨_,p,_,hParent,hCopy⟩
    · exact encode_strict_left_d hM hC hT (hParent.bounds hM.1 hD.mountain).2.2.2 hEncode hSource.2
    · exact CopyCoordinates.parent_copy_below_encode_d hM hC hT hD.coordinates hSource.1.1
        (hParent.bounds hM.1 hD.mountain).2.2.2 hCopy hSource.2

theorem Parent.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r c q q' : M.Domain} (h : Parent M C T D r c q) (h' : Parent M C T D r c q') : q=q' := by
  rcases h.2.2 with ⟨hOld,hP⟩ | ⟨hNew,s,_,b,hb,hRaw,hCase⟩ <;>
    rcases h'.2.2 with ⟨hOld',hP'⟩ | ⟨hNew',s',_,b',_,hRaw',hCase'⟩
  · exact hP.unique hD.mountain hP'
  · exact False.elim (old_new_disjoint_d hM hC h.2.1 hOld hNew')
  · exact False.elim (old_new_disjoint_d hM hC h.2.1 hOld' hNew)
  · obtain ⟨hss,hbb⟩ := CopyCoordinates.raw_decode_unique_d hM hC hT hD.coordinates hRaw hRaw'
    subst s'
    subst b'
    rcases hCase with ⟨hMoved,hP⟩ | ⟨hNot,p,_,hP,hCopy⟩ <;>
      rcases hCase' with ⟨hMoved',hP'⟩ | ⟨hNot',p',_,hP',hCopy'⟩
    · exact hP.unique_d hM.1 hT hD hP'
    · exact False.elim (hNot' hMoved)
    · exact False.elim (hNot hMoved')
    · have hpp := hP.unique hD.mountain hP'
      subst p'
      obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hD.coordinates hb
      exact hJ.graph.unique p q q' ((hRows p q).mpr hCopy) ((hRows p q').mpr hCopy')


private theorem below_last_of_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C) {p s : M.Domain}
    (hSource : CopyCoordinates.Source M D.coordinates s) (hps : M.mem p s) : M.mem p D.coordinates.last := by
  rcases hSource.2 with he | hlt
  · exact he ▸ hps
  · exact ((omega_isOrdinal_d hM hC.omega).mem hD.coordinates.last).transitive s hlt p hps

theorem moved_source_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r s b a h : M.Domain} (hr : M.mem r C.omega)
    (hSource : CopyCoordinates.Source M D.coordinates s) (hCone : InCone M C D s)
    (hBase : MemPair M D.mountain.heights s a) (hLift : Lifted M C T D a b h) :
    (∃ q,MovedParent M C T D r s b q) ↔ M.mem r h := by
  have hStrict := hCone.height_strict_d hM hC hD hSource.1 hBase
  obtain ⟨_,hb,off,hOff,hMul,hAdd⟩ := hLift
  constructor
  · rintro ⟨q,off',_,hMul',u,_,hShift,p,_,hParent,_⟩
    have hoo := hT.mul.mul_unique hM.1 hMul hMul'
    subst off'
    exact (hShift.lt_height_iff_d hM hC hT hStrict hAdd).mp ((hD.mountain.source u s a hBase).mp ⟨p,hParent⟩)
  · intro hR
    obtain ⟨u,hShift⟩ := shifted_row_exists_d hM hC hT (hD.floor_nat hM.1) hOff hr
    have hu := (hShift.lt_height_iff_d hM hC hT hStrict hAdd).mpr hR
    obtain ⟨p,hParent⟩ := (hD.mountain.source u s a hBase).mpr hu
    have hp := (omega_isOrdinal_d hM hC.omega).transitive D.mountain.width hD.mountain.width p (hParent.bounds hM.1 hD.mountain).2.2.1
    obtain ⟨q,_,hEncode⟩ := CopyCoordinates.encode_exists_d hM hC hT hD.coordinates hp hb
    exact ⟨q,off,hOff,hMul,u,hShift.2.1,hShift,p,hp,hParent,hEncode⟩

theorem MovedParent.endpoint_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r s b q h : M.Domain}
    (hSource : CopyCoordinates.Source M D.coordinates s) (hCone : InCone M C D s)
    (hParent : MovedParent M C T D r s b q) (hHeight : Height M C T D q h) : r=h ∨ M.mem r h := by
  obtain ⟨off,_,hMul,u,_,hShift,p,_,hParent,hEncode⟩ := hParent
  have hPCone := hCone.high_parent_d hM hC hD (hShift.floor_le_d hM hC hT) hParent
  have hpLast := below_last_of_source_d hM hC hD hSource (hParent.bounds hM.1 hD.mountain).2.2.2
  have hCopy : CopyCoordinates.ParentCopy M C T D.coordinates b p q :=
    ⟨hEncode.1,hEncode.2.1,Or.inr ⟨hPCone.not_good_d hM hC hD,hEncode⟩⟩
  obtain ⟨a,_,hA⟩ := hD.mountain.heights.total p (hParent.bounds hM.1 hD.mountain).2.2.1
  rcases (height_parent_copy_iff_d hM hC hT hD hpLast hCopy hA).mp hHeight with ⟨_,_,_,off',_,hMul',hAdd⟩ | ⟨hNot,_⟩
  · have hoo := hT.mul.mul_unique hM.1 hMul hMul'
    subst off'
    exact hShift.endpoint_le_d hM hC hT (hD.mountain.endpoint u s p a hParent hA) hAdd
  · exact False.elim (hNot hPCone)

theorem Height.new_column_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {c s b h : M.Domain}
    (hNew : M.mem D.coordinates.last c) (hRaw : CopyCoordinates.RawDecoded M C T D.coordinates c s b)
    (hHeight : Height M C T D c h) : ∃ a, M.mem a C.omega ∧ MemPair M D.mountain.heights s a ∧
      ((InCone M C D s ∧ Lifted M C T D a b h) ∨ (¬InCone M C D s ∧ h=a)) := by
  rcases hHeight.2 with ⟨hOld,_⟩ | ⟨_,s',_,b',_,hRaw',a,ha,hAt,hLift⟩
  · exact False.elim (old_new_disjoint_d hM hC hHeight.1 hOld hNew)
  · obtain ⟨hss,hbb⟩ := CopyCoordinates.raw_decode_unique_d hM hC hT hD.coordinates hRaw hRaw'
    subst s'
    subst b'
    refine ⟨a,ha,hAt,?_⟩
    rcases hLift with ⟨hCone,off,hOff,hMul,hAdd⟩ | hNot
    · exact Or.inl ⟨hCone,ha,hRaw.2.1,off,hOff,hMul,hAdd⟩
    · exact Or.inr hNot


private theorem unmoved_source_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r s b a h : M.Domain} (hr : M.mem r C.omega)
    (hSource : CopyCoordinates.Source M D.coordinates s) (hNot : ¬(InCone M C D s ∧ (D.floor=r ∨ M.mem D.floor r)))
    (hBase : MemPair M D.mountain.heights s a)
    (hColumn : (InCone M C D s ∧ Lifted M C T D a b h) ∨ (¬InCone M C D s ∧ h=a)) :
    (∃ p,ParentAt M D.mountain r s p) ↔ M.mem r h := by
  rcases hColumn with ⟨hCone,hLift⟩ | ⟨_,heq⟩
  · have hBelow : M.mem r D.floor := by
      rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare D.floor (hD.floor_nat hM.1) r hr with he | hlt | hgt
      · exact False.elim (hNot ⟨hCone,Or.inl (hM.1.eq_of_same_members _ _ he)⟩)
      · exact False.elim (hNot ⟨hCone,Or.inr hlt⟩)
      · exact hgt
    have hStrict := hCone.height_strict_d hM hC hD hSource.1 hBase
    have hRA := ((omega_isOrdinal_d hM hC.omega).mem (hD.mountain.heights.bounds hM.1 hBase).2).transitive D.floor hStrict r hBelow
    have hRH : M.mem r h := by
      rcases hLift.base_le_d hM hC hT with he | hAH
      · exact he ▸ hRA
      · have hh : M.mem h C.omega := by
          obtain ⟨_,_,_,_,_,hAdd⟩ := hLift
          exact (hAdd.bounds hM.1 hT.add).2.2
        exact ((omega_isOrdinal_d hM hC.omega).mem hh).transitive a hAH r hRA
    exact ⟨fun _ => hRH,fun _ => (hD.mountain.source r s a hBase).mpr hRA⟩
  · subst h
    exact hD.mountain.source r s a hBase

theorem source_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r c h : M.Domain} (hHeight : Height M C T D c h) :
    (∃ q,Parent M C T D r c q) ↔ M.mem r h := by
  constructor
  · rintro ⟨q,hr,_,hCase⟩
    rcases hCase with ⟨hOld,hParent⟩ | ⟨hNew,s,_,b,_,hRaw,hCase⟩
    · exact (hD.mountain.source r c h ((height_original_iff_d hM hC hD hOld).mp hHeight)).mp ⟨q,hParent⟩
    · obtain ⟨a,_,hBase,hColumn⟩ := hHeight.new_column_d hM hC hT hD hNew hRaw
      have hSource := CopyCoordinates.raw_decoded_source_bounds_d hM hC hD.coordinates hRaw
      rcases hCase with ⟨hMoved,hParent⟩ | ⟨hNot,p,_,hParent,_⟩
      · rcases hColumn with ⟨_,hLift⟩ | ⟨hNot,_⟩
        · exact (moved_source_iff_d hM hC hT hD hr hSource hMoved.1 hBase hLift).mp ⟨q,hParent⟩
        · exact False.elim (hNot hMoved.1)
      · exact (unmoved_source_iff_d hM hC hT hD hr hSource hNot hBase hColumn).mp ⟨p,hParent⟩
  · intro hRH
    have hr := (omega_isOrdinal_d hM hC.omega).transitive h (hHeight.natural hM.1 hT hD) r hRH
    have hc := hHeight.1
    rcases hHeight.2 with ⟨hOld,hBase⟩ | ⟨hNew,s,hs,b,hb,hRaw,a,ha,hBase,hLift⟩
    · obtain ⟨q,hParent⟩ := (hD.mountain.source r c h hBase).mpr hRH
      exact ⟨q,hr,hc,Or.inl ⟨hOld,hParent⟩⟩
    · have hSource := CopyCoordinates.raw_decoded_source_bounds_d hM hC hD.coordinates hRaw
      have hColumn : (InCone M C D s ∧ Lifted M C T D a b h) ∨ (¬InCone M C D s ∧ h=a) := by
        rcases hLift with ⟨hCone,off,hOff,hMul,hAdd⟩ | hNot
        · exact Or.inl ⟨hCone,ha,hb,off,hOff,hMul,hAdd⟩
        · exact Or.inr hNot
      classical
      by_cases hMoves : InCone M C D s ∧ (D.floor=r ∨ M.mem D.floor r)
      · rcases hColumn with ⟨_,hLift⟩ | ⟨hNot,_⟩
        · obtain ⟨q,hParent⟩ := (moved_source_iff_d hM hC hT hD hr hSource hMoves.1 hBase hLift).mpr hRH
          exact ⟨q,hr,hc,Or.inr ⟨hNew,s,hs,b,hb,hRaw,Or.inl ⟨hMoves,hParent⟩⟩⟩
        · exact False.elim (hNot hMoves.1)
      · obtain ⟨p,hParent⟩ := (unmoved_source_iff_d hM hC hT hD hr hSource hMoves hBase hColumn).mpr hRH
        have hp := (omega_isOrdinal_d hM hC.omega).transitive D.mountain.width hD.mountain.width p (hParent.bounds hM.1 hD.mountain).2.2.1
        obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hD.coordinates hb
        obtain ⟨q,_,hAt⟩ := hJ.graph.total p hp
        exact ⟨q,hr,hc,Or.inr ⟨hNew,s,hs,b,hb,hRaw,Or.inr ⟨hMoves,p,hp,hParent,(hRows p q).mp hAt⟩⟩⟩

theorem endpoint_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r c q h : M.Domain}
    (hParent : Parent M C T D r c q) (hHeight : Height M C T D q h) : r=h ∨ M.mem r h := by
  rcases hParent.2.2 with ⟨hOld,hParent⟩ | ⟨_,s,_,b,_,hRaw,hCase⟩
  · have hqc := (hParent.bounds hM.1 hD.mountain).2.2.2
    have hqOld : M.mem q D.coordinates.last := by
      rcases hOld with he | hlt
      · exact he ▸ hqc
      · exact ((omega_isOrdinal_d hM hC.omega).mem hD.coordinates.last).transitive c hlt q hqc
    exact hD.mountain.endpoint r c q h hParent ((height_original_iff_d hM hC hD (Or.inr hqOld)).mp hHeight)
  · have hSource := CopyCoordinates.raw_decoded_source_bounds_d hM hC hD.coordinates hRaw
    rcases hCase with ⟨hMove,hParent⟩ | ⟨_,p,_,hParent,hCopy⟩
    · exact hParent.endpoint_d hM hC hT hD hSource hMove.1 hHeight
    · have hpLast := below_last_of_source_d hM hC hD hSource (hParent.bounds hM.1 hD.mountain).2.2.2
      obtain ⟨a,_,hBase⟩ := hD.mountain.heights.total p (hParent.bounds hM.1 hD.mountain).2.2.1
      exact nat_le_trans_d hM hC (hHeight.natural hM.1 hT hD) (hD.mountain.endpoint r s p a hParent hBase)
        (hHeight.parent_copy_ge_d hM hC hT hD hpLast hCopy hBase)


private def parentSchema : Project.Delta0BinarySchema 22 where
  body := parentFormula ⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩ ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩
    ⟨⟨.bound 12,.bound 11,.bound 10,.bound 9⟩,⟨.bound 8,.bound 7,.bound 6,.bound 5⟩,.bound 4,.bound 3⟩ (.bound 2) (.bound 1) (.bound 0)
  freeClosed := parentFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    ⟨⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩ _ _ _ rfl rfl rfl
  delta0 := parentFormula_delta0 _ _ _ _ _ _

private theorem parentSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (D : Context M.Domain) (r c p : M.Domain) :
    Project.Formula.satisfies ((((copyEnv C T D).push r).push c).push p) parentSchema.body ↔ Parent M C T D r c p :=
  parentFormula_iff he _ _ _ _ _ _ _

structure Copies (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Context M.Domain) (n : M.Domain) (Y : Data M.Domain) : Prop where
  width : Y.width=n
  forests : ∀ F, M.mem F Y.forests ↔ Forest M C.omega n F
  heights : ∀ c h, MemPair M Y.heights c h ↔ M.mem c n ∧ Height M C T D c h
  parents : ∀ r c p, ParentAt M Y r c p ↔ M.mem c n ∧ Parent M C T D r c p

theorem copy_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {n : M.Domain} (hn : M.mem n C.omega) :
    ∃ Y, Y.Valid M C ∧ Copies M C T D n Y := by
  obtain ⟨Heights,hHeights,hHeightRows⟩ := height_graph_exists_d hM hC hT hD hn
  obtain ⟨Forests,Parents,hParents,hForests,hParentRows⟩ := forest_family_exists_d hM hC parentSchema (copyEnv C T D) hn
    (fun r _ c _ p _ hφ => ((parentSchema_iff hM.1 C T D r c p).mp hφ).left_d hM hC hT hD)
    (fun r _ c _ p _ q _ hφ hφ' => ((parentSchema_iff hM.1 C T D r c p).mp hφ).unique_d hM hC hT hD
      ((parentSchema_iff hM.1 C T D r c q).mp hφ'))
  let Y : Data M.Domain := ⟨n,Heights,Forests,Parents⟩
  have hForest (r F : M.Domain) (hRow : MemPair M Parents r F) : Forest M C.omega n F := ((hParentRows r F).mp hRow).2.1
  have hRows (r c p : M.Domain) : ParentAt M Y r c p ↔ M.mem c n ∧ Parent M C T D r c p := by
    constructor
    · rintro ⟨F,_,hF,hAt⟩
      obtain ⟨hc,hp⟩ := (hForest r F hF).bounds hM.1 hAt
      exact ⟨hc,(parentSchema_iff hM.1 C T D r c p).mp ((((hParentRows r F).mp hF).2.2 c hc p hp).mp hAt)⟩
    · rintro ⟨hc,hParent⟩
      have hp := ((omega_isOrdinal_d hM hC.omega).mem hn).transitive c hc p (hParent.left_d hM hC hT hD)
      obtain ⟨F,hF,hRow⟩ := hParents.total r hParent.1
      exact ⟨F,hF,hRow,(((hParentRows r F).mp hRow).2.2 c hc p hp).mpr ((parentSchema_iff hM.1 C T D r c p).mpr hParent)⟩
  refine ⟨Y,⟨hn,hHeights,hParents,hForest,?_,?_⟩,rfl,hForests,hHeightRows,hRows⟩
  · intro r c h hAt
    obtain ⟨hc,hHeight⟩ := (hHeightRows c h).mp hAt
    refine Iff.trans ?_ (source_iff_d hM hC hT hD hHeight)
    exact ⟨fun ⟨p,hp⟩ => ⟨p,((hRows r c p).mp hp).2⟩,fun ⟨p,hp⟩ => ⟨p,(hRows r c p).mpr ⟨hc,hp⟩⟩⟩
  · intro r c p h hParent hAt
    exact endpoint_d hM hC hT hD ((hRows r c p).mp hParent).2 ((hHeightRows p h).mp hAt).2

theorem Copies.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Context M.Domain} {n : M.Domain} {Y Z : Data M.Domain}
    (hY : Y.Valid M C) (hZ : Z.Valid M C) (h : Copies M C T D n Y) (h' : Copies M C T D n Z) : Y=Z :=
  Ordinary.data_ext he hY hZ (h.width.trans h'.width.symm)
    (he.eq_of_same_members _ _ (fun F => (h.forests F).trans (h'.forests F).symm))
    (fun c v => (h.heights c v).trans (h'.heights c v).symm)
    (fun r c p => (h.parents r c p).trans (h'.parents r c p).symm)

theorem Context.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D D' : Context M.Domain}
    (hD : D.Valid M C) (hD' : D'.Valid M C) (hCoords : D.coordinates=D'.coordinates) (hMountains : D.mountain=D'.mountain) : D=D' := by
  cases D with
  | mk A X floor rise =>
    cases D' with
    | mk A' X' floor' rise' =>
      dsimp only at hCoords hMountains
      subst A'
      subst X'
      have hFloor := hD.mountain.heights.unique A.root floor floor' hD.floor hD'.floor
      subst floor'
      obtain ⟨h,_,hAt,_,hDiff⟩ := hD.rise
      obtain ⟨h',_,hAt',_,hDiff'⟩ := hD'.rise
      have hHeight := hD.mountain.heights.unique A.last h h' hAt hAt'
      subst h'
      have hRise := truncated_difference_unique_d hM hC hDiff hDiff'
      change rise=rise' at hRise
      subst rise'
      rfl

theorem copy_from_bad_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K d k W Q : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K d A.last A.root) (hLayer : RowAt M L.states H k W Q) (hk : M.mem k K)
    {R : RowStateSpace M.Domain} {J : M.Domain} (hRows : RowRun M C m R W Q J)
    {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R W J X) {n : M.Domain} (hn : M.mem n C.omega) :
    ∃ D Y, D.coordinates=A ∧ D.mountain=X ∧ D.Valid M C ∧ Y.Valid M C ∧ Copies M C T D n Y := by
  obtain ⟨D,hDA,hDX,hD⟩ := context_from_bad_exists_d hM hC hLayers hA hBad hLayer hk hRows hX hFrom
  obtain ⟨Y,hY,hCopies⟩ := copy_exists_d hM hC hT hD hn
  exact ⟨D,Y,hDA,hDX,hD,hY,hCopies⟩

theorem parent_original_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {D : Context M.Domain} (hD : D.Valid M C)
    {r c p : M.Domain} (hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last) :
    Parent M C T D r c p ↔ ParentAt M D.mountain r c p := by
  constructor
  · intro hP
    rcases hP.2.2 with ⟨_,hParent⟩ | ⟨hNew,_⟩
    · exact hParent
    · exact False.elim (old_new_disjoint_d hM hC hP.2.1 hOld hNew)
  · intro hParent
    obtain ⟨hr,hc,_,_⟩ := hParent.bounds hM.1 hD.mountain
    have hcNat := (omega_isOrdinal_d hM hC.omega).transitive D.mountain.width hD.mountain.width c hc
    exact ⟨hr,hcNat,Or.inl ⟨hOld,hParent⟩⟩

theorem Copies.original_heights_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {D : Context M.Domain} (hD : D.Valid M C)
    {n c height : M.Domain} {Y : Data M.Domain} (h : Copies M C T D n Y)
    (hc : M.mem c n) (hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last) :
    MemPair M Y.heights c height ↔ MemPair M D.mountain.heights c height := by
  rw [h.heights c height,height_original_iff_d hM hC hD hOld]
  exact ⟨And.right,fun h => ⟨hc,h⟩⟩

theorem Copies.original_parents_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {D : Context M.Domain} (hD : D.Valid M C)
    {n r c p : M.Domain} {Y : Data M.Domain} (h : Copies M C T D n Y)
    (hc : M.mem c n) (hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last) :
    ParentAt M Y r c p ↔ ParentAt M D.mountain r c p := by
  rw [h.parents r c p,parent_original_iff_d hM hC hD hOld]
  exact ⟨And.right,fun h => ⟨hc,h⟩⟩

theorem Copies.parent_copy_heights_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {n p b c a height : M.Domain} {Y : Data M.Domain}
    (h : Copies M C T D n Y) (hp : M.mem p D.coordinates.last) (hc : M.mem c n)
    (hCopy : CopyCoordinates.ParentCopy M C T D.coordinates b p c) (hBase : MemPair M D.mountain.heights p a) :
    MemPair M Y.heights c height ↔ ((InCone M C D p ∧ Lifted M C T D a b height) ∨ (¬InCone M C D p ∧ height=a)) := by
  rw [h.heights c height,height_parent_copy_iff_d hM hC hT hD hp hCopy hBase]
  exact ⟨And.right,fun h => ⟨hc,h⟩⟩


/-- 对象公式只需读取原height与差值；真实坏根推导补齐整个Lower上下文。 -/
theorem context_valid_of_reads_from_bad_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K d k W Q : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K d A.last A.root) (hLayer : RowAt M L.states H k W Q) (hk : M.mem k K)
    {R : RowStateSpace M.Domain} {J : M.Domain} (hRows : RowRun M C m R W Q J)
    {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R W J X) {floor rise height : M.Domain}
    (hFloor : MemPair M X.heights A.root floor) (hHeight : MemPair M X.heights A.last height)
    (hDiff : TruncatedDifference M C.omega C.zero height floor rise) :
    (⟨A,X,floor,rise⟩ : Context M.Domain).Valid M C := by
  obtain ⟨D,hAeq,hXeq,hD⟩ := context_from_bad_exists_d hM hC hLayers hA hBad hLayer hk hRows hX hFrom
  cases D with
  | mk A' X' floor' rise' =>
    dsimp only at hAeq hXeq
    subst A'
    subst X'
    have hFloorEq := hX.heights.unique A.root floor' floor hD.floor hFloor
    subst floor'
    obtain ⟨oldHeight,_,hOld,_,hOldDiff⟩ := hD.rise
    have hHeightEq := hX.heights.unique A.last oldHeight height hOld hHeight
    subst oldHeight
    have hRiseEq := truncated_difference_unique_d hM hC hOldDiff hDiff
    change rise'=rise at hRiseEq
    subst rise'
    exact hD

end KP1Y.OneYFinite.CopiedMountain.Lower
