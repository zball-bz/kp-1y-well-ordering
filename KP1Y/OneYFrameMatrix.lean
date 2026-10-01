import KP1Y.OneYFrameTransport
import KP1Y.OneYForestSelection
import KP1Y.OneYLinearForest
import KP1Y.OneYNaturalDifferenceFacts
import KP1Y.OneYNaturalDifferenceOrder
import KP1Y.FunctionalImage

/-! 真实有限帧矩阵：收集唯一 cutoff 父图，再用其实际深度构造 (row,column) 值图。
不假设森林幂集存在，也不把 BM4 父图恢复当作矩阵的输入字段。
-/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def CutoffCertificate (M : SetTheory.Structure.{u}) (w m P k Q : M.Domain) : Prop :=
  Forest M w m Q ∧ CutoffForest M m P k Q

def cutoffCertificateFormula {d : Nat} (w m P k Q : Project.Term d) : Project.Formula 1 d :=
  .conj (forestFormula w m Q) (Project.Formula.forallMem m (Project.Formula.forallMem m.weaken
    (.iff (memPairFormula Q.weaken.weaken (.bound 1) (.bound 0))
      (.disj (.conj (.mem (.bound 1) k.weaken.weaken) (successorFormula (.bound 1) (.bound 0)))
        (.conj (.neg (.mem (.bound 1) k.weaken.weaken)) (memPairFormula P.weaken.weaken (.bound 1) (.bound 0)))))))

theorem cutoffCertificateFormula_delta0 {d : Nat} (w m P k Q : Project.Term d) :
    (cutoffCertificateFormula w m P k Q).IsDelta0 :=
  .conj (forestFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _)
    (.disj (.conj (.mem _ _) (successorFormula_delta0 _ _)) (.conj (.neg (.mem _ _)) (memPairFormula_delta0 _ _ _))))))

theorem cutoffCertificateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (w m P k Q : Project.Term d) :
    Project.Formula.satisfies env (cutoffCertificateFormula w m P k Q) ↔
      CutoffCertificate M (w.eval env) (m.eval env) (P.eval env) (k.eval env) (Q.eval env) := by
  simp only [cutoffCertificateFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,forestFormula_iff he,memPairFormula_iff he,successorFormula_iff he,Term.eval_weaken]
  constructor
  · rintro ⟨hQ,hRows⟩
    refine ⟨hQ,?_⟩
    intro c p
    constructor
    · intro hcp
      obtain ⟨hc,hp⟩ := hQ.bounds he hcp
      exact ⟨hc,hp,(hRows c hc p hp).mp hcp⟩
    · rintro ⟨hc,hp,hCase⟩
      exact (hRows c hc p hp).mpr hCase
  · rintro ⟨hQ,hRows⟩
    exact ⟨hQ,fun c hc p hp => (hRows c p).trans ⟨fun h => h.2.2,fun h => ⟨hc,hp,h⟩⟩⟩

theorem cutoff_certificate_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w m P k Q R : M.Domain} (hQ : CutoffCertificate M w m P k Q) (hR : CutoffCertificate M w m P k R) : Q=R :=
  hQ.1.ext he hR.1 (fun c p => (hQ.2 c p).trans (hR.2 c p).symm)

/-- row r 的 cutoff 是实际截断差 m−r，输入差表已经是实际全局函数图。 -/
def FrameRow (M : SetTheory.Structure.{u}) (w m P Pairs Diff r Q : M.Domain) : Prop :=
  ∃ k, M.mem k w ∧ ∃ key, M.mem key Pairs ∧ Codes M key m r ∧ MemPair M Diff key k ∧ CutoffCertificate M w m P k Q

private def frameRowSchema : Project.Delta0BinarySchema 5 where
  body := Project.Formula.existsMem (.bound 6) (Project.Formula.existsMem (.bound 4)
    (.conj (codeFormula (.bound 0) (.bound 7) (.bound 3))
      (.conj (memPairFormula (.bound 4) (.bound 0) (.bound 1))
        (cutoffCertificateFormula (.bound 8) (.bound 7) (.bound 6) (.bound 1) (.bound 2)))))
  freeClosed := by
    simp [cutoffCertificateFormula,forestFormula,successorFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (cutoffCertificateFormula_delta0 _ _ _ _ _))))

private def frameRowEnv {M : SetTheory.Structure.{u}} (w m P Pairs Diff : M.Domain) : Env M 5 :=
  ((((oneEnv w).push m).push P).push Pairs).push Diff

private theorem frameRowSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (w m P Pairs Diff r Q : M.Domain) :
    Project.Formula.satisfies (((frameRowEnv w m P Pairs Diff).push r).push Q) frameRowSchema.body ↔
      FrameRow M w m P Pairs Diff r Q := by
  simp only [frameRowSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,memPairFormula_iff he,cutoffCertificateFormula_iff he]
  rfl

theorem frame_row_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P Pairs Diff r : M.Domain}
    (hP : Forest M C.omega m P) (hDiff : DifferenceTable M C Pairs Diff) (hr : M.mem r C.omega) :
    ∃ Q, FrameRow M C.omega m P Pairs Diff r Q := by
  obtain ⟨key,hCode⟩ := codes_total hM m r
  have hk := (hDiff.pairs key).mpr ⟨m,hP.width,r,hr,hCode⟩
  obtain ⟨k,hkNat,hAt⟩ := hDiff.graph.total key hk
  obtain ⟨Q,hQ,hCut⟩ := cutoff_forest_exists_d hM hC hP k
  exact ⟨Q,k,hkNat,key,hk,hCode,hAt,hQ,hCut⟩

theorem frame_row_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {m P Pairs Diff r Q R : M.Domain}
    (hDiff : DifferenceTable M C Pairs Diff)
    (hQ : FrameRow M C.omega m P Pairs Diff r Q) (hR : FrameRow M C.omega m P Pairs Diff r R) : Q=R := by
  obtain ⟨k,_,key,_,hCode,hAt,hCut⟩ := hQ
  obtain ⟨k',_,key',_,hCode',hAt',hCut'⟩ := hR
  have hKeys := codes_unique hM.1 hCode hCode'
  subst key'
  have hkk' := hDiff.graph.unique key k k' hAt hAt'
  subst k'
  exact cutoff_certificate_unique hM.1 hCut hCut'

/-- Δ₀ 收集唯一行森林，再构造实际 row→forest 图；不使用有限幂集作为隐含输入。 -/
theorem frame_row_family_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m height P Pairs Diff : M.Domain}
    (hP : Forest M C.omega m P) (hHeight : M.mem height C.omega) (hDiff : DifferenceTable M C Pairs Diff) :
    ∃ Forests Rows, Graph M Rows height Forests ∧ ∀ r Q, MemPair M Rows r Q ↔
      M.mem r height ∧ FrameRow M C.omega m P Pairs Diff r Q := by
  let env := frameRowEnv C.omega m P Pairs Diff
  have hNat := (omega_isOrdinal_d hM hC.omega).transitive height hHeight
  obtain ⟨Forests,hForests⟩ := KP1Y.functional_image_d hM frameRowSchema env height
    (by
      intro r hr
      obtain ⟨Q,hQ⟩ := frame_row_exists_d hM hC hP hDiff (hNat r hr)
      exact ⟨Q,(frameRowSchema_iff hM.1 C.omega m P Pairs Diff r Q).mpr hQ⟩)
    (fun _ _ _ _ hQ hR => frame_row_unique_d hM hDiff
      ((frameRowSchema_iff hM.1 _ _ _ _ _ _ _).mp hQ) ((frameRowSchema_iff hM.1 _ _ _ _ _ _ _).mp hR))
  obtain ⟨Rows,hSupport,hRaw⟩ := relation_comprehension_d hM frameRowSchema env height Forests
  have hRows (r Q : M.Domain) : MemPair M Rows r Q ↔ M.mem r height ∧ FrameRow M C.omega m P Pairs Diff r Q := by
    rw [hRaw r Q,frameRowSchema_iff hM.1]
    refine ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,?_,h.2⟩⟩
    exact (hForests Q).mpr ⟨r,h.1,(frameRowSchema_iff hM.1 _ _ _ _ _ _ _).mpr h.2⟩
  refine ⟨Forests,Rows,⟨hSupport,?_,?_⟩,hRows⟩
  · intro r hr
    obtain ⟨Q,hQ⟩ := frame_row_exists_d hM hC hP hDiff (hNat r hr)
    exact ⟨Q,(hForests Q).mpr ⟨r,hr,(frameRowSchema_iff hM.1 _ _ _ _ _ _ _).mpr hQ⟩,(hRows r Q).mpr ⟨hr,hQ⟩⟩
  · intro r Q R hQ hR
    exact frame_row_unique_d hM hDiff ((hRows r Q).mp hQ).2 ((hRows r R).mp hR).2

private def matrixValueEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (height m Forests Rows : M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push height).push m).push Forests).push Rows

private def matrixValueSchema : Project.Delta0BinarySchema 9 where
  body := Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 5)
    (Project.Formula.existsMem (.bound 5) (.conj (codeFormula (.bound 4) (.bound 2) (.bound 1))
      (.conj (memPairFormula (.bound 5) (.bound 2) (.bound 0))
        (depthFormula ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 7) (.bound 0) (.bound 1) (.bound 3))))))
  freeClosed := by
    have hDepth := depthFormula_freeClosed
      (show (⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ : ExpressionData (Project.Term 14)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 7) (.bound 0) (.bound 1) (.bound 3) rfl rfl rfl rfl
    simp [codeFormula,pairFormula,memPairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hDepth]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (depthFormula_delta0 _ _ _ _ _)))))

private theorem matrixValueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (height m Forests Rows key d : M.Domain) :
    Project.Formula.satisfies (((matrixValueEnv C height m Forests Rows).push key).push d) matrixValueSchema.body ↔
      ∃ r, M.mem r height ∧ ∃ c, M.mem c m ∧ ∃ Q, M.mem Q Forests ∧
        Codes M key r c ∧ MemPair M Rows r Q ∧ Depth M C m Q c d := by
  simp only [matrixValueSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,memPairFormula_iff he,depthFormula_iff he]
  rfl

theorem depth_matrix_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {height m Forests Rows : M.Domain}
    (hRows : Graph M Rows height Forests) (hForest : ∀ r Q, MemPair M Rows r Q → Forest M C.omega m Q) :
    ∃ Cells Values, IsProduct M Cells height m ∧ Graph M Values Cells C.omega ∧
      ∀ r, M.mem r height → ∀ c, M.mem c m → ∀ Q, MemPair M Rows r Q → ∀ key, Codes M key r c →
        ∀ d, MemPair M Values key d ↔ Depth M C m Q c d := by
  obtain ⟨Cells,hCells⟩ := product_exists hM height m
  let env := matrixValueEnv C height m Forests Rows
  obtain ⟨Values,hSupport,hRaw⟩ := relation_comprehension_d hM matrixValueSchema env Cells C.omega
  have hValues (key d : M.Domain) : MemPair M Values key d ↔ M.mem key Cells ∧ M.mem d C.omega ∧
      ∃ r, M.mem r height ∧ ∃ c, M.mem c m ∧ ∃ Q, M.mem Q Forests ∧
        Codes M key r c ∧ MemPair M Rows r Q ∧ Depth M C m Q c d := by
    exact (hRaw key d).trans (and_congr Iff.rfl (and_congr Iff.rfl
      (matrixValueSchema_iff hM.1 C height m Forests Rows key d)))
  have hGraph : Graph M Values Cells C.omega := by
    refine ⟨hSupport,?_,?_⟩
    · intro key hk
      obtain ⟨r,hr,c,hc,hCode⟩ := (hCells key).mp hk
      obtain ⟨Q,hQ,hAt⟩ := hRows.total r hr
      obtain ⟨d,hD⟩ := depth_exists_d hM hC (hForest r Q hAt) hc
      exact ⟨d,hD.1,(hValues key d).mpr ⟨hk,hD.1,r,hr,c,hc,Q,hQ,hCode,hAt,hD⟩⟩
    · intro key d e hd he
      obtain ⟨_,_,r,_,c,_,Q,_,hCode,hAt,hD⟩ := (hValues key d).mp hd
      obtain ⟨_,_,r',_,c',_,Q',_,hCode',hAt',hE⟩ := (hValues key e).mp he
      obtain ⟨hr,hc⟩ := codes_injective hM.1 hCode hCode'
      subst r'
      subst c'
      have hQQ := hRows.unique r Q Q' hAt hAt'
      subst Q'
      exact depth_unique_d hM hC (hForest r Q hAt) hD hE
  refine ⟨Cells,Values,hCells,hGraph,?_⟩
  intro r hr c hc Q hAt key hCode d
  constructor
  · intro hValue
    obtain ⟨_,_,r',_,c',_,Q',_,hCode',hAt',hD⟩ := (hValues key d).mp hValue
    obtain ⟨hr',hc'⟩ := codes_injective hM.1 hCode hCode'
    subst r'
    subst c'
    have hQQ := hRows.unique r Q Q' hAt hAt'
    subst Q'
    exact hD
  · intro hD
    exact (hValues key d).mpr ⟨(hCells key).mpr ⟨r,hr,c,hc,hCode⟩,hD.1,r,hr,c,hc,Q,(hRows.bounds hM.1 hAt).2,hCode,hAt,hD⟩

structure ForestFrameMatrix (α : Type u) where
  height : α
  differencePairs : α
  difference : α
  forests : α
  rows : α
  cells : α
  values : α

structure ForestFrameMatrix.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (m P : M.Domain) (A : ForestFrameMatrix M.Domain) : Prop where
  height : M.SuccessorOf A.height m
  difference : DifferenceTable M C A.differencePairs A.difference
  rows : Graph M A.rows A.height A.forests
  row_meaning : ∀ r Q, MemPair M A.rows r Q ↔ M.mem r A.height ∧ FrameRow M C.omega m P A.differencePairs A.difference r Q
  cells : IsProduct M A.cells A.height m
  values : Graph M A.values A.cells C.omega
  entries : ∀ r, M.mem r A.height → ∀ c, M.mem c m → ∀ Q, MemPair M A.rows r Q →
    ∀ key, Codes M key r c → ∀ d, MemPair M A.values key d ↔ Depth M C m Q c d

/-- 对任意实际森林构造 width+1 行、width 列的有限深度帧矩阵，包括宽度0。 -/
theorem forest_frame_matrix_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain} (hP : Forest M C.omega m P) :
    ∃ A, ForestFrameMatrix.Valid M C m P A := by
  obtain ⟨height,hHeight,hHeightNat⟩ := hC.omega.1.2 m hP.width
  obtain ⟨Pairs,Diff,hDiff⟩ := difference_table_exists_d hM hC
  obtain ⟨Forests,Rows,hRows,hMeaning⟩ := frame_row_family_exists_d hM hC hP hHeightNat hDiff
  have hForest : ∀ r Q, MemPair M Rows r Q → Forest M C.omega m Q := by
    intro r Q hAt
    obtain ⟨_,_,_,_,_,_,_,hQ,_⟩ := (hMeaning r Q).mp hAt
    exact hQ
  obtain ⟨Cells,Values,hCells,hValues,hEntries⟩ := depth_matrix_exists_d hM hC hRows hForest
  exact ⟨⟨height,Pairs,Diff,Forests,Rows,Cells,Values⟩,hHeight,hDiff,hRows,hMeaning,hCells,hValues,hEntries⟩

/-- 以一个森林自身的计算深度作值，实际最右较小值搜索恰好恢复原直接父图。 -/
theorem depth_selects_self_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P V : M.Domain}
    (hP : Forest M C.omega m P) (hV : Graph M V m C.omega)
    (hDepth : ∀ c d, MemPair M V c d ↔ Depth M C m P c d) : Selects false M C m P V P := by
  have hDirect (c p : M.Domain) (hcp : MemPair M P c p) : RestrictedParent false M C m P V c p := by
    have hBounds := hP.bounds hM.1 hcp
    obtain ⟨d,hd,hcd⟩ := hV.total c hBounds.1
    obtain ⟨e,he,hpe⟩ := hV.total p hBounds.2
    have hSucc := depth_parent_successor_d hM hC hP hcp ((hDepth c d).mp hcd) ((hDepth p e).mp hpe)
    refine ⟨⟨ancestor_direct_d hM hC hP hcp,e,he,d,hd,hpe,hcd,hSucc.predecessor_mem,True.intro⟩,?_⟩
    intro q _ hCandidate
    obtain ⟨b,hcb,hRel⟩ := ancestor_parent_cases_d hM hC hP hCandidate.1
    have hbp := hP.unique c b p hcb hcp
    subst b
    exact hRel.imp id (fun hAnc => hAnc.1)
  refine ⟨hP,hV,hP,?_⟩
  intro c p
  constructor
  · exact hDirect c p
  · intro hRestricted
    obtain ⟨b,hcb,_⟩ := ancestor_parent_cases_d hM hC hP hRestricted.1.1
    have hpb := restricted_parent_unique_d hM false hC hP hRestricted (hDirect c b hcb)
    subst b
    exact hcb

theorem ForestFrameMatrix.Valid.row_forest {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} {m P : M.Domain} {A : ForestFrameMatrix M.Domain}
    (hA : A.Valid M C m P) {r Q : M.Domain} (hAt : MemPair M A.rows r Q) : Forest M C.omega m Q := by
  obtain ⟨_,_,_,_,_,_,_,hQ,_⟩ := (hA.row_meaning r Q).mp hAt
  exact hQ

/-- 每一行的数值图确为所造二维矩阵的该行，且具有逐点 Depth 语义。 -/
theorem ForestFrameMatrix.Valid.row_values_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain} {A : ForestFrameMatrix M.Domain}
    (hA : A.Valid M C m P) {r : M.Domain} (hr : M.mem r A.height) :
    ∃ Q V, MemPair M A.rows r Q ∧ Graph M V m C.omega ∧
      (∀ c d, MemPair M V c d ↔ Depth M C m Q c d) ∧
      ∀ c, M.mem c m → ∀ key, Codes M key r c → ∀ d, MemPair M A.values key d ↔ MemPair M V c d := by
  obtain ⟨Q,_,hAt⟩ := hA.rows.total r hr
  have hQ := hA.row_forest hAt
  obtain ⟨V,hV,hDepth⟩ := depth_graph_exists_d hM hC hQ
  have hNat : M.MemberSubset m C.omega := (omega_isOrdinal_d hM hC.omega).transitive m hQ.width
  exact ⟨Q,V,hAt,hV.mono_values hNat,hDepth,fun c hc key hCode d =>
    (hA.entries r hr c hc Q hAt key hCode d).trans (hDepth c d).symm⟩

theorem FrameRow.cutoff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P Pairs Diff r Q k : M.Domain}
    (hDiff : DifferenceTable M C Pairs Diff) (hRow : FrameRow M C.omega m P Pairs Diff r Q)
    (hCut : TruncatedDifference M C.omega C.zero m r k) : CutoffCertificate M C.omega m P k Q := by
  obtain ⟨k',_,key,_,hCode,hAt,hQ⟩ := hRow
  have hOld := (hDiff.rows m hCut.1 r hCut.2.1 key hCode k').mp hAt
  exact truncated_difference_unique_d hM hC hOld hCut ▸ hQ

theorem ForestFrameMatrix.Valid.initial_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain}
    (hP : Forest M C.omega m P) {A : ForestFrameMatrix M.Domain} (hA : A.Valid M C m P)
    {Q : M.Domain} (hAt : MemPair M A.rows C.zero Q) :
    ∀ c p, MemPair M Q c p ↔ M.mem c m ∧ M.mem p m ∧ M.SuccessorOf c p := by
  have hQ := FrameRow.cutoff_d hM hC hA.difference ((hA.row_meaning C.zero Q).mp hAt).2
    (truncated_difference_zero_d hM hC hP.width)
  intro c p
  constructor
  · intro hcp
    have hc := (hQ.1.bounds hM.1 hcp).1
    exact (cutoff_parent_before hQ.2 hc).mp hcp
  · rintro ⟨hc,hp,hs⟩
    exact (cutoff_parent_before hQ.2 hc).mpr ⟨hc,hp,hs⟩

theorem ForestFrameMatrix.Valid.terminal_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain}
    (hP : Forest M C.omega m P) {A : ForestFrameMatrix M.Domain} (hA : A.Valid M C m P)
    {Q : M.Domain} (hAt : MemPair M A.rows m Q) : Q=P := by
  obtain ⟨_,k,_,key,_,hCode,hDiff,hQ,hCut⟩ := (hA.row_meaning m Q).mp hAt
  have hDifference := (hA.difference.rows m hP.width m hP.width key hCode k).mp hDiff
  have hk := truncated_difference_diagonal_d hM hC hDifference
  subst k
  exact hQ.ext hM.1 hP (cutoff_terminal hM.1 hP hCut hC.zero_empty)

theorem ForestFrameMatrix.Valid.entry_le_column_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain}
    {A : ForestFrameMatrix M.Domain} (hA : A.Valid M C m P)
    {r c key d : M.Domain} (hr : M.mem r A.height) (hc : M.mem c m) (hCode : Codes M key r c)
    (hAt : MemPair M A.values key d) : d=c ∨ M.mem d c := by
  obtain ⟨Q,_,hQ⟩ := hA.rows.total r hr
  exact depth_le_column_d hM hC (hA.row_forest hQ) ((hA.entries r hr c hc Q hQ key hCode d).mp hAt)

theorem cutoff_linear_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P k Q : M.Domain}
    (hQ : CutoffCertificate M C.omega m P k Q) : LinearPrefix M m Q k := by
  intro c hc hck p
  apply (cutoff_parent_before hQ.2 hck).trans
  exact ⟨fun h => h.2.2,fun hs => ⟨hc,
    ((omega_isOrdinal_d hM hC.omega).mem hQ.1.width).transitive c hc p hs.predecessor_mem,hs⟩⟩

/-- 一个下降 cutoff 步的真实最右较小值搜索精确恢复新的父图，包括关键列 k。 -/
theorem cutoff_step_selects_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P k next Q R V : M.Domain}
    (hk : M.mem k C.omega) (hs : M.SuccessorOf next k)
    (hQ : CutoffCertificate M C.omega m P next Q) (hR : CutoffCertificate M C.omega m P k R)
    (hV : Graph M V m C.omega) (hDepth : ∀ c d, MemPair M V c d ↔ Depth M C m R c d) :
    Selects false M C m Q V R := by
  classical
  obtain ⟨next',hNext',hNextNat⟩ := hC.omega.1.2 k hk
  have hNextEq := Structure.SuccessorOf.eq hM.1 hNext' hs
  subst next'
  have hLinearQ := cutoff_linear_prefix_d hM hC hQ
  have hLinearR := cutoff_linear_prefix_d hM hC hR
  have hParent (c p : M.Domain) (hcp : MemPair M R c p) : RestrictedParent false M C m Q V c p := by
    have hBounds := hR.1.bounds hM.1 hcp
    obtain ⟨d,hd,hcd⟩ := hV.total c hBounds.1
    obtain ⟨e,he,hpe⟩ := hV.total p hBounds.2
    have hSucc := depth_parent_successor_d hM hC hR.1 hcp ((hDepth c d).mp hcd) ((hDepth p e).mp hpe)
    by_cases hCritical : c=k
    · subst c
      have hpk := hR.1.left k p hcp
      have hep := linear_prefix_depth_d hM hC hR.1 hk hLinearR hpk ((hDepth p e).mp hpe)
      subst e
      have hAnc := linear_prefix_ancestor_d hM hC hQ.1 hNextNat hLinearQ hBounds.1 hs.predecessor_mem hpk
      refine ⟨⟨hAnc,p,he,d,hd,hpe,hcd,hSucc.predecessor_mem,True.intro⟩,?_⟩
      intro q _ hCandidate
      obtain ⟨u,_,v,_,hqu,hkv,huv,_⟩ := hCandidate.2
      have huq := linear_prefix_depth_d hM hC hR.1 hk hLinearR hCandidate.1.1 ((hDepth q u).mp hqu)
      subst u
      have hvd := hV.unique k v d hkv hcd
      subst v
      rcases (hSucc q).mp huv with hqp | heq
      · exact Or.inr hqp
      · exact Or.inl (hM.1.eq_of_same_members q p heq)
    · have hOld := (cutoff_step_other hM.1 hs hR.2 hQ.2 hCritical p).mp hcp
      refine ⟨⟨ancestor_direct_d hM hC hQ.1 hOld,e,he,d,hd,hpe,hcd,hSucc.predecessor_mem,True.intro⟩,?_⟩
      intro q _ hCandidate
      exact ancestor_le_parent_d hM hC hQ.1 hOld hCandidate.1
  refine ⟨hQ.1,hV,hR.1,?_⟩
  intro c p
  constructor
  · exact hParent c p
  · intro hRestricted
    by_cases hNo : NoParent M m R c
    · obtain ⟨e,_,d,_,_,hcd,hed,_⟩ := hRestricted.1.2
      have hd := depth_of_no_parent_d hM hC hR.1 hNo ((hDepth c d).mp hcd)
      exact False.elim (hC.zero_empty e (hd ▸ hed))
    · have hSome : ∃ q, M.mem q m ∧ MemPair M R c q := by
        apply Classical.byContradiction
        intro hNone
        exact hNo (fun q hq hcp => hNone ⟨q,hq,hcp⟩)
      obtain ⟨q,_,hcq⟩ := hSome
      have hpq := restricted_parent_unique_d hM false hC hQ.1 hRestricted (hParent c q hcq)
      subst q
      exact hcq

/-- 相邻实际矩阵行的父图确为 BM4 的继承候选最右选择结果。 -/
theorem ForestFrameMatrix.Valid.successive_selection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain} (hP : Forest M C.omega m P)
    {A : ForestFrameMatrix M.Domain} (hA : A.Valid M C m P) {r s Q R V : M.Domain}
    (hs : M.SuccessorOf s r) (hQr : MemPair M A.rows r Q) (hRs : MemPair M A.rows s R)
    (hV : Graph M V m C.omega) (hDepth : ∀ c d, MemPair M V c d ↔ Depth M C m R c d) : Selects false M C m Q V R := by
  have hr := (hA.rows.bounds hM.1 hQr).1
  have hsH := (hA.rows.bounds hM.1 hRs).1
  have hrm : M.mem r m := by
    rcases (hA.height r).mp hr with hrm | hEq
    · exact hrm
    · have hrEq := hM.1.eq_of_same_members r m hEq
      subst r
      have hsEq := Structure.SuccessorOf.eq hM.1 hs hA.height
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.height (hsEq ▸ hsH))
  have hHeightNat := natural_successor_mem_d hM hC hP.width hA.height
  have hNat := (omega_isOrdinal_d hM hC.omega).transitive A.height hHeightNat
  obtain ⟨_,k,hk,key,_,hCode,hDiff,hQ⟩ := (hA.row_meaning r Q).mp hQr
  obtain ⟨_,l,hl,key',_,hCode',hDiff',hR⟩ := (hA.row_meaning s R).mp hRs
  have hD := (hA.difference.rows m hP.width r (hNat r hr) key hCode k).mp hDiff
  have hD' := (hA.difference.rows m hP.width s (hNat s hsH) key' hCode' l).mp hDiff'
  exact cutoff_step_selects_d hM hC hl (truncated_difference_successor_of_lt_d hM hC hs hrm hD hD') hQ hR hV hDepth

structure MatrixRowValues (M : SetTheory.Structure.{u}) (w m Cells Values r V : M.Domain) : Prop where
  graph : Graph M V m w
  entries : ∀ c, M.mem c m → ∀ key, M.mem key Cells → Codes M key r c →
    ∀ d, M.mem d w → (MemPair M Values key d ↔ MemPair M V c d)

theorem ForestFrameMatrix.Valid.row_values_exist_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain} {A : ForestFrameMatrix M.Domain}
    (hA : A.Valid M C m P) {r : M.Domain} (hr : M.mem r A.height) :
    ∃ V, MatrixRowValues M C.omega m A.cells A.values r V := by
  obtain ⟨_,V,_,hV,_,hEntries⟩ := hA.row_values_d hM hC hr
  exact ⟨V,hV,fun c hc key _ hCode d _ => hEntries c hc key hCode d⟩

theorem ForestFrameMatrix.Valid.row_depth_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {m P : M.Domain} {A : ForestFrameMatrix M.Domain}
    (hA : A.Valid M C m P) {r Q V : M.Domain} (hAt : MemPair M A.rows r Q)
    (hV : MatrixRowValues M C.omega m A.cells A.values r V) :
    ∀ c d, MemPair M V c d ↔ Depth M C m Q c d := by
  classical
  intro c d
  by_cases hc : M.mem c m
  · obtain ⟨key,hCode⟩ := codes_total hM r c
    have hr := (hA.rows.bounds hM.1 hAt).1
    have hk := (hA.cells key).mpr ⟨r,hr,c,hc,hCode⟩
    by_cases hd : M.mem d C.omega
    · exact (hV.entries c hc key hk hCode d hd).symm.trans (hA.entries r hr c hc Q hAt key hCode d)
    · exact iff_of_false (fun h => hd (hV.graph.bounds hM.1 h).2) (fun h => hd h.1)
  · exact iff_of_false (fun h => hc (hV.graph.bounds hM.1 h).1) (fun h => hc (h.column_bound hM.1))

theorem ForestFrameMatrix.Valid.initial_selection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P L : M.Domain}
    (hP : Forest M C.omega m P) (hL : LinearForest M C.omega m L)
    {A : ForestFrameMatrix M.Domain} (hA : A.Valid M C m P) {Q V : M.Domain}
    (hAt : MemPair M A.rows C.zero Q) (hV : MatrixRowValues M C.omega m A.cells A.values C.zero V) :
    Selects false M C m L V Q := by
  have hQ := hA.row_forest hAt
  have hQL : Q=L := by
    apply hQ.ext hM.1 hL.1
    intro c p
    rw [hA.initial_parent_d hM hC hP hAt c p,hL.2 c p]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,
      ((omega_isOrdinal_d hM hC.omega).mem hP.width).transitive c h.1 p h.2.predecessor_mem,h.2⟩⟩
  subst L
  exact depth_selects_self_d hM hC hQ hV.graph (hA.row_depth_iff_d hM hAt hV)

/-- 独立于 cutoff 的实际有限 BM4 父图算法证书：从线性森林起，逐行在前一父链中选最右较小值。 -/
structure MatrixParentRun (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (m height Cells Values Forests Rows L : M.Domain) : Prop where
  height_nat : M.mem height C.omega
  linear : LinearForest M C.omega m L
  graph : Graph M Rows height Forests
  forests : ∀ r Q, MemPair M Rows r Q → Forest M C.omega m Q
  values_exist : ∀ r, M.mem r height → ∃ V, MatrixRowValues M C.omega m Cells Values r V
  initial : ∀ Q V, MemPair M Rows C.zero Q → MatrixRowValues M C.omega m Cells Values C.zero V → Selects false M C m L V Q
  step : ∀ r s Q R V, M.SuccessorOf s r → MemPair M Rows r Q → MemPair M Rows s R →
    MatrixRowValues M C.omega m Cells Values s V → Selects false M C m Q V R

theorem ForestFrameMatrix.Valid.parent_run_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain} (hP : Forest M C.omega m P)
    {A : ForestFrameMatrix M.Domain} (hA : A.Valid M C m P) :
    ∃ L, MatrixParentRun M C m A.height A.cells A.values A.forests A.rows L := by
  obtain ⟨L,hL⟩ := linear_forest_exists_d hM hC.omega hP.width
  exact ⟨L,natural_successor_mem_d hM hC hP.width hA.height,hL,hA.rows,
    fun _ _ hAt => hA.row_forest hAt,fun _ hr => hA.row_values_exist_d hM hC hr,
    fun _ _ hAt hV => hA.initial_selection_d hM hC hP hL hAt hV,
    fun _ _ _ _ _ hs hQ hR hV => hA.successive_selection_d hM hC hP hs hQ hR hV.graph (hA.row_depth_iff_d hM hR hV)⟩

private def parentRunAgreementSchema : Project.UnarySchema 2 where
  body := .forallE (.forallE (.imp
    (.conj (memPairFormula (.bound 4) (.bound 2) (.bound 1)) (memPairFormula (.bound 3) (.bound 2) (.bound 0)))
    (Project.Formula.extensionalEq (.bound 1) (.bound 0))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem parentRunAgreementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (Rows Other r : M.Domain) :
    Project.Formula.satisfies (((oneEnv Rows).push Other).push r) parentRunAgreementSchema.body ↔
      ∀ Q R, MemPair M Rows r Q → MemPair M Other r R → Q=R := by
  simp only [parentRunAgreementSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,memPairFormula_iff he]
  exact ⟨fun h Q R hQ hR => h Q R ⟨hQ,hR⟩,fun h Q R hs => h Q R hs.1 hs.2⟩

/-- 任意两张满足该实际逐行算法的父图历史相同；归纳只施于字面集合图相等公式。 -/
theorem MatrixParentRun.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m height Cells Values Forests Rows L OtherForests Other OtherL : M.Domain}
    (h : MatrixParentRun M C m height Cells Values Forests Rows L)
    (h' : MatrixParentRun M C m height Cells Values OtherForests Other OtherL) : Rows=Other := by
  have hLinear := linear_forest_unique hM.1 h.linear h'.linear
  subst OtherL
  have hAll := natural_induction_d hM parentRunAgreementSchema ((oneEnv Rows).push Other) hC.omega
    (fun zero hEmpty => (parentRunAgreementSchema_iff hM.1 Rows Other zero).mpr (by
      have hz := hM.1.eq_of_same_members zero C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))
      subst zero
      intro Q R hQ hR
      obtain ⟨V,hV⟩ := h.values_exist C.zero (h.graph.bounds hM.1 hQ).1
      exact (h.initial Q V hQ hV).unique hM.1 (h'.initial R V hR hV)))
    (fun r _ ih s hs => (parentRunAgreementSchema_iff hM.1 Rows Other s).mpr (by
      intro Q R hQ hR
      have hsH := (h.graph.bounds hM.1 hQ).1
      have hrH := ((omega_isOrdinal_d hM hC.omega).mem h.height_nat).transitive s hsH r hs.predecessor_mem
      obtain ⟨Q0,_,hQ0⟩ := h.graph.total r hrH
      obtain ⟨R0,_,hR0⟩ := h'.graph.total r hrH
      have hPrev := (parentRunAgreementSchema_iff hM.1 Rows Other r).mp ih Q0 R0 hQ0 hR0
      subst R0
      obtain ⟨V,hV⟩ := h.values_exist s hsH
      exact (h.step r s Q0 Q V hs hQ0 hQ hV).unique hM.1 (h'.step r s Q0 R V hs hR0 hR hV)))
  apply h.graph.ext hM.1 h'.graph
  intro r hr Q
  obtain ⟨R,_,hR⟩ := h'.graph.total r hr
  have hSame := (parentRunAgreementSchema_iff hM.1 Rows Other r).mp
    (hAll r ((omega_isOrdinal_d hM hC.omega).transitive height h.height_nat r hr))
  constructor
  · intro hQ
    exact (hSame Q R hQ hR).symm ▸ hR
  · intro hQ
    obtain ⟨P,_,hP⟩ := h.graph.total r hr
    exact hSame P Q hP hQ ▸ hP

/-- 对此帧矩阵运行真实有限父选择算法，其终端行恢复原森林 P。 -/
theorem ForestFrameMatrix.Valid.terminal_parent_of_run_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain} (hP : Forest M C.omega m P)
    {A : ForestFrameMatrix M.Domain} (hA : A.Valid M C m P) {Forests Rows L Q : M.Domain}
    (hRun : MatrixParentRun M C m A.height A.cells A.values Forests Rows L) (hAt : MemPair M Rows m Q) : Q=P := by
  obtain ⟨L',hOwn⟩ := hA.parent_run_d hM hC hP
  have hRows := hRun.unique_d hM hC hOwn
  subst Rows
  exact hA.terminal_parent_d hM hC hP hAt

end KP1Y.OneYFinite
