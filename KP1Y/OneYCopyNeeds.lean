import KP1Y.OneYCopyTower
import KP1Y.OneYCopyIterationFacts
import KP1Y.OneYCopiedMountainSyntax
import KP1Y.ReflectionAdmission

/-! 虚拟边界列的精确需要模板：低层全高度、活动层min(level,height)、高层零。 -/
namespace KP1Y.OneYFinite.CopyNeeds
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u v

structure Data (α : Type u) where
  horizon : α
  width : α
  forests : α
  codes : α
  tower : α
  boundary : α
  active : α
  level : α

def Data.map {α : Type u} {β : Type v} (D : Data α) (f : α → β) : Data β :=
  ⟨f D.horizon,f D.width,f D.forests,f D.codes,f D.tower,f D.boundary,f D.active,f D.level⟩
def Data.eval {M : SetTheory.Structure.{u}} {n : Nat} (D : Data (Project.Term n)) (e : Env M n) : Data M.Domain := D.map (fun t => t.eval e)
def Data.weaken {n : Nat} (D : Data (Project.Term n)) : Data (Project.Term (n+1)) := D.map (fun t => t.weaken)

theorem Data.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat} (D : Data (Project.Term n)) (e : Env M n) (x : M.Domain) :
    D.weaken.eval (e.push x)=D.eval e := by
  cases D
  simp [Data.eval,Data.weaken,Data.map,Term.eval_weaken]

structure Data.Closed {n : Nat} (D : Data (Project.Term n)) : Prop where
  horizon : D.horizon.freeSupport=[]
  width : D.width.freeSupport=[]
  forests : D.forests.freeSupport=[]
  codes : D.codes.freeSupport=[]
  tower : D.tower.freeSupport=[]
  boundary : D.boundary.freeSupport=[]
  active : D.active.freeSupport=[]
  level : D.level.freeSupport=[]

theorem Data.Closed.weaken {n : Nat} {D : Data (Project.Term n)} (h : D.Closed) : D.weaken.Closed := by
  constructor <;> simp [Data.weaken,Data.map,h.horizon,h.width,h.forests,h.codes,h.tower,h.boundary,h.active,h.level]

structure Data.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (D : Data M.Domain) : Prop where
  horizon : M.mem D.horizon C.omega
  width : M.mem D.width C.omega
  boundary : M.mem D.boundary D.width
  active : M.mem D.active C.omega
  level : M.mem D.level C.omega
  graph : Graph M D.tower D.horizon D.codes
  values : ∀ k code, MemPair M D.tower k code → CodeValid M C D.width D.forests code

/-- 父行范围，尚未投影掉row。高于active的层严格没有需要项。 -/
def NeedRow (M : SetTheory.Structure.{u}) (K level k row height : M.Domain) : Prop :=
  M.mem row height ∧ (M.mem k K ∨ (k=K ∧ M.mem row level))

def needRowFormula {n : Nat} (K level k row height : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem row height) (.disj (.mem k K) (.conj (Project.Formula.extensionalEq k K) (.mem row level)))

theorem needRowFormula_delta0 {n : Nat} (K level k row height : Project.Term n) : (needRowFormula K level k row height).IsDelta0 :=
  .conj (.mem _ _) (.disj (.mem _ _) (.conj (.atom _ _ _) (.mem _ _)))

theorem needRowFormula_freeClosed {n : Nat} (K level k row height : Project.Term n)
    (hK : K.freeSupport=[]) (hLevel : level.freeSupport=[]) (hk : k.freeSupport=[])
    (hRow : row.freeSupport=[]) (hHeight : height.freeSupport=[]) : (needRowFormula K level k row height).FreeClosed := by
  simp [needRowFormula,Definitional.Formula.FreeClosed,hK,hLevel,hk,hRow,hHeight]

theorem needRowFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (K level k row height : Project.Term n) : Project.Formula.satisfies e (needRowFormula K level k row height) ↔
      NeedRow M (K.eval e) (level.eval e) (k.eval e) (row.eval e) (height.eval e) := by
  simp only [needRowFormula,NeedRow,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq he]

/-- needHeight由其全部内部自然数成员唯一给定。此定义等价于原三分支min算法。 -/
def NeedHeight (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (K level k height need : M.Domain) : Prop :=
  M.mem need C.omega ∧ ∀ row, M.mem row C.omega → (M.mem row need ↔ NeedRow M K level k row height)

def needHeightFormula {n : Nat} (w K level k height need : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem need w) (Project.Formula.forallMem w (.iff (.mem (.bound 0) need.weaken)
    (needRowFormula K.weaken level.weaken k.weaken (.bound 0) height.weaken)))

theorem needHeightFormula_delta0 {n : Nat} (w K level k height need : Project.Term n) : (needHeightFormula w K level k height need).IsDelta0 :=
  .conj (.mem _ _) (.forallMem _ (.iff (.mem _ _) (needRowFormula_delta0 _ _ _ _ _)))

theorem needHeightFormula_freeClosed {n : Nat} (w K level k height need : Project.Term n)
    (hw : w.freeSupport=[]) (hK : K.freeSupport=[]) (hLevel : level.freeSupport=[])
    (hk : k.freeSupport=[]) (hHeight : height.freeSupport=[]) (hNeed : need.freeSupport=[]) :
    (needHeightFormula w K level k height need).FreeClosed := by
  simp [needHeightFormula,needRowFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hw,hK,hLevel,hk,hHeight,hNeed]

theorem needHeightFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (K level k height need : Project.Term n) :
    Project.Formula.satisfies e (needHeightFormula C.omega K level k height need) ↔
      NeedHeight M (C.eval e) (K.eval e) (level.eval e) (k.eval e) (height.eval e) (need.eval e) := by
  simp only [needHeightFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,needRowFormula_iff he,Term.eval_weaken]
  rfl

theorem need_height_low_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {K level k height : M.Domain} (hHeight : M.mem height C.omega) (hk : M.mem k K) : NeedHeight M C K level k height height :=
  ⟨hHeight,fun _ _ => ⟨fun h => ⟨h,Or.inl hk⟩,And.left⟩⟩

theorem need_height_active_small_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {K level height : M.Domain}
    (hHeight : M.mem height C.omega) (hLevel : M.mem level C.omega) (hLe : height=level ∨ M.mem height level) :
    NeedHeight M C K level K height height := by
  refine ⟨hHeight,fun row _ => ⟨?_,And.left⟩⟩
  intro hr
  have hrl : M.mem row level := by
    rcases hLe with he | hlt
    · exact he ▸ hr
    · exact ((omega_isOrdinal_d hM hC.omega).mem hLevel).transitive height hlt row hr
  exact ⟨hr,Or.inr ⟨rfl,hrl⟩⟩

theorem need_height_active_large_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {K level height : M.Domain}
    (hHeight : M.mem height C.omega) (hLevel : M.mem level C.omega) (hLe : level=height ∨ M.mem level height) :
    NeedHeight M C K level K height level := by
  refine ⟨hLevel,fun row _ => ⟨?_,?_⟩⟩
  · intro hr
    have hrh : M.mem row height := by
      rcases hLe with he | hlt
      · exact he ▸ hr
      · exact ((omega_isOrdinal_d hM hC.omega).mem hHeight).transitive level hlt row hr
    exact ⟨hrh,Or.inr ⟨rfl,hr⟩⟩
  · rintro ⟨_,hCase⟩
    rcases hCase with hSelf | ⟨_,hr⟩
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K hSelf)
    · exact hr

theorem need_height_high_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {K level k height : M.Domain}
    (hK : M.mem K C.omega) (hHigh : M.mem K k) : NeedHeight M C K level k height C.zero := by
  refine ⟨hC.zero_nat,fun row _ => ⟨fun h => False.elim (hC.zero_empty row h),?_⟩⟩
  rintro ⟨_,hCase⟩
  rcases hCase with hLow | ⟨he,_⟩
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K
      (((omega_isOrdinal_d hM hC.omega).mem hK).transitive k hLow K hHigh))
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K (he ▸ hHigh))

theorem need_height_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {K level k height : M.Domain}
    (hK : M.mem K C.omega) (hLevel : M.mem level C.omega) (hk : M.mem k C.omega) (hHeight : M.mem height C.omega) :
    ∃ need, NeedHeight M C K level k height need := by
  have hw := omega_isOrdinal_d hM hC.omega
  rcases hw.wellOrder.linear.compare k hk K hK with he | hLow | hHigh
  · have hkK := hM.1.eq_of_same_members k K he
    subst k
    rcases hw.wellOrder.linear.compare height hHeight level hLevel with he | hSmall | hLarge
    · exact ⟨height,need_height_active_small_d hM hC hHeight hLevel (Or.inl (hM.1.eq_of_same_members height level he))⟩
    · exact ⟨height,need_height_active_small_d hM hC hHeight hLevel (Or.inr hSmall)⟩
    · exact ⟨level,need_height_active_large_d hM hC hHeight hLevel (Or.inr hLarge)⟩
  · exact ⟨height,need_height_low_d hHeight hLow⟩
  · exact ⟨C.zero,need_height_high_d hM hC hK hHigh⟩

theorem NeedHeight.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {K level k height a b : M.Domain}
    (hA : NeedHeight M C K level k height a) (hB : NeedHeight M C K level k height b) : a=b := by
  apply hM.1.eq_of_same_members
  intro r
  constructor
  · intro hra
    have hr := (omega_isOrdinal_d hM hC.omega).transitive a hA.1 r hra
    exact (hB.2 r hr).mpr ((hA.2 r hr).mp hra)
  · intro hrb
    have hr := (omega_isOrdinal_d hM hC.omega).transitive b hB.1 r hrb
    exact (hA.2 r hr).mpr ((hB.2 r hr).mp hrb)

theorem NeedHeight.le_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {K level k height need : M.Domain}
    (hHeight : M.mem height C.omega) (h : NeedHeight M C K level k height need) : need=height ∨ M.mem need height := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem h.1) (hw.mem hHeight)
  intro r hr
  exact ((h.2 r (hw.transitive need h.1 r hr)).mp hr).1


def BoundaryHeight (M : SetTheory.Structure.{u}) (D : Data M.Domain) (k h : M.Domain) : Prop :=
  ∃ code, M.mem code D.codes ∧ MemPair M D.tower k code ∧ ∃ heights parents,
    Codes M code heights parents ∧ MemPair M heights D.boundary h

def boundaryHeightFormula {n : Nat} (D : Data (Project.Term n)) (k h : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem D.codes (.conj (memPairFormula D.tower.weaken k.weaken (.bound 0))
    (withCodeFormula (.bound 0) (memPairFormula (.bound 1) D.boundary.weaken.weaken.weaken.weaken h.weaken.weaken.weaken.weaken)))

theorem boundaryHeightFormula_delta0 {n : Nat} (D : Data (Project.Term n)) (k h : Project.Term n) : (boundaryHeightFormula D k h).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (withCodeFormula_delta0 _ (memPairFormula_delta0 _ _ _)))

theorem boundaryHeightFormula_freeClosed {n : Nat} {D : Data (Project.Term n)} (hD : D.Closed)
    (k h : Project.Term n) (hk : k.freeSupport=[]) (hh : h.freeSupport=[]) : (boundaryHeightFormula D k h).FreeClosed := by
  have hBody : (memPairFormula (Project.Term.bound (depth := n+4) 1) D.boundary.weaken.weaken.weaken.weaken h.weaken.weaken.weaken.weaken).FreeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hD.boundary,hh]
  have hWith := withCodeFormula_freeClosed (Project.Term.bound (depth := n+1) 0) rfl hBody
  have hAt : (memPairFormula D.tower.weaken k.weaken (Project.Term.bound (depth := n+1) 0)).FreeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hD.tower,hk]
  simp [boundaryHeightFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hD.codes,hAt,hWith]

theorem boundaryHeightFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (D : Data (Project.Term n)) (k h : Project.Term n) : Project.Formula.satisfies e (boundaryHeightFormula D k h) ↔
      BoundaryHeight M (D.eval e) (k.eval e) (h.eval e) := by
  have hCode (code : M.Domain) : Project.Formula.satisfies (e.push code)
      (withCodeFormula (.bound 0) (memPairFormula (.bound 1) D.boundary.weaken.weaken.weaken.weaken h.weaken.weaken.weaken.weaken)) ↔
      ∃ heights parents, Codes M code heights parents ∧ MemPair M heights (D.boundary.eval e) (h.eval e) := by
    apply withCodeFormula_iff_exists he (e.push code) (.bound 0) _ (fun heights _ => MemPair M heights (D.boundary.eval e) (h.eval e))
    intro b heights parents
    simp only [memPairFormula_iff he,Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push]
  simp only [boundaryHeightFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,Term.eval_weaken,hCode]
  rfl

theorem BoundaryHeight.natural {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {D : Data M.Domain} (hD : D.Valid M C) {k h : M.Domain} (hValueAt : BoundaryHeight M D k h) : M.mem h C.omega := by
  obtain ⟨code,_,hAt,heights,parents,hCode,hValue⟩ := hValueAt
  have hY := (hD.values k code hAt).read he hCode
  exact (hY.heights.bounds he hValue).2

theorem BoundaryHeight.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {D : Data M.Domain} (hD : D.Valid M C) {k a b : M.Domain} (hA : BoundaryHeight M D k a) (hB : BoundaryHeight M D k b) : a=b := by
  obtain ⟨code,_,hAt,heights,parents,hCode,hValue⟩ := hA
  obtain ⟨code',_,hAt',heights',parents',hCode',hValue'⟩ := hB
  have hCodes := hD.graph.unique k code code' hAt hAt'
  subst code'
  obtain ⟨hHs,hPs⟩ := codes_injective he hCode hCode'
  subst heights'
  exact ((hD.values k code hAt).read he hCode).heights.unique D.boundary a b hValue hValue'

theorem boundary_height_exists_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {D : Data M.Domain} (hD : D.Valid M C) {k : M.Domain} (hk : M.mem k D.horizon) : ∃ h, M.mem h C.omega ∧ BoundaryHeight M D k h := by
  obtain ⟨code,hCodeMem,hAt⟩ := hD.graph.total k hk
  obtain ⟨heights,parents,hCode,hY⟩ := hD.values k code hAt
  obtain ⟨h,hh,hValue⟩ := hY.heights.total D.boundary hD.boundary
  exact ⟨h,hh,code,hCodeMem,hAt,heights,parents,hCode,hValue⟩

private def dataEnv {M : SetTheory.Structure.{u}} (D : Data M.Domain) : Env M 8 :=
  (((((((oneEnv D.horizon).push D.width).push D.forests).push D.codes).push D.tower).push D.boundary).push D.active).push D.level

private def boundaryHeightSchema : Project.Delta0BinarySchema 8 where
  body := boundaryHeightFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5,.bound 4,.bound 3,.bound 2⟩ (.bound 1) (.bound 0)
  freeClosed := boundaryHeightFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ _ _ rfl rfl
  delta0 := boundaryHeightFormula_delta0 _ _ _

theorem boundary_heights_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {D : Data M.Domain} (hD : D.Valid M C) :
    ∃ Heights, Graph M Heights D.horizon C.omega ∧ ∀ k h, MemPair M Heights k h ↔ M.mem k D.horizon ∧ BoundaryHeight M D k h := by
  have hφ (k h : M.Domain) : Project.Formula.satisfies (((dataEnv D).push k).push h) boundaryHeightSchema.body ↔ BoundaryHeight M D k h :=
    boundaryHeightFormula_iff hM.1 _ _ _ _
  obtain ⟨Heights,hSupport,hRaw⟩ := relation_comprehension_d hM boundaryHeightSchema (dataEnv D) D.horizon C.omega
  have hRows (k h : M.Domain) : MemPair M Heights k h ↔ M.mem k D.horizon ∧ BoundaryHeight M D k h := by
    have hr := hRaw k h
    rw [hφ] at hr
    exact hr.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.natural hM.1 hD,h.2⟩⟩
  refine ⟨Heights,⟨hSupport,?_,?_⟩,hRows⟩
  · intro k hk
    obtain ⟨h,hh,hHeight⟩ := boundary_height_exists_d hD hk
    exact ⟨h,hh,(hRows k h).mpr ⟨hk,hHeight⟩⟩
  · intro k a b hA hB
    exact ((hRows k a).mp hA).2.unique hM.1 hD ((hRows k b).mp hB).2

structure NeedHeights (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (D : Data M.Domain) (G : M.Domain) : Prop where
  graph : Graph M G D.horizon C.omega
  rows : ∀ k need, MemPair M G k need ↔ M.mem k D.horizon ∧ ∃ h, BoundaryHeight M D k h ∧ NeedHeight M C D.active D.level k h need

private def needHeightGraphSchema : Project.Delta0BinarySchema 4 where
  body := Project.Formula.existsMem (.bound 5)
    (.conj (memPairFormula (.bound 3) (.bound 2) (.bound 0)) (needHeightFormula (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 0) (.bound 1)))
  freeClosed := by
    simp [needHeightFormula,needRowFormula,Project.Formula.existsMem,Project.Formula.forallMem,
      Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (needHeightFormula_delta0 _ _ _ _ _ _))

theorem need_heights_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Data M.Domain} (hD : D.Valid M C) : ∃ G, NeedHeights M C D G := by
  obtain ⟨Heights,hHeights,hHeightRows⟩ := boundary_heights_exists_d hM hD
  let e := (((oneEnv C.omega).push D.active).push D.level).push Heights
  have hφ (k need : M.Domain) : Project.Formula.satisfies ((e.push k).push need) needHeightGraphSchema.body ↔
      ∃ h, M.mem h C.omega ∧ MemPair M Heights k h ∧ NeedHeight M C D.active D.level k h need := by
    simp only [needHeightGraphSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff hM.1]
    have hNeed (h : M.Domain) := needHeightFormula_iff hM.1 (((e.push k).push need).push h)
      ⟨.bound 6,.bound 6,.bound 6,.bound 6,.bound 6⟩ (.bound 5) (.bound 4) (.bound 2) (.bound 0) (.bound 1)
    simp only [hNeed]
    rfl
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM needHeightGraphSchema e D.horizon C.omega
  have hRows (k need : M.Domain) : MemPair M G k need ↔ M.mem k D.horizon ∧ ∃ h, BoundaryHeight M D k h ∧ NeedHeight M C D.active D.level k h need := by
    have hr := hRaw k need
    rw [hφ] at hr
    constructor
    · intro hAt
      obtain ⟨hk,_,h,_,hH,hNeed⟩ := hr.mp hAt
      exact ⟨hk,h,((hHeightRows k h).mp hH).2,hNeed⟩
    · rintro ⟨hk,h,hH,hNeed⟩
      exact hr.mpr ⟨hk,hNeed.1,h,hH.natural hM.1 hD,(hHeightRows k h).mpr ⟨hk,hH⟩,hNeed⟩
  refine ⟨G,⟨hSupport,?_,?_⟩,hRows⟩
  · intro k hk
    obtain ⟨h,hh,hH⟩ := boundary_height_exists_d hD hk
    obtain ⟨need,hNeed⟩ := need_height_exists_d hM hC hD.active hD.level ((omega_isOrdinal_d hM hC.omega).transitive D.horizon hD.horizon k hk) hh
    exact ⟨need,hNeed.1,(hRows k need).mpr ⟨hk,h,hH,hNeed⟩⟩
  · intro k a b hA hB
    obtain ⟨_,h,hH,hNeedA⟩ := (hRows k a).mp hA
    obtain ⟨_,h',hH',hNeedB⟩ := (hRows k b).mp hB
    have hhh := hH.unique hM.1 hD hH'
    subst h'
    exact hNeedA.unique_d hM hC hNeedB

theorem NeedHeights.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {D : Data M.Domain} {G H : M.Domain} (hG : NeedHeights M C D G) (hH : NeedHeights M C D H) : G=H :=
  hG.graph.ext he hH.graph (fun k _ need => (hG.rows k need).trans (hH.rows k need).symm)


/-- 一条真实需要项的完整(k,row)发生位置，先保留row再投影为Packet。 -/
def Occurrence (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (D : Data M.Domain) (k row q p : M.Domain) : Prop :=
  ∃ code, M.mem code D.codes ∧ MemPair M D.tower k code ∧ ∃ heights parents, Codes M code heights parents ∧
    ∃ h, M.mem h C.omega ∧ MemPair M heights D.boundary h ∧ NeedRow M D.active D.level k row h ∧
      ParentAt M ⟨D.width,heights,D.forests,parents⟩ row D.boundary p ∧ Lower.RootAt M C ⟨D.width,heights,D.forests,parents⟩ row D.boundary q

private def occurrenceInnerFormula {n : Nat} (C : ExpressionData (Project.Term n)) (D : Data (Project.Term n))
    (k row q p heights parents h : Project.Term n) : Project.Formula 1 n :=
  .conj (memPairFormula heights D.boundary h) (.conj (needRowFormula D.active D.level k row h)
    (.conj (parentAtFormula ⟨D.width,heights,D.forests,parents⟩ row D.boundary p)
      (Lower.rootAtFormula C ⟨D.width,heights,D.forests,parents⟩ row D.boundary q)))

private theorem occurrenceInnerFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (D : Data (Project.Term n))
    (k row q p heights parents h : Project.Term n) : (occurrenceInnerFormula C D k row q p heights parents h).IsDelta0 :=
  .conj (memPairFormula_delta0 _ _ _) (.conj (needRowFormula_delta0 _ _ _ _ _)
    (.conj (parentAtFormula_delta0 _ _ _ _) (Lower.rootAtFormula_delta0 _ _ _ _ _)))

private theorem occurrenceInnerFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {D : Data (Project.Term n)} (hD : D.Closed) (k row q p heights parents h : Project.Term n)
    (hk : k.freeSupport=[]) (hRow : row.freeSupport=[]) (hq : q.freeSupport=[]) (hp : p.freeSupport=[])
    (hHeights : heights.freeSupport=[]) (hParents : parents.freeSupport=[]) (hh : h.freeSupport=[]) :
    (occurrenceInnerFormula C D k row q p heights parents h).FreeClosed := by
  have hY : (⟨D.width,heights,D.forests,parents⟩ : CopiedMountain.Data (Project.Term n)).Closed := ⟨hD.width,hHeights,hD.forests,hParents⟩
  have hPar := parentAtFormula_freeClosed hY row D.boundary p hRow hD.boundary hp
  have hRoot := Lower.rootAtFormula_freeClosed hC hY row D.boundary q hRow hD.boundary hq
  have hNeed := needRowFormula_freeClosed D.active D.level k row h hD.active hD.level hk hRow hh
  simp [occurrenceInnerFormula,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,hHeights,hD.boundary,hh,hPar,hRoot,hNeed]

private theorem occurrenceInnerFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (D : Data (Project.Term n)) (k row q p heights parents h : Project.Term n) :
    Project.Formula.satisfies e (occurrenceInnerFormula C D k row q p heights parents h) ↔
      MemPair M (heights.eval e) (D.boundary.eval e) (h.eval e) ∧ NeedRow M (D.active.eval e) (D.level.eval e) (k.eval e) (row.eval e) (h.eval e) ∧
        ParentAt M ⟨D.width.eval e,heights.eval e,D.forests.eval e,parents.eval e⟩ (row.eval e) (D.boundary.eval e) (p.eval e) ∧
        Lower.RootAt M (C.eval e) ⟨D.width.eval e,heights.eval e,D.forests.eval e,parents.eval e⟩ (row.eval e) (D.boundary.eval e) (q.eval e) := by
  simp only [occurrenceInnerFormula,Project.Formula.satisfies_conj_iff,memPairFormula_iff he,
    needRowFormula_iff he,parentAtFormula_iff he,Lower.rootAtFormula_iff he]
  rfl

def occurrenceFormula {n : Nat} (C : ExpressionData (Project.Term n)) (D : Data (Project.Term n)) (k row q p : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem D.codes (.conj (memPairFormula D.tower.weaken k.weaken (.bound 0))
    (withCodeFormula (.bound 0) (Project.Formula.existsMem C.omega.weaken.weaken.weaken.weaken
      (occurrenceInnerFormula C.weaken.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken.weaken
        k.weaken.weaken.weaken.weaken.weaken row.weaken.weaken.weaken.weaken.weaken q.weaken.weaken.weaken.weaken.weaken
        p.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0)))))

theorem occurrenceFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (D : Data (Project.Term n)) (k row q p : Project.Term n) :
    (occurrenceFormula C D k row q p).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (withCodeFormula_delta0 _ (.existsMem _ (occurrenceInnerFormula_delta0 _ _ _ _ _ _ _ _ _))))

theorem occurrenceFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {D : Data (Project.Term n)} (hD : D.Closed) (k row q p : Project.Term n)
    (hk : k.freeSupport=[]) (hRow : row.freeSupport=[]) (hq : q.freeSupport=[]) (hp : p.freeSupport=[]) : (occurrenceFormula C D k row q p).FreeClosed := by
  have hInner := occurrenceInnerFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken hD.weaken.weaken.weaken.weaken.weaken
    k.weaken.weaken.weaken.weaken.weaken row.weaken.weaken.weaken.weaken.weaken q.weaken.weaken.weaken.weaken.weaken p.weaken.weaken.weaken.weaken.weaken
    (.bound 2) (.bound 1) (.bound 0) (by simpa using hk) (by simpa using hRow) (by simpa using hq) (by simpa using hp) rfl rfl rfl
  have hBody : (Project.Formula.existsMem C.omega.weaken.weaken.weaken.weaken
      (occurrenceInnerFormula C.weaken.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken.weaken
        k.weaken.weaken.weaken.weaken.weaken row.weaken.weaken.weaken.weaken.weaken q.weaken.weaken.weaken.weaken.weaken
        p.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))).FreeClosed := by
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hInner]
  have hWith := withCodeFormula_freeClosed (Project.Term.bound (depth := n+1) 0) rfl hBody
  have hAt : (memPairFormula D.tower.weaken k.weaken (Project.Term.bound (depth := n+1) 0)).FreeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hD.tower,hk]
  simp [occurrenceFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hD.codes,hAt]
  simpa only [Project.Formula.existsMem] using hWith

theorem occurrenceFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (D : Data (Project.Term n)) (k row q p : Project.Term n) :
    Project.Formula.satisfies e (occurrenceFormula C D k row q p) ↔ Occurrence M (C.eval e) (D.eval e) (k.eval e) (row.eval e) (q.eval e) (p.eval e) := by
  have hCode (code : M.Domain) : Project.Formula.satisfies (e.push code)
      (withCodeFormula (.bound 0) (Project.Formula.existsMem C.omega.weaken.weaken.weaken.weaken
        (occurrenceInnerFormula C.weaken.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken.weaken
          k.weaken.weaken.weaken.weaken.weaken row.weaken.weaken.weaken.weaken.weaken q.weaken.weaken.weaken.weaken.weaken
          p.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0)))) ↔
      ∃ heights parents, Codes M code heights parents ∧ ∃ h, M.mem h (C.omega.eval e) ∧
        MemPair M heights (D.boundary.eval e) h ∧ NeedRow M (D.active.eval e) (D.level.eval e) (k.eval e) (row.eval e) h ∧
          ParentAt M ⟨D.width.eval e,heights,D.forests.eval e,parents⟩ (row.eval e) (D.boundary.eval e) (p.eval e) ∧
          Lower.RootAt M (C.eval e) ⟨D.width.eval e,heights,D.forests.eval e,parents⟩ (row.eval e) (D.boundary.eval e) (q.eval e) := by
    apply withCodeFormula_iff_exists he (e.push code) (.bound 0) _ _
    intro b heights parents
    simp only [Project.Formula.satisfies_existsMem_iff,occurrenceInnerFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken,
      Data.weaken,Data.map,Project.Term.eval_bound_two_push,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push]
  simp only [occurrenceFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,Term.eval_weaken,hCode]
  rfl


theorem Occurrence.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Data M.Domain} (hD : D.Valid M C) {k row q p q' p' : M.Domain}
    (h : Occurrence M C D k row q p) (h' : Occurrence M C D k row q' p') : q=q' ∧ p=p' := by
  obtain ⟨code,_,hAt,heights,parents,hCode,_,_,_,_,hParent,hRoot⟩ := h
  obtain ⟨code',_,hAt',heights',parents',hCode',_,_,_,_,hParent',hRoot'⟩ := h'
  have hCodes := hD.graph.unique k code code' hAt hAt'
  subst code'
  obtain ⟨hHs,hPs⟩ := codes_injective hM.1 hCode hCode'
  subst heights'
  subst parents'
  have hY := (hD.values k code hAt).read hM.1 hCode
  exact ⟨hRoot.unique_d hM hC hY hRoot',hParent.unique hY hParent'⟩

theorem Occurrence.template_bounds_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Data M.Domain} (hD : D.Valid M C) {k row q p : M.Domain}
    (h : Occurrence M C D k row q p) : (q=p ∨ M.mem q p) ∧ M.mem p D.boundary := by
  obtain ⟨code,_,hAt,heights,parents,hCode,_,_,_,_,hParent,hRoot⟩ := h
  have hY := (hD.values k code hAt).read hM.1 hCode
  obtain ⟨F,_,hF,hParent⟩ := hParent
  obtain ⟨F',_,hF',hRoot⟩ := hRoot
  have hFF := hY.parents.unique row F F' hF hF'
  subst F'
  have hForest := hY.forest row F hF
  exact ⟨CopyInvariant.root_le_parent_d hM hC hForest hParent hRoot,hForest.left D.boundary p hParent⟩

theorem Occurrence.indices_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Data M.Domain} (hD : D.Valid M C) {k row q p : M.Domain}
    (h : Occurrence M C D k row q p) : M.mem k D.horizon ∧ M.mem row C.omega ∧ M.mem q C.omega ∧ M.mem p C.omega := by
  obtain ⟨code,_,hAt,heights,parents,hCode,height,hh,_,hNeed,hParent,hRoot⟩ := h
  have hY := (hD.values k code hAt).read hM.1 hCode
  have hP := hParent.bounds hM.1 hY
  have hQ := hRoot.bounds hM.1 hY
  have hw := omega_isOrdinal_d hM hC.omega
  exact ⟨(hD.graph.bounds hM.1 hAt).1,hw.transitive height hh row hNeed.1,
    hw.transitive D.width hD.width q hQ.2.1,hw.transitive D.width hD.width p hP.2.2.1⟩

theorem Occurrence.levels {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {D : Data M.Domain} {k row q p : M.Domain}
    (h : Occurrence M C D k row q p) : M.mem k D.active ∨ (k=D.active ∧ M.mem row D.level) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hNeed,_,_⟩ := h
  exact hNeed.2

theorem occurrence_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Data M.Domain} (hD : D.Valid M C) {G k need row : M.Domain}
    (hNeeds : NeedHeights M C D G) (hAt : MemPair M G k need) (hr : M.mem row need) : ∃ q p, Occurrence M C D k row q p := by
  obtain ⟨_,height,hHeight,hCut⟩ := (hNeeds.rows k need).mp hAt
  have hRowNat := (omega_isOrdinal_d hM hC.omega).transitive need (hNeeds.graph.bounds hM.1 hAt).2 row hr
  have hNeed := (hCut.2 row hRowNat).mp hr
  obtain ⟨code,hCodeMem,hCodeAt,heights,parents,hCode,hValue⟩ := hHeight
  have hY := (hD.values k code hCodeAt).read hM.1 hCode
  obtain ⟨p,hParent⟩ := (hY.source row D.boundary height hValue).mpr hNeed.1
  obtain ⟨q,hRoot⟩ := Lower.root_at_exists_d hM hC hY hRowNat hD.boundary
  exact ⟨q,p,code,hCodeMem,hCodeAt,heights,parents,hCode,height,(hY.heights.bounds hM.1 hValue).2,hValue,hNeed,hParent,hRoot⟩

theorem Occurrence.need_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Data M.Domain} (hD : D.Valid M C) {G k row q p : M.Domain}
    (hNeeds : NeedHeights M C D G) (h : Occurrence M C D k row q p) : ∃ need, MemPair M G k need ∧ M.mem row need := by
  have hIndices := h.indices_d hM hC hD
  obtain ⟨need,_,hAt⟩ := hNeeds.graph.total k hIndices.1
  obtain ⟨_,height,hH,hCut⟩ := (hNeeds.rows k need).mp hAt
  obtain ⟨code,hCodeMem,hCodeAt,heights,parents,hCode,h',hh',hValue,hNeed,_,_⟩ := h
  have hBoundary : BoundaryHeight M D k h' := ⟨code,hCodeMem,hCodeAt,heights,parents,hCode,hValue⟩
  have he := hBoundary.unique hM.1 hD hH
  subst h'
  exact ⟨need,hAt,(hCut.2 row hIndices.2.1).mpr hNeed⟩


/-- 固定行stride的(k,row)地址；过滤后仍保留原层/行顺序及重复Packet。 -/
def IndexedNeed (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Data M.Domain) (rowBound i packet : M.Domain) : Prop :=
  ∃ k, M.mem k D.horizon ∧ ∃ row, M.mem row rowBound ∧ ∃ q, M.mem q C.omega ∧ ∃ p, M.mem p C.omega ∧
    CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times C.zero rowBound k row i ∧
      Occurrence M C D k row q p ∧ KP1Y.Ranking.Packet M packet k q p

def indexedNeedFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Data (Project.Term n)) (rowBound i packet : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem D.horizon (Project.Formula.existsMem rowBound.weaken
    (Project.Formula.existsMem C.omega.weaken.weaken (Project.Formula.existsMem C.omega.weaken.weaken.weaken
      (.conj (copyPositionFormula C.omega.weaken.weaken.weaken.weaken T.addPairs.weaken.weaken.weaken.weaken T.plus.weaken.weaken.weaken.weaken
        T.mulPairs.weaken.weaken.weaken.weaken T.times.weaken.weaken.weaken.weaken C.zero.weaken.weaken.weaken.weaken
        rowBound.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) i.weaken.weaken.weaken.weaken)
        (.conj (occurrenceFormula C.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) (.bound 0))
          (KP1Y.Ranking.packetFormula packet.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (.bound 0)))))))

theorem indexedNeedFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (D : Data (Project.Term n)) (rowBound i packet : Project.Term n) : (indexedNeedFormula C T D rowBound i packet).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (copyPositionFormula_delta0 _ _ _ _ _ _ _ _ _ _)
    (.conj (occurrenceFormula_delta0 _ _ _ _ _ _) (KP1Y.Ranking.packetFormula_delta0 _ _ _ _))))))

theorem indexedNeedFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {D : Data (Project.Term n)} (hD : D.Closed)
    (rowBound i packet : Project.Term n) (hBound : rowBound.freeSupport=[]) (hi : i.freeSupport=[]) (hPacket : packet.freeSupport=[]) :
    (indexedNeedFormula C T D rowBound i packet).FreeClosed := by
  have hOcc := occurrenceFormula_freeClosed hC.weaken.weaken.weaken.weaken hD.weaken.weaken.weaken.weaken
    (Project.Term.bound (depth := n+4) 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl
  have hPack := KP1Y.Ranking.packetFormula_freeClosed packet.weaken.weaken.weaken.weaken
    (Project.Term.bound (depth := n+4) 3) (.bound 1) (.bound 0) (by simpa using hPacket) rfl rfl rfl
  simp [indexedNeedFormula,copyPositionFormula,mulAtFormula,addAtFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hD.horizon,hC.omega,hC.zero,
    hT.addPairs,hT.plus,hT.mulPairs,hT.times,hBound,hi,hOcc,hPack]

theorem indexedNeedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (D : Data (Project.Term n)) (rowBound i packet : Project.Term n) :
    Project.Formula.satisfies e (indexedNeedFormula C T D rowBound i packet) ↔
      IndexedNeed M (C.eval e) (T.eval e) (D.eval e) (rowBound.eval e) (i.eval e) (packet.eval e) := by
  simp only [indexedNeedFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    copyPositionFormula_iff he,occurrenceFormula_iff he,KP1Y.Ranking.packetFormula_iff he,
    ExpressionData.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem IndexedNeed.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Data M.Domain} (hD : D.Valid M C) {rowBound i e e' : M.Domain} (hBound : M.mem rowBound C.omega)
    (h : IndexedNeed M C T D rowBound i e) (h' : IndexedNeed M C T D rowBound i e') : e=e' := by
  obtain ⟨k,hk,row,hRow,q,_,p,_,hPos,hOcc,hPacket⟩ := h
  obtain ⟨k',hk',row',hRow',q',_,p',_,hPos',hOcc',hPacket'⟩ := h'
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨hkk,hrr⟩ := copy_position_injective_d hM hC hT.add hT.mul hC.zero_nat hBound
    (hw.transitive D.horizon hD.horizon k hk) (hw.transitive D.horizon hD.horizon k' hk') hRow hRow' hPos hPos'
  subst k'
  subst row'
  obtain ⟨hqq,hpp⟩ := hOcc.unique_d hM hC hD hOcc'
  subst q'
  subst p'
  obtain ⟨pair,hCode,hPair⟩ := hPacket
  obtain ⟨pair',hCode',hPair'⟩ := hPacket'
  have hpairs := codes_unique hM.1 hPair hPair'
  subst pair'
  exact codes_unique hM.1 hCode hCode'

structure NeedMap (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (R : KP1Y.Reflection.Data M.Domain) (D : Data M.Domain) (rowBound size P : M.Domain) : Prop where
  graph : Filter.PartialGraph M P size R.needCodes
  rows : ∀ i e, MemPair M P i e ↔ M.mem i size ∧ M.mem e R.needCodes ∧ IndexedNeed M C T D rowBound i e

private def indexedNeedSchema : Project.Delta0BinarySchema 20 where
  body := indexedNeedFormula ⟨.bound 21,.bound 20,.bound 19,.bound 18,.bound 17⟩
    ⟨.bound 16,.bound 15,.bound 14,.bound 13,.bound 12,.bound 11⟩
    ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6,.bound 5,.bound 4,.bound 3⟩ (.bound 2) (.bound 1) (.bound 0)
  freeClosed := indexedNeedFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ _ _ _ rfl rfl rfl
  delta0 := indexedNeedFormula_delta0 _ _ _ _ _ _

private def indexEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Data M.Domain) (rowBound : M.Domain) : Env M 20 :=
  (((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push D.horizon).push D.width).push D.forests).push D.codes).push D.tower).push D.boundary).push D.active).push D.level).push rowBound

theorem need_map_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    (R : KP1Y.Reflection.Data M.Domain) {D : Data M.Domain} (hD : D.Valid M C) {rowBound size : M.Domain}
    (hBound : M.mem rowBound C.omega) : ∃ P, NeedMap M C T R D rowBound size P := by
  have hφ (i e : M.Domain) : Project.Formula.satisfies (((indexEnv C T D rowBound).push i).push e) indexedNeedSchema.body ↔
      IndexedNeed M C T D rowBound i e := indexedNeedFormula_iff hM.1 _ _ _ _ _ _ _
  obtain ⟨P,hSupport,hRaw⟩ := relation_comprehension_d hM indexedNeedSchema (indexEnv C T D rowBound) size R.needCodes
  have hRows (i e : M.Domain) : MemPair M P i e ↔ M.mem i size ∧ M.mem e R.needCodes ∧ IndexedNeed M C T D rowBound i e := by
    simpa only [hφ] using hRaw i e
  exact ⟨P,⟨hSupport,fun i e e' hAt hAt' => ((hRows i e).mp hAt).2.2.unique_d hM hC hT hD hBound ((hRows i e').mp hAt').2.2⟩,hRows⟩

/-- 规范稳定过滤证书。stride是实际NeedHeights图的最小正严格上界。 -/
def Lists (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (R : KP1Y.Reflection.Data M.Domain) (D : Data M.Domain) (N : M.Domain) : Prop :=
  ∃ Heights rowBound size P len I, NeedHeights M C D Heights ∧ SequenceBound M C D.horizon Heights rowBound ∧
    KP1Y.Arithmetic.Product M D.horizon rowBound size ∧ NeedMap M C T R D rowBound size P ∧
    Filter.Filtered M C.omega P size R.needCodes len N I

theorem lists_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    (R : KP1Y.Reflection.Data M.Domain) {D : Data M.Domain} (hD : D.Valid M C) : ∃ N, Lists M C T R D N := by
  obtain ⟨Heights,hHeights⟩ := need_heights_exists_d hM hC hD
  obtain ⟨rowBound,hBound⟩ := sequence_bound_exists_d hM hC hD.horizon hHeights.graph
  obtain ⟨size,hSize,hProduct⟩ := natural_product_exists_d hM hC hD.horizon hBound.1.1
  obtain ⟨P,hMap⟩ := need_map_exists_d (size := size) hM hC hT R hD hBound.1.1
  obtain ⟨len,N,I,hFilter⟩ := Filter.filtered_exists_d hM hC hSize hMap.graph
  exact ⟨N,Heights,rowBound,size,P,len,I,hHeights,hBound,hProduct,hMap,hFilter⟩

theorem Lists.list_mem {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega) {D : Data M.Domain} {N : M.Domain}
    (h : Lists M C T R D N) : M.mem N R.needLists := by
  obtain ⟨_,_,_,_,len,_,_,_,_,_,hFilter⟩ := h
  exact (hR.needLists N).mpr ⟨len,hOmega.symm ▸ hFilter.length,hFilter.output⟩


theorem Occurrence.row_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Data M.Domain} (hD : D.Valid M C)
    {Heights rowBound k row q p : M.Domain} (hHeights : NeedHeights M C D Heights)
    (hBound : SequenceBound M C D.horizon Heights rowBound) (h : Occurrence M C D k row q p) : M.mem row rowBound := by
  obtain ⟨need,hAt,hr⟩ := h.need_height_d hM hC hD hHeights
  have hNeedBound := hBound.value_lt hM.1 hHeights.graph hAt
  exact ((omega_isOrdinal_d hM hC.omega).mem hBound.1.1).transitive need hNeedBound row hr

theorem Occurrence.indexed_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega)
    {D : Data M.Domain} (hD : D.Valid M C) {Heights rowBound size k row q p : M.Domain}
    (hHeights : NeedHeights M C D Heights) (hBound : SequenceBound M C D.horizon Heights rowBound)
    (hSize : KP1Y.Arithmetic.Product M D.horizon rowBound size) (h : Occurrence M C D k row q p) :
    ∃ i, M.mem i size ∧ ∃ packet, M.mem packet R.needCodes ∧ IndexedNeed M C T D rowBound i packet ∧ KP1Y.Ranking.Packet M packet k q p := by
  obtain ⟨hk,hr,hq,hp⟩ := h.indices_d hM hC hD
  have hRowBound := h.row_bounded_d hM hC hD hHeights hBound
  have hkNat := (omega_isOrdinal_d hM hC.omega).transitive D.horizon hD.horizon k hk
  obtain ⟨i,_,hPos⟩ := copy_position_exists_d hM hC hT.add hT.mul hC.zero_nat hBound.1.1 hkNat hr
  have hSizeNat := natural_product_closed_d hM hC hD.horizon hBound.1.1 hSize
  have hZeroSum := natural_sum_comm_d hM hC hSizeNat hC.zero_nat (KP1Y.Arithmetic.sum_zero_d hM size hC.zero_empty)
  have hi := copy_position_bounded_d hM hC hT.add hT.mul hC.zero_nat hBound.1.1 hD.horizon hSize hZeroSum hk hRowBound hPos
  obtain ⟨packet,hPacket,hCode⟩ := KP1Y.Reflection.need_code_exists_d hM hR (hOmega.symm ▸ hkNat) (hOmega.symm ▸ hq) (hOmega.symm ▸ hp)
  exact ⟨i,hi,packet,hPacket,⟨k,hk,row,hRowBound,q,hq,p,hp,hPos,h,hCode⟩,hCode⟩

/-- 精确覆盖全部且仅所需发生行；没有以所有末列边替代需要范围。 -/
theorem Lists.need_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega)
    {D : Data M.Domain} (hD : D.Valid M C) {N k q p : M.Domain} (hList : Lists M C T R D N) :
    KP1Y.Reflection.NeedAt M R N k q p ↔ ∃ row, Occurrence M C D k row q p := by
  obtain ⟨Heights,rowBound,size,P,len,I,hHeights,hBound,hSize,hMap,hFilter⟩ := hList
  constructor
  · rintro ⟨j,_,packet,_,hAt,hPacket⟩
    obtain ⟨i,_,hP⟩ := (hFilter.range_iff hM.1 hMap.graph).mp ⟨j,(hFilter.output.bounds hM.1 hAt).1,hAt⟩
    obtain ⟨_,_,k',_,row,_,q',_,p',_,_,hOcc,hPacket'⟩ := (hMap.rows i packet).mp hP
    obtain ⟨hkk,hqq,hpp⟩ := hPacket'.injective hM.1 hPacket
    subst k'
    subst q'
    subst p'
    exact ⟨row,hOcc⟩
  · rintro ⟨row,hOcc⟩
    obtain ⟨i,hi,packet,hPacket,hIndexed,hCode⟩ := hOcc.indexed_exists_d hM hC hT hR hOmega hD hHeights hBound hSize
    have hP := (hMap.rows i packet).mpr ⟨hi,hPacket,hIndexed⟩
    obtain ⟨j,hj,hAt⟩ := (hFilter.range_iff hM.1 hMap.graph).mpr ⟨i,hi,hP⟩
    exact ⟨j,hOmega.symm ▸ (omega_isOrdinal_d hM hC.omega).transitive len hFilter.length j hj,packet,hPacket,hAt,hCode⟩

theorem Lists.template_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega)
    {D : Data M.Domain} (hD : D.Valid M C) {N : M.Domain} (hList : Lists M C T R D N) : KP1Y.Reflection.Template M R D.boundary N := by
  refine ⟨hOmega.symm ▸ (omega_isOrdinal_d hM hC.omega).transitive D.width hD.width D.boundary hD.boundary,hList.list_mem hR hOmega,?_⟩
  intro k _ q _ p _ hNeed
  obtain ⟨row,hOcc⟩ := (hList.need_iff_d hM hC hT hR hOmega hD).mp hNeed
  exact hOcc.template_bounds_d hM hC hD

theorem Lists.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {R : KP1Y.Reflection.Data M.Domain} {D : Data M.Domain} (hD : D.Valid M C) {N N' : M.Domain}
    (h : Lists M C T R D N) (h' : Lists M C T R D N') : N=N' := by
  obtain ⟨Heights,rowBound,size,P,len,I,hHeights,hBound,hSize,hMap,hFilter⟩ := h
  obtain ⟨Heights',rowBound',size',P',len',I',hHeights',hBound',hSize',hMap',hFilter'⟩ := h'
  have hHs := hHeights.unique hM.1 hHeights'
  subst Heights'
  have hRB := hBound.unique_d hM hC hBound'
  subst rowBound'
  have hSS := KP1Y.Arithmetic.product_unique_d hM hSize hSize'
  subst size'
  have hPP : P=P' := relation_ext hM.1 hMap.graph.support hMap'.graph.support (fun i e => (hMap.rows i e).trans (hMap'.rows i e).symm)
  subst P'
  have hSizeNat := natural_product_closed_d hM hC hD.horizon hBound.1.1 hSize
  exact (hFilter.unique_d hM hC hSizeNat hMap.graph hFilter').2.1

end KP1Y.OneYFinite.CopyNeeds
