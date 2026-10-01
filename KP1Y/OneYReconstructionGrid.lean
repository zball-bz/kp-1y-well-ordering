import KP1Y.OneYReconstruction

/-! 从实际有限父行家族构造重建网格。对任意输入历史先规范化取值，保证Σ₁递归全定义。 -/
namespace KP1Y.OneYFinite.Reconstruction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u v

structure GridData (α : Type u) where
  naturals : ExpressionData α
  width : α
  rows : α
  heights : α
  forests : α
  parents : α
  tops : α
  pairs : α
  plus : α

def GridData.map {α : Type u} {β : Type v} (D : GridData α) (f : α → β) : GridData β :=
  ⟨D.naturals.map f,f D.width,f D.rows,f D.heights,f D.forests,f D.parents,f D.tops,f D.pairs,f D.plus⟩

def GridData.eval {M : SetTheory.Structure.{u}} {n : Nat} (D : GridData (Project.Term n)) (e : Env M n) : GridData M.Domain :=
  D.map (fun t => t.eval e)

def GridData.weaken {n : Nat} (D : GridData (Project.Term n)) : GridData (Project.Term (n+1)) := D.map (fun t => t.weaken)

theorem GridData.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat}
    (D : GridData (Project.Term n)) (e : Env M n) (a : M.Domain) : D.weaken.eval (e.push a)=D.eval e := by
  rcases D with ⟨⟨w,z,o,S,E⟩,m,B,H,F,P,T,Pairs,Plus⟩
  simp [GridData.weaken,GridData.eval,GridData.map,ExpressionData.map,Term.eval_weaken]

structure GridData.Closed {n : Nat} (D : GridData (Project.Term n)) : Prop where
  naturals : D.naturals.Closed
  width : D.width.freeSupport=[]
  rows : D.rows.freeSupport=[]
  heights : D.heights.freeSupport=[]
  forests : D.forests.freeSupport=[]
  parents : D.parents.freeSupport=[]
  tops : D.tops.freeSupport=[]
  pairs : D.pairs.freeSupport=[]
  plus : D.plus.freeSupport=[]

theorem GridData.Closed.weaken {n : Nat} {D : GridData (Project.Term n)} (h : D.Closed) : D.weaken.Closed := by
  rcases h with ⟨hC,hm,hB,hH,hF,hP,hT,hPairs,hPlus⟩
  refine ⟨hC.weaken,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> simp_all [GridData.weaken,GridData.map]

def ParentAt (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (r c p : M.Domain) : Prop :=
  ∃ F, M.mem F D.forests ∧ MemPair M D.parents r F ∧ MemPair M F c p

def parentAtFormula {n : Nat} (D : GridData (Project.Term n)) (r c p : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem D.forests (.conj (memPairFormula D.parents.weaken r.weaken (.bound 0))
    (memPairFormula (.bound 0) c.weaken p.weaken))

theorem parentAtFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (r c p : Project.Term n) :
    (parentAtFormula D r c p).IsDelta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem parentAtFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (r c p : Project.Term n) (hr : r.freeSupport=[]) (hc : c.freeSupport=[])
    (hp : p.freeSupport=[]) : (parentAtFormula D r c p).FreeClosed := by
  simp [parentAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hD.forests,hD.parents,hr,hc,hp]

theorem parentAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (r c p : Project.Term n) :
    Project.Formula.satisfies e (parentAtFormula D r c p) ↔ ParentAt M (D.eval e) (r.eval e) (c.eval e) (p.eval e) := by
  simp only [parentAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,Term.eval_weaken]
  rfl

structure GridData.Valid (M : SetTheory.Structure.{u}) (D : GridData M.Domain) : Prop where
  naturals : D.naturals.Valid M
  width : M.mem D.width D.naturals.omega
  rows : M.mem D.rows D.naturals.omega
  heights : Graph M D.heights D.width D.rows
  tops : Graph M D.tops D.width D.naturals.omega
  parents : Graph M D.parents D.rows D.forests
  forests : ∀ r F, MemPair M D.parents r F → Forest M D.naturals.omega D.width F
  live : ∀ r, M.mem r D.rows → ∀ c, M.mem c D.width → ∀ h, MemPair M D.heights c h →
    ((∃ p, ParentAt M D r c p) ↔ M.mem r h)
  endpoint : ∀ r c p, ParentAt M D r c p → ∀ h, MemPair M D.heights p h → r=h ∨ M.mem r h
  addition : AdditionTable M D.naturals D.pairs D.plus

theorem ParentAt.bounds {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : GridData M.Domain} (hD : D.Valid M) {r c p : M.Domain} (h : ParentAt M D r c p) :
    M.mem r D.rows ∧ M.mem c D.width ∧ M.mem p D.width ∧ M.mem p c := by
  obtain ⟨F,_,hRow,hParent⟩ := h
  have hF := hD.forests r F hRow
  exact ⟨(hD.parents.bounds he hRow).1,(hF.bounds he hParent).1,(hF.bounds he hParent).2,hF.left c p hParent⟩

theorem ParentAt.unique {M : SetTheory.Structure.{u}} {D : GridData M.Domain} (hD : D.Valid M)
    {r c p q : M.Domain} (hp : ParentAt M D r c p) (hq : ParentAt M D r c q) : p=q := by
  obtain ⟨F,_,hF,hp⟩ := hp
  obtain ⟨G,_,hG,hq⟩ := hq
  have hFG := hD.parents.unique r F G hF hG
  subst G
  exact (hD.forests r F hF).unique c p q hp hq

/-- 只有具备正确行域的真实列图才被读取；畸形历史列不作为数值函数使用。 -/
def ValidCell (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (H p r x : M.Domain) : Prop :=
  ∃ f, M.mem f D.naturals.sequences ∧ MemPair M H p f ∧ Graph M f D.rows D.naturals.omega ∧ MemPair M f r x

def validCellFormula {n : Nat} (D : GridData (Project.Term n)) (H p r x : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem D.naturals.sequences
    (.conj (memPairFormula H.weaken p.weaken (.bound 0))
      (.conj (graphFormula (.bound 0) D.rows.weaken D.naturals.omega.weaken)
        (memPairFormula (.bound 0) r.weaken x.weaken)))

theorem validCellFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (H p r x : Project.Term n) :
    (validCellFormula D H p r x).IsDelta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _)
      (.conj (graphFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))

theorem validCellFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (H p r x : Project.Term n) (hH : H.freeSupport=[]) (hp : p.freeSupport=[])
    (hr : r.freeSupport=[]) (hx : x.freeSupport=[]) : (validCellFormula D H p r x).FreeClosed := by
  simp [validCellFormula,memPairFormula,graphFormula,codeFormula,pairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hD.naturals.sequences,hD.naturals.omega,hD.rows,hH,hp,hr,hx]

theorem validCellFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (H p r x : Project.Term n) :
    Project.Formula.satisfies e (validCellFormula D H p r x) ↔
      ValidCell M (D.eval e) (H.eval e) (p.eval e) (r.eval e) (x.eval e) := by
  simp only [validCellFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,graphFormula_iff he,Term.eval_weaken]
  rfl

theorem ValidCell.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {D : GridData M.Domain}
    {H p r x : M.Domain} (h : ValidCell M D H p r x) : M.mem r D.rows ∧ M.mem x D.naturals.omega := by
  obtain ⟨_,_,_,hF,hAt⟩ := h
  exact hF.bounds he hAt

theorem ValidCell.unique {M : SetTheory.Structure.{u}} {D : GridData M.Domain} {H A W p r x y : M.Domain}
    (hH : Graph M H A W) (hx : ValidCell M D H p r x) (hy : ValidCell M D H p r y) : x=y := by
  obtain ⟨f,_,hf,hF,hx⟩ := hx
  obtain ⟨g,_,hg,_,hy⟩ := hy
  have hfg := hH.unique p f g hf hg
  subst g
  exact hF.unique r x y hx hy

def PreviousValue (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (H p r x : M.Domain) : Prop :=
  ValidCell M D H p r x ∨ (x=D.naturals.zero ∧ ∀ y, M.mem y D.naturals.omega → ¬ValidCell M D H p r y)

def previousValueFormula {n : Nat} (D : GridData (Project.Term n)) (H p r x : Project.Term n) : Project.Formula 1 n :=
  .disj (validCellFormula D H p r x) (.conj (Project.Formula.extensionalEq x D.naturals.zero)
    (Project.Formula.forallMem D.naturals.omega (.neg (validCellFormula D.weaken H.weaken p.weaken r.weaken (.bound 0)))))

theorem previousValueFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (H p r x : Project.Term n) :
    (previousValueFormula D H p r x).IsDelta0 :=
  .disj (validCellFormula_delta0 _ _ _ _ _) (.conj (.atom _ _ _)
    (.forallMem _ (.neg (validCellFormula_delta0 _ _ _ _ _))))

theorem previousValueFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (H p r x : Project.Term n) (hH : H.freeSupport=[]) (hp : p.freeSupport=[])
    (hr : r.freeSupport=[]) (hx : x.freeSupport=[]) : (previousValueFormula D H p r x).FreeClosed := by
  have hNow := validCellFormula_freeClosed hD H p r x hH hp hr hx
  have hAll := validCellFormula_freeClosed hD.weaken H.weaken p.weaken r.weaken (.bound 0)
    (by simpa using hH) (by simpa using hp) (by simpa using hr) rfl
  simp [previousValueFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,
    hNow,hAll,hx,hD.naturals.zero,hD.naturals.omega]

theorem previousValueFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (H p r x : Project.Term n) :
    Project.Formula.satisfies e (previousValueFormula D H p r x) ↔
      PreviousValue M (D.eval e) (H.eval e) (p.eval e) (r.eval e) (x.eval e) := by
  simp only [previousValueFormula,Project.Formula.satisfies_disj_iff,validCellFormula_iff he,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_neg_iff,GridData.eval_weaken,Term.eval_weaken]
  rfl

theorem previous_value_exists {M : SetTheory.Structure.{u}} (he : Extensional M) {D : GridData M.Domain}
    (hD : D.Valid M) (H p r : M.Domain) : ∃ x, M.mem x D.naturals.omega ∧ PreviousValue M D H p r x := by
  classical
  by_cases hSome : ∃ x, ValidCell M D H p r x
  · obtain ⟨x,hx⟩ := hSome
    exact ⟨x,(hx.bounds he).2,Or.inl hx⟩
  · exact ⟨D.naturals.zero,hD.naturals.zero_nat,Or.inr ⟨rfl,fun x _ hx => hSome ⟨x,hx⟩⟩⟩

theorem PreviousValue.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {D : GridData M.Domain}
    (hD : D.Valid M) {H p r x : M.Domain} (h : PreviousValue M D H p r x) : M.mem x D.naturals.omega := by
  rcases h with h | ⟨heq,_⟩
  · exact (h.bounds he).2
  · exact heq ▸ hD.naturals.zero_nat

theorem PreviousValue.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : GridData M.Domain} {H A W p r x y : M.Domain} (hH : Graph M H A W)
    (hx : PreviousValue M D H p r x) (hy : PreviousValue M D H p r y) : x=y := by
  rcases hx with hx | ⟨hx,hNo⟩ <;> rcases hy with hy | ⟨hy,hNo'⟩
  · exact hx.unique hH hy
  · exact False.elim (hNo' x (hx.bounds he).2 hx)
  · exact False.elim (hNo y (hy.bounds he).2 hy)
  · exact hx.trans hy.symm

def Contributes (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (H c r x : M.Domain) : Prop :=
  (∃ p, M.mem p c ∧ ParentAt M D r c p ∧ PreviousValue M D H p r x) ∨
    (x=D.naturals.zero ∧ ∀ p, M.mem p c → ¬ParentAt M D r c p)

def contributesFormula {n : Nat} (D : GridData (Project.Term n)) (H c r x : Project.Term n) : Project.Formula 1 n :=
  .disj (Project.Formula.existsMem c (.conj (parentAtFormula D.weaken r.weaken c.weaken (.bound 0))
    (previousValueFormula D.weaken H.weaken (.bound 0) r.weaken x.weaken)))
    (.conj (Project.Formula.extensionalEq x D.naturals.zero)
      (Project.Formula.forallMem c (.neg (parentAtFormula D.weaken r.weaken c.weaken (.bound 0)))))

theorem contributesFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (H c r x : Project.Term n) :
    (contributesFormula D H c r x).IsDelta0 :=
  .disj (.existsMem _ (.conj (parentAtFormula_delta0 _ _ _ _) (previousValueFormula_delta0 _ _ _ _ _)))
    (.conj (.atom _ _ _) (.forallMem _ (.neg (parentAtFormula_delta0 _ _ _ _))))

theorem contributesFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (H c r x : Project.Term n) (hH : H.freeSupport=[]) (hc : c.freeSupport=[])
    (hr : r.freeSupport=[]) (hx : x.freeSupport=[]) : (contributesFormula D H c r x).FreeClosed := by
  have hP := parentAtFormula_freeClosed hD.weaken r.weaken c.weaken (.bound 0) (by simpa using hr) (by simpa using hc) rfl
  have hV := previousValueFormula_freeClosed hD.weaken H.weaken (.bound 0) r.weaken x.weaken
    (by simpa using hH) rfl (by simpa using hr) (by simpa using hx)
  simp [contributesFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,
    hP,hV,hc,hx,hD.naturals.zero]

theorem contributesFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (H c r x : Project.Term n) :
    Project.Formula.satisfies e (contributesFormula D H c r x) ↔
      Contributes M (D.eval e) (H.eval e) (c.eval e) (r.eval e) (x.eval e) := by
  simp only [contributesFormula,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,parentAtFormula_iff he,previousValueFormula_iff he,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_neg_iff,GridData.eval_weaken,Term.eval_weaken]
  rfl

theorem contribution_exists {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : GridData M.Domain} (hD : D.Valid M) (H c r : M.Domain) :
    ∃ x, M.mem x D.naturals.omega ∧ Contributes M D H c r x := by
  classical
  by_cases hSome : ∃ p, M.mem p c ∧ ParentAt M D r c p
  · obtain ⟨p,hpc,hp⟩ := hSome
    obtain ⟨x,hx,hV⟩ := previous_value_exists he hD H p r
    exact ⟨x,hx,Or.inl ⟨p,hpc,hp,hV⟩⟩
  · exact ⟨D.naturals.zero,hD.naturals.zero_nat,Or.inr ⟨rfl,fun p hpc hp => hSome ⟨p,hpc,hp⟩⟩⟩

theorem Contributes.bounds {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : GridData M.Domain} (hD : D.Valid M) {H c r x : M.Domain} (h : Contributes M D H c r x) :
    M.mem x D.naturals.omega := by
  rcases h with ⟨_,_,_,hV⟩ | ⟨heq,_⟩
  · exact hV.bounds he hD
  · exact heq ▸ hD.naturals.zero_nat

theorem Contributes.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : GridData M.Domain} (hD : D.Valid M) {H A W c r x y : M.Domain} (hH : Graph M H A W)
    (hx : Contributes M D H c r x) (hy : Contributes M D H c r y) : x=y := by
  rcases hx with ⟨p,hpc,hp,hx⟩ | ⟨hx,hNo⟩ <;> rcases hy with ⟨q,hqc,hq,hy⟩ | ⟨hy,hNo'⟩
  · have hpq := hp.unique hD hq
    subst q
    exact hx.unique he hH hy
  · exact False.elim (hNo' p hpc hp)
  · exact False.elim (hNo q hqc hq)
  · exact hx.trans hy.symm

private def dataEnv {M : SetTheory.Structure.{u}} (D : GridData M.Domain) : Env M 13 :=
  let e := ((((oneEnv D.naturals.omega).push D.naturals.zero).push D.naturals.one).push D.naturals.sequences).push D.naturals.expressions
  (((((((e.push D.width).push D.rows).push D.heights).push D.forests).push D.parents).push D.tops).push D.pairs).push D.plus

private def dataTerms (k : Nat) : GridData (Project.Term (13+k)) where
  naturals := ⟨.bound ⟨k+12,by omega⟩,.bound ⟨k+11,by omega⟩,.bound ⟨k+10,by omega⟩,
    .bound ⟨k+9,by omega⟩,.bound ⟨k+8,by omega⟩⟩
  width := .bound ⟨k+7,by omega⟩
  rows := .bound ⟨k+6,by omega⟩
  heights := .bound ⟨k+5,by omega⟩
  forests := .bound ⟨k+4,by omega⟩
  parents := .bound ⟨k+3,by omega⟩
  tops := .bound ⟨k+2,by omega⟩
  pairs := .bound ⟨k+1,by omega⟩
  plus := .bound ⟨k,by omega⟩

private theorem dataTerms_closed (k : Nat) : (dataTerms k).Closed :=
  ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

structure ContributionGraph (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (H c K : M.Domain) : Prop where
  graph : Graph M K D.naturals.omega D.naturals.omega
  rows : ∀ r, M.mem r D.naturals.omega → ∀ x, M.mem x D.naturals.omega →
    (MemPair M K r x ↔ Contributes M D H c r x)

def contributionGraphFormula {n : Nat} (D : GridData (Project.Term n)) (H c K : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula K D.naturals.omega D.naturals.omega)
    (Project.Formula.forallMem D.naturals.omega (Project.Formula.forallMem D.naturals.omega.weaken
      (.iff (memPairFormula K.weaken.weaken (.bound 1) (.bound 0))
        (contributesFormula D.weaken.weaken H.weaken.weaken c.weaken.weaken (.bound 1) (.bound 0)))))

theorem contributionGraphFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (H c K : Project.Term n) :
    (contributionGraphFormula D H c K).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _)
    (contributesFormula_delta0 _ _ _ _ _))))

theorem contributionGraphFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (H c K : Project.Term n) (hH : H.freeSupport=[]) (hc : c.freeSupport=[]) (hK : K.freeSupport=[]) :
    (contributionGraphFormula D H c K).FreeClosed := by
  have hRows := contributesFormula_freeClosed hD.weaken.weaken H.weaken.weaken c.weaken.weaken (.bound 1) (.bound 0)
    (by simpa using hH) (by simpa using hc) rfl rfl
  simp [contributionGraphFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hD.naturals.omega,hK,hRows]

theorem contributionGraphFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (H c K : Project.Term n) :
    Project.Formula.satisfies e (contributionGraphFormula D H c K) ↔
      ContributionGraph M (D.eval e) (H.eval e) (c.eval e) (K.eval e) := by
  simp only [contributionGraphFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he,
    contributesFormula_iff he,GridData.eval_weaken,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.graph,h.rows⟩⟩

private def contributionSchema : Project.Delta0BinarySchema 15 where
  body := contributesFormula (dataTerms 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := contributesFormula_freeClosed (dataTerms_closed 4) _ _ _ _ rfl rfl rfl rfl
  delta0 := contributesFormula_delta0 _ _ _ _ _

private theorem contributionSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (D : GridData M.Domain) (H c r x : M.Domain) :
    Project.Formula.satisfies (((((dataEnv D).push H).push c).push r).push x) contributionSchema.body ↔
      Contributes M D H c r x := by
  rw [contributionSchema,contributesFormula_iff he]
  rfl

theorem contribution_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H A W : M.Domain} (hH : Graph M H A W) (c : M.Domain) :
    ∃ K, ContributionGraph M D H c K := by
  obtain ⟨K,hSupport,hK⟩ := relation_comprehension_d hM contributionSchema (((dataEnv D).push H).push c)
    D.naturals.omega D.naturals.omega
  have hRows : ∀ r x, MemPair M K r x ↔ M.mem r D.naturals.omega ∧ M.mem x D.naturals.omega ∧ Contributes M D H c r x := by
    intro r x
    simpa only [contributionSchema_iff hM.1] using hK r x
  refine ⟨K,⟨hSupport,?_,?_⟩,?_⟩
  · intro r hr
    obtain ⟨x,hx,hContrib⟩ := contribution_exists hM.1 hD H c r
    exact ⟨x,hx,(hRows r x).mpr ⟨hr,hx,hContrib⟩⟩
  · intro r x y hrx hry
    exact ((hRows r x).mp hrx).2.2.unique hM.1 hD hH ((hRows r y).mp hry).2.2
  · intro r hr x hx
    exact (hRows r x).trans ⟨fun h => h.2.2,fun h => ⟨hr,hx,h⟩⟩

theorem ContributionGraph.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : GridData M.Domain} {H c K J : M.Domain} (hK : ContributionGraph M D H c K)
    (hJ : ContributionGraph M D H c J) : K=J := by
  apply hK.graph.ext he hJ.graph
  intro r hr x
  constructor
  · intro hAt
    have hx := (hK.graph.bounds he hAt).2
    exact (hJ.rows r hr x hx).mpr ((hK.rows r hr x hx).mp hAt)
  · intro hAt
    have hx := (hJ.graph.bounds he hAt).2
    exact (hK.rows r hr x hx).mpr ((hJ.rows r hr x hx).mp hAt)

theorem ContributionGraph.lookup_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : GridData M.Domain} (hD : D.Valid M) {H c K r x : M.Domain} (hK : ContributionGraph M D H c K)
    (hr : M.mem r D.naturals.omega) : MemPair M K r x ↔ Contributes M D H c r x :=
  ⟨fun h => (hK.rows r hr x (hK.graph.bounds he h).2).mp h,
    fun h => (hK.rows r hr x (h.bounds he hD)).mpr h⟩

theorem valid_cell_rows_congr {M : SetTheory.Structure.{u}} {D : GridData M.Domain}
    {H J c p r x : M.Domain} (hRows : RowsAgreeOn M H J c) (hp : M.mem p c) :
    ValidCell M D H p r x ↔ ValidCell M D J p r x :=
  ⟨fun ⟨f,hf,hAt,hF,hx⟩ => ⟨f,hf,(hRows p hp f).mp hAt,hF,hx⟩,
    fun ⟨f,hf,hAt,hF,hx⟩ => ⟨f,hf,(hRows p hp f).mpr hAt,hF,hx⟩⟩

theorem previous_value_rows_congr {M : SetTheory.Structure.{u}} {D : GridData M.Domain}
    {H J c p r x : M.Domain} (hRows : RowsAgreeOn M H J c) (hp : M.mem p c) :
    PreviousValue M D H p r x ↔ PreviousValue M D J p r x := by
  have hCells := fun x => valid_cell_rows_congr (x := x) (D := D) (r := r) hRows hp
  constructor
  · rintro (h | ⟨hx,hNo⟩)
    · exact Or.inl ((hCells x).mp h)
    · exact Or.inr ⟨hx,fun y hy h => hNo y hy ((hCells y).mpr h)⟩
  · rintro (h | ⟨hx,hNo⟩)
    · exact Or.inl ((hCells x).mpr h)
    · exact Or.inr ⟨hx,fun y hy h => hNo y hy ((hCells y).mp h)⟩

theorem contributes_rows_congr {M : SetTheory.Structure.{u}} {D : GridData M.Domain}
    {H J c r x : M.Domain} (hRows : RowsAgreeOn M H J c) : Contributes M D H c r x ↔ Contributes M D J c r x := by
  constructor
  · rintro (⟨p,hp,hParent,hV⟩ | hNo)
    · exact Or.inl ⟨p,hp,hParent,(previous_value_rows_congr hRows hp).mp hV⟩
    · exact Or.inr hNo
  · rintro (⟨p,hp,hParent,hV⟩ | hNo)
    · exact Or.inl ⟨p,hp,hParent,(previous_value_rows_congr hRows hp).mpr hV⟩
    · exact Or.inr hNo

theorem ContributionGraph.transport_rows {M : SetTheory.Structure.{u}} {D : GridData M.Domain}
    {H J c K : M.Domain} (hK : ContributionGraph M D H c K) (hRows : RowsAgreeOn M H J c) : ContributionGraph M D J c K :=
  ⟨hK.graph,fun r hr x hx => (hK.rows r hr x hx).trans (contributes_rows_congr hRows)⟩

def RebuildStep (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (c H f W : M.Domain) : Prop :=
  ∃ V, M.mem V W ∧ Graph M H c V ∧ ∃ K, M.mem K W ∧ ContributionGraph M D H c K ∧
    ∃ h, M.mem h D.rows ∧ ∃ top, M.mem top D.naturals.omega ∧
      MemPair M D.heights c h ∧ MemPair M D.tops c top ∧ FilledColumn M D.naturals D.pairs D.plus K D.rows h top f

def rebuildStepFormula {n : Nat} (D : GridData (Project.Term n)) (c H f W : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem W (.conj (graphFormula H.weaken c.weaken (.bound 0))
    (Project.Formula.existsMem W.weaken (.conj
      (contributionGraphFormula D.weaken.weaken H.weaken.weaken c.weaken.weaken (.bound 0))
      (Project.Formula.existsMem D.rows.weaken.weaken (Project.Formula.existsMem D.naturals.omega.weaken.weaken.weaken
        (.conj (memPairFormula D.heights.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken (.bound 1))
          (.conj (memPairFormula D.tops.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken (.bound 0))
            (filledColumnFormula D.naturals.weaken.weaken.weaken.weaken D.pairs.weaken.weaken.weaken.weaken
              D.plus.weaken.weaken.weaken.weaken (.bound 2) D.rows.weaken.weaken.weaken.weaken
              (.bound 1) (.bound 0) f.weaken.weaken.weaken.weaken))))))))

theorem rebuildStepFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (c H f W : Project.Term n) :
    (rebuildStepFormula D c H f W).IsDelta0 :=
  .existsMem _ (.conj (graphFormula_delta0 _ _ _) (.existsMem _ (.conj (contributionGraphFormula_delta0 _ _ _ _)
    (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (filledColumnFormula_delta0 _ _ _ _ _ _ _ _))))))))

theorem rebuildStepFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (c H f W : Project.Term n) (hc : c.freeSupport=[]) (hH : H.freeSupport=[])
    (hf : f.freeSupport=[]) (hW : W.freeSupport=[]) : (rebuildStepFormula D c H f W).FreeClosed := by
  have hContrib := contributionGraphFormula_freeClosed hD.weaken.weaken H.weaken.weaken c.weaken.weaken (.bound 0)
    (by simpa using hH) (by simpa using hc) rfl
  have hFill := filledColumnFormula_freeClosed hD.naturals.weaken.weaken.weaken.weaken
    D.pairs.weaken.weaken.weaken.weaken D.plus.weaken.weaken.weaken.weaken (.bound 2) D.rows.weaken.weaken.weaken.weaken
    (.bound 1) (.bound 0) f.weaken.weaken.weaken.weaken (by simpa using hD.pairs) (by simpa using hD.plus) rfl
    (by simpa using hD.rows) rfl rfl (by simpa using hf)
  simp [rebuildStepFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hContrib,hFill,hc,hH,hW,hD.rows,hD.naturals.omega,hD.heights,hD.tops]

theorem rebuildStepFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (c H f W : Project.Term n) :
    Project.Formula.satisfies e (rebuildStepFormula D c H f W) ↔ RebuildStep M (D.eval e) (c.eval e) (H.eval e) (f.eval e) (W.eval e) := by
  simp only [rebuildStepFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    graphFormula_iff he,contributionGraphFormula_iff he,memPairFormula_iff he,filledColumnFormula_iff he,
    GridData.eval_weaken,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

def rebuildMatrix : KP1Y.SigmaRecursion.StepMatrix 13 where
  body := rebuildStepFormula (dataTerms 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := rebuildStepFormula_freeClosed (dataTerms_closed 4) _ _ _ _ rfl rfl rfl rfl
  delta0 := rebuildStepFormula_delta0 _ _ _ _ _

theorem rebuildMatrix_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (D : GridData M.Domain) (c H f W : M.Domain) :
    rebuildMatrix.denote (dataEnv D) c H f W ↔ RebuildStep M D c H f W := by
  rw [KP1Y.SigmaRecursion.StepMatrix.denote,rebuildMatrix,rebuildStepFormula_iff he]
  rfl

theorem rebuild_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) :
    KP1Y.SigmaRecursion.Total M D.width (rebuildMatrix.denote (dataEnv D)) := by
  intro c hc H V hH
  obtain ⟨K,hK⟩ := contribution_graph_exists_d hM hD hH c
  obtain ⟨h,hh,hHeight⟩ := hD.heights.total c hc
  obtain ⟨top,ht,hTop⟩ := hD.tops.total c hc
  obtain ⟨f,hF⟩ := filled_column_exists_d hM hD.naturals hK.graph hD.addition hD.rows hh ht
  obtain ⟨W,hW⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V K
  exact ⟨f,W,(rebuildMatrix_iff hM.1 D c H f W).mpr
    ⟨V,(hW V).mpr (Or.inl rfl),hH,K,(hW K).mpr (Or.inr rfl),hK,h,hh,top,ht,hHeight,hTop,hF⟩⟩

theorem rebuild_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) :
    KP1Y.SigmaRecursion.Functional M D.width (rebuildMatrix.denote (dataEnv D)) := by
  intro c _ H f g W W' hf hg
  obtain ⟨_,_,_,K,_,hK,h,_,top,_,hHeight,hTop,hF⟩ := (rebuildMatrix_iff hM.1 D c H f W).mp hf
  obtain ⟨_,_,_,K',_,hK',h',_,top',_,hHeight',hTop',hG⟩ := (rebuildMatrix_iff hM.1 D c H g W').mp hg
  have hKK := hK.unique hM.1 hK'
  have hhh := hD.heights.unique c h h' hHeight hHeight'
  have htt := hD.tops.unique c top top' hTop hTop'
  subst K'
  subst h'
  subst top'
  exact hF.unique_d hM hD.naturals hK.graph hD.addition hG

theorem reconstruction_history_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) :
    ∃ H V Q, KP1Y.SigmaRecursion.ValueHistory M (rebuildMatrix.denote (dataEnv D)) H D.width V Q :=
  KP1Y.SigmaRecursion.value_recursion_d hM rebuildMatrix (dataEnv D)
    ((omega_isOrdinal_d hM hD.naturals.omega).mem hD.width) (rebuild_total_d hM hD) (rebuild_functional_d hM hD)

/-- 对完整网格的三分支方程；父项值通过规范化的实际先前列读取。 -/
structure GridColumn (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (H c f : M.Domain) : Prop where
  graph : Graph M f D.rows D.naturals.omega
  top : ∀ h, M.mem h D.rows → ∀ t, M.mem t D.naturals.omega →
    MemPair M D.heights c h → MemPair M D.tops c t → MemPair M f h t
  absent : ∀ h, M.mem h D.rows → MemPair M D.heights c h → ∀ r, M.mem r D.rows →
    ∀ x, M.mem x D.naturals.omega → MemPair M f r x → M.mem h r → x=D.naturals.zero
  step : ∀ h, M.mem h D.rows → MemPair M D.heights c h → ∀ r, M.mem r h →
    ∀ s, M.mem s D.rows → ∀ u, M.mem u D.naturals.omega → ∀ v, M.mem v D.naturals.omega →
      ∀ b, M.mem b D.naturals.omega → M.SuccessorOf s r → MemPair M f r u → MemPair M f s v →
        Contributes M D H c r b → AddAt M D.pairs D.plus v b u

theorem FilledColumn.to_grid_column {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H c K h top f : M.Domain}
    (hK : ContributionGraph M D H c K) (hHeight : MemPair M D.heights c h) (hTop : MemPair M D.tops c top)
    (hF : FilledColumn M D.naturals D.pairs D.plus K D.rows h top f) : GridColumn M D H c f := by
  refine ⟨hF.graph,?_,?_,?_⟩
  · intro h' _ t _ hHeight' hTop'
    have hhh := hD.heights.unique c h' h hHeight' hHeight
    have htt := hD.tops.unique c t top hTop' hTop
    subst h'
    subst t
    exact hF.top
  · intro h' _ hHeight' r hr x _ hrx hhr
    have hhh := hD.heights.unique c h' h hHeight' hHeight
    subst h'
    exact hF.absent r hr x hrx hhr
  · intro h' _ hHeight' r hr s hs u hu v hv b hb hSucc hru hsv hContrib
    have hhh := hD.heights.unique c h' h hHeight' hHeight
    subst h'
    have hrω := (omega_isOrdinal_d hM hD.naturals.omega).transitive D.rows hD.rows r (hF.graph.bounds hM.1 hru).1
    exact hF.step r hr s hs u hu v hv b hb hSucc hru hsv ((hK.rows r hrω b hb).mpr hContrib)

theorem GridColumn.to_filled_column {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H c K h top f : M.Domain}
    (hK : ContributionGraph M D H c K) (hHeight : MemPair M D.heights c h) (hTop : MemPair M D.tops c top)
    (hF : GridColumn M D H c f) : FilledColumn M D.naturals D.pairs D.plus K D.rows h top f := by
  have hh := (hD.heights.bounds hM.1 hHeight).2
  have ht := (hD.tops.bounds hM.1 hTop).2
  refine ⟨hD.rows,hh,hF.graph,hF.top h hh top ht hHeight hTop,?_,?_⟩
  · intro r hr x hrx hhr
    exact hF.absent h hh hHeight r hr x (hF.graph.bounds hM.1 hrx).2 hrx hhr
  · intro r hr s hs u hu v hv b hb hSucc hru hsv hrb
    exact hF.step h hh hHeight r hr s hs u hu v hv b hb hSucc hru hsv
      ((hK.rows r (hK.graph.bounds hM.1 hrb).1 b hb).mp hrb)

structure Reconstructs (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (H : M.Domain) : Prop where
  graph : Graph M H D.width D.naturals.sequences
  columns : ∀ c, M.mem c D.width → ∀ f, M.mem f D.naturals.sequences → MemPair M H c f → GridColumn M D H c f

theorem reconstruction_history_column_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} {H V Q c f : M.Domain}
    (hHistory : KP1Y.SigmaRecursion.ValueHistory M (rebuildMatrix.denote (dataEnv D)) H D.width V Q)
    (hc : M.mem c D.width) (hAt : MemPair M H c f) :
    ∃ P K h top, Prefix M P H c V ∧ ContributionGraph M D P c K ∧
      MemPair M D.heights c h ∧ MemPair M D.tops c top ∧
        FilledColumn M D.naturals D.pairs D.plus K D.rows h top f := by
  obtain ⟨P,hPV,hQP⟩ := hHistory.prefixes.total c hc
  obtain ⟨hPref,W,_,hStep⟩ := hHistory.obeys c hc P hPV f (hHistory.values.bounds hM.1 hAt).2 hQP hAt
  obtain ⟨_,_,_,K,_,hK,h,_,top,_,hHeight,hTop,hF⟩ := (rebuildMatrix_iff hM.1 D c P f W).mp hStep
  exact ⟨P,K,h,top,hPref,hK,hHeight,hTop,hF⟩

theorem reconstruction_from_history_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H V Q : M.Domain}
    (hHistory : KP1Y.SigmaRecursion.ValueHistory M (rebuildMatrix.denote (dataEnv D)) H D.width V Q) :
    Reconstructs M D H := by
  have hGraph : Graph M H D.width D.naturals.sequences := KP1Y.Assignments.graph_tighten_values hHistory.values (by
    intro c f hAt
    obtain ⟨_,_,_,_,_,_,_,_,hF⟩ := reconstruction_history_column_d hM hHistory (hHistory.values.bounds hM.1 hAt).1 hAt
    exact (hD.naturals.sequences f).mpr ⟨D.rows,hD.rows,hF.graph⟩)
  refine ⟨hGraph,?_⟩
  intro c hc f _ hAt
  obtain ⟨P,K,h,top,hPref,hK,hHeight,hTop,hF⟩ := reconstruction_history_column_d hM hHistory hc hAt
  have hRows : RowsAgreeOn M P H c := fun p hp g => hPref.all_rows hM.1 hHistory.values p hp g
  exact hF.to_grid_column hM hD (hK.transport_rows hRows) hHeight hTop

theorem reconstruction_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) : ∃ H, Reconstructs M D H := by
  obtain ⟨H,V,Q,hHistory⟩ := reconstruction_history_exists_d hM hD
  exact ⟨H,reconstruction_from_history_d hM hD hHistory⟩

theorem Reconstructs.column {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : GridData M.Domain} {H c f : M.Domain} (hH : Reconstructs M D H) (hAt : MemPair M H c f) : GridColumn M D H c f :=
  hH.columns c (hH.graph.bounds he hAt).1 f (hH.graph.bounds he hAt).2 hAt

theorem Reconstructs.valid_cell_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : GridData M.Domain} {H c f r x : M.Domain} (hH : Reconstructs M D H) (hAt : MemPair M H c f) :
    ValidCell M D H c r x ↔ MemPair M f r x := by
  constructor
  · rintro ⟨g,_,hCg,_,hrx⟩
    have hfg := hH.graph.unique c g f hCg hAt
    exact hfg ▸ hrx
  · intro hrx
    exact ⟨f,(hH.graph.bounds he hAt).2,hAt,(hH.column he hAt).graph,hrx⟩

theorem Reconstructs.previous_value_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : GridData M.Domain} {H c f r x : M.Domain} (hH : Reconstructs M D H) (hAt : MemPair M H c f) :
    PreviousValue M D H c r x ↔ MemPair M f r x ∨ (¬M.mem r D.rows ∧ x=D.naturals.zero) := by
  have hCells := fun x => hH.valid_cell_iff (r := r) (x := x) he hAt
  have hF := (hH.column he hAt).graph
  constructor
  · rintro (h | ⟨hx,hNo⟩)
    · exact Or.inl ((hCells x).mp h)
    · refine Or.inr ⟨?_,hx⟩
      intro hr
      obtain ⟨y,hy,hry⟩ := hF.total r hr
      exact hNo y hy ((hCells y).mpr hry)
  · rintro (h | ⟨hNot,hx⟩)
    · exact Or.inl ((hCells x).mpr h)
    · exact Or.inr ⟨hx,fun y _ hy => hNot (hF.bounds he ((hCells y).mp hy)).1⟩

private def columnAgreementSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 4)
    (.imp (.conj (memPairFormula (.bound 4) (.bound 2) (.bound 1)) (memPairFormula (.bound 3) (.bound 2) (.bound 0)))
      (Project.Formula.extensionalEq (.bound 1) (.bound 0))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.forallMem _ (.imp (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (.atom _ _ _)))

private theorem columnAgreementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (S H J c : M.Domain) :
    Project.Formula.satisfies ((((oneEnv S).push H).push J).push c) columnAgreementSchema.body ↔
      ∀ f, M.mem f S → ∀ g, M.mem g S → MemPair M H c f → MemPair M J c g → f=g := by
  simp only [columnAgreementSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he]
  exact ⟨fun h f hf g hg hF hG => h f hf g hg ⟨hF,hG⟩,fun h f hf g hg hs => h f hf g hg hs.1 hs.2⟩

theorem reconstruction_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H J : M.Domain} (hH : Reconstructs M D H) (hJ : Reconstructs M D J) : H=J := by
  let env := ((oneEnv D.naturals.sequences).push H).push J
  have hAll := KP1Y.induction_d hM columnAgreementSchema.toUnarySchema env
    (fun c ih => (columnAgreementSchema_iff hM.1 D.naturals.sequences H J c).mpr (by
      intro f hf g hg hCf hCg
      have hc := (hH.graph.bounds hM.1 hCf).1
      have hBefore : RowsAgreeOn M H J c := by
        intro p hp x
        have hpm := ((omega_isOrdinal_d hM hD.naturals.omega).mem hD.width).transitive c hc p hp
        obtain ⟨f',hf',hpf⟩ := hH.graph.total p hpm
        obtain ⟨g',hg',hpg⟩ := hJ.graph.total p hpm
        have hfg := (columnAgreementSchema_iff hM.1 D.naturals.sequences H J p).mp (ih p hp) f' hf' g' hg' hpf hpg
        subst g'
        constructor
        · intro hpx
          exact (hH.graph.unique p x f' hpx hpf).symm ▸ hpg
        · intro hpx
          exact (hJ.graph.unique p x f' hpx hpg).symm ▸ hpf
      obtain ⟨K,hK⟩ := contribution_graph_exists_d hM hD hH.graph c
      obtain ⟨h,_,hHeight⟩ := hD.heights.total c hc
      obtain ⟨top,_,hTop⟩ := hD.tops.total c hc
      have hF := (hH.columns c hc f hf hCf).to_filled_column hM hD hK hHeight hTop
      have hG := (hJ.columns c hc g hg hCg).to_filled_column hM hD (hK.transport_rows hBefore) hHeight hTop
      exact hF.unique_d hM hD.naturals hK.graph hD.addition hG))
  apply hH.graph.ext hM.1 hJ.graph
  intro c hc f
  have hAgree := (columnAgreementSchema_iff hM.1 D.naturals.sequences H J c).mp (hAll c)
  constructor
  · intro hCf
    obtain ⟨g,hg,hCg⟩ := hJ.graph.total c hc
    exact (hAgree f (hH.graph.bounds hM.1 hCf).2 g hg hCf hCg).symm ▸ hCg
  · intro hCf
    obtain ⟨g,hg,hCg⟩ := hH.graph.total c hc
    exact hAgree g hg f (hJ.graph.bounds hM.1 hCf).2 hCg hCf ▸ hCg

theorem Reconstructs.parent_equation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H c f p r s h u v b : M.Domain}
    (hH : Reconstructs M D H) (hCf : MemPair M H c f) (hHeight : MemPair M D.heights c h)
    (hParent : ParentAt M D r c p) (hSucc : M.SuccessorOf s r)
    (hru : MemPair M f r u) (hsv : MemPair M f s v) (hCell : ValidCell M D H p r b) :
    AddAt M D.pairs D.plus v b u := by
  have hBounds := hParent.bounds hM.1 hD
  have hrh := (hD.live r hBounds.1 c hBounds.2.1 h hHeight).mp ⟨p,hParent⟩
  have hCol := hH.column hM.1 hCf
  exact hCol.step h (hD.heights.bounds hM.1 hHeight).2 hHeight r hrh s (hCol.graph.bounds hM.1 hsv).1
    u (hCol.graph.bounds hM.1 hru).2 v (hCol.graph.bounds hM.1 hsv).2 b (hCell.bounds hM.1).2 hSucc hru hsv
      (Or.inl ⟨p,hBounds.2.2.2,hParent,Or.inl hCell⟩)

private def ExtendedColumnValue (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (B f r x : M.Domain) : Prop := MemPair M f r x ∨ (¬M.mem r B ∧ x=C.zero)

private theorem extended_above_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {Pairs Plus K B h top f r x : M.Domain}
    (hF : FilledColumn M C Pairs Plus K B h top f) (hhr : M.mem h r) :
    ExtendedColumnValue M C B f r x ↔ x=C.zero := by
  classical
  constructor
  · rintro (hrx | ⟨_,hx⟩)
    · exact hF.absent r (hF.graph.bounds he hrx).1 x hrx hhr
    · exact hx
  · intro hx
    by_cases hr : M.mem r B
    · obtain ⟨y,_,hry⟩ := hF.graph.total r hr
      have hy := hF.absent r hr y hry hhr
      exact Or.inl ((hx.trans hy.symm).symm ▸ hry)
    · exact Or.inr ⟨hr,hx⟩

private theorem filled_columns_extended_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K L B B' h top f g r x : M.Domain}
    (hK : Graph M K C.omega C.omega) (hPlus : AdditionTable M C Pairs Plus) (hRows : RowsAgreeOn M K L h)
    (hF : FilledColumn M C Pairs Plus K B h top f) (hG : FilledColumn M C Pairs Plus L B' h top g)
    (hr : M.mem r C.omega) : ExtendedColumnValue M C B f r x ↔ ExtendedColumnValue M C B' g r x := by
  obtain ⟨len,f',hF',hPrefF⟩ := hF.lower_d hM hC
  obtain ⟨len',g',hG',hPrefG⟩ := hG.lower_d hM hC
  have hLen := Structure.SuccessorOf.eq hM.1 hF'.length hG'.length
  subst len'
  have hfg := hF'.unique_of_contributions_d hM hC hK hPlus hRows hG'
  subst g'
  have hLow : (r=h ∨ M.mem r h) → (ExtendedColumnValue M C B f r x ↔ ExtendedColumnValue M C B' g r x) := by
    intro hrLe
    have hrLen : M.mem r len := by
      rcases hrLe with he | hrh
      · exact he.symm ▸ hF'.length.predecessor_mem
      · exact (hF'.length r).mpr (Or.inl hrh)
    have hrB : M.mem r B := by
      rcases hrLe with he | hrh
      · exact he ▸ hF.height
      · exact ((omega_isOrdinal_d hM hC.omega).mem hF.rows).transitive h hF.height r hrh
    have hrB' : M.mem r B' := by
      rcases hrLe with he | hrh
      · exact he ▸ hG.height
      · exact ((omega_isOrdinal_d hM hC.omega).mem hG.rows).transitive h hG.height r hrh
    have hValues := (hPrefF.all_rows hM.1 hF.graph r hrLen x).symm.trans (hPrefG.all_rows hM.1 hG.graph r hrLen x)
    constructor
    · rintro (hfx | ⟨hNot,_⟩)
      · exact Or.inl (hValues.mp hfx)
      · exact False.elim (hNot hrB)
    · rintro (hgx | ⟨hNot,_⟩)
      · exact Or.inl (hValues.mpr hgx)
      · exact False.elim (hNot hrB')
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare r hr h hF'.height with he | hrh | hhr
  · exact hLow (Or.inl (hM.1.eq_of_same_members r h he))
  · exact hLow (Or.inr hrh)
  · exact (extended_above_iff hM.1 hF hhr).trans (extended_above_iff hM.1 hG hhr).symm

structure PrefixData (M : SetTheory.Structure.{u}) (D E : GridData M.Domain) (n : M.Domain) : Prop where
  naturals : D.naturals=E.naturals
  length : M.mem n D.naturals.omega
  left_width : M.MemberSubset n D.width
  right_width : M.MemberSubset n E.width
  heights : RowsAgreeOn M D.heights E.heights n
  tops : RowsAgreeOn M D.tops E.tops n
  parents : ∀ c, M.mem c n → ∀ r, M.mem r D.naturals.omega → ∀ p, ParentAt M D r c p ↔ ParentAt M E r c p

private theorem addition_tables_equal {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D E : GridData M.Domain} (hD : D.Valid M) (hE : E.Valid M) (hNat : D.naturals=E.naturals) :
    D.pairs=E.pairs ∧ D.plus=E.plus := by
  have hPairs : D.pairs=E.pairs := by
    apply he.eq_of_same_members
    intro key
    refine (hD.addition.pairs key).trans ?_
    simpa only [hNat] using (hE.addition.pairs key).symm
  have hOther : AdditionTable M D.naturals D.pairs E.plus := by
    simpa only [hNat,hPairs] using hE.addition
  exact ⟨hPairs,hD.addition.unique he hOther⟩

private theorem contributes_of_cell_agreement {M : SetTheory.Structure.{u}}
    {D E : GridData M.Domain} {H J c r x : M.Domain} (hNat : D.naturals=E.naturals)
    (hr : M.mem r D.naturals.omega) (hx : M.mem x D.naturals.omega)
    (hParents : ∀ p, ParentAt M D r c p ↔ ParentAt M E r c p)
    (hBefore : ∀ p, M.mem p c → ∀ s, M.mem s D.naturals.omega → ∀ y, M.mem y D.naturals.omega →
      (PreviousValue M D H p s y ↔ PreviousValue M E J p s y)) :
    Contributes M D H c r x ↔ Contributes M E J c r x := by
  constructor
  · rintro (⟨p,hp,hParent,hValue⟩ | ⟨hZero,hNo⟩)
    · exact Or.inl ⟨p,hp,(hParents p).mp hParent,(hBefore p hp r hr x hx).mp hValue⟩
    · exact Or.inr ⟨hZero.trans (congrArg ExpressionData.zero hNat),fun p hp hP => hNo p hp ((hParents p).mpr hP)⟩
  · rintro (⟨p,hp,hParent,hValue⟩ | ⟨hZero,hNo⟩)
    · exact Or.inl ⟨p,hp,(hParents p).mpr hParent,(hBefore p hp r hr x hx).mpr hValue⟩
    · exact Or.inr ⟨hZero.trans (congrArg ExpressionData.zero hNat).symm,fun p hp hP => hNo p hp ((hParents p).mp hP)⟩

private def appendDataEnv {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n) (D : GridData M.Domain) : Env M (n+13) :=
  let e' := ((((e.push D.naturals.omega).push D.naturals.zero).push D.naturals.one).push D.naturals.sequences).push D.naturals.expressions
  (((((((e'.push D.width).push D.rows).push D.heights).push D.forests).push D.parents).push D.tops).push D.pairs).push D.plus

private def dataTermsAt (n k : Nat) (h : k+13≤n) : GridData (Project.Term n) where
  naturals := ⟨.bound ⟨k+12,by omega⟩,.bound ⟨k+11,by omega⟩,.bound ⟨k+10,by omega⟩,
    .bound ⟨k+9,by omega⟩,.bound ⟨k+8,by omega⟩⟩
  width := .bound ⟨k+7,by omega⟩
  rows := .bound ⟨k+6,by omega⟩
  heights := .bound ⟨k+5,by omega⟩
  forests := .bound ⟨k+4,by omega⟩
  parents := .bound ⟨k+3,by omega⟩
  tops := .bound ⟨k+2,by omega⟩
  pairs := .bound ⟨k+1,by omega⟩
  plus := .bound ⟨k,by omega⟩

private theorem dataTermsAt_closed (n k : Nat) (h : k+13≤n) : (dataTermsAt n k h).Closed :=
  ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private def prefixCellEnv {M : SetTheory.Structure.{u}} (D E : GridData M.Domain) (H J n : M.Domain) : Env M 29 :=
  (((appendDataEnv (dataEnv D) E).push H).push J).push n

private def prefixCellSchema : Project.UnarySchema 29 where
  body := .imp (.mem (.bound 0) (.bound 1))
    (Project.Formula.forallMem (.bound 29) (Project.Formula.forallMem (.bound 30)
      (.iff (previousValueFormula (dataTermsAt 32 19 (by omega)) (.bound 5) (.bound 2) (.bound 1) (.bound 0))
        (previousValueFormula (dataTermsAt 32 6 (by omega)) (.bound 4) (.bound 2) (.bound 1) (.bound 0)))))
  freeClosed := by
    have hLeft := previousValueFormula_freeClosed (dataTermsAt_closed 32 19 (by omega))
      (.bound 5) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl
    have hRight := previousValueFormula_freeClosed (dataTermsAt_closed 32 6 (by omega))
      (.bound 4) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hLeft,hRight]

private theorem prefixCellSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (D E : GridData M.Domain) (H J n c : M.Domain) :
    Project.Formula.satisfies ((prefixCellEnv D E H J n).push c) prefixCellSchema.body ↔
      (M.mem c n → ∀ r, M.mem r D.naturals.omega → ∀ x, M.mem x D.naturals.omega →
        (PreviousValue M D H c r x ↔ PreviousValue M E J c r x)) := by
  simp only [prefixCellSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,previousValueFormula_iff he]
  rfl

/-- 高度、顶部和父图在前缀一致则所有规范取值一致，允许两边的行界不同。 -/
theorem reconstruction_prefix_values_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D E : GridData M.Domain} (hD : D.Valid M) (hE : E.Valid M) {H J n : M.Domain}
    (hPrefix : PrefixData M D E n) (hH : Reconstructs M D H) (hJ : Reconstructs M E J) :
    ∀ c, M.mem c n → ∀ r, M.mem r D.naturals.omega → ∀ x, M.mem x D.naturals.omega →
      (PreviousValue M D H c r x ↔ PreviousValue M E J c r x) := by
  have hAll := KP1Y.induction_d hM prefixCellSchema (prefixCellEnv D E H J n)
    (fun c ih => (prefixCellSchema_iff hM.1 D E H J n c).mpr (by
      intro hc r hr x hx
      have hBefore : ∀ p, M.mem p c → ∀ s, M.mem s D.naturals.omega → ∀ y, M.mem y D.naturals.omega →
          (PreviousValue M D H p s y ↔ PreviousValue M E J p s y) := by
        intro p hp
        have hpn := ((omega_isOrdinal_d hM hD.naturals.omega).mem hPrefix.length).transitive c hc p hp
        exact (prefixCellSchema_iff hM.1 D E H J n p).mp (ih p hp) hpn
      obtain ⟨f,_,hCf⟩ := hH.graph.total c (hPrefix.left_width c hc)
      obtain ⟨g,_,hCg⟩ := hJ.graph.total c (hPrefix.right_width c hc)
      obtain ⟨h,hh,hHeight⟩ := hD.heights.total c (hPrefix.left_width c hc)
      obtain ⟨top,_,hTop⟩ := hD.tops.total c (hPrefix.left_width c hc)
      have hHeight' := (hPrefix.heights c hc h).mp hHeight
      have hTop' := (hPrefix.tops c hc top).mp hTop
      obtain ⟨K,hK⟩ := contribution_graph_exists_d hM hD hH.graph c
      obtain ⟨L,hL⟩ := contribution_graph_exists_d hM hE hJ.graph c
      have hNat := hPrefix.naturals
      obtain ⟨hPairs,hPlus⟩ := addition_tables_equal hM.1 hD hE hNat
      have hF := (hH.column hM.1 hCf).to_filled_column hM hD hK hHeight hTop
      have hG := (hJ.column hM.1 hCg).to_filled_column hM hE hL hHeight' hTop'
      have hG' : FilledColumn M D.naturals D.pairs D.plus L E.rows h top g := by
        simpa only [hNat,hPairs,hPlus] using hG
      have hRows : RowsAgreeOn M K L h := by
        intro s hs y
        have hsω := (omega_isOrdinal_d hM hD.naturals.omega).transitive D.rows hD.rows s
          (((omega_isOrdinal_d hM hD.naturals.omega).mem hD.rows).transitive h hh s hs)
        have hsω' : M.mem s E.naturals.omega := hNat ▸ hsω
        constructor
        · intro hsy
          have hy := (hK.graph.bounds hM.1 hsy).2
          have hy' : M.mem y E.naturals.omega := hNat ▸ hy
          have hContrib := (hK.rows s hsω y hy).mp hsy
          exact (hL.rows s hsω' y hy').mpr
            ((contributes_of_cell_agreement hNat hsω hy (hPrefix.parents c hc s hsω) hBefore).mp hContrib)
        · intro hsy
          have hy' := (hL.graph.bounds hM.1 hsy).2
          have hy : M.mem y D.naturals.omega := hNat.symm ▸ hy'
          have hContrib := (hL.rows s hsω' y hy').mp hsy
          exact (hK.rows s hsω y hy).mpr
            ((contributes_of_cell_agreement hNat hsω hy (hPrefix.parents c hc s hsω) hBefore).mpr hContrib)
      have hValues := filled_columns_extended_iff_d (r := r) (x := x) hM hD.naturals hK.graph hD.addition hRows hF hG' hr
      have hLeft := hH.previous_value_iff (r := r) (x := x) hM.1 hCf
      have hRight := hJ.previous_value_iff (r := r) (x := x) hM.1 hCg
      have hMiddle : (MemPair M f r x ∨ (¬M.mem r D.rows ∧ x=D.naturals.zero)) ↔
          (MemPair M g r x ∨ (¬M.mem r E.rows ∧ x=E.naturals.zero)) := by
        simpa only [ExtendedColumnValue,hNat] using hValues
      exact hLeft.trans (hMiddle.trans hRight.symm)))
  exact fun c => (prefixCellSchema_iff hM.1 D E H J n c).mp (hAll c)

private def gridStepFormula {n : Nat} (D : GridData (Project.Term n)) (H c f h : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem h (Project.Formula.forallMem D.rows.weaken
    (Project.Formula.forallMem D.naturals.omega.weaken.weaken (Project.Formula.forallMem D.naturals.omega.weaken.weaken.weaken
      (Project.Formula.forallMem D.naturals.omega.weaken.weaken.weaken.weaken
        (.imp (successorFormula (.bound 3) (.bound 4))
          (.imp (memPairFormula f.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2))
            (.imp (memPairFormula f.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
              (.imp (contributesFormula D.weaken.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken.weaken
                c.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 0))
                (addAtFormula D.pairs.weaken.weaken.weaken.weaken.weaken D.plus.weaken.weaken.weaken.weaken.weaken
                  (.bound 1) (.bound 0) (.bound 2))))))))))

private theorem gridStepFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (H c f h : Project.Term n) :
    (gridStepFormula D H c f h).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.imp (successorFormula_delta0 _ _)
    (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _)
      (.imp (contributesFormula_delta0 _ _ _ _ _) (addAtFormula_delta0 _ _ _ _ _)))))))))

private theorem gridStepFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (H c f h : Project.Term n) (hH : H.freeSupport=[]) (hc : c.freeSupport=[])
    (hf : f.freeSupport=[]) (hh : h.freeSupport=[]) : (gridStepFormula D H c f h).FreeClosed := by
  have hContrib := contributesFormula_freeClosed hD.weaken.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken.weaken
    c.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 0) (by simpa using hH) (by simpa using hc) rfl rfl
  simp [gridStepFormula,successorFormula,memPairFormula,codeFormula,pairFormula,addAtFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hD.rows,hD.naturals.omega,hD.pairs,hD.plus,hf,hh,hContrib]

private theorem gridStepFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (H c f h : Project.Term n) :
    Project.Formula.satisfies e (gridStepFormula D H c f h) ↔
      ∀ r, M.mem r (h.eval e) → ∀ s, M.mem s (D.eval e).rows → ∀ u, M.mem u (D.eval e).naturals.omega →
        ∀ v, M.mem v (D.eval e).naturals.omega → ∀ b, M.mem b (D.eval e).naturals.omega → M.SuccessorOf s r →
          MemPair M (f.eval e) r u → MemPair M (f.eval e) s v → Contributes M (D.eval e) (H.eval e) (c.eval e) r b →
            AddAt M (D.eval e).pairs (D.eval e).plus v b u := by
  simp only [gridStepFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    successorFormula_iff he,memPairFormula_iff he,contributesFormula_iff he,addAtFormula_iff he,GridData.eval_weaken,Term.eval_weaken]
  rfl

def gridColumnFormula {n : Nat} (D : GridData (Project.Term n)) (H c f : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula f D.rows D.naturals.omega)
    (.conj (Project.Formula.forallMem D.rows (Project.Formula.forallMem D.naturals.omega.weaken
      (.imp (memPairFormula D.heights.weaken.weaken c.weaken.weaken (.bound 1))
        (.imp (memPairFormula D.tops.weaken.weaken c.weaken.weaken (.bound 0)) (memPairFormula f.weaken.weaken (.bound 1) (.bound 0))))))
      (.conj (Project.Formula.forallMem D.rows (.imp (memPairFormula D.heights.weaken c.weaken (.bound 0))
        (Project.Formula.forallMem D.rows.weaken (Project.Formula.forallMem D.naturals.omega.weaken.weaken
          (.imp (memPairFormula f.weaken.weaken.weaken (.bound 1) (.bound 0))
            (.imp (.mem (.bound 2) (.bound 1)) (Project.Formula.extensionalEq (.bound 0) D.naturals.zero.weaken.weaken.weaken)))))))
        (Project.Formula.forallMem D.rows (.imp (memPairFormula D.heights.weaken c.weaken (.bound 0))
          (gridStepFormula D.weaken H.weaken c.weaken f.weaken (.bound 0))))))

theorem gridColumnFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (H c f : Project.Term n) :
    (gridColumnFormula D H c f).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.conj
    (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))
    (.conj (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
      (.imp (memPairFormula_delta0 _ _ _) (.imp (.mem _ _) (.atom _ _ _)))))))
      (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (gridStepFormula_delta0 _ _ _ _ _)))))

theorem gridColumnFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (H c f : Project.Term n) (hH : H.freeSupport=[]) (hc : c.freeSupport=[])
    (hf : f.freeSupport=[]) : (gridColumnFormula D H c f).FreeClosed := by
  have hStep := gridStepFormula_freeClosed hD.weaken H.weaken c.weaken f.weaken (.bound 0)
    (by simpa using hH) (by simpa using hc) (by simpa using hf) rfl
  simp [gridColumnFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hStep,hD.rows,hD.naturals.omega,hD.naturals.zero,hD.heights,hD.tops,hc,hf]

theorem gridColumnFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (H c f : Project.Term n) :
    Project.Formula.satisfies e (gridColumnFormula D H c f) ↔ GridColumn M (D.eval e) (H.eval e) (c.eval e) (f.eval e) := by
  simp only [gridColumnFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    gridStepFormula_iff he,GridData.eval_weaken,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,fun h => ⟨h.graph,h.top,h.absent,h.step⟩⟩

def reconstructsFormula {n : Nat} (D : GridData (Project.Term n)) (H : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula H D.width D.naturals.sequences)
    (Project.Formula.forallMem D.width (Project.Formula.forallMem D.naturals.sequences.weaken
      (.imp (memPairFormula H.weaken.weaken (.bound 1) (.bound 0))
        (gridColumnFormula D.weaken.weaken H.weaken.weaken (.bound 1) (.bound 0)))))

theorem reconstructsFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (H : Project.Term n) :
    (reconstructsFormula D H).IsDelta0 := .conj (graphFormula_delta0 _ _ _)
      (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (gridColumnFormula_delta0 _ _ _ _))))

theorem reconstructsFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (H : Project.Term n) (hH : H.freeSupport=[]) : (reconstructsFormula D H).FreeClosed := by
  have hCol := gridColumnFormula_freeClosed hD.weaken.weaken H.weaken.weaken (.bound 1) (.bound 0) (by simpa using hH) rfl rfl
  simp [reconstructsFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hCol,hD.width,hD.naturals.sequences,hH]

theorem reconstructsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (H : Project.Term n) :
    Project.Formula.satisfies e (reconstructsFormula D H) ↔ Reconstructs M (D.eval e) (H.eval e) := by
  simp only [reconstructsFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,
    gridColumnFormula_iff he,GridData.eval_weaken,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.graph,h.columns⟩⟩

private def cellKeyFormula {n : Nat} (D : GridData (Project.Term n)) (H key x : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem D.width (Project.Formula.existsMem D.rows.weaken
    (.conj (codeFormula key.weaken.weaken (.bound 1) (.bound 0))
      (validCellFormula D.weaken.weaken H.weaken.weaken (.bound 1) (.bound 0) x.weaken.weaken)))

private theorem cellKeyFormula_delta0 {n : Nat} (D : GridData (Project.Term n)) (H key x : Project.Term n) :
    (cellKeyFormula D H key x).IsDelta0 := .existsMem _ (.existsMem _
      (.conj (codeFormula_delta0 _ _ _) (validCellFormula_delta0 _ _ _ _ _)))

private theorem cellKeyFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (H key x : Project.Term n) (hH : H.freeSupport=[]) (hk : key.freeSupport=[]) (hx : x.freeSupport=[]) :
    (cellKeyFormula D H key x).FreeClosed := by
  have hCell := validCellFormula_freeClosed hD.weaken.weaken H.weaken.weaken (.bound 1) (.bound 0) x.weaken.weaken
    (by simpa using hH) rfl rfl (by simpa using hx)
  simp [cellKeyFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hCell,hD.width,hD.rows,hk]

private theorem cellKeyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (D : GridData (Project.Term n)) (H key x : Project.Term n) :
    Project.Formula.satisfies e (cellKeyFormula D H key x) ↔
      ∃ c, M.mem c (D.eval e).width ∧ ∃ r, M.mem r (D.eval e).rows ∧
        Codes M (key.eval e) c r ∧ ValidCell M (D.eval e) (H.eval e) c r (x.eval e) := by
  simp only [cellKeyFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,validCellFormula_iff he,GridData.eval_weaken,Term.eval_weaken]
  rfl

private def cellKeySchema : Project.Delta0BinarySchema 14 where
  body := cellKeyFormula (dataTerms 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := cellKeyFormula_freeClosed (dataTerms_closed 3) _ _ _ rfl rfl rfl
  delta0 := cellKeyFormula_delta0 _ _ _ _

private theorem cellKeySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (D : GridData M.Domain) (H key x : M.Domain) :
    Project.Formula.satisfies ((((dataEnv D).push H).push key).push x) cellKeySchema.body ↔
      ∃ c, M.mem c D.width ∧ ∃ r, M.mem r D.rows ∧ Codes M key c r ∧ ValidCell M D H c r x := by
  rw [cellKeySchema,cellKeyFormula_iff he]
  rfl

structure ValueGraph (M : SetTheory.Structure.{u}) (D : GridData M.Domain) (H Keys Values : M.Domain) : Prop where
  keys : IsProduct M Keys D.width D.rows
  graph : Graph M Values Keys D.naturals.omega
  rows : ∀ c r key, Codes M key c r → ∀ x, MemPair M Values key x ↔ ValidCell M D H c r x

theorem grid_value_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} {H : M.Domain} (hH : Reconstructs M D H) : ∃ Keys Values, ValueGraph M D H Keys Values := by
  obtain ⟨Keys,hKeys⟩ := product_exists hM D.width D.rows
  obtain ⟨Values,hSupport,hV⟩ := relation_comprehension_d hM cellKeySchema ((dataEnv D).push H) Keys D.naturals.omega
  have hRaw : ∀ key x, MemPair M Values key x ↔ M.mem key Keys ∧ M.mem x D.naturals.omega ∧
      ∃ c, M.mem c D.width ∧ ∃ r, M.mem r D.rows ∧ Codes M key c r ∧ ValidCell M D H c r x := by
    intro key x
    simpa only [cellKeySchema_iff hM.1] using hV key x
  have hRows : ∀ c r key, Codes M key c r → ∀ x, MemPair M Values key x ↔ ValidCell M D H c r x := by
    intro c r key hCode x
    constructor
    · intro hAt
      obtain ⟨_,_,c',_,r',_,hCode',hCell⟩ := (hRaw key x).mp hAt
      obtain ⟨hcc,hrr⟩ := codes_injective hM.1 hCode hCode'
      subst c'
      subst r'
      exact hCell
    · intro hCell
      have hBounds := hCell.bounds hM.1
      have hSaved := hCell
      obtain ⟨f,_,hCf,_,_⟩ := hCell
      have hc := (hH.graph.bounds hM.1 hCf).1
      exact (hRaw key x).mpr ⟨(hKeys key).mpr ⟨c,hc,r,hBounds.1,hCode⟩,hBounds.2,c,hc,r,hBounds.1,hCode,hSaved⟩
  refine ⟨Keys,Values,hKeys,⟨hSupport,?_,?_⟩,hRows⟩
  · intro key hk
    obtain ⟨c,hc,r,hr,hCode⟩ := (hKeys key).mp hk
    obtain ⟨f,_,hCf⟩ := hH.graph.total c hc
    obtain ⟨x,hx,hrx⟩ := (hH.column hM.1 hCf).graph.total r hr
    exact ⟨x,hx,(hRows c r key hCode x).mpr ((hH.valid_cell_iff hM.1 hCf).mpr hrx)⟩
  · intro key x y hkx hky
    obtain ⟨_,_,c,_,r,_,hCode,hx⟩ := (hRaw key x).mp hkx
    exact hx.unique hH.graph ((hRows c r key hCode y).mp hky)

theorem reconstruction_with_values_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) :
    ∃ H Keys Values, Reconstructs M D H ∧ ValueGraph M D H Keys Values := by
  obtain ⟨H,hH⟩ := reconstruction_exists_d hM hD
  obtain ⟨Keys,Values,hV⟩ := grid_value_graph_exists_d hM hH
  exact ⟨H,Keys,Values,hH,hV⟩

end KP1Y.OneYFinite.Reconstruction
