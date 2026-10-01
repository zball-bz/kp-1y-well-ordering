import KP1Y.SequenceSpaces
import KP1Y.SmallNaturals

/-! 全部合法 1-Y 表达式的实际集合。长度和值属于模型内部 ω；不加入种子生成条件。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u v

def NatSequence (M : SetTheory.Structure.{u}) (w s m : M.Domain) : Prop :=
  M.mem m w ∧ Graph M s m w

def LegalAt (M : SetTheory.Structure.{u}) (w z o s m : M.Domain) : Prop :=
  NatSequence M w s m ∧
    (∀ i, M.mem i m → ∀ a, M.mem a w → MemPair M s i a → M.mem z a) ∧
    (m=z ∨ MemPair M s z o)

def Legal (M : SetTheory.Structure.{u}) (w z o s : M.Domain) : Prop :=
  ∃ m, M.mem m w ∧ LegalAt M w z o s m

def legalAtFormula {n : Nat} (w z o s m : Project.Term n) : Project.Formula 1 n :=
  .conj (.conj (.mem m w) (graphFormula s m w))
    (.conj (Project.Formula.forallMem m (Project.Formula.forallMem w.weaken
      (.imp (memPairFormula s.weaken.weaken (.bound 1) (.bound 0))
        (.mem z.weaken.weaken (.bound 0)))))
      (.disj (Project.Formula.extensionalEq m z) (memPairFormula s z o)))

def legalFormula {n : Nat} (w z o s : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem w (legalAtFormula w.weaken z.weaken o.weaken s.weaken (.bound 0))

theorem legalAtFormula_delta0 {n : Nat} (w z o s m : Project.Term n) :
    (legalAtFormula w z o s m).IsDelta0 :=
  .conj (.conj (.mem _ _) (graphFormula_delta0 _ _ _))
    (.conj (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.mem _ _))))
      (.disj (.atom _ _ _) (memPairFormula_delta0 _ _ _)))

theorem legalFormula_delta0 {n : Nat} (w z o s : Project.Term n) :
    (legalFormula w z o s).IsDelta0 := .existsMem _ (legalAtFormula_delta0 _ _ _ _ _)

theorem legalAtFormula_freeClosed {n : Nat} (w z o s m : Project.Term n)
    (hw : w.freeSupport=[]) (hz : z.freeSupport=[]) (ho : o.freeSupport=[])
    (hs : s.freeSupport=[]) (hm : m.freeSupport=[]) : (legalAtFormula w z o s m).FreeClosed := by
  simp [legalAtFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hz,ho,hs,hm]

theorem legalFormula_freeClosed {n : Nat} (w z o s : Project.Term n)
    (hw : w.freeSupport=[]) (hz : z.freeSupport=[]) (ho : o.freeSupport=[])
    (hs : s.freeSupport=[]) : (legalFormula w z o s).FreeClosed := by
  have h := legalAtFormula_freeClosed w.weaken z.weaken o.weaken s.weaken (.bound 0)
    (by simpa using hw) (by simpa using hz) (by simpa using ho) (by simpa using hs) rfl
  simp [legalFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,h]

theorem legalAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (w z o s m : Project.Term n) :
    Project.Formula.satisfies e (legalAtFormula w z o s m) ↔
      LegalAt M (w.eval e) (z.eval e) (o.eval e) (s.eval e) (m.eval e) := by
  simp only [legalAtFormula,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    memPairFormula_iff he,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Term.eval_weaken]
  rfl

theorem legalFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (w z o s : Project.Term n) :
    Project.Formula.satisfies e (legalFormula w z o s) ↔
      Legal M (w.eval e) (z.eval e) (o.eval e) (s.eval e) := by
  simp only [legalFormula,Project.Formula.satisfies_existsMem_iff,legalAtFormula_iff he,Term.eval_weaken]
  rfl

structure ExpressionData (α : Type u) where
  omega : α
  zero : α
  one : α
  sequences : α
  expressions : α

def ExpressionData.map {α : Type u} {β : Type v} (C : ExpressionData α) (f : α → β) : ExpressionData β :=
  ⟨f C.omega,f C.zero,f C.one,f C.sequences,f C.expressions⟩

def ExpressionData.eval {M : SetTheory.Structure.{u}} {n : Nat}
    (C : ExpressionData (Project.Term n)) (e : Env M n) : ExpressionData M.Domain := C.map (fun t => t.eval e)

def ExpressionData.weaken {n : Nat} (C : ExpressionData (Project.Term n)) : ExpressionData (Project.Term (n+1)) :=
  C.map (fun t => t.weaken)

theorem ExpressionData.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat}
    (C : ExpressionData (Project.Term n)) (e : Env M n) (a : M.Domain) :
    C.weaken.eval (e.push a)=C.eval e := by
  cases C
  simp [ExpressionData.weaken,ExpressionData.eval,ExpressionData.map,Term.eval_weaken]

structure ExpressionData.Closed {n : Nat} (C : ExpressionData (Project.Term n)) : Prop where
  omega : C.omega.freeSupport=[]
  zero : C.zero.freeSupport=[]
  one : C.one.freeSupport=[]
  sequences : C.sequences.freeSupport=[]
  expressions : C.expressions.freeSupport=[]

theorem ExpressionData.Closed.weaken {n : Nat} {C : ExpressionData (Project.Term n)} (h : C.Closed) :
    C.weaken.Closed := by
  rcases h with ⟨hw,hz,ho,hs,he⟩
  constructor <;> simp_all [ExpressionData.weaken,ExpressionData.map]

structure ExpressionData.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) : Prop where
  omega : M.IsOmega C.omega
  zero_empty : ∀ x, ¬M.mem x C.zero
  zero_nat : M.mem C.zero C.omega
  one_succ : M.SuccessorOf C.one C.zero
  one_nat : M.mem C.one C.omega
  sequences : ∀ s, M.mem s C.sequences ↔ ∃ m, M.mem m C.omega ∧ Graph M s m C.omega
  expressions : ∀ s, M.mem s C.expressions ↔ Legal M C.omega C.zero C.one s

private def legalSchema : Project.Delta0UnarySchema 3 where
  body := legalFormula (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := legalFormula_freeClosed _ _ _ _ rfl rfl rfl rfl
  delta0 := legalFormula_delta0 _ _ _ _

theorem expression_data_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} (hw : M.IsOmega w) : ∃ C : ExpressionData M.Domain, C.omega=w ∧ C.Valid M := by
  obtain ⟨z,hz,hzw⟩ := hw.1.1
  obtain ⟨o,ho,how⟩ := hw.1.2 z hzw
  obtain ⟨S,hS⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hw w
  obtain ⟨E,hE⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM)
    legalSchema (((oneEnv w).push z).push o) S
  refine ⟨⟨w,z,o,S,E⟩,rfl,hw,hz,hzw,ho,how,hS,?_⟩
  intro s
  have hs : Project.Formula.satisfies ((((oneEnv w).push z).push o).push s) legalSchema.body ↔ Legal M w z o s :=
    legalFormula_iff hM.1 _ _ _ _ _
  rw [hE s,hs]
  exact ⟨And.right,fun ⟨m,hm,hL⟩ => ⟨(hS s).mpr ⟨m,hm,hL.1.2⟩,m,hm,hL⟩⟩

theorem graph_domain_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {s m n V W : M.Domain} (hm : Graph M s m V) (hn : Graph M s n W) : m=n := by
  apply he.eq_of_same_members
  intro x
  constructor
  · intro hx
    obtain ⟨a,_,ha⟩ := hm.total x hx
    exact (hn.bounds he ha).1
  · intro hx
    obtain ⟨a,_,ha⟩ := hn.total x hx
    exact (hm.bounds he ha).1

theorem legal_length_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w z o s m n : M.Domain} (hm : LegalAt M w z o s m) (hn : LegalAt M w z o s n) : m=n :=
  graph_domain_unique he hm.1.2 hn.1.2

theorem legal_values_positive {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w z o s m i a : M.Domain} (h : LegalAt M w z o s m) (hi : MemPair M s i a) : M.mem z a :=
  h.2.1 i (h.1.2.bounds he hi).1 a (h.1.2.bounds he hi).2 hi

theorem ExpressionData.Valid.zero_mem_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a : M.Domain} (ha : M.mem a C.omega) :
    M.mem C.zero a ↔ a≠C.zero := by
  constructor
  · intro h he
    exact hC.zero_empty C.zero (he ▸ h)
  · intro hne
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare C.zero hC.zero_nat a ha with hs | hlt | hgt
    · exact False.elim (hne (hM.1.eq_of_same_members C.zero a hs).symm)
    · exact hlt
    · exact False.elim (hC.zero_empty a hgt)

theorem empty_legal_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} (hC : C.Valid M) :
    LegalAt M C.omega C.zero C.one C.zero C.zero :=
  ⟨⟨hC.zero_nat,empty_graph hC.zero_empty⟩,fun i hi => False.elim (hC.zero_empty i hi),Or.inl rfl⟩

theorem empty_expression_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} (hC : C.Valid M) :
    M.mem C.zero C.expressions := (hC.expressions C.zero).mpr ⟨C.zero,hC.zero_nat,empty_legal_d hC⟩

theorem expression_is_sequence {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} (hC : C.Valid M)
    {s : M.Domain} (hs : M.mem s C.expressions) : M.mem s C.sequences := by
  obtain ⟨m,hm,hL⟩ := (hC.expressions s).mp hs
  exact (hC.sequences s).mpr ⟨m,hm,hL.1.2⟩

theorem prefix_legal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s m t n : M.Domain}
    (hL : LegalAt M C.omega C.zero C.one s m) (hn : M.mem n C.omega)
    (hSub : M.MemberSubset n m) (hP : Prefix M t s n C.omega) :
    LegalAt M C.omega C.zero C.one t n := by
  refine ⟨⟨hn,hP.graph⟩,?_,?_⟩
  · intro i hi a ha hia
    exact hL.2.1 i (hSub i hi) a ha ((hP.rows i hi a ha).mp hia)
  · by_cases hz : n=C.zero
    · exact Or.inl hz
    · have hzn := (hC.zero_mem_iff hM hn).mpr hz
      have hzm := hSub C.zero hzn
      have hHead : MemPair M s C.zero C.one := by
        rcases hL.2.2 with he | hh
        · exact False.elim (hC.zero_empty C.zero (he ▸ hzm))
        · exact hh
      exact Or.inr ((hP.rows C.zero hzn C.one hC.one_nat).mpr hHead)

theorem legal_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s m n : M.Domain}
    (hL : LegalAt M C.omega C.zero C.one s m) (hn : M.mem n C.omega)
    (hSub : M.MemberSubset n m) :
    ∃ t, Prefix M t s n C.omega ∧ LegalAt M C.omega C.zero C.one t n ∧
      ∀ u, Prefix M u s n C.omega → u=t := by
  obtain ⟨t,hT⟩ := restrict_prefix_d hM hL.1.2 hSub
  refine ⟨t,hT,prefix_legal_d hM hC hL hn hSub hT,?_⟩
  intro u hU
  exact hU.graph.ext hM.1 hT.graph (fun i hi a =>
    (hU.all_rows hM.1 hL.1.2 i hi a).trans (hT.all_rows hM.1 hL.1.2 i hi a).symm)

def PreviousLength (M : SetTheory.Structure.{u}) (w z m p : M.Domain) : Prop :=
  M.mem p w ∧ ((m=z ∧ p=z) ∨ M.SuccessorOf m p)

def previousLengthFormula {n : Nat} (w z m p : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem p w) (.disj
    (.conj (Project.Formula.extensionalEq m z) (Project.Formula.extensionalEq p z))
    (KP1Y.Bounded.successorFormula m p))

theorem previousLengthFormula_delta0 {n : Nat} (w z m p : Project.Term n) :
    (previousLengthFormula w z m p).IsDelta0 :=
  .conj (.mem _ _) (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (KP1Y.Bounded.successorFormula_delta0 _ _))

theorem previousLengthFormula_freeClosed {n : Nat} (w z m p : Project.Term n)
    (hw : w.freeSupport=[]) (hz : z.freeSupport=[]) (hm : m.freeSupport=[])
    (hp : p.freeSupport=[]) : (previousLengthFormula w z m p).FreeClosed := by
  simp [previousLengthFormula,KP1Y.Bounded.successorFormula,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hw,hz,hm,hp]

theorem previousLengthFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (w z m p : Project.Term n) :
    Project.Formula.satisfies e (previousLengthFormula w z m p) ↔
      PreviousLength M (w.eval e) (z.eval e) (m.eval e) (p.eval e) := by
  simp only [previousLengthFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    KP1Y.Bounded.successorFormula_iff he]
  rfl

theorem previous_length_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} (hm : M.mem m C.omega) :
    ∃ p, PreviousLength M C.omega C.zero m p := by
  rcases natural_cases hM hC.omega hm with he | ⟨p,hp,hs⟩
  · have hz := hM.1.eq_of_same_members m C.zero (fun x => iff_of_false (he x) (hC.zero_empty x))
    exact ⟨C.zero,hC.zero_nat,Or.inl ⟨hz,rfl⟩⟩
  · exact ⟨p,hp,Or.inr hs⟩

theorem previous_length_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m p q : M.Domain}
    (hp : PreviousLength M C.omega C.zero m p) (hq : PreviousLength M C.omega C.zero m q) : p=q := by
  rcases hp.2 with ⟨hm,hp⟩ | hp' <;> rcases hq.2 with ⟨hm',hq⟩ | hq'
  · exact hp.trans hq.symm
  · exact False.elim (hC.zero_empty q (hm ▸ hq'.predecessor_mem))
  · exact False.elim (hC.zero_empty p (hm' ▸ hp'.predecessor_mem))
  · exact Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hp.1) hp' hq'

def DropLast (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (s m t : M.Domain) : Prop :=
  ∃ p, PreviousLength M C.omega C.zero m p ∧ Prefix M t s p C.omega

def dropLastFormula {n : Nat} (C : ExpressionData (Project.Term n)) (s m t : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega
    (.conj (previousLengthFormula C.omega.weaken C.zero.weaken m.weaken (.bound 0))
      (prefixFormula t.weaken s.weaken (.bound 0) C.omega.weaken))

theorem dropLastFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (s m t : Project.Term n) :
    (dropLastFormula C s m t).IsDelta0 :=
  .existsMem _ (.conj (previousLengthFormula_delta0 _ _ _ _) (prefixFormula_delta0 _ _ _ _))

theorem dropLastFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (s m t : Project.Term n) (hs : s.freeSupport=[]) (hm : m.freeSupport=[])
    (ht : t.freeSupport=[]) : (dropLastFormula C s m t).FreeClosed := by
  simp [dropLastFormula,previousLengthFormula,prefixFormula,graphFormula,memPairFormula,codeFormula,
    pairFormula,KP1Y.Bounded.successorFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.omega,hC.zero,hs,hm,ht]

theorem dropLastFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (s m t : Project.Term n) :
    Project.Formula.satisfies e (dropLastFormula C s m t) ↔
      DropLast M (C.eval e) (s.eval e) (m.eval e) (t.eval e) := by
  simp only [dropLastFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    previousLengthFormula_iff he,prefixFormula_iff he,Term.eval_weaken]
  exact ⟨fun ⟨p,_,hp,hP⟩ => ⟨p,hp,hP⟩,fun ⟨p,hp,hP⟩ => ⟨p,hp.1,hp,hP⟩⟩

theorem legal_drop_last_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s m : M.Domain}
    (hL : LegalAt M C.omega C.zero C.one s m) :
    ∃ t, DropLast M C s m t ∧ M.mem t C.expressions ∧ ∀ u, DropLast M C s m u → u=t := by
  obtain ⟨p,hp⟩ := previous_length_exists_d hM hC hL.1.1
  have hSub : M.MemberSubset p m := by
    intro x hx
    rcases hp.2 with ⟨_,hpz⟩ | hs
    · exact False.elim (hC.zero_empty x (hpz ▸ hx))
    · exact (hs x).mpr (Or.inl hx)
  obtain ⟨t,hT,hLegal,hUnique⟩ := legal_prefix_d hM hC hL hp.1 hSub
  refine ⟨t,⟨p,hp,hT⟩,(hC.expressions t).mpr ⟨p,hp.1,hLegal⟩,?_⟩
  rintro u ⟨q,hq,hU⟩
  have hqp := previous_length_unique_d hM hC hq hp
  subst q
  exact hUnique u hU

theorem pair_expression_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a : M.Domain}
    (ha : M.mem a C.omega) (hPositive : M.mem C.zero a) :
    ∃ two s, M.SuccessorOf two C.one ∧ LegalAt M C.omega C.zero C.one s two ∧
      (∀ i v, MemPair M s i v ↔ (i=C.zero ∧ v=C.one) ∨ (i=C.one ∧ v=a)) ∧
      ∀ t, Graph M t two C.omega →
        (∀ i v, MemPair M t i v ↔ (i=C.zero ∧ v=C.one) ∨ (i=C.one ∧ v=a)) → t=s := by
  obtain ⟨two,hTwo,hTwoNat⟩ := hC.omega.1.2 C.one hC.one_nat
  obtain ⟨first,hFirst,hFirstRows⟩ := append_graph_d hM (empty_graph (V := C.omega) hC.zero_empty)
    hC.one_succ (fun _ h => h) hC.one_nat
  obtain ⟨s,hS,hSRows⟩ := append_graph_d hM hFirst hTwo (fun _ h => h) ha
  have hRows : ∀ i v, MemPair M s i v ↔ (i=C.zero ∧ v=C.one) ∨ (i=C.one ∧ v=a) := by
    intro i v
    rw [hSRows i v,hFirstRows i v]
    have hNone : ¬MemPair M C.zero i v := by
      rintro ⟨p,hp,_⟩
      exact hC.zero_empty p hp
    simp only [hNone,false_or]
  refine ⟨two,s,hTwo,⟨⟨hTwoNat,hS⟩,?_,Or.inr ((hRows C.zero C.one).mpr (Or.inl ⟨rfl,rfl⟩))⟩,hRows,?_⟩
  · intro i _ v _ hiv
    rcases (hRows i v).mp hiv with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact hC.one_succ.predecessor_mem
    · exact hPositive
  · intro t hT hTRows
    exact hT.ext hM.1 hS (fun i _ v => (hTRows i v).trans (hRows i v).symm)

theorem seed_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {h : M.Domain} (hh : M.mem h C.omega) :
    ∃ a two s, M.SuccessorOf a h ∧ M.mem a C.omega ∧ M.SuccessorOf two C.one ∧
      LegalAt M C.omega C.zero C.one s two ∧
      (∀ i v, MemPair M s i v ↔ (i=C.zero ∧ v=C.one) ∨ (i=C.one ∧ v=a)) ∧
      M.mem s C.expressions := by
  obtain ⟨a,ha,haw⟩ := hC.omega.1.2 h hh
  have hPos : M.mem C.zero a := by
    apply (hC.zero_mem_iff hM haw).mpr
    intro he
    exact hC.zero_empty h (he ▸ ha.predecessor_mem)
  obtain ⟨two,s,hTwo,hL,hRows,_⟩ := pair_expression_exists_d hM hC haw hPos
  exact ⟨a,two,s,ha,haw,hTwo,hL,hRows,(hC.expressions s).mpr ⟨two,hL.1.1,hL⟩⟩

end KP1Y.OneYFinite
