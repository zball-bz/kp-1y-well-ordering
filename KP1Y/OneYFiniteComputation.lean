import KP1Y.OneYExpression
import KP1Y.BoundedNaturalInduction
import KP1Y.OrdinalArithmeticTerms
import KP1Y.SigmaFunctionGraph
import KP1Y.FunctionIteration

/-! 内部自然数的后继、前驱、有界最大搜索与加法。搜索的空结果用界本身表示，与第 0 列区分。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def NoMatchBelow (M : SetTheory.Structure.{u}) (A b : M.Domain) : Prop :=
  ∀ x, M.mem x b → ¬M.mem x A

def GreatestBelow (M : SetTheory.Structure.{u}) (A b p : M.Domain) : Prop :=
  M.mem p b ∧ M.mem p A ∧ ∀ q, M.mem q b → M.mem q A → q=p ∨ M.mem q p

/-- p=b 恰表示没有候选；找到的最大候选严格位于 b 以下。 -/
def BoundedSearch (M : SetTheory.Structure.{u}) (A b p : M.Domain) : Prop :=
  (p=b ∧ NoMatchBelow M A b) ∨ GreatestBelow M A b p

def noMatchBelowFormula {n : Nat} (A b : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem b (.neg (.mem (.bound 0) A.weaken))

def greatestBelowFormula {n : Nat} (A b p : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem p b) (.conj (.mem p A)
    (Project.Formula.forallMem b (.imp (.mem (.bound 0) A.weaken)
      (.disj (Project.Formula.extensionalEq (.bound 0) p.weaken) (.mem (.bound 0) p.weaken)))))

def boundedSearchFormula {n : Nat} (A b p : Project.Term n) : Project.Formula 1 n :=
  .disj (.conj (Project.Formula.extensionalEq p b) (noMatchBelowFormula A b))
    (greatestBelowFormula A b p)

theorem noMatchBelowFormula_delta0 {n : Nat} (A b : Project.Term n) :
    (noMatchBelowFormula A b).IsDelta0 := .forallMem _ (.neg (.mem _ _))

theorem greatestBelowFormula_delta0 {n : Nat} (A b p : Project.Term n) :
    (greatestBelowFormula A b p).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.forallMem _ (.imp (.mem _ _) (.disj (.atom _ _ _) (.mem _ _)))))

theorem boundedSearchFormula_delta0 {n : Nat} (A b p : Project.Term n) :
    (boundedSearchFormula A b p).IsDelta0 :=
  .disj (.conj (.atom _ _ _) (noMatchBelowFormula_delta0 _ _)) (greatestBelowFormula_delta0 _ _ _)

theorem boundedSearchFormula_freeClosed {n : Nat} (A b p : Project.Term n)
    (hA : A.freeSupport=[]) (hb : b.freeSupport=[]) (hp : p.freeSupport=[]) :
    (boundedSearchFormula A b p).FreeClosed := by
  simp [boundedSearchFormula,noMatchBelowFormula,greatestBelowFormula,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hA,hb,hp]

theorem noMatchBelowFormula_iff {M : SetTheory.Structure.{u}} {n : Nat}
    (e : Env M n) (A b : Project.Term n) :
    Project.Formula.satisfies e (noMatchBelowFormula A b) ↔ NoMatchBelow M (A.eval e) (b.eval e) := by
  simp only [noMatchBelowFormula,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Term.eval_weaken]
  rfl

theorem greatestBelowFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (A b p : Project.Term n) :
    Project.Formula.satisfies e (greatestBelowFormula A b p) ↔
      GreatestBelow M (A.eval e) (b.eval e) (p.eval e) := by
  simp only [greatestBelowFormula,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Term.eval_weaken]
  rfl

theorem boundedSearchFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (A b p : Project.Term n) :
    Project.Formula.satisfies e (boundedSearchFormula A b p) ↔
      BoundedSearch M (A.eval e) (b.eval e) (p.eval e) := by
  simp only [boundedSearchFormula,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,noMatchBelowFormula_iff,greatestBelowFormula_iff he]
  rfl

private def memberSchema : Project.Delta0UnarySchema 1 where
  body := .mem (.bound 0) (.bound 1)
  freeClosed := by simp [Definitional.Formula.FreeClosed]
  delta0 := .mem _ _

private theorem memberSchema_iff {M : SetTheory.Structure.{u}} (A x : M.Domain) :
    Project.Formula.satisfies ((oneEnv A).push x) memberSchema.body ↔ M.mem x A := by
  simp only [memberSchema,Project.Formula.satisfies_mem_iff]
  rfl

theorem greatest_below_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w A b : M.Domain} (hw : M.IsOmega w) (hb : M.mem b w)
    (hSome : ∃ x, M.mem x b ∧ M.mem x A) : ∃ p, GreatestBelow M A b p := by
  obtain ⟨B,hB⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) memberSchema (oneEnv A) b
  have hRows : ∀ x, M.mem x B ↔ M.mem x b ∧ M.mem x A := by
    intro x
    simpa only [memberSchema_iff] using hB x
  obtain ⟨x,hxb,hxA⟩ := hSome
  obtain ⟨p,hp,hMax⟩ := bounded_nat_max_d hM hw hb (fun x hx => ((hRows x).mp hx).1)
    ⟨x,(hRows x).mpr ⟨hxb,hxA⟩⟩
  exact ⟨p,((hRows p).mp hp).1,((hRows p).mp hp).2,
    fun q hqb hqA => hMax q ((hRows q).mpr ⟨hqb,hqA⟩)⟩

theorem greatest_below_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {A b p q : M.Domain} (hb : M.IsOrdinal b)
    (hp : GreatestBelow M A b p) (hq : GreatestBelow M A b q) : p=q := by
  rcases hq.2.2 p hp.1 hp.2.1 with he | hpq
  · exact he
  · rcases hp.2.2 q hq.1 hq.2.1 with he | hqp
    · exact he.symm
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p
        ((hb.mem hp.1).transitive q hqp p hpq))

theorem bounded_search_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w A b : M.Domain} (hw : M.IsOmega w) (hb : M.mem b w) :
    ∃ p, M.mem p w ∧ BoundedSearch M A b p := by
  classical
  by_cases hSome : ∃ x, M.mem x b ∧ M.mem x A
  · obtain ⟨p,hp⟩ := greatest_below_exists_d hM hw hb hSome
    exact ⟨p,(omega_isOrdinal_d hM hw).transitive b hb p hp.1,Or.inr hp⟩
  · exact ⟨b,hb,Or.inl ⟨rfl,fun x hxb hxA => hSome ⟨x,hxb,hxA⟩⟩⟩

theorem bounded_search_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {A b p q : M.Domain} (hb : M.IsOrdinal b)
    (hp : BoundedSearch M A b p) (hq : BoundedSearch M A b q) : p=q := by
  rcases hp with ⟨hp,hnone⟩ | hp <;> rcases hq with ⟨hq,hnone'⟩ | hq
  · exact hp.trans hq.symm
  · exact False.elim (hnone q hq.1 hq.2.1)
  · exact False.elim (hnone' p hp.1 hp.2.1)
  · exact greatest_below_unique_d hM hb hp hq

theorem bounded_search_none_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {A b p : M.Domain} (h : BoundedSearch M A b p) : p=b ↔ NoMatchBelow M A b := by
  rcases h with ⟨he,hn⟩ | hg
  · exact iff_of_true he hn
  · constructor
    · intro he
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hg.1))
    · intro hn
      exact False.elim (hn p hg.1 hg.2.1)

theorem bounded_search_some_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {A b p : M.Domain} (h : BoundedSearch M A b p) : M.mem p b ↔ GreatestBelow M A b p := by
  constructor
  · intro hpb
    rcases h with ⟨he,_⟩ | hg
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hpb))
    · exact hg
  · exact And.left

def boundedSearchSchema : Project.Delta0BinarySchema 1 where
  body := boundedSearchFormula (.bound 2) (.bound 1) (.bound 0)
  freeClosed := boundedSearchFormula_freeClosed _ _ _ rfl rfl rfl
  delta0 := boundedSearchFormula_delta0 _ _ _

theorem boundedSearchSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (A b p : M.Domain) :
    Project.Formula.satisfies (((oneEnv A).push b).push p) boundedSearchSchema.body ↔ BoundedSearch M A b p :=
  boundedSearchFormula_iff he _ _ _ _

theorem bounded_search_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} (hw : M.IsOmega w) (A : M.Domain) :
    ∃ F, Graph M F w w ∧ ∀ b p, MemPair M F b p ↔ M.mem b w ∧ M.mem p w ∧ BoundedSearch M A b p := by
  obtain ⟨F,hSupport,hF⟩ := relation_comprehension_d hM boundedSearchSchema (oneEnv A) w w
  have hRows : ∀ b p, MemPair M F b p ↔ M.mem b w ∧ M.mem p w ∧ BoundedSearch M A b p := by
    intro b p
    simpa only [boundedSearchSchema_iff hM.1] using hF b p
  refine ⟨F,⟨hSupport,?_,?_⟩,hRows⟩
  · intro b hb
    obtain ⟨p,hp,hSearch⟩ := bounded_search_exists_d (A := A) hM hw hb
    exact ⟨p,hp,(hRows b p).mpr ⟨hb,hp,hSearch⟩⟩
  · intro b p q hp hq
    obtain ⟨hb,_,hp'⟩ := (hRows b p).mp hp
    exact bounded_search_unique_d hM ((omega_isOrdinal_d hM hw).mem hb) hp' ((hRows b q).mp hq).2.2

/-- 实际 Δ₀ 候选集合及其所有内部自然数截断上的搜索函数图。 -/
theorem bounded_search_for_formula_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : Project.Delta0UnarySchema n) (e : Env M n) {w : M.Domain} (hw : M.IsOmega w) :
    ∃ A F, (∀ x, M.mem x A ↔ M.mem x w ∧ Project.Formula.satisfies (e.push x) φ.body) ∧
      Graph M F w w ∧ ∀ b p, MemPair M F b p ↔ M.mem b w ∧ M.mem p w ∧ BoundedSearch M A b p := by
  obtain ⟨A,hA⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) φ e w
  obtain ⟨F,hF,hRows⟩ := bounded_search_graph_d hM hw A
  exact ⟨A,F,hA,hF,hRows⟩

def successorSchema : Project.Delta0BinarySchema 0 where
  body := successorFormula (.bound 0) (.bound 1)
  freeClosed := by simp [successorFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := successorFormula_delta0 _ _

theorem successorSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (e : Env M 0) (a b : M.Domain) :
    Project.Formula.satisfies ((e.push a).push b) successorSchema.body ↔ M.SuccessorOf b a := by
  simp only [successorSchema,successorFormula_iff he]
  rfl

theorem successor_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} (hw : M.IsOmega w) :
    ∃ F, Graph M F w w ∧ ∀ a b, MemPair M F a b ↔ M.mem a w ∧ M.mem b w ∧ M.SuccessorOf b a := by
  let e : Env M 0 := ⟨Fin.elim0,fun _ => w⟩
  obtain ⟨F,hSupport,hF⟩ := relation_comprehension_d hM successorSchema e w w
  have hRows : ∀ a b, MemPair M F a b ↔ M.mem a w ∧ M.mem b w ∧ M.SuccessorOf b a := by
    intro a b
    simpa only [successorSchema_iff hM.1] using hF a b
  refine ⟨F,⟨hSupport,?_,?_⟩,hRows⟩
  · intro a ha
    obtain ⟨b,hb,hbw⟩ := hw.1.2 a ha
    exact ⟨b,hbw,(hRows a b).mpr ⟨ha,hbw,hb⟩⟩
  · intro a b c hab hac
    exact Structure.SuccessorOf.eq hM.1 ((hRows a b).mp hab).2.2 ((hRows a c).mp hac).2.2

def predecessorSchema : Project.Delta0BinarySchema 2 where
  body := previousLengthFormula (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := previousLengthFormula_freeClosed _ _ _ _ rfl rfl rfl rfl
  delta0 := previousLengthFormula_delta0 _ _ _ _

theorem predecessorSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (w z a b : M.Domain) :
    Project.Formula.satisfies ((((oneEnv w).push z).push a).push b) predecessorSchema.body ↔ PreviousLength M w z a b :=
  previousLengthFormula_iff he _ _ _ _ _

theorem predecessor_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) :
    ∃ F, Graph M F C.omega C.omega ∧
      ∀ a b, MemPair M F a b ↔ M.mem a C.omega ∧ PreviousLength M C.omega C.zero a b := by
  obtain ⟨F,hSupport,hF⟩ := relation_comprehension_d hM predecessorSchema ((oneEnv C.omega).push C.zero) C.omega C.omega
  have hRows : ∀ a b, MemPair M F a b ↔ M.mem a C.omega ∧ PreviousLength M C.omega C.zero a b := by
    intro a b
    have he : MemPair M F a b ↔ M.mem a C.omega ∧ M.mem b C.omega ∧ PreviousLength M C.omega C.zero a b := by
      simpa only [predecessorSchema_iff hM.1] using hF a b
    exact he.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.1,h.2⟩⟩
  refine ⟨F,⟨hSupport,?_,?_⟩,hRows⟩
  · intro a ha
    obtain ⟨b,hb⟩ := previous_length_exists_d hM hC ha
    exact ⟨b,hb.1,(hRows a b).mpr ⟨ha,hb⟩⟩
  · intro a b c hab hac
    exact previous_length_unique_d hM hC ((hRows a b).mp hab).2 ((hRows a c).mp hac).2

def sumFormula {n : Nat} (a b c : Project.Term n) : Project.Formula 1 n :=
  .existsE (KP1Y.Arithmetic.sumCertificateFormula a.weaken b.weaken c.weaken (.bound 0))

theorem sumFormula_freeClosed {n : Nat} (a b c : Project.Term n)
    (ha : a.freeSupport=[]) (hb : b.freeSupport=[]) (hc : c.freeSupport=[]) : (sumFormula a b c).FreeClosed := by
  unfold sumFormula
  simpa only [Definitional.Formula.FreeClosed] using
    (KP1Y.Arithmetic.sumCertificateFormula_freeClosed (n := n+1) a.weaken b.weaken c.weaken (.bound 0)
      (by simpa using ha) (by simpa using hb) (by simpa using hc) rfl)

theorem sumFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (a b c : Project.Term n) :
    Project.Formula.satisfies e (sumFormula a b c) ↔ KP1Y.Arithmetic.Sum M (a.eval e) (b.eval e) (c.eval e) := by
  simp only [sumFormula,Project.Formula.satisfies_exists_iff,KP1Y.Arithmetic.sumCertificateFormula_iff hM,Term.eval_weaken]
  rfl

private def naturalSumSchema : Project.UnarySchema 2 where
  body := .forallE (.imp (sumFormula (.bound 2) (.bound 1) (.bound 0)) (.mem (.bound 0) (.bound 3)))
  freeClosed := by
    have hs := sumFormula_freeClosed (n := 4) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hs]

private theorem naturalSumSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (w a b : M.Domain) : Project.Formula.satisfies (((oneEnv w).push a).push b) naturalSumSchema.body ↔
      ∀ c, KP1Y.Arithmetic.Sum M a b c → M.mem c w := by
  simp only [naturalSumSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    sumFormula_iff hM,Project.Formula.satisfies_mem_iff]
  rfl

theorem natural_sum_closed_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w a b c : M.Domain} (hw : M.IsOmega w) (ha : M.mem a w) (hb : M.mem b w)
    (hSum : KP1Y.Arithmetic.Sum M a b c) : M.mem c w := by
  have hAll := natural_induction_d hM naturalSumSchema ((oneEnv w).push a) hw
    (fun z hz => (naturalSumSchema_iff hM w a z).mpr (by
      intro c hc
      exact hc.zero_value_d hM hz ▸ ha))
    (fun p hp ih s hs => (naturalSumSchema_iff hM w a s).mpr (by
      intro c hc
      obtain ⟨d,hd⟩ := KP1Y.Arithmetic.sum_exists_d hM a ((omega_isOrdinal_d hM hw).mem hp)
      have hdw := (naturalSumSchema_iff hM w a p).mp ih d hd
      obtain ⟨t,ht,htw⟩ := hw.1.2 d hdw
      have hcd := KP1Y.Arithmetic.sum_successor_d hM hs hd hc
      exact (Structure.SuccessorOf.eq hM.1 hcd ht) ▸ htw))
  exact (naturalSumSchema_iff hM w a b).mp (hAll b hb) c hSum

theorem natural_sum_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w a b : M.Domain} (hw : M.IsOmega w) (ha : M.mem a w) (hb : M.mem b w) :
    ∃ c, M.mem c w ∧ KP1Y.Arithmetic.Sum M a b c := by
  obtain ⟨c,hc⟩ := KP1Y.Arithmetic.sum_exists_d hM a ((omega_isOrdinal_d hM hw).mem hb)
  exact ⟨c,natural_sum_closed_d hM hw ha hb hc,hc⟩

/-- 固定任意内部左参数的自然数加法实际函数图；所有右参数遍历完整内部 ω。 -/
theorem natural_addition_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w a : M.Domain} (hw : M.IsOmega w) (ha : M.mem a w) :
    ∃ F, Graph M F w w ∧ ∀ b c, MemPair M F b c ↔
      M.mem b w ∧ M.mem c w ∧ KP1Y.Arithmetic.Sum M a b c := by
  have hTotal : ∀ b, M.mem b w → ∃ c B,
      Project.Formula.satisfies ((((oneEnv a).push b).push c).push B) KP1Y.Arithmetic.sumMatrix.body := by
    intro b hb
    obtain ⟨c,_,hc⟩ := natural_sum_exists_d hM hw ha hb
    obtain ⟨B,hB⟩ := (KP1Y.Arithmetic.sum_sigmaOne_iff_d hM (oneEnv a) b c).mp hc
    exact ⟨c,B,hB⟩
  obtain ⟨F,hF,hRows⟩ := sigma_function_graph_d hM KP1Y.Arithmetic.sumMatrix (oneEnv a) w w hTotal
    (fun b hb c B hB => natural_sum_closed_d hM hw ha hb
      ((KP1Y.Arithmetic.sum_sigmaOne_iff_d hM (oneEnv a) b c).mpr ⟨B,hB⟩))
    (fun b _ c d B D hB hD => KP1Y.Arithmetic.sum_unique_d hM
      ((KP1Y.Arithmetic.sum_sigmaOne_iff_d hM (oneEnv a) b c).mpr ⟨B,hB⟩)
      ((KP1Y.Arithmetic.sum_sigmaOne_iff_d hM (oneEnv a) b d).mpr ⟨D,hD⟩))
  refine ⟨F,hF,fun b c => ?_⟩
  rw [hRows b c,← KP1Y.Arithmetic.sum_sigmaOne_iff_d hM (oneEnv a) b c]
  rfl

def PredecessorIterator (M : SetTheory.Structure.{u}) (w z a H : M.Domain) : Prop :=
  Graph M H w w ∧ MemPair M H z a ∧
    ∀ i, M.mem i w → ∀ j, M.mem j w → ∀ x, M.mem x w → ∀ y, M.mem y w →
      M.SuccessorOf j i → MemPair M H i x → MemPair M H j y → PreviousLength M w z x y

def predecessorIteratorFormula {n : Nat} (w z a H : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula H w w) (.conj (memPairFormula H z a)
    (Project.Formula.forallMem w (Project.Formula.forallMem w.weaken
      (Project.Formula.forallMem w.weaken.weaken (Project.Formula.forallMem w.weaken.weaken.weaken
        (.imp (successorFormula (.bound 2) (.bound 3))
          (.imp (memPairFormula H.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
            (.imp (memPairFormula H.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
              (previousLengthFormula w.weaken.weaken.weaken.weaken z.weaken.weaken.weaken.weaken (.bound 1) (.bound 0))))))))))

theorem predecessorIteratorFormula_delta0 {n : Nat} (w z a H : Project.Term n) :
    (predecessorIteratorFormula w z a H).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
    (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.imp (successorFormula_delta0 _ _)
      (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _) (previousLengthFormula_delta0 _ _ _ _)))))))))

theorem predecessorIteratorFormula_freeClosed {n : Nat} (w z a H : Project.Term n)
    (hw : w.freeSupport=[]) (hz : z.freeSupport=[]) (ha : a.freeSupport=[])
    (hH : H.freeSupport=[]) : (predecessorIteratorFormula w z a H).FreeClosed := by
  simp [predecessorIteratorFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    successorFormula,previousLengthFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hw,hz,ha,hH]

theorem predecessorIteratorFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (w z a H : Project.Term n) :
    Project.Formula.satisfies e (predecessorIteratorFormula w z a H) ↔
      PredecessorIterator M (w.eval e) (z.eval e) (a.eval e) (H.eval e) := by
  simp only [predecessorIteratorFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,
    memPairFormula_iff he,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    successorFormula_iff he,previousLengthFormula_iff he,Term.eval_weaken]
  rfl

theorem predecessor_iterator_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a : M.Domain} (ha : M.mem a C.omega) :
    ∃ H, PredecessorIterator M C.omega C.zero a H := by
  have hNext (x y : M.Domain) :
      KP1Y.Iteration.nextDenote predecessorSchema ((oneEnv C.omega).push C.zero) x y ↔
        PreviousLength M C.omega C.zero x y := predecessorSchema_iff hM.1 _ _ _ _
  obtain ⟨H,hH⟩ := KP1Y.Iteration.iterator_exists_d hM predecessorSchema ((oneEnv C.omega).push C.zero)
    hC.omega ha
    (fun x hx => by
      obtain ⟨y,hy⟩ := previous_length_exists_d hM hC hx
      exact ⟨y,hy.1,(hNext x y).mpr hy⟩)
    (fun x _ y _ z _ hxy hxz => previous_length_unique_d hM hC ((hNext x y).mp hxy) ((hNext x z).mp hxz))
  exact ⟨H,hH.graph,hH.initial C.zero hC.zero_nat hC.zero_empty,
    fun i _ j _ x _ y _ hs hix hjy => (hNext x y).mp (hH.transition i j x y hs hix hjy)⟩

private def iteratorAgreementSchema : Project.UnarySchema 2 where
  body := .forallE (.forallE (.imp
    (.conj (memPairFormula (.bound 4) (.bound 2) (.bound 1)) (memPairFormula (.bound 3) (.bound 2) (.bound 0)))
    (Project.Formula.extensionalEq (.bound 1) (.bound 0))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
      Definitional.Formula.FreeClosed]

private theorem iteratorAgreementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (H J i : M.Domain) : Project.Formula.satisfies (((oneEnv H).push J).push i) iteratorAgreementSchema.body ↔
      ∀ x y, MemPair M H i x → MemPair M J i y → x=y := by
  simp only [iteratorAgreementSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he]
  exact ⟨fun h x y hx hy => h x y ⟨hx,hy⟩,fun h x y hs => h x y hs.1 hs.2⟩

theorem predecessor_iterator_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a H J : M.Domain}
    (hH : PredecessorIterator M C.omega C.zero a H)
    (hJ : PredecessorIterator M C.omega C.zero a J) : H=J := by
  have hAll := natural_induction_d hM iteratorAgreementSchema ((oneEnv H).push J) hC.omega
    (fun z hz => (iteratorAgreementSchema_iff hM.1 H J z).mpr (by
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      intro x y hx hy
      exact (hH.1.unique C.zero x a hx hH.2.1).trans (hJ.1.unique C.zero y a hy hJ.2.1).symm))
    (fun i hi ih j hs => (iteratorAgreementSchema_iff hM.1 H J j).mpr (by
      obtain ⟨x,hx,hix⟩ := hH.1.total i hi
      obtain ⟨y,hy,hiy⟩ := hJ.1.total i hi
      have hxy := (iteratorAgreementSchema_iff hM.1 H J i).mp ih x y hix hiy
      subst y
      intro p q hjp hjq
      have hj := (hH.1.bounds hM.1 hjp).1
      exact previous_length_unique_d hM hC
        (hH.2.2 i hi j hj x hx p (hH.1.bounds hM.1 hjp).2 hs hix hjp)
        (hJ.2.2 i hi j hj x hy q (hJ.1.bounds hM.1 hjq).2 hs hiy hjq)))
  apply hH.1.ext hM.1 hJ.1
  intro i hi x
  obtain ⟨y,_,hiy⟩ := hJ.1.total i hi
  have hAgree := (iteratorAgreementSchema_iff hM.1 H J i).mp (hAll i hi)
  constructor
  · intro hix
    exact (hAgree x y hix hiy).symm ▸ hiy
  · intro hjx
    obtain ⟨z,_,hiz⟩ := hH.1.total i hi
    exact hAgree z x hiz hjx ▸ hiz

/-- a−b 的定义：从 a 开始在内部 ω 上迭代截断前驱 b 次。 -/
def TruncatedDifference (M : SetTheory.Structure.{u}) (w z a b c : M.Domain) : Prop :=
  M.mem a w ∧ M.mem b w ∧ ∃ H, PredecessorIterator M w z a H ∧ MemPair M H b c

def differenceFormula {n : Nat} (w z a b c : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem a w) (.conj (.mem b w) (.existsE
    (.conj (predecessorIteratorFormula w.weaken z.weaken a.weaken (.bound 0))
      (memPairFormula (.bound 0) b.weaken c.weaken))))

theorem differenceFormula_freeClosed {n : Nat} (w z a b c : Project.Term n)
    (hw : w.freeSupport=[]) (hz : z.freeSupport=[]) (ha : a.freeSupport=[])
    (hb : b.freeSupport=[]) (hc : c.freeSupport=[]) : (differenceFormula w z a b c).FreeClosed := by
  have hI := predecessorIteratorFormula_freeClosed w.weaken z.weaken a.weaken (.bound 0)
    (by simpa using hw) (by simpa using hz) (by simpa using ha) rfl
  simp [differenceFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hw,ha,hb,hc,hI]

theorem differenceFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (w z a b c : Project.Term n) :
    Project.Formula.satisfies e (differenceFormula w z a b c) ↔
      TruncatedDifference M (w.eval e) (z.eval e) (a.eval e) (b.eval e) (c.eval e) := by
  simp only [differenceFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff,predecessorIteratorFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem truncated_difference_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) :
    ∃ c, M.mem c C.omega ∧ TruncatedDifference M C.omega C.zero a b c := by
  obtain ⟨H,hH⟩ := predecessor_iterator_exists_d hM hC ha
  obtain ⟨c,hc,hbc⟩ := hH.1.total b hb
  exact ⟨c,hc,ha,hb,H,hH,hbc⟩

theorem truncated_difference_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c d : M.Domain}
    (hc : TruncatedDifference M C.omega C.zero a b c)
    (hd : TruncatedDifference M C.omega C.zero a b d) : c=d := by
  obtain ⟨_,_,H,hH,hbc⟩ := hc
  obtain ⟨_,_,J,hJ,hbd⟩ := hd
  have hHJ := predecessor_iterator_unique_d hM hC hH hJ
  subst J
  exact hH.1.unique b c d hbc hbd

theorem truncated_difference_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a : M.Domain} (ha : M.mem a C.omega) :
    TruncatedDifference M C.omega C.zero a C.zero a := by
  obtain ⟨H,hH⟩ := predecessor_iterator_exists_d hM hC ha
  exact ⟨ha,hC.zero_nat,H,hH,hH.2.1⟩

theorem truncated_difference_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b b' c d : M.Domain}
    (hs : M.SuccessorOf b' b) (hc : TruncatedDifference M C.omega C.zero a b c)
    (hd : TruncatedDifference M C.omega C.zero a b' d) : PreviousLength M C.omega C.zero c d := by
  obtain ⟨_,hb,H,hH,hbc⟩ := hc
  obtain ⟨_,hb',J,hJ,hb'd⟩ := hd
  have hHJ := predecessor_iterator_unique_d hM hC hH hJ
  subst J
  exact hH.2.2 b hb b' hb' c (hH.1.bounds hM.1 hbc).2 d (hH.1.bounds hM.1 hb'd).2 hs hbc hb'd

theorem truncated_difference_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a : M.Domain} (ha : M.mem a C.omega) :
    ∃ F, Graph M F C.omega C.omega ∧ ∀ b c, MemPair M F b c ↔ TruncatedDifference M C.omega C.zero a b c := by
  obtain ⟨F,hF⟩ := predecessor_iterator_exists_d hM hC ha
  refine ⟨F,hF.1,fun b c => ?_⟩
  constructor
  · intro hbc
    exact ⟨ha,(hF.1.bounds hM.1 hbc).1,F,hF,hbc⟩
  · rintro ⟨_,_,H,hH,hbc⟩
    exact predecessor_iterator_unique_d hM hC hH hF ▸ hbc

end KP1Y.OneYFinite
