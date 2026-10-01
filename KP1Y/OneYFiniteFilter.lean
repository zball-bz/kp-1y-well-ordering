import KP1Y.OneYExpression
import KP1Y.OneYNaturalDifferenceOrder

/-! 对任意集合值的内部有限部分函数作稳定过滤：保留定义域次序与重复值，不填充假值。 -/
namespace KP1Y.OneYFinite.Filter
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u

structure PartialGraph (M : SetTheory.Structure.{u}) (P n A : M.Domain) : Prop where
  support : ∀ e, M.mem e P → ∃ i, M.mem i n ∧ ∃ a, M.mem a A ∧ Codes M e i a
  unique : ∀ i a b, MemPair M P i a → MemPair M P i b → a=b

theorem PartialGraph.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {P n A i a : M.Domain}
    (hP : PartialGraph M P n A) (hia : MemPair M P i a) : M.mem i n ∧ M.mem a A := by
  obtain ⟨e,heP,hCode⟩ := hia
  obtain ⟨i',hi,a',ha,hCode'⟩ := hP.support e heP
  obtain ⟨hii,haa⟩ := codes_injective he hCode hCode'
  subst i'
  subst a'
  exact ⟨hi,ha⟩

def partialGraphFormula {n : Nat} (P size A : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.forallMem P (Project.Formula.existsMem size.weaken
    (Project.Formula.existsMem A.weaken.weaken (codeFormula (.bound 2) (.bound 1) (.bound 0)))))
    (Project.Formula.forallMem size (Project.Formula.forallMem A.weaken (Project.Formula.forallMem A.weaken.weaken
      (.imp (.conj (memPairFormula P.weaken.weaken.weaken (.bound 2) (.bound 1))
        (memPairFormula P.weaken.weaken.weaken (.bound 2) (.bound 0))) (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))

theorem partialGraphFormula_delta0 {n : Nat} (P size A : Project.Term n) : (partialGraphFormula P size A).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (codeFormula_delta0 _ _ _))))
    (.forallMem _ (.forallMem _ (.forallMem _ (.imp (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (.atom _ _ _)))))

theorem partialGraphFormula_freeClosed {n : Nat} (P size A : Project.Term n)
    (hP : P.freeSupport=[]) (hn : size.freeSupport=[]) (hA : A.freeSupport=[]) : (partialGraphFormula P size A).FreeClosed := by
  simp [partialGraphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hP,hn,hA]

theorem partialGraphFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (P size A : Project.Term n) : Project.Formula.satisfies e (partialGraphFormula P size A) ↔
      PartialGraph M (P.eval e) (size.eval e) (A.eval e) := by
  simp only [partialGraphFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_imp_iff,codeFormula_iff he,memPairFormula_iff he,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Term.eval_weaken]
  constructor
  · rintro ⟨hSupport,hUnique⟩
    have hBounds : ∀ i a, MemPair M (P.eval e) i a → M.mem i (size.eval e) ∧ M.mem a (A.eval e) := by
      rintro i a ⟨v,hv,hCode⟩
      obtain ⟨i',hi,a',ha,hCode'⟩ := hSupport v hv
      change Codes M v i' a' at hCode'
      obtain ⟨hii,haa⟩ := codes_injective he hCode hCode'
      subst i'
      subst a'
      exact ⟨hi,ha⟩
    exact ⟨hSupport,fun i a b ha hb => hUnique i (hBounds i a ha).1 a (hBounds i a ha).2 b (hBounds i b hb).2 ⟨ha,hb⟩⟩
  · intro hP
    exact ⟨hP.support,fun i _ a _ b _ hs => hP.unique i a b hs.1 hs.2⟩

theorem PartialGraph.restrict_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P n A : M.Domain} (hP : PartialGraph M P n A) (m : M.Domain) :
    ∃ Q, PartialGraph M Q m A ∧ ∀ i a, MemPair M Q i a ↔ M.mem i m ∧ MemPair M P i a := by
  obtain ⟨Q,hSupport,hQ⟩ := relation_comprehension_d hM KP1Y.Recursion.memberSchema (oneEnv P) m A
  have hRows : ∀ i a, MemPair M Q i a ↔ M.mem i m ∧ MemPair M P i a := by
    intro i a
    rw [hQ i a,KP1Y.Recursion.memberSchema_iff hM.1]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(hP.bounds hM.1 h.2).2,h.2⟩⟩
  exact ⟨Q,⟨hSupport,fun i a b ha hb => hP.unique i a b ((hRows i a).mp ha).2 ((hRows i b).mp hb).2⟩,hRows⟩

structure Filtered (M : SetTheory.Structure.{u}) (w P n A len F I : M.Domain) : Prop where
  length : M.mem len w
  output : Graph M F len A
  indices : Graph M I len n
  increasing : ∀ j, M.mem j len → ∀ k, M.mem k len → M.mem j k →
    ∀ i p, MemPair M I j i → MemPair M I k p → M.mem i p
  coverage : ∀ i, M.mem i n → ((∃ a, M.mem a A ∧ MemPair M P i a) ↔ ∃ j, M.mem j len ∧ MemPair M I j i)
  values : ∀ j, M.mem j len → ∀ i, M.mem i n → MemPair M I j i →
    ∀ a, M.mem a A → (MemPair M F j a ↔ MemPair M P i a)

def filteredFormula {n : Nat} (w P size A len F I : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem len w) (.conj (graphFormula F len A) (.conj (graphFormula I len size)
    (.conj (Project.Formula.forallMem len (Project.Formula.forallMem len.weaken
      (.imp (.mem (.bound 1) (.bound 0)) (Project.Formula.forallMem size.weaken.weaken
        (Project.Formula.forallMem size.weaken.weaken.weaken
          (.imp (memPairFormula I.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
            (.imp (memPairFormula I.weaken.weaken.weaken.weaken (.bound 2) (.bound 0)) (.mem (.bound 1) (.bound 0)))))))))
      (.conj (Project.Formula.forallMem size
        (.iff (Project.Formula.existsMem A.weaken (memPairFormula P.weaken.weaken (.bound 1) (.bound 0)))
          (Project.Formula.existsMem len.weaken (memPairFormula I.weaken.weaken (.bound 0) (.bound 1)))))
        (Project.Formula.forallMem len (Project.Formula.forallMem size.weaken
          (.imp (memPairFormula I.weaken.weaken (.bound 1) (.bound 0))
            (Project.Formula.forallMem A.weaken.weaken (.iff
              (memPairFormula F.weaken.weaken.weaken (.bound 2) (.bound 0))
              (memPairFormula P.weaken.weaken.weaken (.bound 1) (.bound 0)))))))))))

theorem filteredFormula_delta0 {n : Nat} (w P size A len F I : Project.Term n) : (filteredFormula w P size A len F I).IsDelta0 :=
  .conj (.mem _ _) (.conj (graphFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (.forallMem _ (.forallMem _ (.imp (.mem _ _) (.forallMem _ (.forallMem _
      (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _) (.mem _ _))))))))
      (.conj (.forallMem _ (.iff (.existsMem _ (memPairFormula_delta0 _ _ _)) (.existsMem _ (memPairFormula_delta0 _ _ _))))
        (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.forallMem _
          (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))))))))

theorem filteredFormula_freeClosed {n : Nat} (w P size A len F I : Project.Term n)
    (hw : w.freeSupport=[]) (hP : P.freeSupport=[]) (hn : size.freeSupport=[]) (hA : A.freeSupport=[])
    (hl : len.freeSupport=[]) (hF : F.freeSupport=[]) (hI : I.freeSupport=[]) : (filteredFormula w P size A len F I).FreeClosed := by
  simp [filteredFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hP,hn,hA,hl,hF,hI]

theorem filteredFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (w P size A len F I : Project.Term n) :
    Project.Formula.satisfies e (filteredFormula w P size A len F I) ↔
      Filtered M (w.eval e) (P.eval e) (size.eval e) (A.eval e) (len.eval e) (F.eval e) (I.eval e) := by
  simp only [filteredFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    graphFormula_iff he,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    memPairFormula_iff he,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_existsMem_iff,Term.eval_weaken]
  constructor
  · rintro ⟨hLen,hF,hI,hInc,hCov,hVal⟩
    exact ⟨hLen,hF,hI,fun j hj k hk hjk i p hji hkp => hInc j hj k hk hjk
      i (hI.bounds he hji).2 p (hI.bounds he hkp).2 hji hkp,hCov,hVal⟩
  · intro h
    exact ⟨h.length,h.output,h.indices,fun j hj k hk hjk i _ p _ hji hkp => h.increasing j hj k hk hjk i p hji hkp,h.coverage,h.values⟩

theorem Filtered.range_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w P n A len F I a : M.Domain} (hP : PartialGraph M P n A) (h : Filtered M w P n A len F I) :
    (∃ j, M.mem j len ∧ MemPair M F j a) ↔ ∃ i, M.mem i n ∧ MemPair M P i a := by
  constructor
  · rintro ⟨j,hj,hja⟩
    obtain ⟨i,hi,hji⟩ := h.indices.total j hj
    exact ⟨i,hi,(h.values j hj i hi hji a (h.output.bounds he hja).2).mp hja⟩
  · rintro ⟨i,hi,hia⟩
    have ha := (hP.bounds he hia).2
    obtain ⟨j,hj,hji⟩ := (h.coverage i hi).mp ⟨a,ha,hia⟩
    exact ⟨j,hj,(h.values j hj i hi hji a ha).mpr hia⟩

theorem Filtered.skip_last {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w P Q p n A len F I : M.Domain} (hs : M.SuccessorOf n p) (h : Filtered M w Q p A len F I)
    (hRows : ∀ i a, MemPair M Q i a ↔ M.mem i p ∧ MemPair M P i a)
    (hNo : ∀ a, M.mem a A → ¬MemPair M P p a) : Filtered M w P n A len F I := by
  refine ⟨h.length,h.output,h.indices.mono_values (fun i hi => (hs i).mpr (Or.inl hi)),h.increasing,?_,?_⟩
  · intro i hi
    constructor
    · rintro ⟨a,ha,hia⟩
      rcases (hs i).mp hi with hip | hip
      · exact (h.coverage i hip).mp ⟨a,ha,(hRows i a).mpr ⟨hip,hia⟩⟩
      · have heq := he.eq_of_same_members i p hip
        subst i
        exact False.elim (hNo a ha hia)
    · rintro ⟨j,hj,hji⟩
      have hip := (h.indices.bounds he hji).2
      obtain ⟨a,ha,hia⟩ := (h.coverage i hip).mpr ⟨j,hj,hji⟩
      exact ⟨a,ha,((hRows i a).mp hia).2⟩
  · intro j hj i _ hji a ha
    have hip := (h.indices.bounds he hji).2
    exact (h.values j hj i hip hji a ha).trans ((hRows i a).trans ⟨And.right,fun hia => ⟨hip,hia⟩⟩)

theorem Filtered.append_last_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {P Q p n A len F I a : M.Domain}
    (hP : PartialGraph M P n A) (hs : M.SuccessorOf n p) (h : Filtered M C.omega Q p A len F I)
    (hRows : ∀ i v, MemPair M Q i v ↔ M.mem i p ∧ MemPair M P i v)
    (ha : M.mem a A) (hpa : MemPair M P p a) : ∃ next G J, Filtered M C.omega P n A next G J := by
  obtain ⟨next,hNext,hNextNat⟩ := hC.omega.1.2 len h.length
  obtain ⟨G,hG,hGRows⟩ := append_graph_d hM h.output hNext (fun _ h => h) ha
  obtain ⟨J,hJ,hJRows⟩ := append_graph_d hM h.indices hNext
    (fun i hi => (hs i).mpr (Or.inl hi)) hs.predecessor_mem
  have hOldG (j : M.Domain) (hj : M.mem j len) (v : M.Domain) : MemPair M G j v ↔ MemPair M F j v := by
    rw [hGRows j v]
    exact ⟨fun h => h.elim id (fun he => False.elim
      (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) len (he.1 ▸ hj))),Or.inl⟩
  have hJLast : MemPair M J len p := (hJRows len p).mpr (Or.inr ⟨rfl,rfl⟩)
  have hGLast : MemPair M G len a := (hGRows len a).mpr (Or.inr ⟨rfl,rfl⟩)
  refine ⟨next,G,J,hNextNat,hG,hJ,?_,?_,?_⟩
  · intro j _ k _ hjk i q hji hkq
    rcases (hJRows j i).mp hji with hji | hJNew <;>
      rcases (hJRows k q).mp hkq with hkq | hKNew
    · exact h.increasing j (h.indices.bounds hM.1 hji).1 k (h.indices.bounds hM.1 hkq).1 hjk i q hji hkq
    · exact hKNew.2.symm ▸ (h.indices.bounds hM.1 hji).2
    · have hkLen := (h.indices.bounds hM.1 hkq).1
      have hLenK : M.mem len k := hJNew.1 ▸ hjk
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) len
        (((omega_isOrdinal_d hM hC.omega).mem h.length).transitive k hkLen len hLenK))
    · have hSelf := hjk
      rw [hJNew.1,hKNew.1] at hSelf
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) len hSelf)
  · intro i hi
    constructor
    · rintro ⟨v,hv,hiv⟩
      rcases (hs i).mp hi with hip | hip
      · obtain ⟨j,hj,hji⟩ := (h.coverage i hip).mp ⟨v,hv,(hRows i v).mpr ⟨hip,hiv⟩⟩
        exact ⟨j,(hNext j).mpr (Or.inl hj),(hJRows j i).mpr (Or.inl hji)⟩
      · have hipEq := hM.1.eq_of_same_members i p hip
        subst i
        exact ⟨len,hNext.predecessor_mem,hJLast⟩
    · rintro ⟨j,_,hji⟩
      rcases (hJRows j i).mp hji with hji | hNew
      · have hj := (h.indices.bounds hM.1 hji).1
        have hip := (h.indices.bounds hM.1 hji).2
        obtain ⟨v,hv,hiv⟩ := (h.coverage i hip).mpr ⟨j,hj,hji⟩
        exact ⟨v,hv,((hRows i v).mp hiv).2⟩
      · exact ⟨a,ha,hNew.2.symm ▸ hpa⟩
  · intro j _ i _ hji v hv
    rcases (hJRows j i).mp hji with hji | hNew
    · have hj := (h.indices.bounds hM.1 hji).1
      have hip := (h.indices.bounds hM.1 hji).2
      exact (hOldG j hj v).trans ((h.values j hj i hip hji v hv).trans
        ((hRows i v).trans ⟨And.right,fun h => ⟨hip,h⟩⟩))
    · rw [hNew.1,hNew.2]
      constructor
      · intro hgv
        exact (hG.unique len v a hgv hGLast).symm ▸ hpa
      · intro hpv
        exact (hP.unique p v a hpv hpa).symm ▸ hGLast

private def existenceSchema : Project.UnarySchema 4 where
  body := .forallE (.imp (partialGraphFormula (.bound 0) (.bound 1) (.bound 4))
    (Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 4)
      (Project.Formula.existsMem (.bound 4)
        (filteredFormula (.bound 8) (.bound 3) (.bound 4) (.bound 7) (.bound 2) (.bound 1) (.bound 0))))))
  freeClosed := by
    have hPartial := partialGraphFormula_freeClosed (n := 6) (.bound 0) (.bound 1) (.bound 4) rfl rfl rfl
    have hFiltered := filteredFormula_freeClosed (n := 9) (.bound 8) (.bound 3) (.bound 4) (.bound 7) (.bound 2) (.bound 1) (.bound 0)
      rfl rfl rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,Project.Formula.existsMem,hPartial,hFiltered]

private theorem existenceSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (w A Lists IndexLists n : M.Domain) :
    Project.Formula.satisfies (((((oneEnv w).push A).push Lists).push IndexLists).push n) existenceSchema.body ↔
      ∀ P, PartialGraph M P n A → ∃ len, M.mem len w ∧ ∃ F, M.mem F Lists ∧ ∃ I, M.mem I IndexLists ∧
        Filtered M w P n A len F I := by
  simp only [existenceSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    partialGraphFormula_iff he,Project.Formula.satisfies_existsMem_iff,filteredFormula_iff he]
  rfl

/-- 存在性对实际内部源长度n归纳；输出值集合A可以为空或任意非数值集合。 -/
theorem filtered_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {P n A : M.Domain}
    (hn : M.mem n C.omega) (hP : PartialGraph M P n A) :
    ∃ len F I, Filtered M C.omega P n A len F I := by
  obtain ⟨Lists,hLists⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hC.omega A
  let env := (((oneEnv C.omega).push A).push Lists).push C.sequences
  have hAll := natural_induction_d hM existenceSchema env hC.omega
    (fun z hz => (existenceSchema_iff hM.1 C.omega A Lists C.sequences z).mpr (by
      intro P _
      have hF : Graph M C.zero C.zero A := empty_graph hC.zero_empty
      have hI : Graph M C.zero C.zero z := empty_graph hC.zero_empty
      refine ⟨C.zero,hC.zero_nat,C.zero,(hLists C.zero).mpr ⟨C.zero,hC.zero_nat,hF⟩,
        C.zero,(hC.sequences C.zero).mpr ⟨C.zero,hC.zero_nat,empty_graph hC.zero_empty⟩,
        hC.zero_nat,hF,hI,?_,?_,?_⟩
      · intro j hj
        exact False.elim (hC.zero_empty j hj)
      · intro i hi
        exact False.elim (hz i hi)
      · intro j hj
        exact False.elim (hC.zero_empty j hj)))
    (fun p hp ih next hs => (existenceSchema_iff hM.1 C.omega A Lists C.sequences next).mpr (by
      intro P hP
      obtain ⟨Q,hQ,hRows⟩ := hP.restrict_d hM p
      obtain ⟨len,_,F,_,I,_,hOld⟩ := (existenceSchema_iff hM.1 C.omega A Lists C.sequences p).mp ih Q hQ
      classical
      have hNew : ∃ len F I, Filtered M C.omega P next A len F I := by
        by_cases hSome : ∃ a, M.mem a A ∧ MemPair M P p a
        · obtain ⟨a,ha,hpa⟩ := hSome
          exact hOld.append_last_d hM hC hP hs hRows ha hpa
        · exact ⟨len,F,I,hOld.skip_last hM.1 hs hRows (fun a ha hpa => hSome ⟨a,ha,hpa⟩)⟩
      obtain ⟨len,F,I,hF⟩ := hNew
      have hNextNat := natural_successor_mem_d hM hC hp hs
      have hI : Graph M I len C.omega := hF.indices.mono_values
        (fun x hx => (omega_isOrdinal_d hM hC.omega).transitive next hNextNat x hx)
      exact ⟨len,hF.length,F,(hLists F).mpr ⟨len,hF.length,hF.output⟩,
        I,(hC.sequences I).mpr ⟨len,hF.length,hI⟩,hF⟩))
  obtain ⟨len,_,F,_,I,_,hF⟩ := (existenceSchema_iff hM.1 C.omega A Lists C.sequences n).mp (hAll n hn) P hP
  exact ⟨len,F,I,hF⟩

theorem Filtered.peel_undefined {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w P Q p n A len F I : M.Domain} (hs : M.SuccessorOf n p) (h : Filtered M w P n A len F I)
    (hRows : ∀ i a, MemPair M Q i a ↔ M.mem i p ∧ MemPair M P i a)
    (hNo : ∀ a, M.mem a A → ¬MemPair M P p a) : Filtered M w Q p A len F I := by
  have hIndex : Graph M I len p := KP1Y.Assignments.graph_tighten_values h.indices (by
    intro j i hji
    rcases (hs i).mp (h.indices.bounds he hji).2 with hip | hip
    · exact hip
    · have hipEq := he.eq_of_same_members i p hip
      subst i
      obtain ⟨a,ha,hpa⟩ := (h.coverage p hs.predecessor_mem).mpr ⟨j,(h.indices.bounds he hji).1,hji⟩
      exact False.elim (hNo a ha hpa))
  refine ⟨h.length,h.output,hIndex,h.increasing,?_,?_⟩
  · intro i hip
    have hin := (hs i).mpr (Or.inl hip)
    constructor
    · rintro ⟨a,ha,hia⟩
      exact (h.coverage i hin).mp ⟨a,ha,((hRows i a).mp hia).2⟩
    · intro hI
      obtain ⟨a,ha,hia⟩ := (h.coverage i hin).mpr hI
      exact ⟨a,ha,(hRows i a).mpr ⟨hip,hia⟩⟩
  · intro j hj i hip hji a ha
    exact (h.values j hj i ((hs i).mpr (Or.inl hip)) hji a ha).trans
      ((hRows i a).trans ⟨And.right,fun hia => ⟨hip,hia⟩⟩).symm

theorem Filtered.last_index_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {P p n A len F I a : M.Domain}
    (hn : M.mem n C.omega) (hs : M.SuccessorOf n p) (h : Filtered M C.omega P n A len F I)
    (ha : M.mem a A) (hpa : MemPair M P p a) :
    ∃ j, M.mem j C.omega ∧ M.SuccessorOf len j ∧ MemPair M I j p ∧ MemPair M F j a := by
  obtain ⟨j,hj,hjp⟩ := (h.coverage p hs.predecessor_mem).mp ⟨a,ha,hpa⟩
  have hw := omega_isOrdinal_d hM hC.omega
  have hLen := hw.mem h.length
  have hpOrd := (hw.mem hn).mem hs.predecessor_mem
  have hLast : M.SuccessorOf len j := by
    intro k
    constructor
    · intro hk
      rcases hLen.wellOrder.linear.compare k hk j hj with he | hkj | hjk
      · exact Or.inr he
      · exact Or.inl hkj
      · obtain ⟨q,hq,hkq⟩ := h.indices.total k hk
        have hpq := h.increasing j hj k hk hjk p q hjp hkq
        rcases (hs q).mp hq with hqp | hqp
        · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (hpOrd.transitive q hqp p hpq))
        · have hqpEq := hM.1.eq_of_same_members q p hqp
          exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (hqpEq ▸ hpq))
    · rintro (hkj | hkj)
      · exact hLen.transitive j hj k hkj
      · exact hM.1.eq_of_same_members k j hkj ▸ hj
  exact ⟨j,hw.transitive len h.length j hj,hLast,hjp,(h.values j hj p hs.predecessor_mem hjp a ha).mpr hpa⟩

theorem Filtered.peel_defined_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {P Q p n A len F I a : M.Domain}
    (hn : M.mem n C.omega) (hs : M.SuccessorOf n p) (h : Filtered M C.omega P n A len F I)
    (hRows : ∀ i v, MemPair M Q i v ↔ M.mem i p ∧ MemPair M P i v)
    (ha : M.mem a A) (hpa : MemPair M P p a) :
    ∃ j G J, M.SuccessorOf len j ∧ Prefix M G F j A ∧ Prefix M J I j n ∧
      Filtered M C.omega Q p A j G J ∧ MemPair M F j a ∧ MemPair M I j p := by
  obtain ⟨j,hjNat,hLast,hjp,hja⟩ := h.last_index_d hM hC hn hs ha hpa
  have hSub : M.MemberSubset j len := fun k hk => (hLast k).mpr (Or.inl hk)
  obtain ⟨G,hG⟩ := restrict_prefix_d hM h.output hSub
  obtain ⟨J,hJ⟩ := restrict_prefix_d hM h.indices hSub
  have hJp : Graph M J j p := KP1Y.Assignments.graph_tighten_values hJ.graph (by
    intro k i hki
    have hk := (hJ.graph.bounds hM.1 hki).1
    have hkiOld := (hJ.all_rows hM.1 h.indices k hk i).mp hki
    exact h.increasing k (hSub k hk) j hLast.predecessor_mem hk i p hkiOld hjp)
  refine ⟨j,G,J,hLast,hG,hJ,⟨hjNat,hG.graph,hJp,?_,?_,?_⟩,hja,hjp⟩
  · intro k hk l hl hkl i q hki hlq
    exact h.increasing k (hSub k hk) l (hSub l hl) hkl i q
      ((hJ.all_rows hM.1 h.indices k hk i).mp hki) ((hJ.all_rows hM.1 h.indices l hl q).mp hlq)
  · intro i hip
    have hin := (hs i).mpr (Or.inl hip)
    constructor
    · rintro ⟨v,hv,hiv⟩
      obtain ⟨k,hk,hki⟩ := (h.coverage i hin).mp ⟨v,hv,((hRows i v).mp hiv).2⟩
      have hkj : M.mem k j := by
        rcases (hLast k).mp hk with hkj | hkj
        · exact hkj
        · have hkjEq := hM.1.eq_of_same_members k j hkj
          have hji : MemPair M I j i := hkjEq ▸ hki
          have hipEq := h.indices.unique j i p hji hjp
          exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (hipEq ▸ hip))
      exact ⟨k,hkj,(hJ.all_rows hM.1 h.indices k hkj i).mpr hki⟩
    · rintro ⟨k,hk,hki⟩
      have hkiOld := (hJ.all_rows hM.1 h.indices k hk i).mp hki
      obtain ⟨v,hv,hiv⟩ := (h.coverage i hin).mpr ⟨k,hSub k hk,hkiOld⟩
      exact ⟨v,hv,(hRows i v).mpr ⟨hip,hiv⟩⟩
  · intro k hk i hip hki v hv
    have hkiOld := (hJ.all_rows hM.1 h.indices k hk i).mp hki
    exact (hG.all_rows hM.1 h.output k hk v).trans
      ((h.values k (hSub k hk) i ((hs i).mpr (Or.inl hip)) hkiOld v hv).trans
        ((hRows i v).trans ⟨And.right,fun hia => ⟨hip,hia⟩⟩).symm)

private def uniquenessSchema : Project.UnarySchema 2 where
  body := .forallE (.imp (partialGraphFormula (.bound 0) (.bound 1) (.bound 2))
    (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
      (.imp (.conj (filteredFormula (.bound 9) (.bound 6) (.bound 7) (.bound 8) (.bound 5) (.bound 4) (.bound 3))
        (filteredFormula (.bound 9) (.bound 6) (.bound 7) (.bound 8) (.bound 2) (.bound 1) (.bound 0)))
        (.conj (Project.Formula.extensionalEq (.bound 5) (.bound 2))
          (.conj (Project.Formula.extensionalEq (.bound 4) (.bound 1)) (Project.Formula.extensionalEq (.bound 3) (.bound 0))))))))))))
  freeClosed := by
    have hP := partialGraphFormula_freeClosed (n := 4) (.bound 0) (.bound 1) (.bound 2) rfl rfl rfl
    have hF := filteredFormula_freeClosed (n := 10) (.bound 9) (.bound 6) (.bound 7) (.bound 8) (.bound 5) (.bound 4) (.bound 3)
      rfl rfl rfl rfl rfl rfl rfl
    have hG := filteredFormula_freeClosed (n := 10) (.bound 9) (.bound 6) (.bound 7) (.bound 8) (.bound 2) (.bound 1) (.bound 0)
      rfl rfl rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hP,hF,hG]

private theorem uniquenessSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (w A n : M.Domain) :
    Project.Formula.satisfies (((oneEnv w).push A).push n) uniquenessSchema.body ↔
      ∀ P, PartialGraph M P n A → ∀ len F I len' G J,
        Filtered M w P n A len F I → Filtered M w P n A len' G J → len=len' ∧ F=G ∧ I=J := by
  simp only [uniquenessSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    partialGraphFormula_iff he,Project.Formula.satisfies_conj_iff,filteredFormula_iff he,
    Project.Formula.satisfies_extensionalEq_iff_eq he]
  exact ⟨fun h P hP len F I len' G J hF hG => h P hP len F I len' G J ⟨hF,hG⟩,
    fun h P hP len F I len' G J hs => h P hP len F I len' G J hs.1 hs.2⟩

theorem Filtered.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {P n A len F I len' G J : M.Domain}
    (hn : M.mem n C.omega) (hP : PartialGraph M P n A)
    (hF : Filtered M C.omega P n A len F I) (hG : Filtered M C.omega P n A len' G J) : len=len' ∧ F=G ∧ I=J := by
  have hAll := natural_induction_d hM uniquenessSchema ((oneEnv C.omega).push A) hC.omega
    (fun z hz => (uniquenessSchema_iff hM.1 C.omega A z).mpr (by
      intro P _ len F I len' G J hF hG
      have hEmpty : ∀ j, ¬M.mem j len := by
        intro j hj
        obtain ⟨i,hi,_⟩ := hF.indices.total j hj
        exact hz i hi
      have hEmpty' : ∀ j, ¬M.mem j len' := by
        intro j hj
        obtain ⟨i,hi,_⟩ := hG.indices.total j hj
        exact hz i hi
      have hLenEq := hM.1.eq_of_same_members len len' (fun j => iff_of_false (hEmpty j) (hEmpty' j))
      subst len'
      exact ⟨rfl,hF.output.ext hM.1 hG.output (fun j hj => False.elim (hEmpty j hj)),
        hF.indices.ext hM.1 hG.indices (fun j hj => False.elim (hEmpty j hj))⟩))
    (fun p hp ih n hs => (uniquenessSchema_iff hM.1 C.omega A n).mpr (by
      intro P hP len F I len' G J hF hG
      obtain ⟨Q,hQ,hRows⟩ := hP.restrict_d hM p
      classical
      by_cases hSome : ∃ a, M.mem a A ∧ MemPair M P p a
      · obtain ⟨a,ha,hpa⟩ := hSome
        have hn := natural_successor_mem_d hM hC hp hs
        obtain ⟨j,F',I',hLen,hFPref,hIPref,hF',hFa,hIp⟩ := hF.peel_defined_d hM hC hn hs hRows ha hpa
        obtain ⟨j',G',J',hLen',hGPref,hJPref,hG',hGa,hJp⟩ := hG.peel_defined_d hM hC hn hs hRows ha hpa
        obtain ⟨hjj,hFG,hIJ⟩ := (uniquenessSchema_iff hM.1 C.omega A p).mp ih Q hQ j F' I' j' G' J' hF' hG'
        subst j'
        subst G'
        subst J'
        have hLengths := Structure.SuccessorOf.eq hM.1 hLen hLen'
        subst len'
        refine ⟨rfl,?_,?_⟩
        · apply hF.output.ext hM.1 hG.output
          intro k hk v
          rcases (hLen k).mp hk with hkj | hkj
          · exact (hFPref.all_rows hM.1 hF.output k hkj v).symm.trans (hGPref.all_rows hM.1 hG.output k hkj v)
          · have hkjEq := hM.1.eq_of_same_members k j hkj
            rw [hkjEq]
            constructor
            · intro hFv
              exact (hF.output.unique j v a hFv hFa).symm ▸ hGa
            · intro hGv
              exact (hG.output.unique j v a hGv hGa).symm ▸ hFa
        · apply hF.indices.ext hM.1 hG.indices
          intro k hk i
          rcases (hLen k).mp hk with hkj | hkj
          · exact (hIPref.all_rows hM.1 hF.indices k hkj i).symm.trans (hJPref.all_rows hM.1 hG.indices k hkj i)
          · have hkjEq := hM.1.eq_of_same_members k j hkj
            rw [hkjEq]
            constructor
            · intro hFi
              exact (hF.indices.unique j i p hFi hIp).symm ▸ hJp
            · intro hGi
              exact (hG.indices.unique j i p hGi hJp).symm ▸ hIp
      · have hNo : ∀ a, M.mem a A → ¬MemPair M P p a := fun a ha hpa => hSome ⟨a,ha,hpa⟩
        exact (uniquenessSchema_iff hM.1 C.omega A p).mp ih Q hQ len F I len' G J
          (hF.peel_undefined hM.1 hs hRows hNo) (hG.peel_undefined hM.1 hs hRows hNo)))
  exact (uniquenessSchema_iff hM.1 C.omega A n).mp (hAll n hn) P hP len F I len' G J hF hG

theorem filtered_exists_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {P n A : M.Domain}
    (hn : M.mem n C.omega) (hP : PartialGraph M P n A) :
    ∃ len F I, Filtered M C.omega P n A len F I ∧
      ∀ len' G J, Filtered M C.omega P n A len' G J → len'=len ∧ G=F ∧ J=I := by
  obtain ⟨len,F,I,hF⟩ := filtered_exists_d hM hC hn hP
  exact ⟨len,F,I,hF,fun len' G J hG => hG.unique_d hM hC hn hP hF⟩

theorem Filtered.entry_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w P n A len F I i a : M.Domain} (hP : PartialGraph M P n A) (h : Filtered M w P n A len F I) :
    MemPair M P i a ↔ ∃ j, M.mem j len ∧ MemPair M I j i ∧ MemPair M F j a := by
  constructor
  · intro hia
    have hi := (hP.bounds he hia).1
    have ha := (hP.bounds he hia).2
    obtain ⟨j,hj,hji⟩ := (h.coverage i hi).mp ⟨a,ha,hia⟩
    exact ⟨j,hj,hji,(h.values j hj i hi hji a ha).mpr hia⟩
  · rintro ⟨j,hj,hji,hja⟩
    exact (h.values j hj i (h.indices.bounds he hji).2 hji a (h.output.bounds he hja).2).mp hja

theorem Filtered.index_injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {P n A len F I j k i : M.Domain}
    (h : Filtered M C.omega P n A len F I) (hji : MemPair M I j i) (hki : MemPair M I k i) : j=k := by
  have hLen := (omega_isOrdinal_d hM hC.omega).mem h.length
  have hj := (h.indices.bounds hM.1 hji).1
  have hk := (h.indices.bounds hM.1 hki).1
  rcases hLen.wellOrder.linear.compare j hj k hk with he | hjk | hkj
  · exact hM.1.eq_of_same_members j k he
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) i (h.increasing j hj k hk hjk i i hji hki))
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) i (h.increasing k hk j hj hkj i i hki hji))

theorem Filtered.empty_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {P n A len F I : M.Domain}
    (h : Filtered M C.omega P n A len F I) (hNone : ∀ i a, ¬MemPair M P i a) :
    len=C.zero ∧ F=C.zero ∧ I=C.zero := by
  have hEmpty : ∀ j, ¬M.mem j len := by
    intro j hj
    obtain ⟨i,hi,hji⟩ := h.indices.total j hj
    obtain ⟨a,_,hia⟩ := (h.coverage i hi).mpr ⟨j,hj,hji⟩
    exact hNone i a hia
  refine ⟨hM.1.eq_of_same_members len C.zero (fun j => iff_of_false (hEmpty j) (hC.zero_empty j)),?_,?_⟩
  · apply hM.1.eq_of_same_members
    intro e
    refine iff_of_false ?_ (hC.zero_empty e)
    intro he
    obtain ⟨j,hj,_,_,_⟩ := h.output.support e he
    exact hEmpty j hj
  · apply hM.1.eq_of_same_members
    intro e
    refine iff_of_false ?_ (hC.zero_empty e)
    intro he
    obtain ⟨j,hj,_,_,_⟩ := h.indices.support e he
    exact hEmpty j hj

end KP1Y.OneYFinite.Filter
