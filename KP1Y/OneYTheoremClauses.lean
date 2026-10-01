import KP1Y.OneYWellOrdering

/-! 定理 1 结论各子句的纯 ∈ 公式及其语义。参数只有 ω、0、1、有限序列空间、E（`ExpressionData`）、
Keys 与 EN；ν、χ、μ、X、H、Desc(s)、G 等均在公式内量化。字典序、有限步可达与种子都由显式公式定义。 -/
namespace KP1Y.OneYTheorem
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Cardinal
open KP1Y.OneYFinite KP1Y.OneYRank
universe u

/-! ### 秩子句：∃ 序数 χ≤ν ∃ μ:E→χ，μ(∅)=0，非空 s 的每个 E_N(s) 使 μ 严格下降 -/

/-- 语义：共享 `RankWitness`（读取实际 `Expands`）与 χ≤ν。 -/
def RankClause (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) (ν : M.Domain) : Prop :=
  ∃ χ μ, RankWitness M D.expr D.arith χ μ ∧ (χ=ν ∨ M.mem χ ν)

def rankClauseFormula {n : Nat} (C : ExpressionData (Project.Term n)) (Keys EN ν : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (rankWitnessFormula C.weaken.weaken Keys.weaken.weaken EN.weaken.weaken (.bound 1) (.bound 0))
    (.disj (Project.Formula.extensionalEq (.bound 1) ν.weaken.weaken) (.mem (.bound 1) ν.weaken.weaken))))

theorem rankClauseFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Keys EN ν : Project.Term n) (hK : Keys.freeSupport=[]) (hEN : EN.freeSupport=[]) (hν : ν.freeSupport=[]) :
    (rankClauseFormula C Keys EN ν).FreeClosed := by
  have hW := rankWitnessFormula_freeClosed hC.weaken.weaken Keys.weaken.weaken EN.weaken.weaken (.bound 1) (.bound 0)
    (by simpa using hK) (by simpa using hEN) rfl rfl
  simp [rankClauseFormula,Definitional.Formula.FreeClosed,hW,hν]

theorem rankClauseFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Keys EN ν : Project.Term n) {T : MatrixArithmetic M.Domain}
    (hC : (C.eval e).Valid M) (hG : Expansion.Graph M (C.eval e) T (Keys.eval e) (EN.eval e)) :
    Project.Formula.satisfies e (rankClauseFormula C Keys EN ν) ↔
      ∃ χ μ, RankWitness M (C.eval e) T χ μ ∧ (χ=ν.eval e ∨ M.mem χ (ν.eval e)) := by
  simp only [rankClauseFormula,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,
    Project.Formula.satisfies_mem_iff,Term.eval_weaken]
  apply exists_congr
  intro χ
  apply exists_congr
  intro μ
  have hC' : (C.weaken.weaken.eval ((e.push χ).push μ)).Valid M := by
    rw [ExpressionData.eval_weaken,ExpressionData.eval_weaken]
    exact hC
  have hG' : Expansion.Graph M (C.weaken.weaken.eval ((e.push χ).push μ)) T
      (Keys.weaken.weaken.eval ((e.push χ).push μ)) (EN.weaken.weaken.eval ((e.push χ).push μ)) := by
    rw [ExpressionData.eval_weaken,ExpressionData.eval_weaken,Term.eval_weaken,Term.eval_weaken,Term.eval_weaken,
      Term.eval_weaken]
    exact hG
  have h := rankWitnessFormula_iff hM ((e.push χ).push μ) C.weaken.weaken Keys.weaken.weaken EN.weaken.weaken
    (.bound 1) (.bound 0) hC' hG'
  rw [ExpressionData.eval_weaken,ExpressionData.eval_weaken] at h
  exact and_congr h Iff.rfl

/-! ### ≺ 良基 -/

def wellFoundedFormula {n : Nat} (C : ExpressionData (Project.Term n)) (Keys EN : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.conj (Project.Formula.subset (.bound 0) C.expressions.weaken)
      (Project.Formula.existsMem (.bound 0) (Project.Formula.extensionalEq (.bound 0) (.bound 0))))
    (Project.Formula.existsMem (.bound 0) (Project.Formula.forallMem (.bound 1)
      (.neg (precedesFormula C.omega.weaken.weaken.weaken Keys.weaken.weaken.weaken EN.weaken.weaken.weaken
        (.bound 0) (.bound 1))))))

theorem wellFoundedFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Keys EN : Project.Term n) (hK : Keys.freeSupport=[]) (hEN : EN.freeSupport=[]) :
    (wellFoundedFormula C Keys EN).FreeClosed := by
  have hP := precedesFormula_freeClosed C.omega.weaken.weaken.weaken Keys.weaken.weaken.weaken EN.weaken.weaken.weaken
    (.bound 0) (.bound 1) (by simpa using hC.omega) (by simpa using hK) (by simpa using hEN) rfl rfl
  simp [wellFoundedFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hC.expressions,hP]

theorem wellFoundedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Keys EN : Project.Term n) :
    Project.Formula.satisfies e (wellFoundedFormula C Keys EN) ↔
      ∀ X, M.MemberSubset X (C.eval e).expressions → (∃ x, M.mem x X) →
        ∃ x, M.mem x X ∧ ∀ y, M.mem y X → ¬PrecedesIn M (C.eval e).omega (Keys.eval e) (EN.eval e) y x := by
  simp only [wellFoundedFormula,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_neg_iff,precedesFormula_iff he,Term.eval_weaken]
  simp only [and_true,and_imp]
  rfl

/-! ### 集合编码展开轨迹到达 ∅ -/

def terminationFormula {n : Nat} (C : ExpressionData (Project.Term n)) (Keys EN : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.conj (graphFormula (.bound 0) C.omega.weaken C.expressions.weaken)
      (Project.Formula.forallMem C.omega.weaken (Project.Formula.forallMem C.omega.weaken.weaken
        (Project.Formula.forallMem C.expressions.weaken.weaken.weaken
          (Project.Formula.forallMem C.expressions.weaken.weaken.weaken.weaken
            (.imp (.conj (successorFormula (.bound 2) (.bound 3))
                (.conj (memPairFormula (.bound 4) (.bound 3) (.bound 1)) (memPairFormula (.bound 4) (.bound 2) (.bound 0))))
              (Project.Formula.existsMem C.omega.weaken.weaken.weaken.weaken.weaken
                (KP1Y.Dynamics.expansionFormula Keys.weaken.weaken.weaken.weaken.weaken.weaken
                  EN.weaken.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 0) (.bound 1)))))))))
    (Project.Formula.existsMem C.omega.weaken (memPairFormula (.bound 1) (.bound 0) C.zero.weaken.weaken)))

theorem terminationFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Keys EN : Project.Term n) (hK : Keys.freeSupport=[]) (hEN : EN.freeSupport=[]) :
    (terminationFormula C Keys EN).FreeClosed := by
  simp [terminationFormula,graphFormula,successorFormula,memPairFormula,codeFormula,pairFormula,
    KP1Y.Dynamics.expansionFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hC.omega,hC.zero,hC.expressions,hK,hEN]

theorem terminationFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Keys EN : Project.Term n) :
    Project.Formula.satisfies e (terminationFormula C Keys EN) ↔
      ∀ H, Graph M H (C.eval e).omega (C.eval e).expressions →
        (∀ i j x y, M.SuccessorOf j i → MemPair M H i x → MemPair M H j y →
          ∃ N, M.mem N (C.eval e).omega ∧ KP1Y.Dynamics.Expansion M (Keys.eval e) (EN.eval e) x N y) →
        ∃ i, M.mem i (C.eval e).omega ∧ MemPair M H i (C.eval e).zero := by
  simp only [terminationFormula,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,graphFormula_iff he,Project.Formula.satisfies_forallMem_iff,
    successorFormula_iff he,memPairFormula_iff he,Project.Formula.satisfies_existsMem_iff,
    KP1Y.Dynamics.expansionFormula_iff he,Term.eval_weaken]
  apply forall_congr'
  intro H
  constructor
  · intro h hH hStep
    exact h ⟨hH,fun i _ j _ x _ y _ hAnte => hStep i j x y hAnte.1 hAnte.2.1 hAnte.2.2⟩
  · rintro h ⟨hH,hStep⟩
    exact h hH (fun i j x y hs hix hjy => hStep i (hH.bounds he hix).1 j (hH.bounds he hjy).1
      x (hH.bounds he hix).2 y (hH.bounds he hjy).2 ⟨hs,hix,hjy⟩)

/-! ### 有限步可达与字典序良序 -/

def reachFormula {n : Nat} (C : ExpressionData (Project.Term n)) (Keys EN x s : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE
    (Reachability.pathFormula C.weaken.weaken.weaken.weaken Keys.weaken.weaken.weaken.weaken EN.weaken.weaken.weaken.weaken
      (.bound 3) (.bound 2) (.bound 1) (.bound 0) s.weaken.weaken.weaken.weaken x.weaken.weaken.weaken.weaken))))

theorem reachFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Keys EN x s : Project.Term n) (hK : Keys.freeSupport=[]) (hEN : EN.freeSupport=[])
    (hx : x.freeSupport=[]) (hs : s.freeSupport=[]) : (reachFormula C Keys EN x s).FreeClosed := by
  have hP := Reachability.pathFormula_freeClosed hC.weaken.weaken.weaken.weaken Keys.weaken.weaken.weaken.weaken
    EN.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) (.bound 0) s.weaken.weaken.weaken.weaken
    x.weaken.weaken.weaken.weaken (by simpa using hK) (by simpa using hEN) rfl rfl rfl rfl (by simpa using hs) (by simpa using hx)
  simp [reachFormula,Definitional.Formula.FreeClosed,hP]

theorem reachFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Keys EN x s : Project.Term n) :
    Project.Formula.satisfies e (reachFormula C Keys EN x s) ↔
      Reachability.Reaches M (C.eval e) (Keys.eval e) (EN.eval e) (x.eval e) (s.eval e) := by
  simp only [reachFormula,Project.Formula.satisfies_exists_iff,Reachability.pathFormula_iff he,
    ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

def lexWellOrderFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.forallMem X (.neg (lexFormula C.weaken (.bound 0) (.bound 0))))
    (.conj (Project.Formula.forallMem X (Project.Formula.forallMem X.weaken (Project.Formula.forallMem X.weaken.weaken
        (.imp (.conj (lexFormula C.weaken.weaken.weaken (.bound 2) (.bound 1)) (lexFormula C.weaken.weaken.weaken (.bound 1) (.bound 0)))
          (lexFormula C.weaken.weaken.weaken (.bound 2) (.bound 0))))))
      (.conj (Project.Formula.forallMem X (Project.Formula.forallMem X.weaken
          (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0))
            (.disj (lexFormula C.weaken.weaken (.bound 1) (.bound 0)) (lexFormula C.weaken.weaken (.bound 0) (.bound 1))))))
        (.forallE (.imp (.conj (Project.Formula.subset (.bound 0) X.weaken)
            (Project.Formula.existsMem (.bound 0) (Project.Formula.extensionalEq (.bound 0) (.bound 0))))
          (Project.Formula.existsMem (.bound 0) (Project.Formula.forallMem (.bound 1)
            (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (lexFormula C.weaken.weaken.weaken (.bound 1) (.bound 0)))))))))

theorem lexWellOrderFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (X : Project.Term n) (hX : X.freeSupport=[]) : (lexWellOrderFormula C X).FreeClosed := by
  have h1 := lexFormula_freeClosed hC.weaken (.bound 0) (.bound 0) rfl rfl
  have h2 := lexFormula_freeClosed hC.weaken.weaken.weaken (.bound 2) (.bound 1) rfl rfl
  have h3 := lexFormula_freeClosed hC.weaken.weaken.weaken (.bound 1) (.bound 0) rfl rfl
  have h4 := lexFormula_freeClosed hC.weaken.weaken.weaken (.bound 2) (.bound 0) rfl rfl
  have h5 := lexFormula_freeClosed hC.weaken.weaken (.bound 1) (.bound 0) rfl rfl
  have h6 := lexFormula_freeClosed hC.weaken.weaken (.bound 0) (.bound 1) rfl rfl
  simp [lexWellOrderFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hX,h1,h2,h3,h4,h5,h6]

theorem lexWellOrderFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : Project.Term n) :
    Project.Formula.satisfies e (lexWellOrderFormula C X) ↔ LexWellOrder M (C.eval e) (X.eval e) := by
  simp only [lexWellOrderFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_existsMem_iff,lexFormula_iff he,
    ExpressionData.eval_weaken,Term.eval_weaken]
  simp only [and_true,and_imp]
  rfl

/-! ### Desc(s) 与 G -/

def descFormula {n : Nat} (C : ExpressionData (Project.Term n)) (Keys EN : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.expressions (.existsE (.conj
    (.forallE (.iff (.mem (.bound 0) (.bound 1)) (.conj (.mem (.bound 0) C.expressions.weaken.weaken.weaken)
      (reachFormula C.weaken.weaken.weaken Keys.weaken.weaken.weaken EN.weaken.weaken.weaken (.bound 0) (.bound 2)))))
    (lexWellOrderFormula C.weaken.weaken (.bound 0))))

theorem descFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Keys EN : Project.Term n) (hK : Keys.freeSupport=[]) (hEN : EN.freeSupport=[]) :
    (descFormula C Keys EN).FreeClosed := by
  have hR := reachFormula_freeClosed hC.weaken.weaken.weaken Keys.weaken.weaken.weaken EN.weaken.weaken.weaken
    (.bound 0) (.bound 2) (by simpa using hK) (by simpa using hEN) rfl rfl
  have hL := lexWellOrderFormula_freeClosed hC.weaken.weaken (.bound 0) rfl
  simp [descFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.expressions,hR,hL]

theorem descFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Keys EN : Project.Term n) :
    Project.Formula.satisfies e (descFormula C Keys EN) ↔
      ∀ s, M.mem s (C.eval e).expressions → ∃ X,
        (∀ x, M.mem x X ↔ M.mem x (C.eval e).expressions ∧ Reachability.Reaches M (C.eval e) (Keys.eval e) (EN.eval e) x s) ∧
          LexWellOrder M (C.eval e) X := by
  simp only [descFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,reachFormula_iff he,lexWellOrderFormula_iff he,ExpressionData.eval_weaken,
    Term.eval_weaken]
  rfl

def genFormula {n : Nat} (C : ExpressionData (Project.Term n)) (Keys EN : Project.Term n) : Project.Formula 1 n :=
  .existsE (.conj
    (.forallE (.iff (.mem (.bound 0) (.bound 1)) (.conj (.mem (.bound 0) C.expressions.weaken.weaken)
      (.existsE (.conj (seedFormula C.weaken.weaken.weaken (.bound 0))
        (reachFormula C.weaken.weaken.weaken Keys.weaken.weaken.weaken EN.weaken.weaken.weaken (.bound 1) (.bound 0)))))))
    (lexWellOrderFormula C.weaken (.bound 0)))

theorem genFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Keys EN : Project.Term n) (hK : Keys.freeSupport=[]) (hEN : EN.freeSupport=[]) :
    (genFormula C Keys EN).FreeClosed := by
  have hS := seedFormula_freeClosed hC.weaken.weaken.weaken (.bound 0) rfl
  have hR := reachFormula_freeClosed hC.weaken.weaken.weaken Keys.weaken.weaken.weaken EN.weaken.weaken.weaken
    (.bound 1) (.bound 0) (by simpa using hK) (by simpa using hEN) rfl rfl
  have hL := lexWellOrderFormula_freeClosed hC.weaken (.bound 0) rfl
  simp [genFormula,Definitional.Formula.FreeClosed,hC.expressions,hS,hR,hL]

theorem genFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Keys EN : Project.Term n) :
    Project.Formula.satisfies e (genFormula C Keys EN) ↔
      ∃ X, (∀ x, M.mem x X ↔ M.mem x (C.eval e).expressions ∧
          ∃ r, Seed M (C.eval e) r ∧ Reachability.Reaches M (C.eval e) (Keys.eval e) (EN.eval e) x r) ∧
        LexWellOrder M (C.eval e) X := by
  simp only [genFormula,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    seedFormula_iff he,reachFormula_iff he,lexWellOrderFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

/-! ### 全部结论：∀ν (UncountableOrdinal(ν) → 秩子句 ∧ 良基 ∧ 终止 ∧ Desc 良序 ∧ G 良序) -/

def ConclusionClause (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) : Prop :=
  ∀ ν, UncountableOrdinal M D.expr.omega ν →
    RankClause M D ν ∧ WellFoundedClause M D ∧ TerminationClause M D ∧ DescClause M D ∧ GenClause M D

def conclusionFormula {n : Nat} (C : ExpressionData (Project.Term n)) (Keys EN : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (uncountableFormula C.omega.weaken (.bound 0))
    (.conj (rankClauseFormula C.weaken Keys.weaken EN.weaken (.bound 0))
      (.conj (wellFoundedFormula C.weaken Keys.weaken EN.weaken)
        (.conj (terminationFormula C.weaken Keys.weaken EN.weaken)
          (.conj (descFormula C.weaken Keys.weaken EN.weaken) (genFormula C.weaken Keys.weaken EN.weaken))))))

theorem conclusionFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Keys EN : Project.Term n) (hK : Keys.freeSupport=[]) (hEN : EN.freeSupport=[]) :
    (conclusionFormula C Keys EN).FreeClosed := by
  have hK' : Keys.weaken.freeSupport=[] := by simpa using hK
  have hEN' : EN.weaken.freeSupport=[] := by simpa using hEN
  have hU : (uncountableFormula C.omega.weaken (.bound 0)).FreeClosed := by
    simp [uncountableFormula,ontoFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.isOrdinal,Project.Formula.isTransitive,Project.Formula.isWellOrderOn,
      Project.Formula.isLinearOrderOn,Project.Formula.isStrictPartialOrderOn,Project.Formula.isIrreflexiveOn,
      Project.Formula.isTransitiveOn,Project.Formula.isLeastOf,Project.Formula.lessOrEqual,
      Project.Formula.forallMem,Project.Formula.existsMem,Project.Formula.subset,Project.Formula.extensionalEq,
      Definitional.Formula.FreeClosed,hC.omega]
  simp only [conclusionFormula,Definitional.Formula.FreeClosed]
  exact ⟨hU,rankClauseFormula_freeClosed hC.weaken _ _ _ hK' hEN' rfl,
    wellFoundedFormula_freeClosed hC.weaken _ _ hK' hEN',terminationFormula_freeClosed hC.weaken _ _ hK' hEN',
    descFormula_freeClosed hC.weaken _ _ hK' hEN',genFormula_freeClosed hC.weaken _ _ hK' hEN'⟩

theorem conclusionFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (D : TheoremData (Project.Term n)) (hD : (D.eval e).Valid M) :
    Project.Formula.satisfies e (conclusionFormula D.expr D.keys D.expansion) ↔ ConclusionClause M (D.eval e) := by
  simp only [conclusionFormula,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,uncountableFormula_iff hM.1,wellFoundedFormula_iff hM.1,
    terminationFormula_iff hM.1,descFormula_iff hM.1,genFormula_iff hM.1,ExpressionData.eval_weaken,Term.eval_weaken]
  apply forall_congr'
  intro ν
  have hR := rankClauseFormula_iff hM (e.push ν) D.expr.weaken D.keys.weaken D.expansion.weaken (.bound 0)
    (T := (D.eval e).arith) (by rw [ExpressionData.eval_weaken]; exact hD.expr)
    (by rw [ExpressionData.eval_weaken,Term.eval_weaken,Term.eval_weaken]; exact hD.graph)
  rw [ExpressionData.eval_weaken] at hR
  rw [hR]
  rfl

end KP1Y.OneYTheorem
