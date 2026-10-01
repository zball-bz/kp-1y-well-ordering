import KP1Y.TarskiVaught

/-! 在序数载域中选最小反例见证；全部搜索谓词为字面 Δ₀。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def EvaluationData.weaken {n : Nat} (I : EvaluationData (Project.Term n)) : EvaluationData (Project.Term (n+1)) :=
  I.map (fun t => t.weaken)

theorem EvaluationData.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat}
    (I : EvaluationData (Project.Term n)) (env : Env M n) (x : M.Domain) :
    I.weaken.eval (env.push x) = I.eval env := by
  cases I
  simp [EvaluationData.weaken,EvaluationData.eval,EvaluationData.map,Definitional.Term.eval_weaken]

def FalseWitness (M : SetTheory.Structure.{u}) (C : Context M.Domain) (I : EvaluationData M.Domain)
    (p j s bound v x : M.Domain) : Prop :=
  ∃ t, M.mem t I.assignments ∧ Updated M t s bound I.carrier v x ∧ ¬NodeTrue M (I.context C) I.table p j t

def falseWitnessFormula {n : Nat} (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n))
    (p j s bound v x : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem I.assignments
    (.conj (updatedFormula (.bound 0) s.weaken bound.weaken I.carrier.weaken v.weaken x.weaken)
      (.neg (nodeTrueFormula (I.context C).weaken I.table.weaken p.weaken j.weaken (.bound 0))))

theorem falseWitnessFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n))
    (p j s bound v x : Project.Term n) : (falseWitnessFormula C I p j s bound v x).IsDelta0 :=
  .existsMem _ (.conj (updatedFormula_delta0 _ _ _ _ _ _) (.neg (nodeTrueFormula_delta0 _ _ _ _ _)))

theorem falseWitnessFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n)) (p j s bound v x : Project.Term n) :
    Project.Formula.satisfies env (falseWitnessFormula C I p j s bound v x) ↔
      FalseWitness M (C.eval env) (I.eval env) (p.eval env) (j.eval env) (s.eval env) (bound.eval env) (v.eval env) (x.eval env) := by
  simp only [falseWitnessFormula, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff, updatedFormula_iff he, nodeTrueFormula_iff he,
    Context.eval_weaken, EvaluationData.eval_context, Definitional.Term.eval_weaken]
  rfl

def instanceEnv {M : SetTheory.Structure.{u}} (C : Context M.Domain) (I : EvaluationData M.Domain) : Env M 18 where
  bound k := match k.val with
    | 0 => C.omega | 1 => C.carrier | 2 => C.operands | 3 => C.pairs
    | 4 => C.instructions | 5 => C.programs | 6 => C.assignments | 7 => C.columns
    | 8 => C.atomic | 9 => C.atomTag | 10 => C.negTag | 11 => C.impTag | 12 => C.allTag
    | 13 => I.carrier | 14 => I.assignments | 15 => I.columns | 16 => I.atomic | _ => I.table
  free _ := C.omega

private def witnessContext : Context (Project.Term 24) :=
  ⟨.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12,
    .bound 13,.bound 14,.bound 15,.bound 16,.bound 17,.bound 18⟩
private def witnessInstance : EvaluationData (Project.Term 24) :=
  ⟨.bound 19,.bound 20,.bound 21,.bound 22,.bound 23⟩

private def witnessSchema : Project.Delta0UnarySchema 23 where
  body := falseWitnessFormula witnessContext witnessInstance (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [falseWitnessFormula, updatedFormula, nodeTrueFormula, graphFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, Context.withInterpretation, EvaluationData.context,
      witnessContext, witnessInstance, Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := falseWitnessFormula_delta0 _ _ _ _ _ _ _ _

private theorem witnessSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (I : EvaluationData M.Domain) (p j s bound v x : M.Domain) :
    Project.Formula.satisfies (((((((instanceEnv C I).push p).push j).push s).push bound).push v).push x) witnessSchema.body ↔
      FalseWitness M C I p j s bound v x := by
  simp only [witnessSchema, falseWitnessFormula_iff he]
  rfl

def ChosenWitness (M : SetTheory.Structure.{u}) (C : Context M.Domain) (I : EvaluationData M.Domain)
    (zero p j s bound v x : M.Domain) : Prop :=
  M.mem x I.carrier ∧
    ((FalseWitness M C I p j s bound v x ∧ ∀ y, M.mem y x → ¬FalseWitness M C I p j s bound v y) ∨
      (x=zero ∧ ∀ y, M.mem y I.carrier → ¬FalseWitness M C I p j s bound v y))

theorem least_false_witness_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : Context M.Domain) (I : EvaluationData M.Domain) (hOrd : M.IsOrdinal I.carrier)
    (p j s bound v : M.Domain) (hExists : ∃ x, M.mem x I.carrier ∧ FalseWitness M C I p j s bound v x) :
    ∃ x, M.mem x I.carrier ∧ FalseWitness M C I p j s bound v x ∧
      ∀ y, M.mem y x → ¬FalseWitness M C I p j s bound v y := by
  obtain ⟨W,hW⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) witnessSchema
    ((((((instanceEnv C I).push p).push j).push s).push bound).push v) I.carrier
  have hChar (x : M.Domain) : M.mem x W ↔ M.mem x I.carrier ∧ FalseWitness M C I p j s bound v x := by
    simpa only [witnessSchema_iff hM.1] using hW x
  obtain ⟨w,hw,hWitness⟩ := hExists
  obtain ⟨x,hx,hMin⟩ := hOrd.wellOrder.least W (fun y hy => ((hChar y).mp hy).1)
    ⟨w,(hChar w).mpr ⟨hw,hWitness⟩⟩
  have hxA := ((hChar x).mp hx).1
  refine ⟨x,hxA,((hChar x).mp hx).2,?_⟩
  intro y hy hWitnessY
  have hyA := hOrd.transitive x hxA y hy
  rcases hMin y ((hChar y).mpr ⟨hyA,hWitnessY⟩) with he | hxy
  · have hEq := hM.1.eq_of_same_members x y he
    subst y
    exact hOrd.wellOrder.linear.irrefl x hxA hy
  · exact hOrd.wellOrder.linear.irrefl x hxA
      (hOrd.wellOrder.linear.trans x hxA y hyA x hxA hxy hy)

theorem chosen_witness_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : Context M.Domain) (I : EvaluationData M.Domain) (hOrd : M.IsOrdinal I.carrier)
    {zero : M.Domain} (hZero : M.mem zero I.carrier) (p j s bound v : M.Domain) :
    ∃ x, ChosenWitness M C I zero p j s bound v x := by
  classical
  by_cases hExists : ∃ x, M.mem x I.carrier ∧ FalseWitness M C I p j s bound v x
  · obtain ⟨x,hx,hWitness,hMin⟩ := least_false_witness_d hM C I hOrd p j s bound v hExists
    exact ⟨x,hx,Or.inl ⟨hWitness,hMin⟩⟩
  · exact ⟨zero,hZero,Or.inr ⟨rfl,fun y hy h => hExists ⟨y,hy,h⟩⟩⟩

theorem chosen_witness_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {I : EvaluationData M.Domain} (hOrd : M.IsOrdinal I.carrier)
    {zero p j s bound v x y : M.Domain}
    (hx : ChosenWitness M C I zero p j s bound v x) (hy : ChosenWitness M C I zero p j s bound v y) : x=y := by
  rcases hx.2 with ⟨hWx,hMinx⟩ | ⟨hX,hNo⟩
  · rcases hy.2 with ⟨hWy,hMiny⟩ | ⟨_,hNo⟩
    · rcases hOrd.wellOrder.linear.compare x hx.1 y hy.1 with hEq | hxy | hyx
      · exact he.eq_of_same_members x y hEq
      · exact False.elim (hMiny x hxy hWx)
      · exact False.elim (hMinx y hyx hWy)
    · exact False.elim (hNo x hx.1 hWx)
  · rcases hy.2 with ⟨hWy,_⟩ | ⟨hY,_⟩
    · exact False.elim (hNo y hy.1 hWy)
    · exact hX.trans hY.symm

end KP1Y.Satisfaction
