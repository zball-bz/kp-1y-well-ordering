import KP1Y.SequenceCertificate

/-! KPω中的连续Σ₁迭代矩阵：初值、上一项的Σ₁运算、极限历史值域并。 -/
namespace KP1Y.OrdinalIteration
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.Bounded
universe u

def tailEnv {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M (n+1)) : Env M n :=
  ⟨fun i => e.bound i.succ,e.free⟩

def Next {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n) (e : Env M n) (x y z : M.Domain) : Prop :=
  Project.Formula.satisfies (((e.push x).push y).push z) φ.body

def Total {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n) (e : Env M n) : Prop :=
  ∀ x, ∃ y z, Next φ e x y z

def Functional {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n) (e : Env M n) : Prop :=
  ∀ x y y' z z', Next φ e x y z → Next φ e x y' z' → y=y'

def Empty (M : SetTheory.Structure.{u}) (i : M.Domain) : Prop := ∀ x, ¬M.mem x i
def NoPredecessor (M : SetTheory.Structure.{u}) (i : M.Domain) : Prop := ∀ p, M.mem p i → ¬M.SuccessorOf i p

def Step {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1))
    (i P T w : M.Domain) : Prop :=
  ∃ V, M.mem V w ∧ Graph M P i V ∧
    ((Empty M i ∧ T=e.bound 0) ∨
      (∃ p, M.mem p i ∧ ∃ x, M.mem x V ∧ ∃ z, M.mem z w ∧
        M.SuccessorOf i p ∧ MemPair M P p x ∧ Next φ (tailEnv e) x T z) ∨
      ((¬Empty M i ∧ NoPredecessor M i) ∧ ∃ D, M.mem D w ∧ RangeBound M D V P i ∧
        ∀ a, M.mem a T ↔ ∃ x, M.mem x D ∧ M.mem a x))

private def nextSlots {n : Nat} : Fin (n+3) → Fin (n+9) :=
  Fin.cases 0 (Fin.cases 5 (Fin.cases 1 (fun i => ⟨i.val+9,by omega⟩)))

def iterationMatrix {n : Nat} (φ : KP1Y.WitnessMatrix n) : KP1Y.SigmaRecursion.StepMatrix (n+1) where
  body := Project.Formula.existsMem (.bound 0)
    (.conj (graphFormula (.bound 3) (.bound 4) (.bound 0))
      (.disj (.conj (emptyFormula (.bound 4)) (Project.Formula.extensionalEq (.bound 2) (.bound 5)))
        (.disj
          (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 1)
            (Project.Formula.existsMem (.bound 3)
              (.conj (successorFormula (.bound 7) (.bound 2))
                (.conj (memPairFormula (.bound 6) (.bound 2) (.bound 1)) (φ.body.rename nextSlots))))))
          (.conj (.conj (.neg (emptyFormula (.bound 4)))
              (Project.Formula.forallMem (.bound 4) (.neg (successorFormula (.bound 5) (.bound 0)))))
            (Project.Formula.existsMem (.bound 1)
              (.conj (rangeBoundFormula (.bound 0) (.bound 1) (.bound 4) (.bound 5))
                (unionFormula (.bound 3) (.bound 0))))))))
  freeClosed := by
    simp [graphFormula,emptyFormula,successorFormula,rangeBoundFormula,unionFormula,
      memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
      Definitional.Formula.FreeClosed,φ.freeClosed]
  delta0 := .existsMem _ (.conj (graphFormula_delta0 _ _ _)
    (.disj (.conj (emptyFormula_delta0 _) (.atom _ _ _))
      (.disj (.existsMem _ (.existsMem _ (.existsMem _
        (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _) (KP1Y.delta0_rename φ.delta0 _))))))
        (.conj (.conj (.neg (emptyFormula_delta0 _)) (.forallMem _ (.neg (successorFormula_delta0 _ _))))
          (.existsMem _ (.conj (rangeBoundFormula_delta0 _ _ _ _) (unionFormula_delta0 _ _)))))))

private theorem nextSlots_env {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M (n+1)) (i P T w V p x z : M.Domain) :
    ((((((((e.push i).push P).push T).push w).push V).push p).push x).push z).reindex nextSlots =
      (((tailEnv e).push x).push T).push z := by
  rw [Env.mk.injEq]
  constructor
  · funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) k <;> rfl
  · rfl

theorem iterationMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (i P T w : M.Domain) :
    (iterationMatrix φ).denote e i P T w ↔ Step φ e i P T w := by
  simp only [KP1Y.SigmaRecursion.StepMatrix.denote,iterationMatrix,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,
    graphFormula_iff hM.1,emptyFormula_iff,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,
    successorFormula_iff hM.1,rangeBoundFormula_iff hM.1,unionFormula_iff,memPairFormula_iff hM.1,
    Project.Formula.satisfies_rename,nextSlots_env]
  rfl

end KP1Y.OrdinalIteration
