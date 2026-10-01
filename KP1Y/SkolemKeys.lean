import KP1Y.SkolemWitnesses

/-! Skolem 函数的实际参数集合：程序、节点、赋值、变量域和变量号。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u v

structure SkolemBounds (α : Type u) where
  programNodes : α
  variableSlots : α
  assignmentSlots : α
  keys : α

def SkolemBounds.map {α : Type u} {β : Type v} (K : SkolemBounds α) (f : α → β) : SkolemBounds β :=
  ⟨f K.programNodes,f K.variableSlots,f K.assignmentSlots,f K.keys⟩
def SkolemBounds.eval {M : SetTheory.Structure.{u}} {n : Nat}
    (K : SkolemBounds (Project.Term n)) (env : Env M n) : SkolemBounds M.Domain := K.map (fun t => t.eval env)
def SkolemBounds.weaken {n : Nat} (K : SkolemBounds (Project.Term n)) : SkolemBounds (Project.Term (n+1)) := K.map (fun t => t.weaken)

theorem SkolemBounds.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat}
    (K : SkolemBounds (Project.Term n)) (env : Env M n) (x : M.Domain) : K.weaken.eval (env.push x)=K.eval env := by
  cases K
  simp [SkolemBounds.weaken,SkolemBounds.eval,SkolemBounds.map,Definitional.Term.eval_weaken]

structure SkolemBoundsValid (M : SetTheory.Structure.{u}) (C : Context M.Domain) (I : EvaluationData M.Domain)
    (K : SkolemBounds M.Domain) : Prop where
  programNodes : IsProduct M K.programNodes C.programs C.omega
  variableSlots : IsProduct M K.variableSlots C.omega C.omega
  assignmentSlots : IsProduct M K.assignmentSlots I.assignments K.variableSlots
  keys : IsProduct M K.keys K.programNodes K.assignmentSlots

theorem skolem_bounds_exist_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : Context M.Domain) (I : EvaluationData M.Domain) : ∃ K, SkolemBoundsValid M C I K := by
  obtain ⟨PJ,hPJ⟩ := product_exists hM C.programs C.omega
  obtain ⟨BV,hBV⟩ := product_exists hM C.omega C.omega
  obtain ⟨SBV,hSBV⟩ := product_exists hM I.assignments BV
  obtain ⟨Keys,hKeys⟩ := product_exists hM PJ SBV
  exact ⟨⟨PJ,BV,SBV,Keys⟩,hPJ,hBV,hSBV,hKeys⟩

def KeyCode (M : SetTheory.Structure.{u}) (K : SkolemBounds M.Domain) (key p j s bound v : M.Domain) : Prop :=
  ∃ pj, M.mem pj K.programNodes ∧ ∃ bv, M.mem bv K.variableSlots ∧ ∃ sbv, M.mem sbv K.assignmentSlots ∧
    Codes M key pj sbv ∧ Codes M pj p j ∧ Codes M sbv s bv ∧ Codes M bv bound v

def keyCodeFormula {n : Nat} (K : SkolemBounds (Project.Term n)) (key p j s bound v : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem K.programNodes (Project.Formula.existsMem K.variableSlots.weaken
    (Project.Formula.existsMem K.assignmentSlots.weaken.weaken
      (.conj (codeFormula key.weaken.weaken.weaken (.bound 2) (.bound 0))
        (.conj (codeFormula (.bound 2) p.weaken.weaken.weaken j.weaken.weaken.weaken)
          (.conj (codeFormula (.bound 0) s.weaken.weaken.weaken (.bound 1))
            (codeFormula (.bound 1) bound.weaken.weaken.weaken v.weaken.weaken.weaken))))))

theorem keyCodeFormula_delta0 {n : Nat} (K : SkolemBounds (Project.Term n)) (key p j s bound v : Project.Term n) :
    (keyCodeFormula K key p j s bound v).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.conj (codeFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _) (codeFormula_delta0 _ _ _))))))

theorem keyCodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (K : SkolemBounds (Project.Term n)) (key p j s bound v : Project.Term n) :
    Project.Formula.satisfies env (keyCodeFormula K key p j s bound v) ↔
      KeyCode M (K.eval env) (key.eval env) (p.eval env) (j.eval env) (s.eval env) (bound.eval env) (v.eval env) := by
  simp only [keyCodeFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem key_code_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {K : SkolemBounds M.Domain}
    {key p j s bound v p' j' s' bound' v' : M.Domain}
    (h : KeyCode M K key p j s bound v) (h' : KeyCode M K key p' j' s' bound' v') :
    p=p' ∧ j=j' ∧ s=s' ∧ bound=bound' ∧ v=v' := by
  obtain ⟨pj,_,bv,_,sbv,_,hKey,hPJ,hSBV,hBV⟩ := h
  obtain ⟨pj',_,bv',_,sbv',_,hKey',hPJ',hSBV',hBV'⟩ := h'
  obtain ⟨hPj,hSbv⟩ := codes_injective he hKey hKey'
  subst pj'
  subst sbv'
  obtain ⟨hp,hj⟩ := codes_injective he hPJ hPJ'
  obtain ⟨hs,hBv⟩ := codes_injective he hSBV hSBV'
  subst bv'
  exact ⟨hp,hj,hs,codes_injective he hBV hBV'⟩

theorem key_members {M : SetTheory.Structure.{u}} {C : Context M.Domain} {I : EvaluationData M.Domain}
    {K : SkolemBounds M.Domain} (hK : SkolemBoundsValid M C I K) (key : M.Domain) :
    M.mem key K.keys ↔ ∃ p, M.mem p C.programs ∧ ∃ j, M.mem j C.omega ∧ ∃ s, M.mem s I.assignments ∧
      ∃ bound, M.mem bound C.omega ∧ ∃ v, M.mem v C.omega ∧ KeyCode M K key p j s bound v := by
  constructor
  · intro hk
    obtain ⟨pj,hpj,sbv,hsbv,hKey⟩ := (hK.keys key).mp hk
    obtain ⟨p,hp,j,hj,hPJ⟩ := (hK.programNodes pj).mp hpj
    obtain ⟨s,hs,bv,hbv,hSBV⟩ := (hK.assignmentSlots sbv).mp hsbv
    obtain ⟨bound,hb,v,hv,hBV⟩ := (hK.variableSlots bv).mp hbv
    exact ⟨p,hp,j,hj,s,hs,bound,hb,v,hv,pj,hpj,bv,hbv,sbv,hsbv,hKey,hPJ,hSBV,hBV⟩
  · rintro ⟨_,_,_,_,_,_,_,_,_,_,pj,hpj,_,_,sbv,hsbv,hKey,_,_,_⟩
    exact (hK.keys key).mpr ⟨pj,hpj,sbv,hsbv,hKey⟩

end KP1Y.Satisfaction
