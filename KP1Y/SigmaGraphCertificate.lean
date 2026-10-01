import KP1Y.SigmaFunctionGraph
import KP1Y.BoundedSubstitution
import KP1Y.ClosedEnvironments

/-! Σ₁函数图的共同有界证书。图的总性与行证书足以在原关系单值时识别整个输出图。 -/
namespace KP1Y.Functions
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def witnessInstanceFormula {n k : Nat} (φ : KP1Y.WitnessMatrix n)
    (params : Fin n → Project.Term k) (x y z : Project.Term k) : Project.Formula 1 k :=
  φ.body.bind (Fin.cases z (Fin.cases y (Fin.cases x params)))

theorem witnessInstanceFormula_delta0 {n k : Nat} (φ : KP1Y.WitnessMatrix n)
    (params : Fin n → Project.Term k) (x y z : Project.Term k) :
    (witnessInstanceFormula φ params x y z).IsDelta0 := KP1Y.delta0_bind φ.delta0 _

theorem witnessInstanceFormula_freeClosed {n k : Nat} (φ : KP1Y.WitnessMatrix n)
    (params : Fin n → Project.Term k) (x y z : Project.Term k)
    (hp : ∀ i, (params i).freeSupport=[]) (hx : x.freeSupport=[]) (hy : y.freeSupport=[])
    (hz : z.freeSupport=[]) : (witnessInstanceFormula φ params x y z).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ φ.body).mpr φ.freeClosed
  exact Fin.cases hz (Fin.cases hy (Fin.cases hx hp))

theorem witnessInstanceFormula_iff {M : SetTheory.Structure.{u}} {n k : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M k) (params : Fin n → Project.Term k) (x y z : Project.Term k) :
    Project.Formula.satisfies e (witnessInstanceFormula φ params x y z) ↔
      Project.Formula.satisfies ((((Env.substitute e params).push (x.eval e)).push (y.eval e)).push (z.eval e)) φ.body := by
  have hEnv : Env.substitute e (Fin.cases z (Fin.cases y (Fin.cases x params))) =
      (((Env.substitute e params).push (x.eval e)).push (y.eval e)).push (z.eval e) := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    · rfl
  rw [witnessInstanceFormula,Project.Formula.satisfies_bind,hEnv]

structure SigmaGraphCertificate {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n)
    (e : Env M n) (F X Y B : M.Domain) : Prop where
  graph : Graph M F X Y
  rows : ∀ x, M.mem x X → ∀ y, M.mem y Y → MemPair M F x y →
    ∃ z, M.mem z B ∧ Project.Formula.satisfies (((e.push x).push y).push z) φ.body

def sigmaGraphCertificateFormula {n k : Nat} (φ : KP1Y.WitnessMatrix n)
    (params : Fin n → Project.Term k) (F X Y B : Project.Term k) : Project.Formula 1 k :=
  .conj (graphFormula F X Y)
    (Project.Formula.forallMem X (Project.Formula.forallMem Y.weaken
      (.imp (memPairFormula F.weaken.weaken (.bound 1) (.bound 0))
        (Project.Formula.existsMem B.weaken.weaken
          (witnessInstanceFormula φ (fun i => (params i).weaken.weaken.weaken) (.bound 2) (.bound 1) (.bound 0))))))

theorem sigmaGraphCertificateFormula_delta0 {n k : Nat} (φ : KP1Y.WitnessMatrix n)
    (params : Fin n → Project.Term k) (F X Y B : Project.Term k) :
    (sigmaGraphCertificateFormula φ params F X Y B).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
    (.existsMem _ (witnessInstanceFormula_delta0 _ _ _ _ _)))))

theorem sigmaGraphCertificateFormula_freeClosed {n k : Nat} (φ : KP1Y.WitnessMatrix n)
    (params : Fin n → Project.Term k) (F X Y B : Project.Term k)
    (hp : ∀ i, (params i).freeSupport=[]) (hF : F.freeSupport=[]) (hX : X.freeSupport=[])
    (hY : Y.freeSupport=[]) (hB : B.freeSupport=[]) :
    (sigmaGraphCertificateFormula φ params F X Y B).FreeClosed := by
  unfold sigmaGraphCertificateFormula
  simp only [Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  refine ⟨?_,?_⟩
  · simp [graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Definitional.Formula.FreeClosed,hF,hX,hY]
  · refine ⟨?_,?_,?_⟩
    · simp [hX]
    · simp [hY]
    · refine ⟨?_,?_,?_⟩
      · simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
          Definitional.Formula.FreeClosed,hF]
      · simp [hB]
      · apply witnessInstanceFormula_freeClosed
        · intro i
          simpa using hp i
        · rfl
        · rfl
        · rfl

theorem sigmaGraphCertificateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n k : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M k) (params : Fin n → Project.Term k) (F X Y B : Project.Term k) :
    Project.Formula.satisfies e (sigmaGraphCertificateFormula φ params F X Y B) ↔
      SigmaGraphCertificate φ (Env.substitute e params) (F.eval e) (X.eval e) (Y.eval e) (B.eval e) := by
  have hEnv (x y z : M.Domain) :
      Env.substitute (((e.push x).push y).push z) (fun i => (params i).weaken.weaken.weaken) =
        Env.substitute e params := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      exact Term.eval_weaken _ _ _ |>.trans (Term.eval_weaken _ _ _ |>.trans (Term.eval_weaken _ _ _))
    · rfl
  simp only [sigmaGraphCertificateFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,
    Project.Formula.satisfies_existsMem_iff,witnessInstanceFormula_iff,hEnv,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.graph,h.rows⟩⟩

theorem sigma_graph_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M n) (X Y : M.Domain)
    (hTotal : ∀ x, M.mem x X → ∃ y z, Project.Formula.satisfies (((e.push x).push y).push z) φ.body)
    (hBounds : ∀ x, M.mem x X → ∀ y z, Project.Formula.satisfies (((e.push x).push y).push z) φ.body → M.mem y Y)
    (hFun : ∀ x, M.mem x X → ∀ y y' z z', Project.Formula.satisfies (((e.push x).push y).push z) φ.body →
      Project.Formula.satisfies (((e.push x).push y').push z') φ.body → y=y') :
    ∃ F B, SigmaGraphCertificate φ e F X Y B := by
  obtain ⟨F,hF,hRows⟩ := sigma_function_graph_d hM φ e X Y hTotal hBounds hFun
  obtain ⟨B,hB⟩ := KP1Y.joint_collection_d hM φ e X hTotal
  refine ⟨F,B,hF,?_⟩
  intro x hx y _ hAt
  obtain ⟨_,_,z,hz⟩ := (hRows x y).mp hAt
  obtain ⟨y',_,z',hz',hφ'⟩ := hB x hx
  have he := hFun x hx y y' z z' hz hφ'
  exact ⟨z',hz',he.symm ▸ hφ'⟩

theorem SigmaGraphCertificate.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M n} {F F' X Y B B' : M.Domain}
    (h : SigmaGraphCertificate φ e F X Y B) (h' : SigmaGraphCertificate φ e F' X Y B')
    (hFun : ∀ x, M.mem x X → ∀ y y' z z', Project.Formula.satisfies (((e.push x).push y).push z) φ.body →
      Project.Formula.satisfies (((e.push x).push y').push z') φ.body → y=y') : F=F' := by
  apply h.graph.ext he h'.graph
  intro x hx y
  obtain ⟨v,hv,hvAt⟩ := h.graph.total x hx
  obtain ⟨v',hv',hvAt'⟩ := h'.graph.total x hx
  obtain ⟨z,_,hz⟩ := h.rows x hx v hv hvAt
  obtain ⟨z',_,hz'⟩ := h'.rows x hx v' hv' hvAt'
  have hvv' := hFun x hx v v' z z' hz hz'
  subst v'
  constructor
  · intro hxy
    exact (h.graph.unique x v y hvAt hxy) ▸ hvAt'
  · intro hxy
    exact (h'.graph.unique x v y hvAt' hxy) ▸ hvAt

theorem sigmaGraphCertificate_bound_congr {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n)
    (e e' : Env M n) (hb : ∀ i, e.bound i=e'.bound i) (F X Y B : M.Domain) :
    SigmaGraphCertificate φ e F X Y B ↔ SigmaGraphCertificate φ e' F X Y B := by
  have hs (x y z : M.Domain) :
      Project.Formula.satisfies (((e.push x).push y).push z) φ.body ↔
        Project.Formula.satisfies (((e'.push x).push y).push z) φ.body := by
    apply KP1Y.formula_bound_congr φ.body φ.freeClosed
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl hb))
  constructor
  · intro h
    refine ⟨h.graph,?_⟩
    intro x hx y hy hAt
    obtain ⟨z,hz,hφ⟩ := h.rows x hx y hy hAt
    exact ⟨z,hz,(hs x y z).mp hφ⟩
  · intro h
    refine ⟨h.graph,?_⟩
    intro x hx y hy hAt
    obtain ⟨z,hz,hφ⟩ := h.rows x hx y hy hAt
    exact ⟨z,hz,(hs x y z).mpr hφ⟩

theorem sigmaGraphCertificateFormula_iff_bound {M : SetTheory.Structure.{u}} (he : Extensional M) {n k : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M k) (params : Fin n → Project.Term k) (e' : Env M n)
    (hb : ∀ i, (params i).eval e=e'.bound i) (F X Y B : Project.Term k) :
    Project.Formula.satisfies e (sigmaGraphCertificateFormula φ params F X Y B) ↔
      SigmaGraphCertificate φ e' (F.eval e) (X.eval e) (Y.eval e) (B.eval e) :=
  (sigmaGraphCertificateFormula_iff he φ e params F X Y B).trans
    (sigmaGraphCertificate_bound_congr φ (Env.substitute e params) e' hb _ _ _ _)

end KP1Y.Functions
