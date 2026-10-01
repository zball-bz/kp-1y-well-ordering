import KP1Y.ReflectionIndex

/-! R的有界查询及严格阶段局部性，历史可任意，不假定已满足递归。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def ValidQuery (M : SetTheory.Structure.{u}) (C : IndexData M.Domain) (K θ a b : M.Domain) : Prop :=
  M.mem K C.omega ∧ M.mem θ C.cap ∧ M.mem a C.cap ∧ M.mem b C.cap ∧ (θ=a ∨ M.mem θ a) ∧ M.mem a b ∧ M.mem C.omega a

def validQueryFormula {n : Nat} (C : IndexData (Project.Term n)) (K θ a b : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem K C.omega) (.conj (.mem θ C.cap) (.conj (.mem a C.cap) (.conj (.mem b C.cap)
    (.conj (.disj (Project.Formula.extensionalEq θ a) (.mem θ a)) (.conj (.mem a b) (.mem C.omega a))))))

theorem validQueryFormula_delta0 {n : Nat} (C : IndexData (Project.Term n)) (K θ a b : Project.Term n) :
    (validQueryFormula C K θ a b).IsDelta0 := .conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _)
      (.conj (.disj (.atom _ _ _) (.mem _ _)) (.conj (.mem _ _) (.mem _ _))))))

theorem validQueryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : IndexData (Project.Term n)) (K θ a b : Project.Term n) :
    Project.Formula.satisfies e (validQueryFormula C K θ a b) ↔ ValidQuery M (C.eval e) (K.eval e) (θ.eval e) (a.eval e) (b.eval e) := by
  simp only [validQueryFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

def Query (M : SetTheory.Structure.{u}) (C : IndexData M.Domain) (H K θ a b : M.Domain) : Prop :=
  ValidQuery M C K θ a b ∧ ∃ σ, M.mem σ C.bound ∧ Cursor M C.keys C.index b K θ σ ∧ MemPair M H σ a

def queryFormula {n : Nat} (C : IndexData (Project.Term n)) (H K θ a b : Project.Term n) : Project.Formula 1 n :=
  .conj (validQueryFormula C K θ a b) (Project.Formula.existsMem C.bound
    (.conj (cursorFormula C.keys.weaken C.index.weaken b.weaken K.weaken θ.weaken (.bound 0))
      (memPairFormula H.weaken (.bound 0) a.weaken)))

theorem queryFormula_delta0 {n : Nat} (C : IndexData (Project.Term n)) (H K θ a b : Project.Term n) :
    (queryFormula C H K θ a b).IsDelta0 := .conj (validQueryFormula_delta0 _ _ _ _ _)
      (.existsMem _ (.conj (cursorFormula_delta0 _ _ _ _ _ _) (memPairFormula_delta0 _ _ _)))

theorem queryFormula_freeClosed {n : Nat} (C : IndexData (Project.Term n)) (H K θ a b : Project.Term n)
    (hω : C.omega.freeSupport=[]) (hCap : C.cap.freeSupport=[]) (hKeys : C.keys.freeSupport=[])
    (hIndex : C.index.freeSupport=[]) (hBound : C.bound.freeSupport=[]) (hH : H.freeSupport=[])
    (hK : K.freeSupport=[]) (hθ : θ.freeSupport=[]) (ha : a.freeSupport=[]) (hb : b.freeSupport=[]) :
    (queryFormula C H K θ a b).FreeClosed := by
  simp [queryFormula,validQueryFormula,cursorFormula,KP1Y.Ranking.packetFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hω,hCap,hKeys,hIndex,hBound,hH,hK,hθ,ha,hb]

theorem queryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : IndexData (Project.Term n)) (H K θ a b : Project.Term n) :
    Project.Formula.satisfies e (queryFormula C H K θ a b) ↔ Query M (C.eval e) (H.eval e) (K.eval e) (θ.eval e) (a.eval e) (b.eval e) := by
  simp only [queryFormula,Project.Formula.satisfies_conj_iff,validQueryFormula_iff he,
    Project.Formula.satisfies_existsMem_iff,cursorFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem IndexData.Valid.cursor_parameters_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : IndexData M.Domain} (h : C.Valid M) {b K θ b' K' θ' σ : M.Domain}
    (hc : Cursor M C.keys C.index b K θ σ) (hc' : Cursor M C.keys C.index b' K' θ' σ) : b=b' ∧ K=K' ∧ θ=θ' := by
  obtain ⟨_,hK,hθ,_,hCode⟩ := (h.cursor_iff_d hM b K θ σ).mp hc
  obtain ⟨_,hK',hθ',_,hCode'⟩ := (h.cursor_iff_d hM b' K' θ' σ).mp hc'
  exact stage_code_injective_d hM h.block hK hK' hθ hθ' hCode hCode' rfl

def Earlier (M : SetTheory.Structure.{u}) (b K θ b' K' θ' : M.Domain) : Prop :=
  M.mem b b' ∨ b=b' ∧ (M.mem K K' ∨ K=K' ∧ M.mem θ θ')

theorem cursor_earlier_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : IndexData M.Domain}
    (hC : C.Valid M) {b K θ σ b' K' θ' τ : M.Domain} (hσ : Cursor M C.keys C.index b K θ σ)
    (hτ : Cursor M C.keys C.index b' K' θ' τ) (hEarlier : Earlier M b K θ b' K' θ') : M.mem σ τ := by
  obtain ⟨_,hK,hθ,_,hCode⟩ := (hC.cursor_iff_d hM b K θ σ).mp hσ
  obtain ⟨_,_,_,_,hCode'⟩ := (hC.cursor_iff_d hM b' K' θ' τ).mp hτ
  rcases hEarlier with hbb' | ⟨hbb',hLayers⟩
  · exact stage_code_earlier_endpoint_d hM hC.block hK hθ hbb' hCode hCode'
  · subst b'
    rcases hLayers with hKK' | ⟨hKK',hθθ'⟩
    · exact stage_code_earlier_layer_d hM hθ hKK' hCode hCode'
    · subst K'
      exact stage_code_earlier_root_d hM hθθ' hCode hCode'

theorem query_agrees_of_earlier_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : IndexData M.Domain}
    (hC : C.Valid M) {H J b K θ σ b' K' θ' a' : M.Domain} (hσ : Cursor M C.keys C.index b K θ σ)
    (hEarlier : Earlier M b' K' θ' b K θ)
    (hAgree : ∀ τ, M.mem τ σ → ∀ a, M.mem a C.cap → (MemPair M H τ a ↔ MemPair M J τ a)) :
    Query M C H K' θ' a' b' ↔ Query M C J K' θ' a' b' := by
  constructor
  · rintro ⟨hValid,τ,hτ,hCursor,hAt⟩
    exact ⟨hValid,τ,hτ,hCursor,(hAgree τ (cursor_earlier_d hM hC hCursor hσ hEarlier) a' hValid.2.2.1).mp hAt⟩
  · rintro ⟨hValid,τ,hτ,hCursor,hAt⟩
    exact ⟨hValid,τ,hτ,hCursor,(hAgree τ (cursor_earlier_d hM hC hCursor hσ hEarlier) a' hValid.2.2.1).mpr hAt⟩

end KP1Y.Reflection
