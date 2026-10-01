import KP1Y.OneYMatrixExpansion
import KP1Y.OneYForestSpace

/-! 任意实际有限矩阵的 BM4 父算法总运行。内部状态为 (row,forest)，高度外保持森林以使辅助迭代全定义。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Iteration
universe u

def matrixRowValuesFormula {d : Nat} (w : Project.Term d) (A : FiniteMatrix (Project.Term d)) (r V : Project.Term d) : Project.Formula 1 d :=
  .conj (graphFormula V A.width w) (Project.Formula.forallMem A.width
    (Project.Formula.forallMem A.cells.weaken (Project.Formula.forallMem w.weaken.weaken
      (.imp (codeFormula (.bound 1) r.weaken.weaken.weaken (.bound 2))
        (.iff (memPairFormula A.values.weaken.weaken.weaken (.bound 1) (.bound 0))
          (memPairFormula V.weaken.weaken.weaken (.bound 2) (.bound 0)))))))

theorem matrixRowValuesFormula_delta0 {d : Nat} (w : Project.Term d) (A : FiniteMatrix (Project.Term d)) (r V : Project.Term d) :
    (matrixRowValuesFormula w A r V).IsDelta0 := .conj (graphFormula_delta0 _ _ _)
      (.forallMem _ (.forallMem _ (.forallMem _ (.imp (codeFormula_delta0 _ _ _)
        (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))))

theorem matrixRowValuesFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (w : Project.Term d) (A : FiniteMatrix (Project.Term d)) (r V : Project.Term d) :
    Project.Formula.satisfies env (matrixRowValuesFormula w A r V) ↔
      MatrixRowValues M (w.eval env) (A.eval env).width (A.eval env).cells (A.eval env).values (r.eval env) (V.eval env) := by
  simp only [matrixRowValuesFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,graphFormula_iff he,
    codeFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,fun c hc key hk hCode d hd => h.2 c hc key hk d hd hCode⟩,
    fun h => ⟨h.graph,fun c hc key hk d hd hCode => h.entries c hc key hk hCode d hd⟩⟩

def ParentDecision (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) (r P Q : M.Domain) : Prop :=
  (M.mem r A.height ∧ ∃ V, M.mem V C.sequences ∧ MatrixRowValues M C.omega A.width A.cells A.values r V ∧ Selects false M C A.width P V Q) ∨
    (¬M.mem r A.height ∧ Q=P)

def parentDecisionFormula {d : Nat} (C : ExpressionData (Project.Term d)) (A : FiniteMatrix (Project.Term d)) (r P Q : Project.Term d) : Project.Formula 1 d :=
  .disj (.conj (.mem r A.height) (Project.Formula.existsMem C.sequences
    (.conj (matrixRowValuesFormula C.omega.weaken A.weaken r.weaken (.bound 0))
      (selectsFormula false C.weaken A.width.weaken P.weaken (.bound 0) Q.weaken))))
    (.conj (.neg (.mem r A.height)) (Project.Formula.extensionalEq Q P))

theorem parentDecisionFormula_delta0 {d : Nat} (C : ExpressionData (Project.Term d)) (A : FiniteMatrix (Project.Term d)) (r P Q : Project.Term d) :
    (parentDecisionFormula C A r P Q).IsDelta0 := .disj (.conj (.mem _ _) (.existsMem _
      (.conj (matrixRowValuesFormula_delta0 _ _ _ _) (selectsFormula_delta0 _ _ _ _ _ _)))) (.conj (.neg (.mem _ _)) (.atom _ _ _))

theorem parentDecisionFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (C : ExpressionData (Project.Term d)) (A : FiniteMatrix (Project.Term d)) (r P Q : Project.Term d) :
    Project.Formula.satisfies env (parentDecisionFormula C A r P Q) ↔ ParentDecision M (C.eval env) (A.eval env) (r.eval env) (P.eval env) (Q.eval env) := by
  simp only [parentDecisionFormula,ParentDecision,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,matrixRowValuesFormula_iff he,selectsFormula_iff he,
    ExpressionData.eval_weaken,FiniteMatrix.eval_weaken,Term.eval_weaken]
  rfl

def ParentStateNext (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) (Forests old next : M.Domain) : Prop :=
  ∃ r, M.mem r C.omega ∧ ∃ s, M.mem s C.omega ∧ ∃ P, M.mem P Forests ∧ ∃ Q, M.mem Q Forests ∧
    Codes M old r P ∧ Codes M next s Q ∧ M.SuccessorOf s r ∧ ParentDecision M C A s P Q

private def parentStateEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) (Forests : M.Domain) : Env M 10 where
  bound i := match i.val with
    | 0 => C.omega | 1 => C.zero | 2 => C.one | 3 => C.sequences | 4 => C.expressions
    | 5 => A.height | 6 => A.width | 7 => A.cells | 8 => A.values | _ => Forests
  free _ := C.zero

private def parentStateSchema : Project.Delta0BinarySchema 10 where
  body := Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3)
    (Project.Formula.existsMem (.bound 13) (Project.Formula.existsMem (.bound 14)
      (.conj (codeFormula (.bound 5) (.bound 3) (.bound 1))
        (.conj (codeFormula (.bound 4) (.bound 2) (.bound 0)) (.conj (successorFormula (.bound 2) (.bound 3))
          (parentDecisionFormula ⟨.bound 6,.bound 7,.bound 8,.bound 9,.bound 10⟩
            ⟨.bound 11,.bound 12,.bound 13,.bound 14⟩ (.bound 2) (.bound 1) (.bound 0))))))))
  freeClosed := by
    simp [parentDecisionFormula,matrixRowValuesFormula,selectsFormula,forestFormula,restrictedParentFormula,
      parentCandidateFormula,positiveValueFormula,ancestorFormula,parentPathFormula,ExpressionData.weaken,ExpressionData.map,
      FiniteMatrix.weaken,FiniteMatrix.map,graphFormula,successorFormula,codeFormula,pairFormula,memPairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.conj (codeFormula_delta0 _ _ _) (.conj (successorFormula_delta0 _ _) (parentDecisionFormula_delta0 _ _ _ _ _)))))))

private theorem parentStateSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) (Forests old next : M.Domain) :
    Project.Formula.satisfies (((parentStateEnv C A Forests).push old).push next) parentStateSchema.body ↔ ParentStateNext M C A Forests old next := by
  simp only [parentStateSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,successorFormula_iff he,parentDecisionFormula_iff he]
  rfl

theorem ParentStateNext.coordinates {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} {Forests old next r s P Q : M.Domain}
    (h : ParentStateNext M C A Forests old next) (hOld : Codes M old r P) (hNext : Codes M next s Q) :
    M.SuccessorOf s r ∧ ParentDecision M C A s P Q := by
  obtain ⟨r',_,s',_,P',_,Q',_,hOld',hNext',hSucc,hDecision⟩ := h
  obtain ⟨hrr,hPP⟩ := codes_injective he hOld hOld'
  obtain ⟨hss,hQQ⟩ := codes_injective he hNext hNext'
  subst r'
  subst s'
  subst P'
  subst Q'
  exact ⟨hSucc,hDecision⟩

private theorem parent_state_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests States : M.Domain} (hForests : ∀ P, M.mem P Forests ↔ Forest M C.omega A.width P)
    (hStates : IsProduct M States C.omega Forests) {old : M.Domain} (hOld : M.mem old States) :
    ∃ next, M.mem next States ∧ ParentStateNext M C A Forests old next := by
  obtain ⟨r,hr,P,hP,hOldCode⟩ := (hStates old).mp hOld
  obtain ⟨s,hs,hsNat⟩ := hC.omega.1.2 r hr
  classical
  by_cases hsH : M.mem s A.height
  · obtain ⟨V,hV⟩ := hA.row_view_d hM hsH
    obtain ⟨Q,hQ⟩ := select_forest_exists_d hM false hC ((hForests P).mp hP) hV.graph
    have hQMem := (hForests Q).mpr hQ.forest
    obtain ⟨next,hCode⟩ := codes_total hM s Q
    exact ⟨next,(hStates next).mpr ⟨s,hsNat,Q,hQMem,hCode⟩,r,hr,s,hsNat,P,hP,Q,hQMem,hOldCode,hCode,hs,
      Or.inl ⟨hsH,V,(hC.sequences V).mpr ⟨A.width,hA.width,hV.graph⟩,hV,hQ⟩⟩
  · obtain ⟨next,hCode⟩ := codes_total hM s P
    exact ⟨next,(hStates next).mpr ⟨s,hsNat,P,hP,hCode⟩,r,hr,s,hsNat,P,hP,P,hP,hOldCode,hCode,hs,Or.inr ⟨hsH,rfl⟩⟩

private theorem parent_state_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega) {Forests old x y : M.Domain}
    (hx : ParentStateNext M C A Forests old x) (hy : ParentStateNext M C A Forests old y) : x=y := by
  obtain ⟨r,_,s,_,P,_,Q,_,hOld,hX,hSucc,hCase⟩ := hx
  obtain ⟨r',_,s',_,P',_,Q',_,hOld',hY,hSucc',hCase'⟩ := hy
  obtain ⟨hrr,hPP⟩ := codes_injective hM.1 hOld hOld'
  subst r'
  subst P'
  have hss := Structure.SuccessorOf.eq hM.1 hSucc hSucc'
  subst s'
  have hQQ : Q=Q' := by
    rcases hCase with ⟨hs,V,_,hV,hSel⟩ | ⟨hs,hQP⟩ <;> rcases hCase' with ⟨hs',V',_,hV',hSel'⟩ | ⟨hs',hQP'⟩
    · have hVV := hA.row_view_unique_d hM hs hV hV'
      subst V'
      exact hSel.unique hM.1 hSel'
    · exact False.elim (hs' hs)
    · exact False.elim (hs hs')
    · exact hQP.trans hQP'.symm
  subst Q'
  exact codes_unique hM.1 hX hY

private def stateIndexSchema : Project.UnarySchema 4 where
  body := Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 3)
    (Project.Formula.forallMem (.bound 3) (.imp
      (.conj (memPairFormula (.bound 7) (.bound 3) (.bound 2)) (codeFormula (.bound 2) (.bound 1) (.bound 0)))
      (Project.Formula.extensionalEq (.bound 1) (.bound 3)))))
  freeClosed := by
    simp [codeFormula,pairFormula,memPairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem stateIndexSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H States w Forests i : M.Domain) :
    Project.Formula.satisfies (((((oneEnv H).push States).push w).push Forests).push i) stateIndexSchema.body ↔
      ∀ state, M.mem state States → ∀ r, M.mem r w → ∀ P, M.mem P Forests →
        MemPair M H i state ∧ Codes M state r P → r=i := by
  simp only [stateIndexSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,memPairFormula_iff he,codeFormula_iff he]
  rfl

private def stateRowSchema : Project.Delta0BinarySchema 2 where
  body := Project.Formula.existsMem (.bound 2) (.conj (memPairFormula (.bound 4) (.bound 2) (.bound 0))
    (codeFormula (.bound 0) (.bound 2) (.bound 1)))
  freeClosed := by
    simp [codeFormula,pairFormula,memPairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (codeFormula_delta0 _ _ _))

private theorem stateRowSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H States i P : M.Domain) :
    Project.Formula.satisfies ((((oneEnv H).push States).push i).push P) stateRowSchema.body ↔
      ∃ state, M.mem state States ∧ MemPair M H i state ∧ Codes M state i P := by
  simp only [stateRowSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,codeFormula_iff he]
  rfl

/-- 任意实际有限矩阵都有真实父算法运行；总性由森林空间与对象确定性迭代证明。 -/
theorem matrix_parent_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega) :
    ∃ Forests Rows L, MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L := by
  obtain ⟨Forests,hForests⟩ := forest_space_exists_d hM hC hA.width
  obtain ⟨L,hL⟩ := linear_forest_exists_d hM hC.omega hA.width
  obtain ⟨States,hStates⟩ := product_exists hM C.omega Forests
  have hInitialExists : ∃ Q0, M.mem Q0 Forests ∧ ∀ V, M.mem C.zero A.height →
      MatrixRowValues M C.omega A.width A.cells A.values C.zero V → Selects false M C A.width L V Q0 := by
    classical
    by_cases hzH : M.mem C.zero A.height
    · obtain ⟨V0,hV0⟩ := hA.row_view_d hM hzH
      obtain ⟨Q0,hQ0⟩ := select_forest_exists_d hM false hC hL.1 hV0.graph
      refine ⟨Q0,(hForests Q0).mpr hQ0.forest,?_⟩
      intro V _ hV
      have hVV := hA.row_view_unique_d hM hzH hV hV0
      subst V
      exact hQ0
    · exact ⟨L,(hForests L).mpr hL.1,fun _ hz _ => False.elim (hzH hz)⟩
  obtain ⟨Q0,hQ0,hInitial⟩ := hInitialExists
  obtain ⟨initial,hInitialCode⟩ := codes_total hM C.zero Q0
  have hInitialState := (hStates initial).mpr ⟨C.zero,hC.zero_nat,Q0,hQ0,hInitialCode⟩
  let env := parentStateEnv C A Forests
  obtain ⟨H,hH⟩ := iterator_exists_d hM parentStateSchema env hC.omega hInitialState
    (by
      intro old hOld
      obtain ⟨next,hNext,hNextState⟩ := parent_state_total_d hM hC hA hForests hStates hOld
      exact ⟨next,hNext,(parentStateSchema_iff hM.1 C A Forests old next).mpr hNextState⟩)
    (fun _ _ _ _ _ _ hx hy => parent_state_unique_d hM hA
      ((parentStateSchema_iff hM.1 C A Forests _ _).mp hx) ((parentStateSchema_iff hM.1 C A Forests _ _).mp hy))
  have hStep (i j old next : M.Domain) (hs : M.SuccessorOf j i) (hI : MemPair M H i old) (hJ : MemPair M H j next) :
      ParentStateNext M C A Forests old next := (parentStateSchema_iff hM.1 C A Forests old next).mp (hH.transition i j old next hs hI hJ)
  have hIndices := natural_induction_d hM stateIndexSchema (((oneEnv H).push States).push C.omega |>.push Forests) hC.omega
    (fun zero hEmpty => (stateIndexSchema_iff hM.1 H States C.omega Forests zero).mpr (by
      have hz := hM.1.eq_of_same_members zero C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))
      subst zero
      intro state _ r _ P _ hAnte
      have hState := hH.graph.unique C.zero state initial hAnte.1 (hH.initial C.zero hC.zero_nat hC.zero_empty)
      subst state
      exact (codes_injective hM.1 hAnte.2 hInitialCode).1))
    (fun i hi ih j hs => (stateIndexSchema_iff hM.1 H States C.omega Forests j).mpr (by
      intro state _ r _ P _ hAnte
      obtain ⟨old,hOld,hIOld⟩ := hH.graph.total i hi
      obtain ⟨r0,hr0,P0,hP0,hOldCode⟩ := (hStates old).mp hOld
      have hR0 := (stateIndexSchema_iff hM.1 H States C.omega Forests i).mp ih old hOld r0 hr0 P0 hP0 ⟨hIOld,hOldCode⟩
      subst r0
      exact Structure.SuccessorOf.eq hM.1 ((hStep i j old state hs hIOld hAnte.1).coordinates hM.1 hOldCode hAnte.2).1 hs))
  obtain ⟨AllRows,hSupport,hRaw⟩ := relation_comprehension_d hM stateRowSchema ((oneEnv H).push States) C.omega Forests
  have hRows (i P : M.Domain) : MemPair M AllRows i P ↔ M.mem i C.omega ∧ M.mem P Forests ∧
      ∃ state, M.mem state States ∧ MemPair M H i state ∧ Codes M state i P := by
    simpa only [stateRowSchema_iff hM.1] using hRaw i P
  have hAllRows : Graph M AllRows C.omega Forests := by
    refine ⟨hSupport,?_,?_⟩
    · intro i hi
      obtain ⟨state,hState,hAt⟩ := hH.graph.total i hi
      obtain ⟨r,hr,P,hP,hCode⟩ := (hStates state).mp hState
      have hRI := (stateIndexSchema_iff hM.1 H States C.omega Forests i).mp (hIndices i hi) state hState r hr P hP ⟨hAt,hCode⟩
      subst r
      exact ⟨P,hP,(hRows i P).mpr ⟨hi,hP,state,hState,hAt,hCode⟩⟩
    · intro i P Q hIP hIQ
      obtain ⟨_,_,state,_,hAt,hCode⟩ := (hRows i P).mp hIP
      obtain ⟨_,_,state',_,hAt',hCode'⟩ := (hRows i Q).mp hIQ
      have hStatesEq := hH.graph.unique i state state' hAt hAt'
      subst state'
      exact (codes_injective hM.1 hCode hCode').2
  have hInitialRow : MemPair M AllRows C.zero Q0 := (hRows C.zero Q0).mpr
    ⟨hC.zero_nat,hQ0,initial,hInitialState,hH.initial C.zero hC.zero_nat hC.zero_empty,hInitialCode⟩
  have hHeightSub := (omega_isOrdinal_d hM hC.omega).transitive A.height hA.height
  obtain ⟨Rows,hRowsGraph,hRestricted⟩ := restrict_graph_d hM hAllRows hHeightSub
  refine ⟨Forests,Rows,L,hA.height,hL,hRowsGraph,?_,?_,?_,?_⟩
  · intro _ P hAt
    exact (hForests P).mp (hRowsGraph.bounds hM.1 hAt).2
  · intro r hr
    exact hA.row_view_d hM hr
  · intro Q V hAt hV
    have hQAll := ((hRestricted C.zero Q).mp hAt).2
    have hQQ0 := hAllRows.unique C.zero Q Q0 hQAll hInitialRow
    subst Q
    exact hInitial V (hRowsGraph.bounds hM.1 hAt).1 hV
  · intro i j P Q V hs hI hJ hV
    obtain ⟨_,_,old,_,hIOld,hOldCode⟩ := (hRows i P).mp ((hRestricted i P).mp hI).2
    obtain ⟨_,_,next,_,hJNext,hNextCode⟩ := (hRows j Q).mp ((hRestricted j Q).mp hJ).2
    have hDecision := ((hStep i j old next hs hIOld hJNext).coordinates hM.1 hOldCode hNextCode).2
    rcases hDecision with ⟨hj,V',_,hV',hSel⟩ | ⟨hj,_⟩
    · have hVV := hA.row_view_unique_d hM hj hV' hV
      subst V'
      exact hSel
    · exact False.elim (hj (hRowsGraph.bounds hM.1 hJ).1)

end KP1Y.OneYFinite
