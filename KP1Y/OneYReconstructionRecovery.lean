import KP1Y.OneYReconstructionSelection
import KP1Y.OneYCopyNestingDefs

/-! 从真实重建数值与已证明的逐行选择恢复内部ω运行；随后供复制规范性汇合。 -/
namespace KP1Y.OneYFinite.ReconstructionRecovery
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open ReconstructionCanonical Reconstruction MountainReconstruction
universe u

def rowValuesFormula {n : Nat} (D : GridData (Project.Term n)) (H r V : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula V D.width D.naturals.omega) (.forallE (.forallE
    (.iff (memPairFormula V.weaken.weaken (.bound 1) (.bound 0))
      (paddedCellFormula D.weaken.weaken H.weaken.weaken r.weaken.weaken (.bound 1) (.bound 0)))))

theorem rowValuesFormula_freeClosed {n : Nat} {D : GridData (Project.Term n)} (hD : D.Closed)
    (H r V : Project.Term n) (hH : H.freeSupport=[]) (hr : r.freeSupport=[]) (hV : V.freeSupport=[]) :
    (rowValuesFormula D H r V).FreeClosed := by
  have hCell := paddedCellFormula_freeClosed hD.weaken.weaken H.weaken.weaken r.weaken.weaken (.bound 1) (.bound 0)
    (by simpa using hH) (by simpa using hr) rfl rfl
  simp [rowValuesFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hD.width,hD.naturals.omega,hV,hCell]

theorem rowValuesFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (D : GridData (Project.Term n)) (H r V : Project.Term n) :
    Project.Formula.satisfies e (rowValuesFormula D H r V) ↔ RowValues M (D.eval e) (H.eval e) (r.eval e) (V.eval e) := by
  simp only [rowValuesFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff he,paddedCellFormula_iff he,GridData.eval_weaken,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.graph,h.rows⟩⟩

private def recoveryC : ExpressionData (Project.Term 22) := ⟨.bound 21,.bound 20,.bound 19,.bound 18,.bound 17⟩
private def recoveryX : CopiedMountain.Data (Project.Term 22) := ⟨.bound 16,.bound 15,.bound 14,.bound 13⟩
private def recoveryD : GridData (Project.Term 22) := grid recoveryC recoveryX (.bound 12) (.bound 9) (.bound 8) (.bound 11) (.bound 10)

private def recoverySchema : Project.UnarySchema 19 where
  body := .forallE (.forallE (.imp (rowAtFormula (.bound 6) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
    (.conj (rowValuesFormula recoveryD (.bound 7) (.bound 2) (.bound 1))
      (memPairFormula (.bound 13) (.bound 2) (.bound 0)))))
  freeClosed := by
    have hD : recoveryD.Closed := ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    have hValues := rowValuesFormula_freeClosed hD (.bound 7) (.bound 2) (.bound 1) rfl rfl rfl
    have hAt := rowAtFormula_freeClosed (n := 22) (.bound 6) (.bound 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hValues,hAt,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem]

private def recoveryEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain)
    (Top B Parents Pairs Plus H : M.Domain) (R : RowStateSpace M.Domain) (Run : M.Domain) : Env M 19 :=
  ((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push X.width).push X.heights).push X.forests).push X.parents).push Top).push B).push Parents).push Pairs).push Plus).push H).push R.states).push R.values).push R.forests).push Run

private theorem recoverySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (Top B Parents Pairs Plus H : M.Domain)
    (R : RowStateSpace M.Domain) (Run r : M.Domain) :
    Project.Formula.satisfies ((recoveryEnv C X Top B Parents Pairs Plus H R Run).push r) recoverySchema.body ↔
      ∀ W Q, RowAt M R.states Run r W Q → RowValues M (grid C X Top Pairs Plus B Parents) H r W ∧ MemPair M X.parents r Q := by
  simp only [recoverySchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    rowAtFormula_iff he,Project.Formula.satisfies_conj_iff,rowValuesFormula_iff he,memPairFormula_iff he]
  rfl

theorem row_run_reads_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H V P Run : M.Domain} {R : RowStateSpace M.Domain}
    (hTop : Graph M Top X.width C.omega) (hB : SequenceBound M C X.width X.heights B)
    (hParents : Prefix M Parents X.parents B X.forests) (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hRun : RowRun M C X.width R V P Run) (hBase : RowValues M (grid C X Top Pairs Plus B Parents) H C.zero V)
    (hP : MemPair M X.parents C.zero P)
    (hSelect : ∀ r s V0 V1 F Q, M.mem r C.omega → M.SuccessorOf s r →
      RowValues M (grid C X Top Pairs Plus B Parents) H r V0 → RowValues M (grid C X Top Pairs Plus B Parents) H s V1 →
      MemPair M X.parents r F → MemPair M X.parents s Q → Selects true M C X.width F V1 Q)
    {r W Q : M.Domain} (hAt : RowAt M R.states Run r W Q) :
    RowValues M (grid C X Top Pairs Plus B Parents) H r W ∧ MemPair M X.parents r Q := by
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  have hAll := natural_induction_d hM recoverySchema (recoveryEnv C X Top B Parents Pairs Plus H R Run) hC.omega
    (fun z hz => (recoverySchema_iff hM.1 C X Top B Parents Pairs Plus H R Run z).mpr (by
      intro W Q hAt
      have he := hM.1.eq_of_same_members z C.zero (fun a => ⟨fun h => False.elim (hz a h),fun h => False.elim (hC.zero_empty a h)⟩)
      subst z
      obtain ⟨hWV,hQP⟩ := hRun.at_unique hM.1 hAt (hRun.initial_row_at_d hM)
      subst W
      subst Q
      exact ⟨hBase,hP⟩))
    (fun r hr ih s hSucc => (recoverySchema_iff hM.1 C X Top B Parents Pairs Plus H R Run s).mpr (by
      intro W Q hAt
      obtain ⟨V0,F,hAtOld⟩ := hRun.at_exists_d hr
      obtain ⟨hV0,hF⟩ := (recoverySchema_iff hM.1 C X Top B Parents Pairs Plus H R Run r).mp ih V0 F hAtOld
      have hs := natural_successor_mem_d hM hC hr hSucc
      obtain ⟨W',hW'⟩ := row_values_exists_d hM hD hH hs
      obtain ⟨Q',_,hQ'⟩ := hX.parents.total s hs
      have hNext : RowNext M C X.width V0 F W' Q' :=
        (row_next_iff_selection_d hM hC hPlus hX hTop hB hParents hH hV0 hW' hF hSucc).mpr
          (hSelect r s V0 W' F Q' hr hSucc hV0 hW' hF hQ')
      obtain ⟨hWW,hQQ⟩ := RowNext.unique hM.1 (hRun.at_next hM.1 hSucc hAtOld hAt) hNext
      subst W'
      subst Q'
      exact ⟨hW',hQ'⟩))
  have hr : M.mem r C.omega := by obtain ⟨_,_,hAt,_⟩ := hAt; exact (hRun.graph.bounds hM.1 hAt).1
  exact (recoverySchema_iff hM.1 C X Top B Parents Pairs Plus H R Run r).mp (hAll r hr) W Q hAt

theorem selected_reconstruction_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hSelect : ∀ r s V0 V1 F Q, M.mem r C.omega → M.SuccessorOf s r →
      RowValues M (grid C X Top Pairs Plus B Parents) H r V0 → RowValues M (grid C X Top Pairs Plus B Parents) H s V1 →
      MemPair M X.parents r F → MemPair M X.parents s Q → Selects true M C X.width F V1 Q) :
    ∃ R : RowStateSpace M.Domain, ∃ V P Run, RowRun M C X.width R V P Run ∧
      RowValues M (grid C X Top Pairs Plus B Parents) H C.zero V ∧ MemPair M X.parents C.zero P ∧
      ∀ r W Q, RowAt M R.states Run r W Q → RowValues M (grid C X Top Pairs Plus B Parents) H r W ∧ MemPair M X.parents r Q := by
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  obtain ⟨R,hR⟩ := row_state_space_exists_d hM hC hX.width
  obtain ⟨V,hV⟩ := row_values_exists_d hM hD hH hC.zero_nat
  obtain ⟨P,_,hP⟩ := hX.parents.total C.zero hC.zero_nat
  have hBase := hV.numeric_d hM hC hPlus hX hTop hPositive hB hParents hH hP
  obtain ⟨Run,hRun⟩ := row_run_exists_d hM hC hR hBase
  exact ⟨R,V,P,Run,hRun,hV,hP,fun r W Q hAt => row_run_reads_d hM hC hPlus hX hTop hB hParents hH hRun hV hP hSelect hAt⟩

def DecoratedBlockers (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (Top : M.Domain) : Prop :=
  ∀ r s t F Q c q p, M.SuccessorOf s r → M.SuccessorOf t s → MemPair M X.parents r F → MemPair M X.parents s Q →
    MemPair M F c q → MemPair M Q c p → p≠q →
      ∃ z, M.mem z X.width ∧ (z=q ∨ Ancestor M C X.width Q z q) ∧ MemPair M Q z p ∧
        ∃ tc, M.mem tc C.omega ∧ ∃ tz, M.mem tz C.omega ∧ MemPair M Top c tc ∧ MemPair M Top z tz ∧
          ForestOrder.KeyLE M C X c z t tc tz

private def columnSelectEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m F V Q : M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push F).push V).push Q

private def columnSelectSchema : Project.UnarySchema 9 where
  body := .forallE (.iff (memPairFormula (.bound 2) (.bound 1) (.bound 0))
    (restrictedParentFormula true ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 0)))
  freeClosed := by
    have hRestricted := restrictedParentFormula_freeClosed true
      (show (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hRestricted,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem]

private theorem columnSelectSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m F V Q c : M.Domain) :
    Project.Formula.satisfies ((columnSelectEnv C m F V Q).push c) columnSelectSchema.body ↔
      ∀ p, MemPair M Q c p ↔ RestrictedParent true M C m F V c p := by
  simp only [columnSelectSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    memPairFormula_iff he,restrictedParentFormula_iff he]
  rfl

/-- 内部列归纳解除当前行的严格左前缀，仍只调用更高行的选择接口。 -/
theorem row_selection_of_higher_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H r s V W F Q : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hNested : CopiedMountain.Nested M C X) (hTopBound : ReconstructionSelection.PseudoTopBound M C X Top)
    (hBlockers : DecoratedBlockers M C X Top)
    (hV : RowValues M (grid C X Top Pairs Plus B Parents) H r V)
    (hW : RowValues M (grid C X Top Pairs Plus B Parents) H s W)
    (hF : MemPair M X.parents r F) (hQ : MemPair M X.parents s Q) (hSucc : M.SuccessorOf s r)
    (hHigher : ∀ a b V0 V1 F' Q', M.mem a C.omega → (s=a ∨ M.mem s a) → M.SuccessorOf b a →
      RowValues M (grid C X Top Pairs Plus B Parents) H a V0 → RowValues M (grid C X Top Pairs Plus B Parents) H b V1 →
      MemPair M X.parents a F' → MemPair M X.parents b Q' → Selects true M C X.width F' V1 Q') :
    Selects true M C X.width F W Q := by
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  have hNumeric := hW.numeric_d hM hC hPlus hX hTop hPositive hB hParents hH hQ
  have hForestF := hX.forest r F hF
  have hForestQ := hX.forest s Q hQ
  have hs := (hX.parents.bounds hM.1 hQ).1
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := KP1Y.induction_d hM columnSelectSchema (columnSelectEnv C X.width F W Q) (by
    intro c ih
    apply (columnSelectSchema_iff hM.1 C X.width F W Q c).mpr
    have hPrefix := fun i hi => (columnSelectSchema_iff hM.1 C X.width F W Q i).mp (ih i hi)
    intro p
    classical
    by_cases hc : M.mem c X.width
    · by_cases hSome : ∃ p, MemPair M Q c p
      · obtain ⟨pOld,hCP⟩ := hSome
        have hRestricted : RestrictedParent true M C X.width F W c pOld := by
          obtain ⟨height,hh,hHeight⟩ := hX.heights.total c hc
          have hSH := (hX.source s c height hHeight).mp ⟨pOld,Q,(hX.parents.bounds hM.1 hQ).2,hQ,hCP⟩
          have hRH := (hw.mem hh).transitive s hSH r hSucc.predecessor_mem
          obtain ⟨q,F',_,hF',hCQ⟩ := (hX.source r c height hHeight).mpr hRH
          have he := hX.parents.unique r F' F hF' hF
          subst F'
          by_cases hEq : pOld=q
          · exact ReconstructionSelection.restricted_parent_of_direct_d hM hC hNumeric hForestF hCP (hEq.symm ▸ hCQ)
          · obtain ⟨t,hNext,_⟩ := hC.omega.1.2 s hs
            obtain ⟨z,_,hPath,hZP,tc,_,tz,_,hTC,hTZ,hKey⟩ := hBlockers r s t F Q c q pOld hSucc hNext hF hQ hCQ hCP hEq
            exact ReconstructionSelection.reconstructed_parent_of_key_blocker_d hM hC hPlus hX hTop hPositive hB hParents hH
              hV hW hF hQ hSucc hNext hHigher hCQ hCP (hNested r s F Q hSucc hF hQ c pOld hCP) hPrefix hPath hZP hTC hTZ hKey
        constructor
        · intro hP
          exact (hForestQ.unique c pOld p hCP hP) ▸ hRestricted
        · intro hP
          exact (restricted_parent_unique_d hM true hC hForestF hP hRestricted).symm ▸ hCP
      · have hNone : ∀ p, ¬RestrictedParent true M C X.width F W c p := by
          obtain ⟨height,hh,hHeight⟩ := hX.heights.total c hc
          rcases hw.wellOrder.linear.compare height hh s hs with he | hlt | hgt
          · have he := hM.1.eq_of_same_members height s he
            subst height
            have hNo := ReconstructionSelection.reconstructed_top_no_candidate_d hM hC hPlus hX hTop hPositive hB hParents hH
              hW hF hQ hSucc (hNested r s F Q hSucc hF hQ) hTopBound hHeight hPrefix
            exact fun p hP => hNo ⟨p,hP.1⟩
          · intro p hP
            obtain ⟨x,_,y,_,_,hCY,hXY,_⟩ := hP.1.2
            have hZero := ((hW.rows c y).mp hCY).absent_d hM hD hH hHeight hlt
            exact hC.zero_empty x (hZero ▸ hXY)
          · obtain ⟨p,F',_,hF',hP⟩ := (hX.source s c height hHeight).mpr hgt
            have he := hX.parents.unique s F' Q hF' hQ
            exact False.elim (hSome ⟨p,he ▸ hP⟩)
        exact iff_of_false (fun hP => hSome ⟨p,hP⟩) (hNone p)
    · exact iff_of_false (fun hP => hc (hForestQ.bounds hM.1 hP).1) (fun hP => hc (hP.1.1.bounds hM.1).2))
  exact ⟨hForestF,hW.graph,hForestQ,fun c => (columnSelectSchema_iff hM.1 C X.width F W Q c).mp (hAll c)⟩

private theorem row_selection_above_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H r s W F Q : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hB : SequenceBound M C X.width X.heights B)
    (hParents : Prefix M Parents X.parents B X.forests) (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hW : RowValues M (grid C X Top Pairs Plus B Parents) H s W)
    (hF : MemPair M X.parents r F) (hQ : MemPair M X.parents s Q) (hSucc : M.SuccessorOf s r)
    (hAbove : B=r ∨ M.mem B r) : Selects true M C X.width F W Q := by
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hX.parents.bounds hM.1 hF).1
  have hs := (hX.parents.bounds hM.1 hQ).1
  have hHeightBelow (c height : M.Domain) (hHeight : MemPair M X.heights c height) : M.mem height s := by
    have hHB := hB.value_lt hM.1 hX.heights hHeight
    have hHR : M.mem height r := by
      rcases hAbove with he | hlt
      · exact he ▸ hHB
      · exact (hw.mem hr).transitive B hlt height hHB
    exact (hSucc height).mpr (Or.inl hHR)
  refine ⟨hX.forest r F hF,hW.graph,hX.forest s Q hQ,?_⟩
  intro c p
  apply iff_of_false
  · intro hCP
    obtain ⟨height,hh,hHeight⟩ := hX.heights.total c ((hX.forest s Q hQ).bounds hM.1 hCP).1
    have hSH := (hX.source s c height hHeight).mp ⟨p,Q,(hX.parents.bounds hM.1 hQ).2,hQ,hCP⟩
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) height ((hw.mem hh).transitive s hSH height (hHeightBelow c height hHeight))
  · intro hRestricted
    obtain ⟨height,_,hHeight⟩ := hX.heights.total c (hRestricted.1.1.bounds hM.1).2
    obtain ⟨x,_,y,_,_,hCY,hXY,_⟩ := hRestricted.1.2
    have hZero := ((hW.rows c y).mp hCY).absent_d hM hD hH hHeight (hHeightBelow c height hHeight)
    exact hC.zero_empty x (hZero ▸ hXY)

private def RowSelected (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain)
    (D : GridData M.Domain) (H r : M.Domain) : Prop :=
  ∀ s W F Q, M.SuccessorOf s r → RowValues M D H s W → MemPair M X.parents r F → MemPair M X.parents s Q →
    Selects true M C X.width F W Q

private def rowSelectedFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n))
    (D : GridData (Project.Term n)) (H r : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE (.imp (successorFormula (.bound 3) r.weaken.weaken.weaken.weaken)
    (.imp (rowValuesFormula D.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))
      (.imp (memPairFormula X.parents.weaken.weaken.weaken.weaken r.weaken.weaken.weaken.weaken (.bound 1))
        (.imp (memPairFormula X.parents.weaken.weaken.weaken.weaken (.bound 3) (.bound 0))
          (selectsFormula true C.weaken.weaken.weaken.weaken X.width.weaken.weaken.weaken.weaken (.bound 1) (.bound 2) (.bound 0)))))))))

private theorem rowSelectedFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : CopiedMountain.Data (Project.Term n)} (hX : X.Closed) {D : GridData (Project.Term n)} (hD : D.Closed)
    (H r : Project.Term n) (hH : H.freeSupport=[]) (hr : r.freeSupport=[]) : (rowSelectedFormula C X D H r).FreeClosed := by
  have hV := rowValuesFormula_freeClosed hD.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken (.bound 3) (.bound 2)
    (by simpa using hH) rfl rfl
  have hS := selectsFormula_freeClosed true hC.weaken.weaken.weaken.weaken X.width.weaken.weaken.weaken.weaken
    (.bound 1) (.bound 2) (.bound 0) (by simpa using hX.width) rfl rfl rfl
  simp [rowSelectedFormula,Definitional.Formula.FreeClosed,hV,hS,successorFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,hr,hX.parents]

private theorem rowSelectedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n)) (D : GridData (Project.Term n)) (H r : Project.Term n) :
    Project.Formula.satisfies e (rowSelectedFormula C X D H r) ↔ RowSelected M (C.eval e) (X.eval e) (D.eval e) (H.eval e) (r.eval e) := by
  simp only [rowSelectedFormula,RowSelected,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    successorFormula_iff he,rowValuesFormula_iff he,memPairFormula_iff he,selectsFormula_iff he,
    ExpressionData.eval_weaken,GridData.eval_weaken,Term.eval_weaken]
  rfl

private def rowFuelC : ExpressionData (Project.Term 18) := ⟨.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩
private def rowFuelX : CopiedMountain.Data (Project.Term 18) := ⟨.bound 12,.bound 11,.bound 10,.bound 9⟩
private def rowFuelD : GridData (Project.Term 18) := grid rowFuelC rowFuelX (.bound 8) (.bound 5) (.bound 4) (.bound 7) (.bound 6)

private def rowFuelSchema : Project.UnarySchema 15 where
  body := .forallE (.forallE (.imp (.mem (.bound 1) (.bound 17)) (.imp (.mem (.bound 0) (.bound 17))
    (.imp (addAtFormula (.bound 5) (.bound 4) (.bound 1) (.bound 2) (.bound 0))
      (.imp (.disj (Project.Formula.extensionalEq (.bound 7) (.bound 0)) (.mem (.bound 7) (.bound 0)))
        (rowSelectedFormula rowFuelC rowFuelX rowFuelD (.bound 3) (.bound 1)))))))
  freeClosed := by
    have hC : rowFuelC.Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hX : rowFuelX.Closed := ⟨rfl,rfl,rfl,rfl⟩
    have hD : rowFuelD.Closed := ⟨hC,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    have hRow := rowSelectedFormula_freeClosed hC hX hD (.bound 3) (.bound 1) rfl rfl
    simp [Definitional.Formula.FreeClosed,hRow,addAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem]

private def rowFuelEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain)
    (Top B Parents Pairs Plus H : M.Domain) : Env M 15 :=
  ((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push X.width).push X.heights).push X.forests).push X.parents).push Top).push B).push Parents).push Pairs).push Plus).push H

private theorem rowFuelSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (Top B Parents Pairs Plus H fuel : M.Domain) :
    Project.Formula.satisfies ((rowFuelEnv C X Top B Parents Pairs Plus H).push fuel) rowFuelSchema.body ↔
      ∀ r sum, M.mem r C.omega → M.mem sum C.omega → AddAt M Pairs Plus r fuel sum → (B=sum ∨ M.mem B sum) →
        RowSelected M C X (grid C X Top Pairs Plus B Parents) H r := by
  simp only [rowFuelSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    addAtFormula_iff he,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,rowSelectedFormula_iff he]
  rfl

/-- 有限高度界驱动的对象行归纳，解除所有higher-selection；列前缀已由内层对象归纳解除。 -/
theorem structural_reconstruction_selects_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hNested : CopiedMountain.Nested M C X) (hTopBound : ReconstructionSelection.PseudoTopBound M C X Top)
    (hBlockers : DecoratedBlockers M C X Top)
    {r s W F Q : M.Domain} (hW : RowValues M (grid C X Top Pairs Plus B Parents) H s W)
    (hF : MemPair M X.parents r F) (hQ : MemPair M X.parents s Q) (hSucc : M.SuccessorOf s r) : Selects true M C X.width F W Q := by
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM rowFuelSchema (rowFuelEnv C X Top B Parents Pairs Plus H) hC.omega
    (fun z hz => (rowFuelSchema_iff hM.1 C X Top B Parents Pairs Plus H z).mpr (by
      intro r sum hr _ hAdd hAbove s W F Q hSucc hW hF hQ
      have he0 := hM.1.eq_of_same_members z C.zero (fun a => ⟨fun h => False.elim (hz a h),fun h => False.elim (hC.zero_empty a h)⟩)
      subst z
      have heSum := hPlus.add_unique hM.1 hAdd ((hPlus.add_iff_sum hM hr hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM r hC.zero_empty))
      subst sum
      exact row_selection_above_bound_d hM hC hPlus hX hTop hB hParents hH hW hF hQ hSucc hAbove))
    (fun fuel hFuel ih next hFuelSucc => (rowFuelSchema_iff hM.1 C X Top B Parents Pairs Plus H next).mpr (by
      intro r sum hr hSumNat hAdd hAbove s W F Q hSucc hW hF hQ
      obtain ⟨V,hV⟩ := row_values_exists_d hM hD hH hr
      apply row_selection_of_higher_d hM hC hPlus hX hTop hPositive hB hParents hH hNested hTopBound hBlockers hV hW hF hQ hSucc
      intro a b V0 V1 F' Q' ha hSA hAB _ hV1 hF' hQ'
      have hs := natural_successor_mem_d hM hC hr hSucc
      obtain ⟨oldSum,hOldSumNat,hOldSum⟩ := hPlus.add_exists_d hM hC hr hFuel
      obtain ⟨sSum,hSSumNat,hSSum⟩ := hPlus.add_exists_d hM hC hs hFuel
      have hSumOld := KP1Y.Arithmetic.sum_successor_d hM hFuelSucc ((hPlus.add_iff_sum hM hr hFuel).mp hOldSum)
        ((hPlus.add_iff_sum hM hr (natural_successor_mem_d hM hC hFuel hFuelSucc)).mp hAdd)
      have hSumS := natural_sum_left_successor_d hM hC hFuel hSucc ((hPlus.add_iff_sum hM hr hFuel).mp hOldSum)
        ((hPlus.add_iff_sum hM hs hFuel).mp hSSum)
      have he := Structure.SuccessorOf.eq hM.1 hSumS hSumOld
      subst sSum
      obtain ⟨aSum,hASumNat,hASum⟩ := hPlus.add_exists_d hM hC ha hFuel
      have hSumLe : sum=aSum ∨ M.mem sum aSum := by
        rcases hSA with he | hlt
        · subst a
          exact Or.inl (hPlus.add_unique hM.1 hSSum hASum)
        · exact Or.inr (natural_sum_strict_left_d hM hC hs ha hFuel
            ((hPlus.add_iff_sum hM hs hFuel).mp hSSum) ((hPlus.add_iff_sum hM ha hFuel).mp hASum) hlt)
      have hBLe : B=aSum ∨ M.mem B aSum := by
        rcases hAbove with he | hlt
        · exact he.symm ▸ hSumLe
        · rcases hSumLe with he | hgt
          · exact Or.inr (he ▸ hlt)
          · exact Or.inr ((hw.mem hASumNat).transitive sum hgt B hlt)
      exact (rowFuelSchema_iff hM.1 C X Top B Parents Pairs Plus H fuel).mp ih a aSum ha hASumNat hASum hBLe b V1 F' Q' hAB hV1 hF' hQ'))
  have hr := (hX.parents.bounds hM.1 hF).1
  obtain ⟨sum,hSumNat,hSum⟩ := hPlus.add_exists_d hM hC hr hB.1.1
  have hBLe : B=sum ∨ M.mem B sum := ordinal_subset_cases_d hM (hw.mem hB.1.1) (hw.mem hSumNat)
    (KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hB.1.1)
      (natural_sum_comm_d hM hC hr hB.1.1 ((hPlus.add_iff_sum hM hr hB.1.1).mp hSum)))
  exact (rowFuelSchema_iff hM.1 C X Top B Parents Pairs Plus H B).mp (hAll B hB.1.1) r sum hr hSumNat hSum hBLe s W F Q hSucc hW hF hQ

theorem run_metadata_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H V P Run : M.Domain} {R : RowStateSpace M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H) (hRun : RowRun M C X.width R V P Run)
    (hBase : RowValues M (grid C X Top Pairs Plus B Parents) H C.zero V)
    (hRead : ∀ r W Q, RowAt M R.states Run r W Q → RowValues M (grid C X Top Pairs Plus B Parents) H r W ∧ MemPair M X.parents r Q) :
    (∀ c v, MemPair M V c v → M.mem C.zero v) ∧ CopiedMountain.FromRun M C X.width R V Run X ∧
      TopValueGraph M C X.width R Run X.heights Top ∧
      ∀ r, M.mem r C.omega → ∀ c v, RowValue M R.states R.values R.forests Run r c v ↔
        PaddedCell M (grid C X Top Pairs Plus B Parents) H r c v := by
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  have hw := omega_isOrdinal_d hM hC.omega
  have hValue (r : M.Domain) (hr : M.mem r C.omega) (c v : M.Domain) :
      RowValue M R.states R.values R.forests Run r c v ↔ PaddedCell M (grid C X Top Pairs Plus B Parents) H r c v := by
    constructor
    · rintro ⟨W,_,Q,_,hAt,hV⟩
      exact ((hRead r W Q hAt).1.rows c v).mp hV
    · intro hCell
      obtain ⟨W,Q,hAt⟩ := hRun.at_exists_d hr
      have hNum := hRun.at_numeric_d hM hC hAt
      exact ⟨W,(hRun.space.values W).mpr hNum.values,Q,(hRun.space.forests Q).mpr hNum.forest,hAt,
        ((hRead r W Q hAt).1.rows c v).mpr hCell⟩
  have hBasePositive (c v : M.Domain) (hV : MemPair M V c v) : M.mem C.zero v := by
    obtain ⟨height,hh,hHeight⟩ := hX.heights.total c (hBase.graph.bounds hM.1 hV).1
    obtain ⟨top,_,hTopAt⟩ := hTop.total c (hBase.graph.bounds hM.1 hV).1
    have hZeroLe : C.zero=height ∨ M.mem C.zero height := by
      classical
      by_cases he : height=C.zero
      · exact Or.inl he.symm
      · exact Or.inr ((hC.zero_mem_iff hM hh).mpr he)
    exact ((hBase.rows c v).mp hV).live_positive_d hM hD hH hHeight hTopAt (hPositive c top hTopAt) hZeroLe
  have hHeightMeaning (c height : M.Domain) (hHeight : MemPair M X.heights c height) : HeightAt M C R V Run c height := by
    obtain ⟨actual,hActual⟩ := height_at_exists_d hM hC hRun (hX.heights.bounds hM.1 hHeight).1
    obtain ⟨base,_,hBaseValue⟩ := hRun.base.values.total c (hX.heights.bounds hM.1 hHeight).1
    have hPositiveBase := hBasePositive c base hBaseValue
    have hParentsAt (r : M.Domain) (hr : M.mem r C.omega) : M.mem r actual ↔ M.mem r height := by
      obtain ⟨W,Q,hAt⟩ := hRun.at_exists_d hr
      have hQ := (hRead r W Q hAt).2
      have hRows : (∃ p, MemPair M Q c p) ↔ ∃ p, CopiedMountain.ParentAt M X r c p := by
        constructor
        · rintro ⟨p,hP⟩
          exact ⟨p,Q,(hX.parents.bounds hM.1 hQ).2,hQ,hP⟩
        · rintro ⟨p,Q',_,hQ',hP⟩
          exact ⟨p,hX.parents.unique r Q' Q hQ' hQ ▸ hP⟩
      exact (hRun.parent_iff_lt_height_d hM hC hAt hBaseValue hPositiveBase hActual).symm.trans
        (hRows.trans (hX.source r c height hHeight))
    have he := hM.1.eq_of_same_members actual height (fun r => ⟨fun hr =>
      (hParentsAt r (hw.transitive actual (hActual.natural_d hM hC) r hr)).mp hr,
      fun hr => (hParentsAt r (hw.transitive height (hX.heights.bounds hM.1 hHeight).2 r hr)).mpr hr⟩)
    exact he ▸ hActual
  have hHeights : HeightGraph M C X.width R V Run X.heights := by
    refine ⟨hX.heights,fun c height => ?_⟩
    constructor
    · intro h
      exact ⟨(hX.heights.bounds hM.1 h).1,hHeightMeaning c height h⟩
    · rintro ⟨hc,hAt⟩
      obtain ⟨height',_,hHeight⟩ := hX.heights.total c hc
      have he := hAt.unique_d hM hC hRun.base.values (hHeightMeaning c height' hHeight)
      exact he.symm ▸ hHeight
  have hFrom : CopiedMountain.FromRun M C X.width R V Run X := by
    refine ⟨rfl,hHeights,?_⟩
    intro r F
    constructor
    · intro hF
      obtain ⟨W,Q,hAt⟩ := hRun.at_exists_d (hX.parents.bounds hM.1 hF).1
      have he := hX.parents.unique r Q F (hRead r W Q hAt).2 hF
      exact ⟨W,he ▸ hAt⟩
    · rintro ⟨W,hAt⟩
      exact (hRead r W F hAt).2
  refine ⟨hBasePositive,hFrom,?_,hValue⟩
  refine ⟨hTop,fun c v => ?_⟩
  constructor
  · intro hTopAt
    obtain ⟨height,hh,hHeight⟩ := hX.heights.total c (hTop.bounds hM.1 hTopAt).1
    obtain ⟨x,hCell⟩ := padded_cell_exists_d hM hD hH hh (hTop.bounds hM.1 hTopAt).1
    have he := ReconstructionOrder.padded_top_value_d hM hD hH hCell hHeight hTopAt
    exact ⟨height,hh,hHeight,(hValue height hh c v).mpr (he ▸ hCell)⟩
  · rintro ⟨height,hh,hHeight,hValueAt⟩
    obtain ⟨top,_,hTopAt⟩ := hTop.total c (hX.heights.bounds hM.1 hHeight).1
    have he := ReconstructionOrder.padded_top_value_d hM hD hH ((hValue height hh c v).mp hValueAt) hHeight hTopAt
    exact he.symm ▸ hTopAt

/-- 已计算底图F的完整内部运行及真实高度/Top元数据，不返回另一个任意底图。 -/
theorem rebuild_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top Bottom : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hRebuild : Rebuilds M C Pairs Plus X Top Bottom)
    (hSelect : ∀ B Parents H, SequenceBound M C X.width X.heights B → Prefix M Parents X.parents B X.forests →
      Reconstructs M (grid C X Top Pairs Plus B Parents) H → ∀ r s W F Q,
      RowValues M (grid C X Top Pairs Plus B Parents) H s W → MemPair M X.parents r F → MemPair M X.parents s Q →
      M.SuccessorOf s r → Selects true M C X.width F W Q) :
    ∃ R : RowStateSpace M.Domain, ∃ P Run, RowRun M C X.width R Bottom P Run ∧
      CopiedMountain.FromRun M C X.width R Bottom Run X ∧ TopValueGraph M C X.width R Run X.heights Top ∧
      (∀ c v, MemPair M Bottom c v → M.mem C.zero v) := by
  obtain ⟨B,Parents,H,hB,hParents,hH,hBottom⟩ := hRebuild
  obtain ⟨R,V,P,Run,hRun,hV,hP,hRead⟩ := selected_reconstruction_run_exists_d hM hC hPlus hX hTop hPositive hB hParents hH
    (fun r s _ W F Q _ hSucc _ hW hF hQ => hSelect B Parents H hB hParents hH r s W F Q hW hF hQ hSucc)
  have he : V=Bottom := hV.graph.ext hM.1 hBottom.graph (fun c hc v => by
    rw [hV.rows,hBottom.rows]
    constructor
    · exact fun h => h.inside hB.1.2.1
    · exact fun h => ⟨hC.zero_nat,hc,Or.inl h⟩)
  subst V
  obtain ⟨hPositiveBottom,hFrom,hTopRun,_⟩ := run_metadata_d hM hC hPlus hX hTop hPositive hB hParents hH hRun hV hRead
  exact ⟨R,P,Run,hRun,hFrom,hTopRun,hPositiveBottom⟩

theorem structural_rebuild_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top Bottom : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hRebuild : Rebuilds M C Pairs Plus X Top Bottom) (hNested : CopiedMountain.Nested M C X)
    (hTopBound : ReconstructionSelection.PseudoTopBound M C X Top) (hBlockers : DecoratedBlockers M C X Top) :
    ∃ R : RowStateSpace M.Domain, ∃ P Run, RowRun M C X.width R Bottom P Run ∧
      CopiedMountain.FromRun M C X.width R Bottom Run X ∧ TopValueGraph M C X.width R Run X.heights Top ∧
      (∀ c v, MemPair M Bottom c v → M.mem C.zero v) :=
  rebuild_run_exists_d hM hC hPlus hX hTop hPositive hRebuild (fun _B _Parents _H hB hParents hH _r _s _W _F _Q hW hF hQ hSucc =>
    structural_reconstruction_selects_d hM hC hPlus hX hTop hPositive hB hParents hH hNested hTopBound hBlockers hW hF hQ hSucc)

end KP1Y.OneYFinite.ReconstructionRecovery
