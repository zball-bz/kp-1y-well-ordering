import KP1Y.OneYMountainReconstruction
import KP1Y.AssignmentUpdate

/-! 对实际有限山形代码家族作倒序数值重建。塔历史是实际有限函数图，B处外接顶部行。 -/
namespace KP1Y.OneYFinite.TowerReconstruction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u

abbrev StepAt (M : SetTheory.Structure.{u}) (Keys Step i upper lower : M.Domain) : Prop := AddAt M Keys Step i upper lower

structure StepTable (M : SetTheory.Structure.{u}) (B Rows Keys Step : M.Domain) : Prop where
  keys : IsProduct M Keys B Rows
  graph : Graph M Step Keys Rows

theorem StepTable.total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {B Rows Keys Step i upper : M.Domain}
    (h : StepTable M B Rows Keys Step) (hi : M.mem i B) (hUpper : M.mem upper Rows) :
    ∃lower, M.mem lower Rows ∧ StepAt M Keys Step i upper lower := by
  obtain ⟨key,hCode⟩ := codes_total hM i upper
  have hk := (h.keys key).mpr ⟨i,hi,upper,hUpper,hCode⟩
  obtain ⟨lower,hl,hAt⟩ := h.graph.total key hk
  exact ⟨lower,hl,key,hk,hCode,hAt⟩

theorem StepTable.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {B Rows Keys Step i upper lower lower' : M.Domain}
    (h : StepTable M B Rows Keys Step) (hL : StepAt M Keys Step i upper lower) (hL' : StepAt M Keys Step i upper lower') : lower=lower' := by
  obtain ⟨key,_,hCode,hAt⟩ := hL
  obtain ⟨key',_,hCode',hAt'⟩ := hL'
  have hkk := codes_unique he hCode hCode'
  subst key'
  exact h.graph.unique key lower lower' hAt hAt'

structure Tail (M : SetTheory.Structure.{u}) (Rows B N Top Keys Step start H : M.Domain) : Prop where
  graph : Graph M H N Rows
  top : MemPair M H B Top
  transition : ∀i, M.mem i B → ∀j, M.mem j N → (start=i ∨ M.mem start i) → M.SuccessorOf j i →
    ∀upper, M.mem upper Rows → ∀lower, M.mem lower Rows → MemPair M H j upper → MemPair M H i lower → StepAt M Keys Step i upper lower

def tailFormula {n : Nat} (Rows B N Top Keys Step start H : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula H N Rows) (.conj (memPairFormula H B Top)
    (Project.Formula.forallMem B (Project.Formula.forallMem N.weaken (Project.Formula.forallMem Rows.weaken.weaken
      (Project.Formula.forallMem Rows.weaken.weaken.weaken
        (.imp (.conj (.disj (Project.Formula.extensionalEq start.weaken.weaken.weaken.weaken (.bound 3)) (.mem start.weaken.weaken.weaken.weaken (.bound 3)))
          (.conj (successorFormula (.bound 2) (.bound 3)) (.conj (memPairFormula H.weaken.weaken.weaken.weaken (.bound 2) (.bound 1))
            (memPairFormula H.weaken.weaken.weaken.weaken (.bound 3) (.bound 0)))))
          (addAtFormula Keys.weaken.weaken.weaken.weaken Step.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (.bound 0))))))))

theorem tailFormula_delta0 {n : Nat} (Rows B N Top Keys Step start H : Project.Term n) : (tailFormula Rows B N Top Keys Step start H).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (.conj (.disj (.atom _ _ _) (.mem _ _)) (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))
      (addAtFormula_delta0 _ _ _ _ _)))))))

theorem tailFormula_freeClosed {n : Nat} (Rows B N Top Keys Step start H : Project.Term n)
    (hRows : Rows.freeSupport=[]) (hB : B.freeSupport=[]) (hN : N.freeSupport=[]) (hTop : Top.freeSupport=[])
    (hKeys : Keys.freeSupport=[]) (hStep : Step.freeSupport=[]) (hStart : start.freeSupport=[]) (hH : H.freeSupport=[]) :
    (tailFormula Rows B N Top Keys Step start H).FreeClosed := by
  simp [tailFormula,addAtFormula,successorFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hRows,hB,hN,hTop,hKeys,hStep,hStart,hH]

theorem tailFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (Rows B N Top Keys Step start H : Project.Term n) : Project.Formula.satisfies e (tailFormula Rows B N Top Keys Step start H) ↔
      Tail M (Rows.eval e) (B.eval e) (N.eval e) (Top.eval e) (Keys.eval e) (Step.eval e) (start.eval e) (H.eval e) := by
  simp only [tailFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,memPairFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,successorFormula_iff he,addAtFormula_iff he,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,fun i hi j hj hge hs upper hu lower hl hU hL => h.2.2 i hi j hj upper hu lower hl ⟨hge,hs,hU,hL⟩⟩,
    fun h => ⟨h.graph,h.top,fun i hi j hj upper hu lower hl hs => h.transition i hi j hj hs.1 hs.2.1 upper hu lower hl hs.2.2.1 hs.2.2.2⟩⟩

private def constantSchema : Project.Delta0BinarySchema 1 where
  body := Project.Formula.extensionalEq (.bound 0) (.bound 2)
  freeClosed := by simp
  delta0 := .atom _ _ _

theorem constant_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {Rows Top : M.Domain} (N : M.Domain)
    (hTop : M.mem Top Rows) : ∃H, Graph M H N Rows ∧ ∀i v, MemPair M H i v ↔ M.mem i N ∧ v=Top := by
  obtain ⟨H,hSupport,hRaw⟩ := relation_comprehension_d hM constantSchema (oneEnv Top) N Rows
  have hRows (i v : M.Domain) : MemPair M H i v ↔ M.mem i N ∧ v=Top := by
    have hφ : Project.Formula.satisfies (((oneEnv Top).push i).push v) constantSchema.body ↔ v=Top :=
      Project.Formula.satisfies_extensionalEq_iff_eq hM.1 _ _ _
    rw [hRaw i v,hφ]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.symm ▸ hTop,h.2⟩⟩
  refine ⟨H,⟨hSupport,fun i hi => ⟨Top,hTop,(hRows i Top).mpr ⟨hi,rfl⟩⟩,?_⟩,hRows⟩
  exact fun i x y hx hy => ((hRows i x).mp hx).2.trans ((hRows i y).mp hy).2.symm

private def hasTailSchema : Project.Delta0UnarySchema 7 where
  body := Project.Formula.existsMem (.bound 1) (tailFormula (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 0))
  freeClosed := by
    have h := tailFormula_freeClosed (n := 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl rfl rfl rfl
    simpa [Project.Formula.existsMem,Definitional.Formula.FreeClosed] using h
  delta0 := .existsMem _ (tailFormula_delta0 _ _ _ _ _ _ _ _)

private def tailEnv {M : SetTheory.Structure.{u}} (Rows B N Top Keys Step Histories : M.Domain) : Env M 7 :=
  ((((((oneEnv Rows).push B).push N).push Top).push Keys).push Step).push Histories

private theorem hasTailSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (Rows B N Top Keys Step Histories start : M.Domain) :
    Project.Formula.satisfies ((tailEnv Rows B N Top Keys Step Histories).push start) hasTailSchema.body ↔
      ∃H, M.mem H Histories ∧ Tail M Rows B N Top Keys Step start H := by
  simp only [hasTailSchema,Project.Formula.satisfies_existsMem_iff,tailFormula_iff he]
  rfl

private theorem successor_le_of_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {w k j i : M.Domain}
    (hw : M.IsOmega w) (hk : M.mem k w) (hi : M.mem i w) (hs : M.SuccessorOf j k) (hki : M.mem k i) : j=i ∨ M.mem j i := by
  obtain ⟨j',hs',hj'⟩ := hw.1.2 k hk
  have hj : M.mem j w := (Structure.SuccessorOf.eq hM.1 hs hs').symm ▸ hj'
  apply ordinal_subset_cases_d hM ((omega_isOrdinal_d hM hw).mem hj) ((omega_isOrdinal_d hM hw).mem hi)
  intro x hx
  rcases (hs x).mp hx with hxk | he
  · exact ((omega_isOrdinal_d hM hw).mem hi).transitive k hki x hxk
  · exact (hM.1.eq_of_same_members x k he).symm ▸ hki

theorem Tail.extend_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Rows B N Top Keys Step k j H : M.Domain}
    (hB : M.mem B C.omega) (hN : M.SuccessorOf N B) (hTable : StepTable M B Rows Keys Step)
    (hk : M.mem k B) (hj : M.mem j C.omega) (hSucc : M.SuccessorOf j k) (hjLe : M.MemberSubset j B)
    (h : Tail M Rows B N Top Keys Step j H) : ∃G, Tail M Rows B N Top Keys Step k G := by
  have hOrd := omega_isOrdinal_d hM hC.omega
  have hNN := natural_successor_mem_d hM hC hB hN
  have hkω := hOrd.transitive B hB k hk
  have hkN := (hN k).mpr (.inl hk)
  have hjN : M.mem j N := by
    rcases ordinal_subset_cases_d hM (hOrd.mem hj) (hOrd.mem hB) hjLe with he | hjB
    · exact he.symm ▸ hN.predecessor_mem
    · exact (hN j).mpr (.inl hjB)
  obtain ⟨upper,hUpper,hUpperAt⟩ := h.graph.total j hjN
  obtain ⟨lower,hLower,hStep⟩ := hTable.total_d hM hk hUpper
  obtain ⟨G,hG⟩ := KP1Y.Assignments.update_exists_d hM h.graph hLower (i := k)
  have hOld (i v : M.Domain) (hi : M.mem i N) (hv : M.mem v Rows) (hne : i≠k) :
      MemPair M G i v ↔ MemPair M H i v := (hG.rows i hi v hv).trans
    ⟨fun h => h.elim (fun h => False.elim (hne h.1)) And.right,fun h => .inr ⟨hne,h⟩⟩
  have hBk : B≠k := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) B (he.symm ▸ hk)
  refine ⟨G,hG.graph,(hOld B Top hN.predecessor_mem (h.graph.bounds hM.1 h.top).2 hBk).mpr h.top,?_⟩
  intro i hi s hsN hki hs u hu v hv hU hV
  by_cases hik : i=k
  · subst i
    have hsj := Structure.SuccessorOf.eq hM.1 hs hSucc
    subst s
    have hjk : j≠k := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) k (he ▸ hSucc.predecessor_mem)
    have huUpper := h.graph.unique j u upper ((hOld j u hjN hu hjk).mp hU) hUpperAt
    have hvLower : v=lower := by
      rcases (hG.rows k hkN v hv).mp hV with hNew | hOld
      · exact hNew.2
      · exact False.elim (hOld.1 rfl)
    exact huUpper.symm ▸ hvLower.symm ▸ hStep
  · have hki' : M.mem k i := hki.resolve_left (fun he => hik he.symm)
    have hiω := hOrd.transitive B hB i hi
    have hji := successor_le_of_lt_d hM hC.omega hkω hiω hSucc hki'
    have hikN := (hN i).mpr (.inl hi)
    have hsk : s≠k := by
      intro he
      have hks := (hOrd.mem (hOrd.transitive N hNN s hsN)).transitive i hs.predecessor_mem k hki'
      exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) k (he ▸ hks)
    exact h.transition i hi s hsN hji hs u hu v hv ((hOld s u hsN hu hsk).mp hU) ((hOld i v hikN hv hik).mp hV)

theorem tail_history_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Rows B N Top Keys Step : M.Domain}
    (hB : M.mem B C.omega) (hN : M.SuccessorOf N B) (hTable : StepTable M B Rows Keys Step) (hTop : M.mem Top Rows) :
    ∃H, Tail M Rows B N Top Keys Step C.zero H := by
  have hNN := natural_successor_mem_d hM hC hB hN
  obtain ⟨Histories,hHistories⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hC.omega Rows
  have hAll := bounded_backward_induction_d hM hasTailSchema (tailEnv Rows B N Top Keys Step Histories) hC.omega hB
    ((hasTailSchema_iff hM.1 Rows B N Top Keys Step Histories B).mpr (by
      obtain ⟨H,hH,hRows⟩ := constant_graph_exists_d hM N hTop
      refine ⟨H,(hHistories H).mpr ⟨N,hNN,hH⟩,hH,(hRows B Top).mpr ⟨hN.predecessor_mem,rfl⟩,?_⟩
      intro i hi s _ hBi
      rcases hBi with he | hBi
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) B (he.symm ▸ hi))
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) B (((omega_isOrdinal_d hM hC.omega).mem hB).transitive i hi B hBi))))
    (fun k hk j hj hs hjLe ih => (hasTailSchema_iff hM.1 Rows B N Top Keys Step Histories k).mpr (by
      obtain ⟨H,_,hH⟩ := (hasTailSchema_iff hM.1 Rows B N Top Keys Step Histories j).mp ih
      obtain ⟨G,hG⟩ := hH.extend_d hM hC hB hN hTable hk hj hs hjLe
      exact ⟨G,(hHistories G).mpr ⟨N,hNN,hG.graph⟩,hG⟩))
  have hz : C.zero=B ∨ M.mem C.zero B := by
    by_cases he : B=C.zero
    · exact .inl he.symm
    · exact .inr ((hC.zero_mem_iff hM hB).mpr he)
  obtain ⟨H,_,hH⟩ := (hasTailSchema_iff hM.1 Rows B N Top Keys Step Histories C.zero).mp (hAll C.zero hz)
  exact ⟨H,hH⟩

theorem Tail.step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Rows B N Top Keys Step H i j upper lower : M.Domain}
    (hB : M.mem B C.omega) (h : Tail M Rows B N Top Keys Step C.zero H) (hi : M.mem i B) (hj : M.mem j N)
    (hs : M.SuccessorOf j i) (hU : MemPair M H j upper) (hL : MemPair M H i lower) : StepAt M Keys Step i upper lower := by
  have hiω := (omega_isOrdinal_d hM hC.omega).transitive B hB i hi
  have hzi : C.zero=i ∨ M.mem C.zero i := by
    by_cases he : i=C.zero
    · exact .inl he.symm
    · exact .inr ((hC.zero_mem_iff hM hiω).mpr he)
  exact h.transition i hi j hj hzi hs upper (h.graph.bounds hM.1 hU).2 lower (h.graph.bounds hM.1 hL).2 hU hL

private def compareHistorySchema : Project.Delta0UnarySchema 5 where
  body := Project.Formula.forallMem (.bound 5) (Project.Formula.forallMem (.bound 5)
    (.imp (.conj (memPairFormula (.bound 5) (.bound 2) (.bound 1)) (memPairFormula (.bound 4) (.bound 2) (.bound 0)))
      (memPairFormula (.bound 3) (.bound 1) (.bound 0))))
  freeClosed := by simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.forallMem _ (.imp (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (memPairFormula_delta0 _ _ _)))

private theorem compareHistorySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (Rows Rows' H J Good i : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv Rows).push Rows').push H).push J).push Good).push i) compareHistorySchema.body ↔
      ∀u, M.mem u Rows → ∀v, M.mem v Rows' → MemPair M H i u → MemPair M J i v → MemPair M Good u v := by
  simp only [compareHistorySchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he]
  exact ⟨fun h u hu v hv hU hV => h u hu v hv ⟨hU,hV⟩,fun h u hu v hv hs => h u hu v hv hs.1 hs.2⟩

/-- 两条实际倒序历史的逐层关系归纳；Good是一个实际关系集合。 -/
theorem Tail.compare_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Rows Rows' B N Top Top' Keys Keys' Step Step' H J Good : M.Domain}
    (hB : M.mem B C.omega) (hN : M.SuccessorOf N B)
    (hH : Tail M Rows B N Top Keys Step C.zero H) (hJ : Tail M Rows' B N Top' Keys' Step' C.zero J)
    (hTop : MemPair M Good Top Top')
    (hPreserve : ∀i, M.mem i B → ∀u, M.mem u Rows → ∀v, M.mem v Rows' → ∀a, M.mem a Rows → ∀b, M.mem b Rows' →
      StepAt M Keys Step i u a → StepAt M Keys' Step' i v b → MemPair M Good u v → MemPair M Good a b) :
    ∀i, M.mem i N → ∀u v, MemPair M H i u → MemPair M J i v → MemPair M Good u v := by
  let e := ((((oneEnv Rows).push Rows').push H).push J).push Good
  have hAll := bounded_backward_induction_d hM compareHistorySchema e hC.omega hB
    ((compareHistorySchema_iff hM.1 Rows Rows' H J Good B).mpr (by
      intro u _ v _ hU hV
      have hu := hH.graph.unique B u Top hU hH.top
      have hv := hJ.graph.unique B v Top' hV hJ.top
      exact hu.symm ▸ hv.symm ▸ hTop))
    (fun i hi j hj hs hjLe ih => (compareHistorySchema_iff hM.1 Rows Rows' H J Good i).mpr (by
      have hjN : M.mem j N := by
        rcases ordinal_subset_cases_d hM ((omega_isOrdinal_d hM hC.omega).mem hj) ((omega_isOrdinal_d hM hC.omega).mem hB) hjLe with he | hlt
        · exact he.symm ▸ hN.predecessor_mem
        · exact (hN j).mpr (.inl hlt)
      obtain ⟨u,hu,hU⟩ := hH.graph.total j hjN
      obtain ⟨v,hv,hV⟩ := hJ.graph.total j hjN
      have hGood := (compareHistorySchema_iff hM.1 Rows Rows' H J Good j).mp ih u hu v hv hU hV
      intro a ha b hb hA hB'
      exact hPreserve i hi u hu v hv a ha b hb (hH.step_d hM hC hB hi hjN hs hU hA)
        (hJ.step_d hM hC hB hi hjN hs hV hB') hGood))
  intro i hi u v hU hV
  have hiB : i=B ∨ M.mem i B := by
    rcases (hN i).mp hi with hlt | he
    · exact .inr hlt
    · exact .inl (hM.1.eq_of_same_members i B he)
  exact (compareHistorySchema_iff hM.1 Rows Rows' H J Good i).mp (hAll i hiB) u (hH.graph.bounds hM.1 hU).2 v (hJ.graph.bounds hM.1 hV).2 hU hV

private def diagonalSchema : Project.Delta0BinarySchema 0 where
  body := Project.Formula.extensionalEq (.bound 1) (.bound 0)
  freeClosed := by simp
  delta0 := .atom _ _ _

theorem Tail.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Rows B N Top Keys Step H J : M.Domain}
    (hB : M.mem B C.omega) (hN : M.SuccessorOf N B) (hTable : StepTable M B Rows Keys Step)
    (hH : Tail M Rows B N Top Keys Step C.zero H) (hJ : Tail M Rows B N Top Keys Step C.zero J) : H=J := by
  let e : Env M 0 := ⟨Fin.elim0,fun _ => Rows⟩
  obtain ⟨Good,_,hRaw⟩ := relation_comprehension_d hM diagonalSchema e Rows Rows
  have hRows (u v : M.Domain) : MemPair M Good u v ↔ M.mem u Rows ∧ M.mem v Rows ∧ u=v := by
    rw [hRaw u v,diagonalSchema,Project.Formula.satisfies_extensionalEq_iff_eq hM.1]
    rfl
  have hTopRows := (hH.graph.bounds hM.1 hH.top).2
  have hAgree := hH.compare_d hM hC hB hN hJ ((hRows Top Top).mpr ⟨hTopRows,hTopRows,rfl⟩) (by
    intro i _ u _ v _ a ha b hb hA hB' hGood
    have huv := ((hRows u v).mp hGood).2.2
    subst v
    exact (hRows a b).mpr ⟨ha,hb,hTable.unique hM.1 hA hB'⟩)
  apply hH.graph.ext hM.1 hJ.graph
  intro i hi u
  constructor
  · intro hU
    obtain ⟨v,_,hV⟩ := hJ.graph.total i hi
    exact ((hRows u v).mp (hAgree i hi u v hU hV)).2.2.symm ▸ hV
  · intro hV
    obtain ⟨v,_,hU⟩ := hH.graph.total i hi
    exact ((hRows v u).mp (hAgree i hi v u hU hV)).2.2 ▸ hU

def CodeStep (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Pairs Plus width Forests Codes G i upper lower : M.Domain) : Prop :=
  ∃code, M.mem code Codes ∧ MemPair M G i code ∧ ∃heights parents, KP1Y.Kuratowski.Codes M code heights parents ∧
    MountainReconstruction.Rebuilds M C Pairs Plus ⟨width,heights,Forests,parents⟩ upper lower

def codeStepFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Plus width Forests Codes G ForestLists Grids i upper lower : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Codes (.conj (memPairFormula G.weaken i.weaken (.bound 0))
    (CopiedMountain.withCodeFormula (.bound 0)
      (MountainReconstruction.rebuildsFormula C.weaken.weaken.weaken.weaken Pairs.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken
        ⟨width.weaken.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken.weaken,.bound 0⟩
        upper.weaken.weaken.weaken.weaken lower.weaken.weaken.weaken.weaken ForestLists.weaken.weaken.weaken.weaken Grids.weaken.weaken.weaken.weaken)))

theorem codeStepFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Plus width Forests Codes G ForestLists Grids i upper lower : Project.Term n) :
    (codeStepFormula C Pairs Plus width Forests Codes G ForestLists Grids i upper lower).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (CopiedMountain.withCodeFormula_delta0 _ (MountainReconstruction.rebuildsFormula_delta0 _ _ _ _ _ _ _ _)))

theorem codeStepFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Pairs Plus width Forests Codes G ForestLists Grids i upper lower : Project.Term n)
    (hPairs : Pairs.freeSupport=[]) (hPlus : Plus.freeSupport=[]) (hWidth : width.freeSupport=[]) (hForests : Forests.freeSupport=[])
    (hCodes : Codes.freeSupport=[]) (hG : G.freeSupport=[]) (hFL : ForestLists.freeSupport=[]) (hGrids : Grids.freeSupport=[])
    (hi : i.freeSupport=[]) (hu : upper.freeSupport=[]) (hl : lower.freeSupport=[]) :
    (codeStepFormula C Pairs Plus width Forests Codes G ForestLists Grids i upper lower).FreeClosed := by
  have hRebuild := MountainReconstruction.rebuildsFormula_freeClosed hC.weaken.weaken.weaken.weaken
    (X := ⟨width.weaken.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken.weaken,.bound 0⟩)
    ⟨by simpa using hWidth,rfl,by simpa using hForests,rfl⟩
    Pairs.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken upper.weaken.weaken.weaken.weaken lower.weaken.weaken.weaken.weaken
    ForestLists.weaken.weaken.weaken.weaken Grids.weaken.weaken.weaken.weaken
    (by simpa using hPairs) (by simpa using hPlus) (by simpa using hu) (by simpa using hl) (by simpa using hFL) (by simpa using hGrids)
  have hCode := CopiedMountain.withCodeFormula_freeClosed (.bound 0) rfl hRebuild
  simp [codeStepFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hCodes,hG,hi,hCode]

theorem codeStepFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Pairs Plus width Forests Codes G ForestLists Grids i upper lower : Project.Term n)
    (hSpaces : MountainReconstruction.Spaces.Valid M (C.eval e) (Forests.eval e) ⟨ForestLists.eval e,Grids.eval e⟩)
    (hWidth : M.mem (width.eval e) (C.eval e).omega) :
    Project.Formula.satisfies e (codeStepFormula C Pairs Plus width Forests Codes G ForestLists Grids i upper lower) ↔
      CodeStep M (C.eval e) (Pairs.eval e) (Plus.eval e) (width.eval e) (Forests.eval e) (Codes.eval e) (G.eval e) (i.eval e) (upper.eval e) (lower.eval e) := by
  have hBody (code : M.Domain) : Project.Formula.satisfies (e.push code) (CopiedMountain.withCodeFormula (.bound 0)
      (MountainReconstruction.rebuildsFormula C.weaken.weaken.weaken.weaken Pairs.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken
        ⟨width.weaken.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken.weaken,.bound 0⟩
        upper.weaken.weaken.weaken.weaken lower.weaken.weaken.weaken.weaken ForestLists.weaken.weaken.weaken.weaken Grids.weaken.weaken.weaken.weaken)) ↔
      ∃heights parents, KP1Y.Kuratowski.Codes M code heights parents ∧ MountainReconstruction.Rebuilds M (C.eval e) (Pairs.eval e) (Plus.eval e)
        ⟨width.eval e,heights,Forests.eval e,parents⟩ (upper.eval e) (lower.eval e) := by
    apply CopiedMountain.withCodeFormula_iff_exists he (e.push code) (.bound 0) _ _
    intro container heights parents
    have h := MountainReconstruction.rebuildsFormula_iff he ((((e.push code).push container).push heights).push parents)
      C.weaken.weaken.weaken.weaken Pairs.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken
      ⟨width.weaken.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken.weaken,.bound 0⟩
      upper.weaken.weaken.weaken.weaken lower.weaken.weaken.weaken.weaken ForestLists.weaken.weaken.weaken.weaken Grids.weaken.weaken.weaken.weaken
      (by simpa only [ExpressionData.eval_weaken,CopiedMountain.Data.eval,CopiedMountain.Data.map,Term.eval_weaken] using hSpaces)
      (by simpa only [ExpressionData.eval_weaken,CopiedMountain.Data.eval,CopiedMountain.Data.map,Term.eval_weaken] using hWidth)
    simpa only [ExpressionData.eval_weaken,CopiedMountain.Data.eval,CopiedMountain.Data.map,Term.eval_weaken,
      Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using h
  simp only [codeStepFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Term.eval_weaken,hBody]
  rfl

theorem CodeStep.total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B Rows i upper : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hRows : ∀F, M.mem F Rows ↔ Graph M F width C.omega) (hi : M.mem i B) (hU : M.mem upper Rows) :
    ∃lower, M.mem lower Rows ∧ CodeStep M C Pairs Plus width Forests Codes G i upper lower := by
  obtain ⟨code,hCode,hAt⟩ := hG.total i hi
  obtain ⟨heights,parents,hDecode,hX⟩ := hValid i code hAt
  obtain ⟨lower,hLower⟩ := MountainReconstruction.rebuild_exists_d hM hC hPlus hX ((hRows upper).mp hU)
  exact ⟨lower,(hRows lower).mpr hLower.graph,code,hCode,hAt,heights,parents,hDecode,hLower⟩

theorem CodeStep.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B i upper lower lower' : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hU : Graph M upper width C.omega)
    (h : CodeStep M C Pairs Plus width Forests Codes G i upper lower) (h' : CodeStep M C Pairs Plus width Forests Codes G i upper lower') : lower=lower' := by
  obtain ⟨code,_,hCode,heights,parents,hDecode,hRebuild⟩ := h
  obtain ⟨code',_,hCode',heights',parents',hDecode',hRebuild'⟩ := h'
  have he := hG.unique i code code' hCode hCode'
  subst code'
  obtain ⟨hh,hp⟩ := codes_injective hM.1 hDecode hDecode'
  subst heights'
  subst parents'
  exact hRebuild.unique_d hM hC hPlus ((hValid i code hCode).read hM.1 hDecode) hU hRebuild'

private def codeStepEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain)
    (Pairs Plus B width Forests Codes G Rows ForestLists Grids : M.Domain) : Env M 15 :=
  (((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push Pairs).push Plus).push B).push width).push Forests).push Codes).push G).push Rows).push ForestLists).push Grids)

private def codeStepSchema : Project.Delta0BinarySchema 15 where
  body := Project.Formula.existsMem (.bound 9) (Project.Formula.existsMem (.bound 5)
    (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0))
      (codeStepFormula ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ (.bound 13) (.bound 12) (.bound 10) (.bound 9) (.bound 8) (.bound 7)
        (.bound 5) (.bound 4) (.bound 1) (.bound 0) (.bound 2))))
  freeClosed := by
    have h := codeStepFormula_freeClosed (n := 19) (C := ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩) ⟨rfl,rfl,rfl,rfl,rfl⟩
      (.bound 13) (.bound 12) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 5) (.bound 4) (.bound 1) (.bound 0) (.bound 2)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    simp [Project.Formula.existsMem,codeFormula,pairFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,h]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (codeStepFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _)))

private theorem codeStepSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain)
    (Pairs Plus B width Forests Codes G Rows ForestLists Grids key lower : M.Domain)
    (hSpaces : MountainReconstruction.Spaces.Valid M C Forests ⟨ForestLists,Grids⟩) (hWidth : M.mem width C.omega) :
    Project.Formula.satisfies (((codeStepEnv C Pairs Plus B width Forests Codes G Rows ForestLists Grids).push key).push lower) codeStepSchema.body ↔
      ∃i, M.mem i B ∧ ∃upper, M.mem upper Rows ∧ KP1Y.Kuratowski.Codes M key i upper ∧ CodeStep M C Pairs Plus width Forests Codes G i upper lower := by
  simp only [codeStepSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,codeFormula_iff he]
  have h (i upper : M.Domain) := codeStepFormula_iff he
    (((((codeStepEnv C Pairs Plus B width Forests Codes G Rows ForestLists Grids).push key).push lower).push i).push upper)
    ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ (.bound 13) (.bound 12) (.bound 10) (.bound 9) (.bound 8) (.bound 7)
    (.bound 5) (.bound 4) (.bound 1) (.bound 0) (.bound 2) hSpaces hWidth
  simp only [h]
  rfl

theorem code_step_table_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B Rows : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hRows : ∀F, M.mem F Rows ↔ Graph M F width C.omega) :
    ∃Keys Step, StepTable M B Rows Keys Step ∧ ∀i upper lower, StepAt M Keys Step i upper lower ↔
      M.mem i B ∧ M.mem upper Rows ∧ CodeStep M C Pairs Plus width Forests Codes G i upper lower := by
  obtain ⟨S,hS⟩ := MountainReconstruction.spaces_exists_d hM hC Forests
  obtain ⟨Keys,hKeys⟩ := product_exists hM B Rows
  obtain ⟨Step,hSupport,hRaw⟩ := relation_comprehension_d hM codeStepSchema
    (codeStepEnv C Pairs Plus B width Forests Codes G Rows S.forestLists S.grids) Keys Rows
  have hRawRows (key lower : M.Domain) : MemPair M Step key lower ↔ M.mem key Keys ∧ M.mem lower Rows ∧
      ∃i, M.mem i B ∧ ∃upper, M.mem upper Rows ∧ KP1Y.Kuratowski.Codes M key i upper ∧ CodeStep M C Pairs Plus width Forests Codes G i upper lower := by
    rw [hRaw key lower,codeStepSchema_iff hM.1 C Pairs Plus B width Forests Codes G Rows S.forestLists S.grids key lower hS hn]
  have hStep : Graph M Step Keys Rows := by
    refine ⟨hSupport,?_,?_⟩
    · intro key hk
      obtain ⟨i,hi,upper,hu,hCode⟩ := (hKeys key).mp hk
      obtain ⟨lower,hl,hLower⟩ := CodeStep.total_d hM hC hPlus hG hValid hRows hi hu
      exact ⟨lower,hl,(hRawRows key lower).mpr ⟨hk,hl,i,hi,upper,hu,hCode,hLower⟩⟩
    · intro key lower lower' hL hL'
      obtain ⟨_,_,i,_,upper,hu,hCode,hRebuild⟩ := (hRawRows key lower).mp hL
      obtain ⟨_,_,i',_,upper',_,hCode',hRebuild'⟩ := (hRawRows key lower').mp hL'
      obtain ⟨hii,huu⟩ := codes_injective hM.1 hCode hCode'
      subst i'
      subst upper'
      exact hRebuild.unique_d hM hC hPlus hG hValid ((hRows upper).mp hu) hRebuild'
  refine ⟨Keys,Step,⟨hKeys,hStep⟩,fun i upper lower => ?_⟩
  constructor
  · rintro ⟨key,_,hCode,hAt⟩
    obtain ⟨_,_,i',hi,upper',hu,hCode',hRebuild⟩ := (hRawRows key lower).mp hAt
    obtain ⟨hii,huu⟩ := codes_injective hM.1 hCode' hCode
    subst i'
    subst upper'
    exact ⟨hi,hu,hRebuild⟩
  · rintro ⟨hi,hu,hRebuild⟩
    obtain ⟨key,hCode⟩ := codes_total hM i upper
    have hk := (hKeys key).mpr ⟨i,hi,upper,hu,hCode⟩
    have hLowerGraph : Graph M lower width C.omega := by
      obtain ⟨_,_,_,_,_,_,hL⟩ := hRebuild
      exact hL.graph
    exact ⟨key,hk,hCode,(hRawRows key lower).mpr ⟨hk,(hRows lower).mpr hLowerGraph,i,hi,upper,hu,hCode,hRebuild⟩⟩

structure Run (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (Pairs Plus width Forests Codes G B N Top H : M.Domain) : Prop where
  length : M.SuccessorOf N B
  graph : Graph M H N C.sequences
  values : ∀i F, MemPair M H i F → Graph M F width C.omega
  top : MemPair M H B Top
  transition : ∀i, M.mem i B → ∀j, M.SuccessorOf j i → ∀upper lower,
    MemPair M H j upper → MemPair M H i lower → CodeStep M C Pairs Plus width Forests Codes G i upper lower

theorem run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B Top : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hB : M.mem B C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code) (hTop : Graph M Top width C.omega) :
    ∃N H, Run M C Pairs Plus width Forests Codes G B N Top H := by
  obtain ⟨R,hR⟩ := row_state_space_exists_d hM hC hn
  obtain ⟨Keys,Step,hStep,hStepRows⟩ := code_step_table_exists_d hM hC hPlus hn hG hValid hR.values
  obtain ⟨N,hN,_⟩ := hC.omega.1.2 B hB
  obtain ⟨H,hH⟩ := tail_history_exists_d hM hC hB hN hStep ((hR.values Top).mpr hTop)
  have hGraph : Graph M H N C.sequences := hH.graph.mono_values (fun F hF => (hC.sequences F).mpr ⟨width,hn,(hR.values F).mp hF⟩)
  refine ⟨N,H,hN,hGraph,fun i F hAt => (hR.values F).mp (hH.graph.bounds hM.1 hAt).2,hH.top,?_⟩
  intro i hi j hs upper lower hU hL
  exact ((hStepRows i upper lower).mp (hH.step_d hM hC hB hi (hH.graph.bounds hM.1 hU).1 hs hU hL)).2.2

def Assembles (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (Pairs Plus width Forests Codes G B Top F : M.Domain) : Prop :=
  ∃N H, Run M C Pairs Plus width Forests Codes G B N Top H ∧ MemPair M H C.zero F

theorem assembles_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B Top : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hB : M.mem B C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code) (hTop : Graph M Top width C.omega) :
    ∃F, Graph M F width C.omega ∧ Assembles M C Pairs Plus width Forests Codes G B Top F := by
  obtain ⟨N,H,hRun⟩ := run_exists_d hM hC hPlus hn hB hG hValid hTop
  have hN := natural_successor_mem_d hM hC hB hRun.length
  have hZero : M.mem C.zero N := (hC.zero_mem_iff hM hN).mpr (fun he => hC.zero_empty B (he ▸ hRun.length.predecessor_mem))
  obtain ⟨F,_,hF⟩ := hRun.graph.total C.zero hZero
  exact ⟨F,hRun.values C.zero F hF,N,H,hRun,hF⟩

theorem Run.to_tail_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {Pairs Plus width Forests Codes G B N Top H Rows Keys Step : M.Domain}
    (h : Run M C Pairs Plus width Forests Codes G B N Top H)
    (hRows : ∀F, M.mem F Rows ↔ Graph M F width C.omega)
    (hStep : ∀i upper lower, StepAt M Keys Step i upper lower ↔ M.mem i B ∧ M.mem upper Rows ∧ CodeStep M C Pairs Plus width Forests Codes G i upper lower) :
    Tail M Rows B N Top Keys Step C.zero H := by
  refine ⟨KP1Y.Assignments.graph_tighten_values h.graph (fun i F hAt => (hRows F).mpr (h.values i F hAt)),h.top,?_⟩
  intro i hi j _ _ hs upper hu lower _ hU hL
  exact (hStep i upper lower).mpr ⟨hi,hu,h.transition i hi j hs upper lower hU hL⟩

theorem Run.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B N N' Top H J : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hB : M.mem B C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hH : Run M C Pairs Plus width Forests Codes G B N Top H) (hJ : Run M C Pairs Plus width Forests Codes G B N' Top J) : N=N' ∧ H=J := by
  have hNN := Structure.SuccessorOf.eq hM.1 hH.length hJ.length
  subst N'
  obtain ⟨R,hR⟩ := row_state_space_exists_d hM hC hn
  obtain ⟨Keys,Step,hStep,hRows⟩ := code_step_table_exists_d hM hC hPlus hn hG hValid hR.values
  exact ⟨rfl,(hH.to_tail_d hR.values hRows).unique_d hM hC hB hH.length hStep (hJ.to_tail_d hR.values hRows)⟩

theorem Assembles.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B Top F F' : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hB : M.mem B C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (h : Assembles M C Pairs Plus width Forests Codes G B Top F) (h' : Assembles M C Pairs Plus width Forests Codes G B Top F') : F=F' := by
  obtain ⟨N,H,hRun,hAt⟩ := h
  obtain ⟨N',J,hRun',hAt'⟩ := h'
  have hHJ := (hRun.unique_d hM hC hPlus hn hB hG hValid hRun').2
  subst J
  exact hRun.graph.unique C.zero F F' hAt hAt'

theorem CodeStep.legal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G i upper lower : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hUpper : LegalAt M C.omega C.zero C.one upper width)
    (h : CodeStep M C Pairs Plus width Forests Codes G i upper lower) : LegalAt M C.omega C.zero C.one lower width := by
  obtain ⟨code,_,hAt,heights,parents,hDecode,hRebuild⟩ := h
  have hX := (hValid i code hAt).read hM.1 hDecode
  refine ⟨⟨hUpper.1.1,hRebuild.graph⟩,?_,?_⟩
  · intro c _ v _ hAt
    exact hRebuild.positive_d hM hC hPlus hX hUpper.1.2 (fun _ _ h => legal_values_positive hM.1 hUpper h) hAt
  · exact hUpper.2.2.imp id ((hRebuild.first_iff_d hM hC hX hUpper.1.2).mpr)

private def legalRowSchema : Project.Delta0BinarySchema 4 where
  body := legalAtFormula (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 2)
  freeClosed := legalAtFormula_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := legalAtFormula_delta0 _ _ _ _ _

theorem Run.legal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B N Top H : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hB : M.mem B C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hTop : LegalAt M C.omega C.zero C.one Top width) (hRun : Run M C Pairs Plus width Forests Codes G B N Top H) :
    ∀i F, MemPair M H i F → LegalAt M C.omega C.zero C.one F width := by
  obtain ⟨R,hR⟩ := row_state_space_exists_d hM hC hn
  obtain ⟨Keys,Step,hStep,hStepRows⟩ := code_step_table_exists_d hM hC hPlus hn hG hValid hR.values
  have hTail := hRun.to_tail_d hR.values hStepRows
  let e := (((oneEnv C.omega).push C.zero).push C.one).push width
  obtain ⟨Good,_,hRaw⟩ := relation_comprehension_d hM legalRowSchema e R.values R.values
  have hGood (u v : M.Domain) : MemPair M Good u v ↔ M.mem u R.values ∧ M.mem v R.values ∧ LegalAt M C.omega C.zero C.one u width := by
    have hφ : Project.Formula.satisfies ((e.push u).push v) legalRowSchema.body ↔ LegalAt M C.omega C.zero C.one u width := legalAtFormula_iff hM.1 _ _ _ _ _ _
    rw [hRaw u v,hφ]
  have hTopRow := (hR.values Top).mpr hTop.1.2
  have hAll := hTail.compare_d hM hC hB hRun.length hTail ((hGood Top Top).mpr ⟨hTopRow,hTopRow,hTop⟩) (by
    intro i _ u _ v _ a ha b hb hA _ hUV
    exact (hGood a b).mpr ⟨ha,hb,(((hStepRows i u a).mp hA).2.2).legal_d hM hC hPlus hValid ((hGood u v).mp hUV).2.2⟩)
  intro i F hAt
  exact ((hGood F F).mp (hAll i (hRun.graph.bounds hM.1 hAt).1 F F hAt hAt)).2.2

theorem Assembles.graph {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {Pairs Plus width Forests Codes G B Top F : M.Domain} (h : Assembles M C Pairs Plus width Forests Codes G B Top F) : Graph M F width C.omega := by
  obtain ⟨_,_,hRun,hAt⟩ := h
  exact hRun.values C.zero F hAt

theorem Assembles.legal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B Top F : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hB : M.mem B C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hTop : LegalAt M C.omega C.zero C.one Top width) (h : Assembles M C Pairs Plus width Forests Codes G B Top F) :
    LegalAt M C.omega C.zero C.one F width := by
  obtain ⟨_,_,hRun,hAt⟩ := h
  exact hRun.legal_d hM hC hPlus hn hB hG hValid hTop C.zero F hAt

def AllOne (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (width Top : M.Domain) : Prop :=
  Graph M Top width C.omega ∧ ∀c v, MemPair M Top c v ↔ M.mem c width ∧ v=C.one

theorem all_one_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    (width : M.Domain) : ∃Top, AllOne M C width Top := constant_graph_exists_d hM width hC.one_nat

theorem AllOne.legal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {width Top : M.Domain} (hn : M.mem width C.omega) (h : AllOne M C width Top) : LegalAt M C.omega C.zero C.one Top width := by
  refine ⟨⟨hn,h.1⟩,?_,?_⟩
  · intro c _ v _ hAt
    exact ((h.2 c v).mp hAt).2.symm ▸ hC.one_succ.predecessor_mem
  · by_cases he : width=C.zero
    · exact .inl he
    · exact .inr ((h.2 C.zero C.one).mpr ⟨(hC.zero_mem_iff hM hn).mpr he,rfl⟩)

/-- B个真实山形，B处外接全1顶部；返回合法的实际宽度width数值图。 -/
theorem assemble_ones_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hB : M.mem B C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code) :
    ∃Top F, AllOne M C width Top ∧ Assembles M C Pairs Plus width Forests Codes G B Top F ∧ LegalAt M C.omega C.zero C.one F width := by
  obtain ⟨Top,hTop⟩ := all_one_exists_d hM hC width
  obtain ⟨F,_,hF⟩ := assembles_exists_d hM hC hPlus hn hB hG hValid hTop.1
  exact ⟨Top,F,hTop,hF,hF.legal_d hM hC hPlus hn hB hG hValid (hTop.legal_d hM hC hn)⟩

structure FamilyPrefix (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (width Forests G width' Forests' G' B cut : M.Domain) : Prop where
  length : M.mem cut C.omega
  left_width : M.MemberSubset cut width
  right_width : M.MemberSubset cut width'
  rows : ∀k, M.mem k B → ∀code code' heights parents heights' parents', MemPair M G k code → MemPair M G' k code' →
    KP1Y.Kuratowski.Codes M code heights parents → KP1Y.Kuratowski.Codes M code' heights' parents' →
      RowsAgreeOn M heights heights' cut ∧ ∀c, M.mem c cut → ∀r, M.mem r C.omega → ∀p,
        CopiedMountain.ParentAt M ⟨width,heights,Forests,parents⟩ r c p ↔ CopiedMountain.ParentAt M ⟨width',heights',Forests',parents'⟩ r c p

theorem CodeStep.prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G width' Forests' Codes' G' B cut i upper lower upper' lower' : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hValid' : ∀k code, MemPair M G' k code → CopiedMountain.CodeValid M C width' Forests' code)
    (hPrefix : FamilyPrefix M C width Forests G width' Forests' G' B cut) (hi : M.mem i B)
    (hUpper : Graph M upper width C.omega) (hUpper' : Graph M upper' width' C.omega)
    (hTops : RowsAgreeOn M upper upper' cut)
    (h : CodeStep M C Pairs Plus width Forests Codes G i upper lower) (h' : CodeStep M C Pairs Plus width' Forests' Codes' G' i upper' lower') :
    RowsAgreeOn M lower lower' cut := by
  obtain ⟨code,_,hAt,heights,parents,hCode,hRebuild⟩ := h
  obtain ⟨code',_,hAt',heights',parents',hCode',hRebuild'⟩ := h'
  have hGeometry := hPrefix.rows i hi code code' heights parents heights' parents' hAt hAt' hCode hCode'
  exact hRebuild.prefix_d hM hC hPlus ((hValid i code hAt).read hM.1 hCode) ((hValid' i code' hAt').read hM.1 hCode')
    hUpper hUpper' hPrefix.length hPrefix.left_width hPrefix.right_width hGeometry.1 hTops hGeometry.2 hRebuild'

private def rowAgreementSchema : Project.Delta0BinarySchema 2 where
  body := Project.Formula.forallMem (.bound 2) (Project.Formula.forallMem (.bound 4)
    (.iff (memPairFormula (.bound 3) (.bound 1) (.bound 0)) (memPairFormula (.bound 2) (.bound 1) (.bound 0))))
  freeClosed := by simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))

theorem row_agreement_relation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w n n' Rows Rows' : M.Domain} (hRows : ∀F, M.mem F Rows ↔ Graph M F n w) (hRows' : ∀F, M.mem F Rows' ↔ Graph M F n' w) (cut : M.Domain) :
    ∃Good, ∀u v, MemPair M Good u v ↔ M.mem u Rows ∧ M.mem v Rows' ∧ RowsAgreeOn M u v cut := by
  obtain ⟨Good,_,hRaw⟩ := relation_comprehension_d hM rowAgreementSchema ((oneEnv w).push cut) Rows Rows'
  have hφ (u v : M.Domain) : Project.Formula.satisfies ((((oneEnv w).push cut).push u).push v) rowAgreementSchema.body ↔
      ∀c, M.mem c cut → ∀a, M.mem a w → (MemPair M u c a ↔ MemPair M v c a) := by
    simp only [rowAgreementSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff hM.1]
    rfl
  refine ⟨Good,fun u v => ?_⟩
  rw [hRaw u v,hφ]
  constructor
  · rintro ⟨hu,hv,hAgree⟩
    refine ⟨hu,hv,fun c hc a => ?_⟩
    exact ⟨fun h => (hAgree c hc a (((hRows u).mp hu).bounds hM.1 h).2).mp h,
      fun h => (hAgree c hc a (((hRows' v).mp hv).bounds hM.1 h).2).mpr h⟩
  · exact fun h => ⟨h.1,h.2.1,fun c hc a _ => h.2.2 c hc a⟩

theorem Run.prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M)
    {Pairs Plus width Forests Codes G width' Forests' Codes' G' B cut N N' Top Top' H J : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hn' : M.mem width' C.omega) (hB : M.mem B C.omega)
    (hG : Graph M G B Codes) (hG' : Graph M G' B Codes')
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hValid' : ∀k code, MemPair M G' k code → CopiedMountain.CodeValid M C width' Forests' code)
    (hPrefix : FamilyPrefix M C width Forests G width' Forests' G' B cut) (hTops : RowsAgreeOn M Top Top' cut)
    (hH : Run M C Pairs Plus width Forests Codes G B N Top H) (hJ : Run M C Pairs Plus width' Forests' Codes' G' B N' Top' J) :
    ∀i, M.mem i N → ∀u v, MemPair M H i u → MemPair M J i v → RowsAgreeOn M u v cut := by
  have hNN := Structure.SuccessorOf.eq hM.1 hH.length hJ.length
  subst N'
  obtain ⟨R,hR⟩ := row_state_space_exists_d hM hC hn
  obtain ⟨R',hR'⟩ := row_state_space_exists_d hM hC hn'
  obtain ⟨Keys,Step,hStep,hSteps⟩ := code_step_table_exists_d hM hC hPlus hn hG hValid hR.values
  obtain ⟨Keys',Step',hStep',hSteps'⟩ := code_step_table_exists_d hM hC hPlus hn' hG' hValid' hR'.values
  obtain ⟨Good,hGood⟩ := row_agreement_relation_exists_d hM hR.values hR'.values cut
  have hTail := hH.to_tail_d hR.values hSteps
  have hTail' := hJ.to_tail_d hR'.values hSteps'
  have hAll := hTail.compare_d hM hC hB hH.length hTail' ((hGood Top Top').mpr
    ⟨(hR.values Top).mpr (hH.values B Top hH.top),(hR'.values Top').mpr (hJ.values B Top' hJ.top),hTops⟩) (by
    intro i hi u hu v hv a ha b hb hA hB' hUV
    have hRebuild := ((hSteps i u a).mp hA).2.2
    have hRebuild' := ((hSteps' i v b).mp hB').2.2
    exact (hGood a b).mpr ⟨ha,hb,hRebuild.prefix_d hM hC hPlus hValid hValid' hPrefix hi
      ((hR.values u).mp hu) ((hR'.values v).mp hv) ((hGood u v).mp hUV).2.2 hRebuild'⟩)
  exact fun i hi u v hU hV => ((hGood u v).mp (hAll i hi u v hU hV)).2.2

theorem Assembles.prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M)
    {Pairs Plus width Forests Codes G width' Forests' Codes' G' B cut Top Top' F F' : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hn' : M.mem width' C.omega) (hB : M.mem B C.omega)
    (hG : Graph M G B Codes) (hG' : Graph M G' B Codes')
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hValid' : ∀k code, MemPair M G' k code → CopiedMountain.CodeValid M C width' Forests' code)
    (hPrefix : FamilyPrefix M C width Forests G width' Forests' G' B cut) (hTops : RowsAgreeOn M Top Top' cut)
    (h : Assembles M C Pairs Plus width Forests Codes G B Top F) (h' : Assembles M C Pairs Plus width' Forests' Codes' G' B Top' F') :
    RowsAgreeOn M F F' cut := by
  obtain ⟨N,H,hRun,hF⟩ := h
  obtain ⟨N',J,hRun',hF'⟩ := h'
  exact hRun.prefix_d hM hC hPlus hn hn' hB hG hG' hValid hValid' hPrefix hTops hRun' C.zero (hRun.graph.bounds hM.1 hF).1 F F' hF hF'

theorem AllOne.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} {width Top Top' : M.Domain}
    (h : AllOne M C width Top) (h' : AllOne M C width Top') : Top=Top' :=
  h.1.ext he h'.1 (fun c _ v => (h.2 c v).trans (h'.2 c v).symm)

theorem Assembles.empty_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {Pairs Plus Forests Codes G B Top F : M.Domain} (h : Assembles M C Pairs Plus C.zero Forests Codes G B Top F) : F=C.zero :=
  h.graph.ext hM.1 (empty_graph (V := C.omega) hC.zero_empty) (fun c hc => False.elim (hC.zero_empty c hc))

theorem assemble_ones_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B Top Top' F F' : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hB : M.mem B C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hTop : AllOne M C width Top) (hTop' : AllOne M C width Top')
    (h : Assembles M C Pairs Plus width Forests Codes G B Top F) (h' : Assembles M C Pairs Plus width Forests Codes G B Top' F') : F=F' := by
  have he := hTop.unique hM.1 hTop'
  subst Top'
  exact h.unique_d hM hC hPlus hn hB hG hValid h'

theorem Assembles.horizon_zero {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {Pairs Plus width Forests Codes G Top F : M.Domain} (h : Assembles M C Pairs Plus width Forests Codes G C.zero Top F) : F=Top := by
  obtain ⟨_,_,hRun,hAt⟩ := h
  exact hRun.graph.unique C.zero F Top hAt hRun.top

theorem Assembles.positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B Top F c v : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hB : M.mem B C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hTop : LegalAt M C.omega C.zero C.one Top width) (h : Assembles M C Pairs Plus width Forests Codes G B Top F)
    (hAt : MemPair M F c v) : M.mem C.zero v :=
  legal_values_positive hM.1 (h.legal_d hM hC hPlus hn hB hG hValid hTop) hAt

theorem Assembles.first_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus width Forests Codes G B Top F : M.Domain}
    (hPlus : AdditionTable M C Pairs Plus) (hn : M.mem width C.omega) (hB : M.mem B C.omega) (hG : Graph M G B Codes)
    (hValid : ∀k code, MemPair M G k code → CopiedMountain.CodeValid M C width Forests code)
    (hTop : LegalAt M C.omega C.zero C.one Top width) (h : Assembles M C Pairs Plus width Forests Codes G B Top F)
    (hNonempty : width≠C.zero) : MemPair M F C.zero C.one :=
  (h.legal_d hM hC hPlus hn hB hG hValid hTop).2.2.resolve_left hNonempty

end KP1Y.OneYFinite.TowerReconstruction
