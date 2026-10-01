import KP1Y.OneYTowerCanonSetting
import KP1Y.OneYOrdinaryCanonical

/-! 活动层以上(K<k≤B)的普通复制层：对内部间隔作对象反向归纳，证明塔重建行恰是
源层数值的普通source0复制；随后得到这些层的完整规范运行和相邻选择，以及
Terminal层所需的新Top读数 Hr(K+1)=CopiedTop(源K层Top)。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

/-- 值图的普通source0逐行读数（ValueCopies 的rows字段）。 -/
def ValueRows (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (n W U : M.Domain) : Prop :=
  ∀ c s b, OrdinaryCoordinates.Decoded M C T A c s b → ∀ v, MemPair M U c v ↔ M.mem c n ∧ MemPair M W s v

private def valueRowsFormula : Project.Formula 1 24 :=
  .forallE (.forallE (.forallE
    (.imp (OrdinaryCoordinates.decodedFormula ⟨.bound 26,.bound 25,.bound 24,.bound 23,.bound 22⟩
        ⟨.bound 21,.bound 20,.bound 19,.bound 18,.bound 17,.bound 16⟩ ⟨.bound 15,.bound 14,.bound 13,.bound 12⟩
        (.bound 2) (.bound 1) (.bound 0))
      (.forallE (.iff (memPairFormula (.bound 7) (.bound 3) (.bound 0))
        (.conj (.mem (.bound 3) (.bound 12)) (memPairFormula (.bound 5) (.bound 2) (.bound 0))))))))

private def ordinarySchema : Project.UnarySchema 19 where
  body := .imp (.mem (.bound 3) (.bound 0)) (.forallE (.forallE (.forallE (.forallE
    (.imp (memPairFormula (.bound 6) (.bound 4) (.bound 3))
      (.imp (memPairFormula (.bound 5) (.bound 4) (.bound 2))
        (.imp (codeFormula (.bound 2) (.bound 1) (.bound 0)) valueRowsFormula)))))))
  freeClosed := by
    have hDec := OrdinaryCoordinates.decodedFormula_freeClosed (n := 27)
      (C := ⟨.bound 26,.bound 25,.bound 24,.bound 23,.bound 22⟩) ⟨rfl,rfl,rfl,rfl,rfl⟩
      (T := ⟨.bound 21,.bound 20,.bound 19,.bound 18,.bound 17,.bound 16⟩) ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (A := ⟨.bound 15,.bound 14,.bound 13,.bound 12⟩) ⟨rfl,rfl,rfl,rfl⟩ (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl
    simp [valueRowsFormula,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,hDec]

private def ordinaryEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (n K Hr H : M.Domain) : Env M 19 :=
  ((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push n).push K).push Hr).push H

private theorem ordinarySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : CopyCoordinates.Context M.Domain)
    (n K Hr H k : M.Domain) :
    Project.Formula.satisfies ((ordinaryEnv C T A n K Hr H).push k) ordinarySchema.body ↔
      (M.mem K k → ∀ U state W Q, MemPair M Hr k U → MemPair M H k state → Codes M state W Q →
        ValueRows M C T A n W U) := by
  simp only [ordinarySchema,valueRowsFormula,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,codeFormula_iff he,OrdinaryCoordinates.decodedFormula_iff he]
  rfl

variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
  {V P H K level B strict N n Forests CodeSpace G Nr Top Hr : M.Domain}

theorem Setting.value_copies_of_rows (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {k W U : M.Domain} (hU : MemPair M Hr k U) (hRows : ValueRows M C T A n W U) :
    CopiedMountain.Ordinary.ValueCopies M C T A W n C.omega U :=
  ⟨h.run.values k U hU,hRows⟩

/-- 塔高处：全1顶部是源全1层的普通复制。 -/
private theorem Setting.top_rows_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {W Q : M.Domain} (hLayer : RowAt M L.states H B W Q) : ValueRows M C T A n W Top := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRooted := h.layers.at_rooted hM.1 hLayer
  have hBnat := h.tower.bound
  have hLastM := (h.indices_d hM hC).2.2.1
  intro c s b hDec v
  have hs := (hw.mem h.layers.space.rows.width).transitive A.last hLastM s (hDec.source_lt_last_d hM hC hT h.coordinates)
  obtain ⟨w,_,hW⟩ := hRooted.row.values.total s hs
  have hValue : LayerValue M L H B s w :=
    ⟨W,(h.layers.space.rows.values W).mpr hRooted.row.values,Q,(h.layers.space.rows.forests Q).mpr hRooted.row.forest,hLayer,hW⟩
  have hw1 := h.source_one_d hM hC hBnat (Or.inl rfl) hValue
  subst w
  rw [h.top.2 c v]
  constructor
  · rintro ⟨hc,hv⟩
    exact ⟨hc,hv ▸ hW⟩
  · rintro ⟨hc,hv⟩
    exact ⟨hc,hRooted.row.values.unique s v C.one hv hW⟩

/-- 对象反向归纳：K<k≤B 时 Hr(k) 是源第k层数值的普通复制。 -/
theorem Setting.ordinary_values_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) :
    ∀ k, (k=B ∨ M.mem k B) → M.mem K k → ∀ U W Q, MemPair M Hr k U → RowAt M L.states H k W Q →
      CopiedMountain.Ordinary.ValueCopies M C T A W n C.omega U := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hBnat := h.tower.bound
  have hK := (h.indices_d hM hC).1
  have hAll := backward_induction_d hM hC hT.add ordinarySchema (ordinaryEnv C T A n K Hr H) hBnat
    ((ordinarySchema_iff hM.1 C T A n K Hr H B).mpr (by
      intro _ U state W Q hU hState hCode
      have hUT := h.run.graph.unique B U Top hU h.run.top
      subst U
      have hStateMem := (h.layers.graph.bounds hM.1 hState).2
      exact h.top_rows_d hM hC hT ⟨state,hStateMem,hState,hCode⟩))
    (fun p hp q hs ih => (ordinarySchema_iff hM.1 C T A n K Hr H p).mpr (by
      intro hKp U state W Q hU hState hCode
      have hKq : M.mem K q := (hs K).mpr (Or.inl hKp)
      have hpω := hw.transitive B hBnat p hp
      have hLayer : RowAt M L.states H p W Q := ⟨state,(h.layers.graph.bounds hM.1 hState).2,hState,hCode⟩
      obtain ⟨code,heights,parents,sH,sP,W0,Q0,J,hAt,hCodeY,hY,hLayer0,hRun,hX,hFrom,hBranch⟩ := h.layer_read_d hM hp
      obtain ⟨hWW,hQQ⟩ := h.layers.at_unique hM.1 hLayer0 hLayer
      subst W0
      subst Q0
      have hCopy := hBranch.ordinary_d hM hC hK hKp
      obtain ⟨W',Q',hLayer',_⟩ := h.source_next_d hM hC hpω hs hLayer
      have hTopRun := h.source_top_d hM hC hLayer hRun hFrom hs hLayer'
      have hqN : M.mem q Nr := by
        rcases successor_le_d' hM hC hpω hBnat hs hp with he | hlt
        · exact (h.run.length q).mpr (Or.inr (by rw [he]; exact fun _ => Iff.rfl))
        · exact (h.run.length q).mpr (Or.inl hlt)
      obtain ⟨U',_,hU'⟩ := h.run.graph.total q hqN
      obtain ⟨state',hStateMem',hState',hCode'⟩ := hLayer'
      have hRows' := (ordinarySchema_iff hM.1 C T A n K Hr H q).mp ih hKq U' state' W' Q' hU' hState' hCode'
      have hTopCopy := h.value_copies_of_rows hU' hRows'
      obtain ⟨code',_,hAt',heights',parents',hCode'',hRebuild⟩ := h.run.transition p hp q hs U' U hU' hU
      have hcc := h.tower.graph.unique p code' code hAt' hAt
      subst code'
      obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCode'' hCodeY
      subst heights'
      subst parents'
      have hPositive := (h.layers.at_rooted hM.1 hLayer).positive
      exact (Ordinary.Copies.rebuild_values_d hM hC hT h.coordinates hT.add hRun hPositive hX hY hFrom hCopy
        hTopRun hTopCopy hRebuild).rows))
  intro k hk hKk U W Q hU hLayer
  obtain ⟨state,_,hState,hCode⟩ := hLayer
  exact h.value_copies_of_rows hU ((ordinarySchema_iff hM.1 C T A n K Hr H k).mp (hAll k hk) hKk U state W Q hU hState hCode)
where
  successor_le_d' (hM : M.Models KP1Y.theory) (hC : C.Valid M) {r s q : M.Domain} (hr : M.mem r C.omega)
      (hq : M.mem q C.omega) (hSucc : M.SuccessorOf s r) (hrq : M.mem r q) : s=q ∨ M.mem s q := by
    have hw := omega_isOrdinal_d hM hC.omega
    apply ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hr hSucc)) (hw.mem hq)
    intro a ha
    rcases (hSucc a).mp ha with har | he
    · exact (hw.mem hq).transitive r hrq a har
    · exact (hM.1.eq_of_same_members a r he).symm ▸ hrq

end KP1Y.OneYFinite.TowerCanon
