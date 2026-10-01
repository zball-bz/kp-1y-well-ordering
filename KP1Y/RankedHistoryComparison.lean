import KP1Y.RankedHistory
import KP1Y.RankedCarrierSyntax

/-! 实际对象序数归纳证明排名历史的载域逐项等于原L历史；无外部良基假设。 -/
namespace KP1Y.ConstructibleRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking KP1Y.SetLanguage
universe u

def baseEnv {M : SetTheory.Structure.{u}} (e : Env M 26) : Env M 24 :=
  ⟨fun i => e.bound ⟨i.val+2,by omega⟩,e.free⟩

theorem baseEnv_extend {M : SetTheory.Structure.{u}} (e : Env M 24) (FP π : M.Domain) :
    baseEnv ((e.push π).push FP) = e := by
  rw [Env.mk.injEq]
  exact ⟨rfl,rfl⟩

def CompareAt (M : SetTheory.Structure.{u}) (H G Γ V U i : M.Domain) : Prop :=
  M.mem i Γ → ∀ Out, M.mem Out V → ∀ T, M.mem T U →
    MemPair M H i Out ∧ MemPair M G i T → CarrierOf M Out T

private def comparisonSchema : Project.Delta0UnarySchema 5 where
  body := .imp (.mem (.bound 0) (.bound 1)) (Project.Formula.forallMem (.bound 3)
    (Project.Formula.forallMem (.bound 3) (.imp
      (.conj (memPairFormula (.bound 7) (.bound 2) (.bound 1)) (memPairFormula (.bound 6) (.bound 2) (.bound 0)))
      (carrierOfFormula (.bound 1) (.bound 0)))))
  freeClosed := by
    have hCar := carrierOfFormula_freeClosed (n := 8) (.bound 1) (.bound 0) rfl rfl
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
      Definitional.Formula.FreeClosed,hCar]
  delta0 := .imp (.mem _ _) (.forallMem _ (.forallMem _ (.imp
    (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (carrierOfFormula_delta0 _ _))))

private theorem comparisonSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H G Γ V U i : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv H).push G).push V).push U).push Γ).push i) comparisonSchema.body ↔ CompareAt M H G Γ V U i := by
  simp only [comparisonSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff he,carrierOfFormula_iff he]
  rfl

theorem ranked_history_carriers_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hS : FixedSyntax M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4))
    (hP : OrdinalRank M (e.bound 0) (rankContext.eval e).programs (e.bound 1))
    {H G Γ V U Q Q' : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : KP1Y.SigmaRecursion.ValueHistory M (rankedStepMatrix.denote e) H Γ V Q)
    (hOld : KP1Y.SigmaRecursion.ValueHistory M (KP1Y.Constructible.levelStepMatrix.denote (baseEnv e)) G Γ U Q') :
    ∀ i Out T, MemPair M H i Out → MemPair M G i T → CarrierOf M Out T := by
  have hGood := ranked_history_family_d hM e hS hP h
  have hAll := KP1Y.ordinal_induction_d hM comparisonSchema.toUnarySchema
    (((((oneEnv H).push G).push V).push U).push Γ) (by
      intro i hi ih
      apply (comparisonSchema_iff hM.1 H G Γ V U i).mpr
      intro hiΓ Out _ T _ hRows
      obtain ⟨A,θ,F,hPacket,_⟩ := hGood.ranked i Out hRows.1
      have hEarlier (j : M.Domain) (hj : M.mem j i) : CompareAt M H G Γ V U j :=
        (comparisonSchema_iff hM.1 H G Γ V U j).mp (ih j hj)
      have hAT : A=T := by
        rcases KP1Y.ordinal_cases hM.1 hi with hEmpty | ⟨j,_,hs⟩ | hLimit
        · have hA := ranked_history_empty_d hM hGood h hiΓ hEmpty hRows.1 hPacket
          have hT := KP1Y.Constructible.history_empty_value_d hM hOld hiΓ hEmpty hRows.2
          exact hM.1.eq_of_same_members A T (fun x => iff_of_false (hA x) (hT x))
        · have hj := hs.predecessor_mem
          have hjΓ := hΓ.transitive i hiΓ j hj
          obtain ⟨p,hp,hPrev⟩ := h.values.total j hjΓ
          obtain ⟨Tj,hTj,hOldPrev⟩ := hOld.values.total j hjΓ
          obtain ⟨θj,Fj,hPrevPacket⟩ := hEarlier j hj hjΓ p hp Tj hTj ⟨hPrev,hOldPrev⟩
          obtain ⟨B,hSucc⟩ := ranked_history_successor_d hM hΓ hGood h hiΓ hs hRows.1 hPrev
          obtain ⟨SW,hSW⟩ := successor_packet_stage_d hM e hPrevPacket hPacket hSucc
          obtain ⟨D,hDef⟩ := KP1Y.Constructible.history_successor_value_d hM hΓ hOld hiΓ hs hRows.2 hOldPrev
          obtain ⟨SW',_,hSW'⟩ := (defSuccessorMatrix_iff hM (baseEnv e) Tj T D).mp hDef
          exact hSW.output_unique_d hM hS.interpretation.spaces.omega hS.spaces.omega hSW'
        · have hA := ranked_history_union_d hM hGood h hiΓ
            (KP1Y.Constructible.no_predecessor_of_limit_d hM hLimit) hRows.1 hPacket
          have hT := KP1Y.Constructible.history_limit_value_d hM hOld hiΓ hLimit hRows.2
          apply hM.1.eq_of_same_members
          intro x
          constructor
          · intro hx
            obtain ⟨j,hj,p,hAt,Aj,θj,Fj,hPj,hxAj⟩ := (hA x).mp hx
            have hjΓ := hΓ.transitive i hiΓ j hj
            obtain ⟨Tj,hTj,hOldAt⟩ := hOld.values.total j hjΓ
            obtain ⟨θj',Fj',hPj'⟩ := hEarlier j hj hjΓ p (h.values.bounds hM.1 hAt).2 Tj hTj ⟨hAt,hOldAt⟩
            have hAj := (hPj.injective hM.1 hPj').1
            exact (hT x).mpr ⟨j,hj,Tj,hOldAt,hAj ▸ hxAj⟩
          · intro hx
            obtain ⟨j,hj,Tj,hOldAt,hxTj⟩ := (hT x).mp hx
            have hjΓ := hΓ.transitive i hiΓ j hj
            obtain ⟨p,hp,hAt⟩ := h.values.total j hjΓ
            obtain ⟨θj,Fj,hPj⟩ := hEarlier j hj hjΓ p hp Tj (hOld.values.bounds hM.1 hOldAt).2 ⟨hAt,hOldAt⟩
            exact (hA x).mpr ⟨j,hj,p,hAt,Tj,θj,Fj,hPj,hxTj⟩
      exact ⟨θ,F,hAT ▸ hPacket⟩)
  intro i Out T hAt hOldAt
  have hi := (h.values.bounds hM.1 hAt).1
  exact (comparisonSchema_iff hM.1 H G Γ V U i).mp (hAll i (hΓ.mem hi)) hi
    Out (h.values.bounds hM.1 hAt).2 T (hOld.values.bounds hM.1 hOldAt).2 ⟨hAt,hOldAt⟩

end KP1Y.ConstructibleRank
