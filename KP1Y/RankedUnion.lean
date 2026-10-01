import KP1Y.RankedUnionSyntax

/-! 已排名历史的并集操作：Σ₁全定义/单值、实际排名和载域并集方程。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem finite_list_container_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (xs : List M.Domain) : ∃ B, ∀ x, x∈xs → M.mem x B := by
  induction xs with
  | nil =>
      obtain ⟨B,_⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
      exact ⟨B,fun x hx => False.elim (List.not_mem_nil hx)⟩
  | cons x xs ih =>
      obtain ⟨B,hB⟩ := ih
      obtain ⟨C,hC⟩ := SetTheory.KP.exists_insert (KP1Y.models_weakKP hM) B x
      refine ⟨C,?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with he | hy
      · exact (hC y).mpr (Or.inr he)
      · exact (hC y).mpr (Or.inl (hB y hy))

theorem ranked_union_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 1) {H V : M.Domain} (hI : M.IsOrdinal (e.bound 0)) (hH : RankedFamily M H (e.bound 0) V) :
    ∃ Out B, Project.Formula.satisfies (((e.push H).push Out).push B) rankedUnionMatrix.body := by
  obtain ⟨A,κ,Γ,R,BP,BG,W,hCert⟩ := limit_rank_certificate_exists_d hM hI hH
  obtain ⟨q,hq⟩ := codes_total hM Γ R
  obtain ⟨Out,hOut⟩ := codes_total hM A q
  obtain ⟨B,hB⟩ := finite_list_container_d hM [V,A,κ,Γ,R,q,W.first,W.second,W.third,W.fourth,W.fifth,BP,BG]
  refine ⟨Out,B,(rankedUnionMatrix_iff hM e H Out B).mpr
    ⟨V,hB V (by simp),A,hB A (by simp),κ,hB κ (by simp),Γ,hB Γ (by simp),R,hB R (by simp),q,hB q (by simp),
      W,?_,BP,hB BP (by simp),BG,hB BG (by simp),hOut,hq,hCert⟩⟩
  exact ⟨hB _ (by simp),hB _ (by simp),hB _ (by simp),hB _ (by simp),hB _ (by simp)⟩

theorem ranked_union_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 1) {H Out Out' B B' : M.Domain}
    (h : Project.Formula.satisfies (((e.push H).push Out).push B) rankedUnionMatrix.body)
    (h' : Project.Formula.satisfies (((e.push H).push Out').push B') rankedUnionMatrix.body) : Out=Out' := by
  obtain ⟨V,_,A,_,κ,_,Γ,_,R,_,q,_,W,_,BP,_,BG,_,hOut,hq,hCert⟩ := (rankedUnionMatrix_iff hM e H Out B).mp h
  obtain ⟨V',_,A',_,κ',_,Γ',_,R',_,q',_,W',_,BP',_,BG',_,hOut',hq',hCert'⟩ := (rankedUnionMatrix_iff hM e H Out' B').mp h'
  obtain ⟨hA,_,hΓ,hR⟩ := hCert.unique_d hM hCert'
  subst A'
  subst Γ'
  subst R'
  have hqq' := codes_unique hM.1 hq hq'
  subst q'
  exact codes_unique hM.1 hOut hOut'

theorem ranked_union_ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 1) {H Out B : M.Domain}
    (h : Project.Formula.satisfies (((e.push H).push Out).push B) rankedUnionMatrix.body) : RankedPacket M Out := by
  obtain ⟨_,_,A,_,_,_,Γ,_,R,_,q,_,_,_,_,_,_,_,hOut,hq,hCert⟩ := (rankedUnionMatrix_iff hM e H Out B).mp h
  exact ⟨A,Γ,R,⟨q,hOut,hq⟩,hCert.rank_d hM⟩

theorem ranked_union_carrier_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 1) {H Out B A Γ R : M.Domain} (hp : Packet M Out A Γ R)
    (h : Project.Formula.satisfies (((e.push H).push Out).push B) rankedUnionMatrix.body) :
    ∃ V κ, RankedFamily M H (e.bound 0) V ∧ FamilyUnions M H (e.bound 0) V A κ := by
  obtain ⟨V,_,A',_,κ,_,Γ',_,R',_,q,_,_,_,_,_,_,_,hOut,hq,hCert⟩ := (rankedUnionMatrix_iff hM e H Out B).mp h
  have hAA' := (hp.injective hM.1 ⟨q,hOut,hq⟩).1
  subst A'
  exact ⟨V,κ,hCert.family,hCert.unions.meaning⟩

end KP1Y.Ranking
