import KP1Y.OneYNaturalAdditionFacts

/-! 内部自然数乘法闭合与实际全局乘法表。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def mulFormula {n : Nat} (a b c : Project.Term n) : Project.Formula 1 n :=
  .existsE (KP1Y.Arithmetic.productCertificateFormula a.weaken b.weaken c.weaken (.bound 0))

theorem mulFormula_freeClosed {n : Nat} (a b c : Project.Term n)
    (ha : a.freeSupport=[]) (hb : b.freeSupport=[]) (hc : c.freeSupport=[]) : (mulFormula a b c).FreeClosed := by
  unfold mulFormula
  simpa only [Definitional.Formula.FreeClosed] using
    (KP1Y.Arithmetic.productCertificateFormula_freeClosed (n := n+1) a.weaken b.weaken c.weaken (.bound 0)
      (by simpa using ha) (by simpa using hb) (by simpa using hc) rfl)

theorem mulFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (a b c : Project.Term n) :
    Project.Formula.satisfies e (mulFormula a b c) ↔ KP1Y.Arithmetic.Product M (a.eval e) (b.eval e) (c.eval e) := by
  simp only [mulFormula,Project.Formula.satisfies_exists_iff,KP1Y.Arithmetic.productCertificateFormula_iff hM,Term.eval_weaken]
  constructor
  · rintro ⟨B,hB⟩
    exact hB.meaning
  · intro h
    obtain ⟨B,hB⟩ := (KP1Y.Arithmetic.product_sigmaOne_iff_d hM (oneEnv (a.eval e)) (b.eval e) (c.eval e)).mp h
    exact ⟨B,(KP1Y.Arithmetic.productMatrix_iff hM (oneEnv (a.eval e)) (b.eval e) (c.eval e) B).mp hB⟩

private def naturalProductSchema : Project.UnarySchema 2 where
  body := .forallE (.imp (mulFormula (.bound 2) (.bound 1) (.bound 0)) (.mem (.bound 0) (.bound 3)))
  freeClosed := by
    have h := mulFormula_freeClosed (n := 4) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h]

private theorem naturalProductSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (w a b : M.Domain) :
    Project.Formula.satisfies (((oneEnv w).push a).push b) naturalProductSchema.body ↔
      ∀ c, KP1Y.Arithmetic.Product M a b c → M.mem c w := by
  simp only [naturalProductSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    mulFormula_iff hM,Project.Formula.satisfies_mem_iff]
  rfl

theorem natural_product_closed_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hP : KP1Y.Arithmetic.Product M a b c) : M.mem c C.omega := by
  have hOrd := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM naturalProductSchema ((oneEnv C.omega).push a) hC.omega
    (by
      intro z hz
      apply (naturalProductSchema_iff hM C.omega a z).mpr
      intro c hc
      have hcz := hM.1.eq_of_same_members c C.zero (fun x => iff_of_false (hc.zero_value_d hM hz x) (hC.zero_empty x))
      exact hcz ▸ hC.zero_nat)
    (by
      intro p hp ih b hs
      apply (naturalProductSchema_iff hM C.omega a b).mpr
      intro c hc
      obtain ⟨d,hd⟩ := KP1Y.Arithmetic.product_exists_d hM (hOrd.mem ha) (hOrd.mem hp)
      have hdNat := (naturalProductSchema_iff hM C.omega a p).mp ih d hd
      exact natural_sum_closed_d hM hC.omega hdNat ha (KP1Y.Arithmetic.product_successor_d hM hs hd hc))
  exact (naturalProductSchema_iff hM C.omega a b).mp (hAll b hb) c hP

theorem natural_product_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) : ∃ c, M.mem c C.omega ∧ KP1Y.Arithmetic.Product M a b c := by
  have hOrd := omega_isOrdinal_d hM hC.omega
  obtain ⟨c,hc⟩ := KP1Y.Arithmetic.product_exists_d hM (hOrd.mem ha) (hOrd.mem hb)
  exact ⟨c,natural_product_closed_d hM hC ha hb hc,hc⟩

private def multiplicationTableMatrix : KP1Y.WitnessMatrix 1 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 4)
    (.conj (codeFormula (.bound 4) (.bound 1) (.bound 0))
      (KP1Y.Arithmetic.productCertificateFormula (.bound 1) (.bound 0) (.bound 3) (.bound 2))))
  freeClosed := by
    have hP := KP1Y.Arithmetic.productCertificateFormula_freeClosed (n := 6) (.bound 1) (.bound 0) (.bound 3) (.bound 2) rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,codeFormula,pairFormula,Project.Formula.forallMem,hP]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (KP1Y.Arithmetic.productCertificateFormula_delta0 _ _ _ _)))

private theorem multiplicationTableMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (w key c B : M.Domain) :
    Project.Formula.satisfies ((((oneEnv w).push key).push c).push B) multiplicationTableMatrix.body ↔
      ∃ a, M.mem a w ∧ ∃ b, M.mem b w ∧ Codes M key a b ∧ KP1Y.Arithmetic.ProductCertificate M a b c B := by
  simp only [multiplicationTableMatrix,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff hM.1,KP1Y.Arithmetic.productCertificateFormula_iff hM]
  rfl

structure MultiplicationTable (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Pairs Times : M.Domain) : Prop where
  pairs : IsProduct M Pairs C.omega C.omega
  graph : Graph M Times Pairs C.omega
  rows : ∀ a, M.mem a C.omega → ∀ b, M.mem b C.omega → ∀ key, Codes M key a b →
    ∀ c, MemPair M Times key c ↔ KP1Y.Arithmetic.Product M a b c

theorem multiplication_table_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) : ∃ Pairs Times, MultiplicationTable M C Pairs Times := by
  obtain ⟨Pairs,hPairs⟩ := product_exists hM C.omega C.omega
  have hTotal : ∀ key, M.mem key Pairs → ∃ c B,
      Project.Formula.satisfies ((((oneEnv C.omega).push key).push c).push B) multiplicationTableMatrix.body := by
    intro key hk
    obtain ⟨a,ha,b,hb,hCode⟩ := (hPairs key).mp hk
    obtain ⟨c,_,hP⟩ := natural_product_exists_d hM hC ha hb
    obtain ⟨B,hB⟩ := (KP1Y.Arithmetic.product_sigmaOne_iff_d hM (oneEnv a) b c).mp hP
    exact ⟨c,B,(multiplicationTableMatrix_iff hM C.omega key c B).mpr
      ⟨a,ha,b,hb,hCode,(KP1Y.Arithmetic.productMatrix_iff hM (oneEnv a) b c B).mp hB⟩⟩
  obtain ⟨Times,hGraph,hRows⟩ := sigma_function_graph_d hM multiplicationTableMatrix (oneEnv C.omega) Pairs C.omega hTotal
    (fun key _ c B hB => by
      obtain ⟨a,ha,b,hb,_,hCert⟩ := (multiplicationTableMatrix_iff hM C.omega key c B).mp hB
      exact natural_product_closed_d hM hC ha hb hCert.meaning)
    (fun key _ c d B D hB hD => by
      obtain ⟨a,_,b,_,hCode,hCert⟩ := (multiplicationTableMatrix_iff hM C.omega key c B).mp hB
      obtain ⟨a',_,b',_,hCode',hCert'⟩ := (multiplicationTableMatrix_iff hM C.omega key d D).mp hD
      obtain ⟨haa,hbb⟩ := codes_injective hM.1 hCode hCode'
      subst a'
      subst b'
      exact KP1Y.Arithmetic.product_unique_d hM hCert.meaning hCert'.meaning)
  refine ⟨Pairs,Times,hPairs,hGraph,?_⟩
  intro a ha b hb key hCode c
  constructor
  · intro hAt
    obtain ⟨_,_,B,hB⟩ := (hRows key c).mp hAt
    obtain ⟨a',_,b',_,hCode',hCert⟩ := (multiplicationTableMatrix_iff hM C.omega key c B).mp hB
    obtain ⟨haa,hbb⟩ := codes_injective hM.1 hCode hCode'
    subst a'
    subst b'
    exact hCert.meaning
  · intro hP
    obtain ⟨B,hB⟩ := (KP1Y.Arithmetic.product_sigmaOne_iff_d hM (oneEnv a) b c).mp hP
    exact (hRows key c).mpr ⟨(hPairs key).mpr ⟨a,ha,b,hb,hCode⟩,natural_product_closed_d hM hC ha hb hP,
      B,(multiplicationTableMatrix_iff hM C.omega key c B).mpr
        ⟨a,ha,b,hb,hCode,(KP1Y.Arithmetic.productMatrix_iff hM (oneEnv a) b c B).mp hB⟩⟩

def MulAt (M : SetTheory.Structure.{u}) (Pairs Times a b c : M.Domain) : Prop :=
  ∃ key, M.mem key Pairs ∧ Codes M key a b ∧ MemPair M Times key c

def mulAtFormula {n : Nat} (Pairs Times a b c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Pairs (.conj (codeFormula (.bound 0) a.weaken b.weaken)
    (memPairFormula Times.weaken (.bound 0) c.weaken))

theorem mulAtFormula_delta0 {n : Nat} (Pairs Times a b c : Project.Term n) : (mulAtFormula Pairs Times a b c).IsDelta0 :=
  .existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem mulAtFormula_freeClosed {n : Nat} (Pairs Times a b c : Project.Term n)
    (hp : Pairs.freeSupport=[]) (ht : Times.freeSupport=[]) (ha : a.freeSupport=[])
    (hb : b.freeSupport=[]) (hc : c.freeSupport=[]) : (mulAtFormula Pairs Times a b c).FreeClosed := by
  simp [mulAtFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hp,ht,ha,hb,hc]

theorem mulAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (Pairs Times a b c : Project.Term n) : Project.Formula.satisfies e (mulAtFormula Pairs Times a b c) ↔
      MulAt M (Pairs.eval e) (Times.eval e) (a.eval e) (b.eval e) (c.eval e) := by
  simp only [mulAtFormula,MulAt,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem MultiplicationTable.mul_iff_product {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {Pairs Times a b c : M.Domain} (hTable : MultiplicationTable M C Pairs Times)
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) : MulAt M Pairs Times a b c ↔ KP1Y.Arithmetic.Product M a b c := by
  constructor
  · rintro ⟨key,_,hCode,hAt⟩
    exact (hTable.rows a ha b hb key hCode c).mp hAt
  · intro hP
    obtain ⟨key,hCode⟩ := codes_total hM a b
    exact ⟨key,(hTable.pairs key).mpr ⟨a,ha,b,hb,hCode⟩,hCode,(hTable.rows a ha b hb key hCode c).mpr hP⟩

theorem MultiplicationTable.mul_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Times a b : M.Domain} (hTable : MultiplicationTable M C Pairs Times)
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) : ∃ c, M.mem c C.omega ∧ MulAt M Pairs Times a b c := by
  obtain ⟨c,hc,hP⟩ := natural_product_exists_d hM hC ha hb
  exact ⟨c,hc,(hTable.mul_iff_product hM ha hb).mpr hP⟩

theorem MultiplicationTable.mul_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {Pairs Times a b c d : M.Domain} (hTable : MultiplicationTable M C Pairs Times)
    (hc : MulAt M Pairs Times a b c) (hd : MulAt M Pairs Times a b d) : c=d := by
  obtain ⟨key,_,hCode,hAt⟩ := hc
  obtain ⟨key',_,hCode',hAt'⟩ := hd
  have hkk := codes_unique he hCode hCode'
  subst key'
  exact hTable.graph.unique key c d hAt hAt'

end KP1Y.OneYFinite
