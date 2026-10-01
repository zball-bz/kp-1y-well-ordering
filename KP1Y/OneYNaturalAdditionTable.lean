import KP1Y.OneYFiniteComputation

/-! 实际全局自然数加法表 ω×ω→ω。Σ₁收集统一所有内部输入及加法证书。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

private def additionTableMatrix : KP1Y.WitnessMatrix 1 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 4)
    (.conj (codeFormula (.bound 4) (.bound 1) (.bound 0))
      (KP1Y.Arithmetic.sumCertificateFormula (.bound 1) (.bound 0) (.bound 3) (.bound 2))))
  freeClosed := by
    have hSum := KP1Y.Arithmetic.sumCertificateFormula_freeClosed (n := 6) (.bound 1) (.bound 0) (.bound 3) (.bound 2) rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,codeFormula,pairFormula,Project.Formula.forallMem,hSum]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (KP1Y.Arithmetic.sumCertificateFormula_delta0 _ _ _ _)))

private theorem additionTableMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (w key c B : M.Domain) :
    Project.Formula.satisfies ((((oneEnv w).push key).push c).push B) additionTableMatrix.body ↔
      ∃ a, M.mem a w ∧ ∃ b, M.mem b w ∧ Codes M key a b ∧
        KP1Y.OrdinalIteration.ValueCertificate KP1Y.Arithmetic.successorMatrix (oneEnv a) b c B := by
  simp only [additionTableMatrix,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff hM.1,KP1Y.Arithmetic.sumCertificateFormula_iff hM]
  rfl

structure AdditionTable (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Pairs Plus : M.Domain) : Prop where
  pairs : IsProduct M Pairs C.omega C.omega
  graph : Graph M Plus Pairs C.omega
  rows : ∀ a, M.mem a C.omega → ∀ b, M.mem b C.omega → ∀ key, Codes M key a b →
    ∀ c, MemPair M Plus key c ↔ KP1Y.Arithmetic.Sum M a b c

theorem addition_table_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) : ∃ Pairs Plus, AdditionTable M C Pairs Plus := by
  obtain ⟨Pairs,hPairs⟩ := product_exists hM C.omega C.omega
  have hTotal : ∀ key, M.mem key Pairs → ∃ c B,
      Project.Formula.satisfies ((((oneEnv C.omega).push key).push c).push B) additionTableMatrix.body := by
    intro key hk
    obtain ⟨a,ha,b,hb,hCode⟩ := (hPairs key).mp hk
    obtain ⟨c,_,B,hB⟩ := natural_sum_exists_d hM hC.omega ha hb
    exact ⟨c,B,(additionTableMatrix_iff hM C.omega key c B).mpr ⟨a,ha,b,hb,hCode,hB⟩⟩
  obtain ⟨Plus,hGraph,hRows⟩ := sigma_function_graph_d hM additionTableMatrix (oneEnv C.omega) Pairs C.omega hTotal
    (fun key _ c B hB => by
      obtain ⟨a,ha,b,hb,_,hCert⟩ := (additionTableMatrix_iff hM C.omega key c B).mp hB
      exact natural_sum_closed_d hM hC.omega ha hb ⟨B,hCert⟩)
    (fun key _ c d B D hB hD => by
      obtain ⟨a,ha,b,hb,hCode,hCert⟩ := (additionTableMatrix_iff hM C.omega key c B).mp hB
      obtain ⟨a',ha',b',hb',hCode',hCert'⟩ := (additionTableMatrix_iff hM C.omega key d D).mp hD
      obtain ⟨haa,hbb⟩ := codes_injective hM.1 hCode hCode'
      subst a'
      subst b'
      exact KP1Y.Arithmetic.sum_unique_d hM ⟨B,hCert⟩ ⟨D,hCert'⟩)
  refine ⟨Pairs,Plus,hPairs,hGraph,?_⟩
  intro a ha b hb key hCode c
  constructor
  · intro hAt
    obtain ⟨_,_,B,hB⟩ := (hRows key c).mp hAt
    obtain ⟨a',_,b',_,hCode',hCert⟩ := (additionTableMatrix_iff hM C.omega key c B).mp hB
    obtain ⟨haa,hbb⟩ := codes_injective hM.1 hCode hCode'
    subst a'
    subst b'
    exact ⟨B,hCert⟩
  · intro hSum
    have hc := natural_sum_closed_d hM hC.omega ha hb hSum
    obtain ⟨B,hB⟩ := hSum
    exact (hRows key c).mpr ⟨(hPairs key).mpr ⟨a,ha,b,hb,hCode⟩,hc,B,
      (additionTableMatrix_iff hM C.omega key c B).mpr ⟨a,ha,b,hb,hCode,hB⟩⟩

theorem AdditionTable.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {Pairs Plus Other : M.Domain}
    (h : AdditionTable M C Pairs Plus) (h' : AdditionTable M C Pairs Other) : Plus=Other := by
  apply h.graph.ext he h'.graph
  intro key hk c
  obtain ⟨a,ha,b,hb,hCode⟩ := (h.pairs key).mp hk
  exact (h.rows a ha b hb key hCode c).trans (h'.rows a ha b hb key hCode c).symm

def AddAt (M : SetTheory.Structure.{u}) (Pairs Plus a b c : M.Domain) : Prop :=
  ∃ key, M.mem key Pairs ∧ Codes M key a b ∧ MemPair M Plus key c

def addAtFormula {n : Nat} (Pairs Plus a b c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Pairs (.conj (codeFormula (.bound 0) a.weaken b.weaken)
    (memPairFormula Plus.weaken (.bound 0) c.weaken))

theorem addAtFormula_delta0 {n : Nat} (Pairs Plus a b c : Project.Term n) :
    (addAtFormula Pairs Plus a b c).IsDelta0 :=
  .existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem addAtFormula_freeClosed {n : Nat} (Pairs Plus a b c : Project.Term n)
    (hPairs : Pairs.freeSupport=[]) (hPlus : Plus.freeSupport=[])
    (ha : a.freeSupport=[]) (hb : b.freeSupport=[]) (hc : c.freeSupport=[]) :
    (addAtFormula Pairs Plus a b c).FreeClosed := by
  simp [addAtFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hPairs,hPlus,ha,hb,hc]

theorem addAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (Pairs Plus a b c : Project.Term n) :
    Project.Formula.satisfies e (addAtFormula Pairs Plus a b c) ↔
      AddAt M (Pairs.eval e) (Plus.eval e) (a.eval e) (b.eval e) (c.eval e) := by
  simp only [addAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem AddAt.bounds {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {Pairs Plus a b c : M.Domain}
    (hTable : AdditionTable M C Pairs Plus) (h : AddAt M Pairs Plus a b c) :
    M.mem a C.omega ∧ M.mem b C.omega ∧ M.mem c C.omega := by
  obtain ⟨key,hk,hCode,hAt⟩ := h
  obtain ⟨a',ha,b',hb,hCode'⟩ := (hTable.pairs key).mp hk
  obtain ⟨haa,hbb⟩ := codes_injective he hCode hCode'
  subst a'
  subst b'
  exact ⟨ha,hb,(hTable.graph.bounds he hAt).2⟩

theorem AdditionTable.add_iff_sum {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {Pairs Plus a b c : M.Domain}
    (hTable : AdditionTable M C Pairs Plus) (ha : M.mem a C.omega) (hb : M.mem b C.omega) :
    AddAt M Pairs Plus a b c ↔ KP1Y.Arithmetic.Sum M a b c := by
  constructor
  · rintro ⟨key,_,hCode,hAt⟩
    exact (hTable.rows a ha b hb key hCode c).mp hAt
  · intro hSum
    obtain ⟨key,hCode⟩ := codes_total hM a b
    exact ⟨key,(hTable.pairs key).mpr ⟨a,ha,b,hb,hCode⟩,hCode,(hTable.rows a ha b hb key hCode c).mpr hSum⟩

theorem AdditionTable.add_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus a b : M.Domain}
    (hTable : AdditionTable M C Pairs Plus) (ha : M.mem a C.omega) (hb : M.mem b C.omega) :
    ∃ c, M.mem c C.omega ∧ AddAt M Pairs Plus a b c := by
  obtain ⟨c,hc,hSum⟩ := natural_sum_exists_d hM hC.omega ha hb
  exact ⟨c,hc,(hTable.add_iff_sum hM ha hb).mpr hSum⟩

theorem AdditionTable.add_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {Pairs Plus a b c d : M.Domain}
    (hTable : AdditionTable M C Pairs Plus) (hc : AddAt M Pairs Plus a b c) (hd : AddAt M Pairs Plus a b d) : c=d := by
  obtain ⟨key,_,hCode,hAt⟩ := hc
  obtain ⟨key',_,hCode',hAt'⟩ := hd
  have hkk := codes_unique he hCode hCode'
  subst key'
  exact hTable.graph.unique key c d hAt hAt'

end KP1Y.OneYFinite
