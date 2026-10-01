import KP1Y.SequenceRankCertificate
import KP1Y.ProductRankCertificate
import KP1Y.LeastImageRankCertificate

/-! Def排名的固定算法：参数序列排名、定义代码乘积排名、最小定义代码排名。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal
universe u v

structure DefRankWitness (α : Type u) where
  sequences : SequenceRankWitness α
  sequenceBound : α
  sequenceRank : α
  columnRank : α
  productWitness : α
  rowsWitness : α

def DefRankWitness.map {α : Type u} {β : Type v} (W : DefRankWitness α) (f : α → β) : DefRankWitness β :=
  ⟨W.sequences.map f,f W.sequenceBound,f W.sequenceRank,f W.columnRank,f W.productWitness,f W.rowsWitness⟩

def DefRankWitness.eval {M : SetTheory.Structure.{u}} {n : Nat}
    (W : DefRankWitness (Project.Term n)) (e : Env M n) : DefRankWitness M.Domain := W.map (fun t => t.eval e)

structure DefRankWitness.Valid (M : SetTheory.Structure.{u})
    (ω FA A α FP Programs π Values Columns Definitions Def Γ R : M.Domain) (W : DefRankWitness M.Domain) : Prop where
  sequences : W.sequences.Valid M ω FA A α Values W.sequenceBound W.sequenceRank
  columns : ProductRankCertificate M FP W.sequenceRank Programs Values π W.sequenceBound Columns Γ W.columnRank W.productWitness W.rowsWitness
  image : LeastImageRankCertificate M W.columnRank Definitions Columns Def Γ R

def defRankWitnessFormula {n : Nat} (ω FA A α FP Programs π Values Columns Definitions Def Γ R : Project.Term n)
    (W : DefRankWitness (Project.Term n)) : Project.Formula 1 n :=
  .conj (sequenceRankWitnessFormula ω FA A α Values W.sequenceBound W.sequenceRank W.sequences)
    (.conj (productRankCertificateFormula FP W.sequenceRank Programs Values π W.sequenceBound Columns Γ W.columnRank W.productWitness W.rowsWitness)
      (leastImageRankCertificateFormula W.columnRank Definitions Columns Def Γ R))

theorem defRankWitnessFormula_delta0 {n : Nat} (ω FA A α FP Programs π Values Columns Definitions Def Γ R : Project.Term n)
    (W : DefRankWitness (Project.Term n)) : (defRankWitnessFormula ω FA A α FP Programs π Values Columns Definitions Def Γ R W).IsDelta0 :=
  .conj (sequenceRankWitnessFormula_delta0 _ _ _ _ _ _ _ _) (.conj (productRankCertificateFormula_delta0 _ _ _ _ _ _ _ _ _ _ _)
    (leastImageRankCertificateFormula_delta0 _ _ _ _ _ _))

def DefRankWitness.Closed {n : Nat} (W : DefRankWitness (Project.Term n)) : Prop :=
  W.sequences.Closed ∧ W.sequenceBound.freeSupport=[] ∧ W.sequenceRank.freeSupport=[] ∧ W.columnRank.freeSupport=[] ∧
    W.productWitness.freeSupport=[] ∧ W.rowsWitness.freeSupport=[]

theorem defRankWitnessFormula_freeClosed {n : Nat} (ω FA A α FP Programs π Values Columns Definitions Def Γ R : Project.Term n)
    (W : DefRankWitness (Project.Term n)) (hω : ω.freeSupport=[]) (hFA : FA.freeSupport=[])
    (hA : A.freeSupport=[]) (hα : α.freeSupport=[]) (hFP : FP.freeSupport=[]) (hPrograms : Programs.freeSupport=[])
    (hπ : π.freeSupport=[]) (hValues : Values.freeSupport=[]) (hColumns : Columns.freeSupport=[])
    (hDefinitions : Definitions.freeSupport=[]) (hDef : Def.freeSupport=[]) (hΓ : Γ.freeSupport=[])
    (hR : R.freeSupport=[]) (hW : W.Closed) :
    (defRankWitnessFormula ω FA A α FP Programs π Values Columns Definitions Def Γ R W).FreeClosed := by
  obtain ⟨hSW,hSB,hSR,hCR,hPW,hRW⟩ := hW
  simp only [defRankWitnessFormula,Definitional.Formula.FreeClosed]
  exact ⟨sequenceRankWitnessFormula_freeClosed _ _ _ _ _ _ _ _ hω hFA hA hα hValues hSB hSR hSW,
    productRankCertificateFormula_freeClosed _ _ _ _ _ _ _ _ _ _ _ hFP hSR hPrograms hValues hπ hSB hColumns hΓ hCR hPW hRW,
    leastImageRankCertificateFormula_freeClosed _ _ _ _ _ _ hCR hDefinitions hColumns hDef hΓ hR⟩

theorem defRankWitnessFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (ω FA A α FP Programs π Values Columns Definitions Def Γ R : Project.Term n)
    (W : DefRankWitness (Project.Term n)) :
    Project.Formula.satisfies e (defRankWitnessFormula ω FA A α FP Programs π Values Columns Definitions Def Γ R W) ↔
      DefRankWitness.Valid M (ω.eval e) (FA.eval e) (A.eval e) (α.eval e) (FP.eval e) (Programs.eval e) (π.eval e)
        (Values.eval e) (Columns.eval e) (Definitions.eval e) (Def.eval e) (Γ.eval e) (R.eval e) (W.eval e) := by
  simp only [defRankWitnessFormula,Project.Formula.satisfies_conj_iff,sequenceRankWitnessFormula_iff hM,
    productRankCertificateFormula_iff hM,leastImageRankCertificateFormula_iff hM.1]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.sequences,h.columns,h.image⟩⟩

theorem def_rank_witness_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω FA A α FP Programs π Values Columns Definitions Def : M.Domain} (hω : M.IsOmega ω)
    (hFA : OrdinalRank M FA A α) (hFP : OrdinalRank M FP Programs π)
    (hValues : ∀ s, M.mem s Values ↔ ∃ n, M.mem n ω ∧ Graph M s n A)
    (hColumns : IsProduct M Columns Programs Values) (hDefinitions : Onto M Definitions Columns Def) :
    ∃ Γ R W, DefRankWitness.Valid M ω FA A α FP Programs π Values Columns Definitions Def Γ R W := by
  obtain ⟨β,FV,SW,hSW⟩ := sequence_rank_witness_exists_d hM hω hFA hValues
  have hFV := hSW.rank_d hM hω hFA
  obtain ⟨Γ,FC,BP,BG,hProduct⟩ := product_rank_certificate_exists_d hM hFP hFV hColumns
  obtain ⟨R,hImage⟩ := least_image_rank_certificate_exists_d hM (hProduct.rank_d hM hFP hFV) hDefinitions
  exact ⟨Γ,R,⟨SW,β,FV,FC,BP,BG⟩,hSW,hProduct,hImage⟩

theorem DefRankWitness.Valid.rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω FA A α FP Programs π Values Columns Definitions Def Γ R : M.Domain} {W : DefRankWitness M.Domain}
    (hω : M.IsOmega ω) (hFA : OrdinalRank M FA A α) (hFP : OrdinalRank M FP Programs π)
    (hDefinitions : Graph M Definitions Columns Def)
    (h : W.Valid M ω FA A α FP Programs π Values Columns Definitions Def Γ R) : OrdinalRank M R Def Γ :=
  h.image.rank_d hM.1 (h.columns.rank_d hM hFP (h.sequences.rank_d hM hω hFA)) hDefinitions

theorem DefRankWitness.Valid.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω FA A α FP Programs π Values Columns Definitions Def Γ R Γ' R' : M.Domain} {W W' : DefRankWitness M.Domain}
    (hω : M.IsOmega ω) (hFP : Graph M FP Programs π)
    (h : W.Valid M ω FA A α FP Programs π Values Columns Definitions Def Γ R)
    (h' : W'.Valid M ω FA A α FP Programs π Values Columns Definitions Def Γ' R') : Γ=Γ' ∧ R=R' := by
  rcases W with ⟨SW,β,FV,FC,BP,BG⟩
  rcases W' with ⟨SW',β',FV',FC',BP',BG'⟩
  obtain ⟨hβ,hFV⟩ := h.sequences.unique_d hM hω h'.sequences
  change β=β' at hβ
  change FV=FV' at hFV
  subst β'
  subst FV'
  obtain ⟨hΓ,hFC⟩ := h.columns.unique_d hM hFP h.sequences.composition.values h'.columns
  change FC=FC' at hFC
  subst Γ'
  subst FC'
  exact ⟨rfl,h.image.unique hM.1 (h.columns.range.meaning.isOrdinal_d hM) h'.image⟩

end KP1Y.Ranking
