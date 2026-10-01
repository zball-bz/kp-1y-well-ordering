import KP1Y.SetDefClosure
import KP1Y.SetRelationTable
import KP1Y.AtomicTableSyntax
import KP1Y.SequenceCertificateTerms
import KP1Y.RestrictedAtoms

/-! 固定全局纯集合语言语法后，Def后继的载域相关证书字段及其语义。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.Satisfaction KP1Y.Definability
universe u v

structure FixedSyntax (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (zero one two : M.Domain) : Prop where
  interpretation : Interpretation M D zero one two
  spaces : ContextSpaces M C
  link : RelationalContext M D C.atomic C

theorem fixed_syntax_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) :
    ∃ C D zero one two, C.omega=ω ∧ FixedSyntax M C D zero one two := by
  obtain ⟨D,zero,one,two,hOmega,_,hI⟩ := interpretation_exists_d hM hω ω
  obtain ⟨C,hLink,hC⟩ := context_spaces_exists_d hM hI.spaces zero
  exact ⟨C,D,zero,one,two,hLink.omega_eq.trans hOmega,hI,hC,
    ⟨hLink.omega_eq,hLink.carrier_eq,hLink.assignments_eq,rfl,hLink.codes_bound⟩⟩

structure StageWitness (α : Type u) where
  values : α
  sequences : α
  relation : α
  atomic : α
  columns : α
  table : α
  raw : α
  typed : α
  definitions : α

def StageWitness.map {α : Type u} {β : Type v} (W : StageWitness α) (f : α → β) : StageWitness β :=
  ⟨f W.values,f W.sequences,f W.relation,f W.atomic,f W.columns,f W.table,f W.raw,f W.typed,f W.definitions⟩

def StageWitness.eval {M : SetTheory.Structure.{u}} {n : Nat}
    (W : StageWitness (Project.Term n)) (env : Env M n) : StageWitness M.Domain := W.map (fun t => t.eval env)

def StageWitness.weaken {n : Nat} (W : StageWitness (Project.Term n)) : StageWitness (Project.Term (n+1)) :=
  W.map (fun t => t.weaken)

def StageWitness.context {α : Type u} (W : StageWitness α) (C : Context α) (A : α) : Context α :=
  C.withInterpretation A W.values W.columns W.atomic

def StageWitness.data {α : Type u} (W : StageWitness α) (D : RelationalData α) (A : α) : RelationalData α :=
  D.withInterpretation A W.values W.relation

theorem StageWitness.eval_context {M : SetTheory.Structure.{u}} {n : Nat} (env : Env M n)
    (W : StageWitness (Project.Term n)) (C : Context (Project.Term n)) (A : Project.Term n) :
    (W.context C A).eval env = (W.eval env).context (C.eval env) (A.eval env) := rfl

theorem StageWitness.eval_data {M : SetTheory.Structure.{u}} {n : Nat} (env : Env M n)
    (W : StageWitness (Project.Term n)) (D : RelationalData (Project.Term n)) (A : Project.Term n) :
    (W.data D A).eval env = (W.eval env).data (D.eval env) (A.eval env) := rfl

structure StageWitness.Valid (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (zero one two A Def : M.Domain) (W : StageWitness M.Domain) : Prop where
  sequences : SpaceCertificate M D.omega A W.values W.sequences
  relation : SetRelationTable M A zero one two D.symbols W.values W.relation
  atomic : AtomicTable M (W.data D A) W.atomic
  columns : IsProduct M W.columns C.programs W.values
  evaluation : Evaluation M (W.context C A) W.table
  raw : TruthSet M (W.context C A) W.table W.raw
  typed : TypedTruthSet M (W.context C A) (W.data D A) W.raw W.typed
  definitions : DefCertificate M (W.context C A) (W.data D A) W.typed zero Def W.definitions

theorem StageWitness.Valid.stage_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two A Def : M.Domain}
    (hS : FixedSyntax M C D zero one two) {W : StageWitness M.Domain} (h : W.Valid M C D zero one two A Def) :
    DefStage M (W.context C A) (W.data D A) zero one two W.table W.raw W.typed Def := by
  have hValues := space_certificate_exact_d hM hS.interpretation.spaces.omega h.sequences
  have hValuesC : ∀ s, M.mem s W.values ↔ ∃ n, M.mem n C.omega ∧ Graph M s n A := by
    intro s
    simpa only [hS.link.omega_eq] using hValues s
  refine ⟨⟨hS.interpretation.naturals,
    ⟨hS.interpretation.spaces.omega,hS.interpretation.spaces.variables,hValues,hS.interpretation.spaces.codes⟩,
    hS.interpretation.symbols,hS.interpretation.arity,hS.interpretation.arity_rows,h.relation.rows⟩,
    ⟨hS.spaces.omega,hS.spaces.distinct,hS.spaces.tag_naturals,hS.spaces.omega_operands,
      hS.spaces.pairs,hS.spaces.instructions,hS.spaces.programs,hValuesC,h.columns⟩,
    ⟨hS.link.omega_eq,rfl,rfl,rfl,hS.link.codes_bound⟩,
    h.atomic,h.evaluation,h.raw,h.typed,def_certificate_exact hM.1 h.definitions⟩

theorem stage_witness_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two : M.Domain}
    (hS : FixedSyntax M C D zero one two) (A : M.Domain) :
    ∃ Def W, StageWitness.Valid M C D zero one two A Def W := by
  obtain ⟨values,sequences,hSeq⟩ := space_certificate_exists_d hM hS.interpretation.spaces.omega A
  obtain ⟨relation,hRelation⟩ := set_relation_table_exists_d hM A zero one two D.symbols values
  obtain ⟨atomic,hAtomic⟩ := atomic_table_exists_d hM (D.withInterpretation A values relation)
  obtain ⟨columns,hColumns⟩ := product_exists hM C.programs values
  let CA := C.withInterpretation A values columns atomic
  let DA := D.withInterpretation A values relation
  obtain ⟨table,hTable⟩ := evaluation_exists_d hM CA hS.spaces.omega
  obtain ⟨raw,hRaw⟩ := truth_set_exists_d hM CA table
  obtain ⟨typed,hTyped⟩ := typed_truth_set_exists_d hM CA DA raw
  obtain ⟨Def,hDef⟩ := def_set_exists_d hM CA DA typed zero
  obtain ⟨definitions,hDefinitions⟩ := def_certificate_exists_d hM hDef
  exact ⟨Def,⟨values,sequences,relation,atomic,columns,table,raw,typed,definitions⟩,
    hSeq,hRelation,hAtomic,hColumns,hTable,hRaw,hTyped,hDefinitions⟩

theorem StageWitness.Valid.output_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two A Def Def' : M.Domain}
    (hω : M.IsOmega D.omega) (hCω : M.IsOmega C.omega) {W W' : StageWitness M.Domain}
    (h : W.Valid M C D zero one two A Def) (h' : W'.Valid M C D zero one two A Def') : Def=Def' := by
  rcases W with ⟨V,B,R,Atom,Col,H,Raw,Sat,F⟩
  rcases W' with ⟨V',B',R',Atom',Col',H',Raw',Sat',F'⟩
  have hV : V=V' := space_certificate_unique_d hM hω h.sequences h'.sequences
  subst V'
  have hR : R=R' := h.relation.unique hM.1 h'.relation
  subst R'
  have hAtom : Atom=Atom' := h.atomic.unique hM.1 h'.atomic
  subst Atom'
  have hCol : Col=Col' := hM.1.eq_of_same_members Col Col' (fun p => (h.columns p).trans (h'.columns p).symm)
  subst Col'
  have hH : H=H' := evaluation_unique_d hM (C := C.withInterpretation A V Col Atom) hCω h.evaluation h'.evaluation
  subst H'
  have hRaw : Raw=Raw' := hM.1.eq_of_same_members Raw Raw' (fun c => (h.raw c).trans (h'.raw c).symm)
  subst Raw'
  have hSat : Sat=Sat' := hM.1.eq_of_same_members Sat Sat' (fun c => (h.typed c).trans (h'.typed c).symm)
  subst Sat'
  exact (def_certificate_exact hM.1 h.definitions).unique hM.1 (def_certificate_exact hM.1 h'.definitions)

end KP1Y.SetLanguage
