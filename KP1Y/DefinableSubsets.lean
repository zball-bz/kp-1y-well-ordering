import KP1Y.DefinableSubsetsSyntax

/-! 不使用幂集：逐代码作 Δ₀ 分离，再用全定义 Δ₀ 像集形成全部定义子集。 -/
namespace KP1Y.Definability
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

theorem defined_by_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : Context M.Domain) (D : RelationalData M.Domain) (Sat zero c : M.Domain) :
    ∃ S, DefinedBy M C D Sat zero c S := by
  obtain ⟨S,hS⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) definitionPointSchema
    ((((syntaxEnv C D).push Sat).push zero).push c) C.carrier
  have hRows (x : M.Domain) : M.mem x S ↔ M.mem x C.carrier ∧ DefinitionPoint M C D Sat zero c x := by
    simpa only [definitionPointSchema_iff hM.1] using hS x
  exact ⟨S,fun x hx => ((hRows x).mp hx).1,
    fun x hx => (hRows x).trans ⟨And.right,fun h => ⟨hx,h⟩⟩⟩

theorem defined_by_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {D : RelationalData M.Domain} {Sat zero c S T : M.Domain}
    (hS : DefinedBy M C D Sat zero c S) (hT : DefinedBy M C D Sat zero c T) : S=T := by
  apply he.eq_of_same_members
  intro x
  exact ⟨fun hx => (hT.2 x (hS.1 x hx)).mpr ((hS.2 x (hS.1 x hx)).mp hx),
    fun hx => (hS.2 x (hT.1 x hx)).mpr ((hT.2 x (hT.1 x hx)).mp hx)⟩

def DefSet (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (Sat zero Def : M.Domain) : Prop :=
  ∀ S, M.mem S Def ↔ ∃ c, M.mem c C.columns ∧ DefinedBy M C D Sat zero c S

theorem def_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : Context M.Domain) (D : RelationalData M.Domain) (Sat zero : M.Domain) : ∃ Def, DefSet M C D Sat zero Def := by
  obtain ⟨Def,hDef⟩ := KP1Y.functional_image_d hM definedBySchema (((syntaxEnv C D).push Sat).push zero) C.columns
    (fun c _ => by
      obtain ⟨S,hS⟩ := defined_by_exists_d hM C D Sat zero c
      exact ⟨S,(definedBySchema_iff hM.1 C D Sat zero c S).mpr hS⟩)
    (fun c _ S T hS hT => defined_by_unique hM.1
      ((definedBySchema_iff hM.1 C D Sat zero c S).mp hS)
      ((definedBySchema_iff hM.1 C D Sat zero c T).mp hT))
  refine ⟨Def,fun S => ?_⟩
  simpa only [definedBySchema_iff hM.1] using hDef S

theorem DefSet.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Context M.Domain} {D : RelationalData M.Domain}
    {Sat zero Def Def' : M.Domain} (h : DefSet M C D Sat zero Def) (h' : DefSet M C D Sat zero Def') : Def=Def' :=
  he.eq_of_same_members Def Def' (fun S => (h S).trans (h' S).symm)

theorem DefSet.member_subset {M : SetTheory.Structure.{u}} {C : Context M.Domain} {D : RelationalData M.Domain}
    {Sat zero Def S : M.Domain} (h : DefSet M C D Sat zero Def) (hS : M.mem S Def) : M.MemberSubset S C.carrier := by
  obtain ⟨_,_,hDefined⟩ := (h S).mp hS
  exact hDefined.1

theorem empty_member_def_set_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {Sat zero Def e : M.Domain} (hDef : DefSet M C D Sat zero Def) (hEmpty : ∀ x, ¬M.mem x e) : M.mem e Def := by
  obtain ⟨z,hz,hzω⟩ := hC.omega.1.1
  have hez := hM.1.eq_of_same_members e z (fun x => iff_of_false (hEmpty x) (hz x))
  have heω : M.mem e C.omega := hez ▸ hzω
  have hp := (hC.programs e).mpr ⟨e,heω,empty_graph hEmpty⟩
  have hs := (hC.assignments e).mpr ⟨e,heω,empty_graph hEmpty⟩
  obtain ⟨c,hCode⟩ := codes_total hM e e
  have hc := (hC.columns c).mpr ⟨e,hp,e,hs,hCode⟩
  have hNotValid : ¬ValidColumn M C D c := by
    rintro ⟨p,_,s,_,hCode',length,_,bound,_,hP,_⟩
    obtain ⟨hep,_⟩ := codes_injective hM.1 hCode hCode'
    subst p
    obtain ⟨i,hi⟩ := hP.2
    obtain ⟨instr,_,pair,hPair,_⟩ := hP.1.graph.total i hi
    exact hEmpty pair hPair
  have hDefined : DefinedBy M C D Sat zero c e :=
    ⟨fun x hx => False.elim (hEmpty x hx),fun x _ => iff_of_false (hEmpty x) (fun h => hNotValid h.1)⟩
  exact (hDef e).mpr ⟨c,hc,hDefined⟩

end KP1Y.Definability
