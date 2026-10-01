import KP1Y.ConstructibleParameters
import KP1Y.SetDefComprehension
import KP1Y.SeparationRestriction

/-! 构造类的每个Δ₀分离公理：共同传递层中编译定义，再用绝对性运输到类结构。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Classes KP1Y.SetLanguage
universe u

theorem inner_separation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {n : Nat} (φ : Project.Delta0UnarySchema n)
    (e : Env (innerModel hM env hS) n) (a : (innerModel hM env hS).Domain) :
    ∃ b, ∀ x, (innerModel hM env hS).mem x b ↔ (innerModel hM env hS).mem x a ∧
      Project.Formula.satisfies (e.push x) φ.body := by
  obtain ⟨α,T,hT,haT,hParams⟩ := constructible_parameters_d hM env hS a.property
    (fun i => (e.bound i).val) (fun i => (e.bound i).property)
  have hTrans := hT.transitive_d hM env hS
  let hNeT : ∃ y, M.mem y T := ⟨a.val,haT⟩
  let aT : (classModel M (fun y => M.mem y T) hNeT).Domain := ⟨a.val,haT⟩
  let eT : Env (classModel M (fun y => M.mem y T) hNeT) n :=
    ⟨fun i => ⟨(e.bound i).val,hParams i⟩,fun _ => aT⟩
  obtain ⟨β,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) α
  have hβ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hT.ordinal hs
  obtain ⟨U,hU⟩ := is_level_exists_d hM env hS hβ
  obtain ⟨B,hB⟩ := level_successor_d hM env hS hs hT hU
  obtain ⟨W,_,hW⟩ := (defSuccessorMatrix_iff hM env T U B).mp hB
  obtain ⟨S,hSU,hSub,hDefined⟩ := (hW.stage_d hM hS).comprehension_d hM hTrans hNeT
    (KP1Y.restrictSeparationSchema φ).toUnarySchema (eT.push aT)
  have hAbsolute (x : (innerModel hM env hS).Domain) (hxT : M.mem x.val T) :
      Project.Formula.satisfies (eT.push ⟨x.val,hxT⟩) φ.body ↔ Project.Formula.satisfies (e.push x) φ.body := by
    let xT : (classModel M (fun y => M.mem y T) hNeT).Domain := ⟨x.val,hxT⟩
    have hBound : ∀ i, (forgetEnv (eT.push xT)).bound i=(forgetEnv (e.push x)).bound i := by
      intro i
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    exact (delta0_class_absolute hTrans φ.delta0 (eT.push xT)).trans
      ((KP1Y.formula_bound_congr φ.body φ.freeClosed _ _ hBound).trans
        (inner_delta0_absolute_d hM env hS φ.delta0 (e.push x)).symm)
  have hRows (x : (innerModel hM env hS).Domain) (hxT : M.mem x.val T) :
      M.mem x.val S ↔ M.mem x.val a.val ∧ Project.Formula.satisfies (e.push x) φ.body :=
    (hDefined ⟨x.val,hxT⟩).trans
      ((KP1Y.restrictSeparationSchema_iff φ eT aT ⟨x.val,hxT⟩).trans (and_congr Iff.rfl (hAbsolute x hxT)))
  have hSL : InConstructible M env S := ⟨β,U,hU,hSU⟩
  refine ⟨⟨S,hSL⟩,?_⟩
  intro x
  constructor
  · intro hx
    exact (hRows x (hSub x.val hx)).mp hx
  · rintro ⟨hxa,hφ⟩
    exact (hRows x (hTrans a.val haT x.val hxa)).mpr ⟨hxa,hφ⟩

theorem inner_separation_axiom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {n : Nat} (φ : Project.Delta0UnarySchema n)
    (free : FreeVarId → (innerModel hM env hS).Domain) :
    Project.Formula.satisfies ({bound := Fin.elim0,free := free} : Env (innerModel hM env hS) 0)
      (Axioms.Schema.separation φ.toUnarySchema).formula := by
  apply (Project.Formula.satisfies_forallClosure_iff free (Axioms.Schema.separationCore φ.toUnarySchema)).mpr
  intro bound
  let e : Env (innerModel hM env hS) n := ⟨bound,free⟩
  apply (Axioms.Schema.separation_sat_iff_d e φ.toUnarySchema).mpr
  exact inner_separation_d hM env hS φ e

end KP1Y.Constructible
