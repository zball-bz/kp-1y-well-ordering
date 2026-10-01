import KP1Y.ConstructibleCollectionSyntax

/-! 构造类满足普通KP的全部Δ₀收集实例：有效见证界于某层，该层本身作为收集输出。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes KP1Y.SetLanguage
universe u

theorem inner_collection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {n : Nat} (φ : Project.Delta0BinarySchema n)
    (e : Env (innerModel hM env hS) n) (a : (innerModel hM env hS).Domain)
    (hTotal : ∀ x, (innerModel hM env hS).mem x a → ∃ y, Project.Formula.satisfies ((e.push x).push y) φ.body) :
    ∃ b, ∀ x, (innerModel hM env hS).mem x a → ∃ y, (innerModel hM env hS).mem y b ∧
      Project.Formula.satisfies ((e.push x).push y) φ.body := by
  have hTotalM : ∀ x, M.mem x a.val → ∃ y B,
      Project.Formula.satisfies ((((joinedEnv (forgetEnv e) env).push x).push y).push B)
        (constructibleRelationMatrix φ).body := by
    intro x hx
    let x0 : (innerModel hM env hS).Domain := ⟨x,a.property.mem_closed_d hM env hS hx⟩
    obtain ⟨y,hφ⟩ := hTotal x0 hx
    obtain ⟨B,hB⟩ := (constructible_sigmaOne_iff_d hM env y.val).mp y.property
    have hExternal := (inner_delta0_absolute_d hM env hS φ.delta0 ((e.push x0).push y)).mp hφ
    refine ⟨y.val,B,(constructibleRelationMatrix_iff hM φ (forgetEnv e) env x y.val B).mpr
      ⟨?_,(constructibleMatrix_iff hM env y.val B).mp hB⟩⟩
    have hEnv := (forgetEnv_push (e.push x0) y).trans
      (congrArg (fun s : Env M (n+1) => s.push y.val) (forgetEnv_push e x0))
    exact Eq.mp (congrArg (fun s : Env M (n+2) => Project.Formula.satisfies s φ.body) hEnv) hExternal
  obtain ⟨W,hW⟩ := KP1Y.joint_collection_d hM (constructibleRelationMatrix φ) (joinedEnv (forgetEnv e) env) a.val hTotalM
  obtain ⟨F,hRawF⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) boundedConstructibleSchema (env.push W) W
  have hF (y : M.Domain) : M.mem y F ↔ M.mem y W ∧ ∃ B, M.mem B W ∧ ConstructibleCertificate M env y B := by
    simpa only [boundedConstructibleSchema_iff hM] using hRawF y
  have hInClass : ∀ y, M.mem y F → InConstructible M env y := by
    intro y hy
    obtain ⟨_,B,_,hB⟩ := (hF y).mp hy
    exact hB.in_class
  obtain ⟨β,T,hT,hSub⟩ := constructible_set_bounded_d hM env hS F hInClass
  refine ⟨⟨T,hT.constructible_d hM env hS⟩,?_⟩
  intro x hx
  obtain ⟨y,hyW,B,hBW,hWitness⟩ := hW x.val hx
  obtain ⟨hφM,hB⟩ := (constructibleRelationMatrix_iff hM φ (forgetEnv e) env x.val y B).mp hWitness
  let y0 : (innerModel hM env hS).Domain := ⟨y,hB.in_class⟩
  refine ⟨y0,hSub y ((hF y).mpr ⟨hyW,B,hBW,hB⟩),?_⟩
  apply (inner_delta0_absolute_d hM env hS φ.delta0 ((e.push x).push y0)).mpr
  have hEnv := (forgetEnv_push (e.push x) y0).trans
    (congrArg (fun s : Env M (n+1) => s.push y0.val) (forgetEnv_push e x))
  exact Eq.mpr (congrArg (fun s : Env M (n+2) => Project.Formula.satisfies s φ.body) hEnv) hφM

theorem inner_collection_axiom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {n : Nat} (φ : Project.Delta0BinarySchema n)
    (free : FreeVarId → (innerModel hM env hS).Domain) :
    Project.Formula.satisfies ({bound := Fin.elim0,free := free} : Env (innerModel hM env hS) 0)
      (Axioms.Schema.collection φ.toBinarySchema).formula := by
  apply (Project.Formula.satisfies_forallClosure_iff free (Axioms.Schema.collectionCore φ.toBinarySchema)).mpr
  intro bound
  let e : Env (innerModel hM env hS) n := ⟨bound,free⟩
  apply (Axioms.Schema.collection_sat_iff_d e φ.toBinarySchema).mpr
  exact inner_collection_d hM env hS φ e

end KP1Y.Constructible
