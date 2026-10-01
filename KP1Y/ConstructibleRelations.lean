import KP1Y.ConstructibleKP
import KP1Y.ClassSetAbsoluteness
import KP1Y.ClassSchemaTransfer

/-! 构造类对积及带构造参数的实际Δ₀关系表封闭；支持约束与全部查询行同时保留。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes KP1Y.Kuratowski KP1Y.SetLanguage
universe u

theorem pair_set_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {p x y : M.Domain}
    (hx : InConstructible M env x) (hy : InConstructible M env y) (hp : PairSet M p x y) : InConstructible M env p := by
  obtain ⟨p',hp',hPair⟩ := constructible_pair_d hM env hS hx hy
  have hEq := hp.unique hM.1 hPair
  rw [hEq]
  exact hp'

theorem union_of_two_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {U X Y : M.Domain}
    (hX : InConstructible M env X) (hY : InConstructible M env Y) (hU : M.IsUnionOfTwo U X Y) : InConstructible M env U := by
  obtain ⟨p,hp,hPair⟩ := constructible_pair_d hM env hS hX hY
  obtain ⟨V,hV,hUnion⟩ := constructible_union_d hM env hS hp
  have hRows (z : M.Domain) : M.mem z V ↔ M.mem z X ∨ M.mem z Y := by
    constructor
    · intro hz
      obtain ⟨a,ha,hza⟩ := (hUnion z).mp hz
      rcases (hPair a).mp ha with he | he
      · exact Or.inl (he ▸ hza)
      · exact Or.inr (he ▸ hza)
    · rintro (hz | hz)
      · exact (hUnion z).mpr ⟨X,(hPair X).mpr (Or.inl rfl),hz⟩
      · exact (hUnion z).mpr ⟨Y,(hPair Y).mpr (Or.inr rfl),hz⟩
  have hEq := hM.1.eq_of_same_members V U (fun z => (hRows z).trans (hU z).symm)
  exact hEq ▸ hV

theorem product_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {R X Y : M.Domain}
    (hX : InConstructible M env X) (hY : InConstructible M env Y) (hR : IsProduct M R X Y) : InConstructible M env R := by
  let X0 : (innerModel hM env hS).Domain := ⟨X,hX⟩
  let Y0 : (innerModel hM env hS).Domain := ⟨Y,hY⟩
  obtain ⟨R0,hR0⟩ := product_exists (inner_models_kp_d hM env hS) X0 Y0
  have hUp := (product_class_absolute_d hM (constructible_transitive_class_d hM env hS)
    (inner_models_kp_d hM env hS) R0 X0 Y0).mp hR0
  have hEq := hM.1.eq_of_same_members R R0.val (fun p => (hR p).trans (hUp p).symm)
  rw [hEq]
  exact R0.property

theorem relation_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {n : Nat} (φ : Project.Delta0BinarySchema n)
    (e : Env M n) (hParams : ∀ i, InConstructible M env (e.bound i)) {R X Y : M.Domain}
    (hX : InConstructible M env X) (hY : InConstructible M env Y) (hSupport : RelationSupport M R X Y)
    (hRows : ∀ x y, MemPair M R x y ↔ M.mem x X ∧ M.mem y Y ∧ Project.Formula.satisfies ((e.push x).push y) φ.body) :
    InConstructible M env R := by
  let X0 : (innerModel hM env hS).Domain := ⟨X,hX⟩
  let Y0 : (innerModel hM env hS).Domain := ⟨Y,hY⟩
  let e0 : Env (innerModel hM env hS) n := liftParameters e hParams X0
  have hTrans := constructible_transitive_class_d hM env hS
  obtain ⟨R0,hSupport0,hRows0⟩ := relation_comprehension_d (inner_models_kp_d hM env hS) φ e0 X0 Y0
  have hSupportM := (relationSupport_class_absolute hM.1 hTrans R0 X0 Y0).mp hSupport0
  have hRowsM (x y : M.Domain) : MemPair M R0.val x y ↔
      M.mem x X ∧ M.mem y Y ∧ Project.Formula.satisfies ((e.push x).push y) φ.body := by
    constructor
    · intro hAt
      have hBounds := hSupportM.bounds hM.1 hAt
      let x0 : (innerModel hM env hS).Domain := ⟨x,hX.mem_closed_d hM env hS hBounds.1⟩
      let y0 : (innerModel hM env hS).Domain := ⟨y,hY.mem_closed_d hM env hS hBounds.2⟩
      have hInner := (hRows0 x0 y0).mp ((memPair_class_absolute hM.1 hTrans R0 x0 y0).mpr hAt)
      exact ⟨hBounds.1,hBounds.2,(binary_matrix_transfer_iff hTrans φ e0 e (fun _ => rfl) x0 y0).mp hInner.2.2⟩
    · rintro ⟨hx,hy,hφ⟩
      let x0 : (innerModel hM env hS).Domain := ⟨x,hX.mem_closed_d hM env hS hx⟩
      let y0 : (innerModel hM env hS).Domain := ⟨y,hY.mem_closed_d hM env hS hy⟩
      have hInner := (binary_matrix_transfer_iff hTrans φ e0 e (fun _ => rfl) x0 y0).mpr hφ
      exact (memPair_class_absolute hM.1 hTrans R0 x0 y0).mp ((hRows0 x0 y0).mpr ⟨hx,hy,hInner⟩)
  have hEq := relation_ext hM.1 hSupport hSupportM (fun x y => (hRows x y).trans (hRowsM x y).symm)
  rw [hEq]
  exact R0.property

end KP1Y.Constructible
