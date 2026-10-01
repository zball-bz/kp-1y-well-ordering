import KP1Y.OneYLowerCanonDepthRoot
import KP1Y.OneYLowerCanonOrder
import KP1Y.OneYLowerDepthTransport
import KP1Y.OneYLowerValueTransport
import KP1Y.OneYGraphPseudo

/-! 图层Key的通用运输框架：行对应、首差行、Key前置，以及源列共同父的父行/伪父传播。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

theorem canon_depth_at_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C) {c r a b : M.Domain}
    (ha : ForestOrder.DepthAt M C X c r a) (hb : ForestOrder.DepthAt M C X c r b) : a=b := by
  obtain ⟨F,_,hF,hDa⟩ := ha
  obtain ⟨F',_,hF',hDb⟩ := hb
  have hFF := hX.parents.unique r F F' hF hF'
  subst F'
  exact depth_unique_d hM hC (hX.forest r F hF) hDa hDb

theorem canon_depth_at_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C) {c r : M.Domain}
    (hr : M.mem r C.omega) (hc : M.mem c X.width) : ∃ d, M.mem d C.omega ∧ ForestOrder.DepthAt M C X c r d := by
  obtain ⟨F,hF,hRow⟩ := hX.parents.total r hr
  obtain ⟨d,hd⟩ := depth_exists_d hM hC (hX.forest r F hRow) hc
  exact ⟨d,hd.1,F,hF,hRow,hd⟩

/-- 一行的Eq/Lt由两组具体深度的比较决定。 -/
theorem canon_row_transfer_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {c z cc zz σ ρ dc dz dcc dzz : M.Domain}
    (hDC : ForestOrder.DepthAt M C X c σ dc) (hDZ : ForestOrder.DepthAt M C X z σ dz)
    (hDCC : ForestOrder.DepthAt M C Y cc ρ dcc) (hDZZ : ForestOrder.DepthAt M C Y zz ρ dzz)
    (hEqImp : dc=dz → dcc=dzz) (hLtImp : M.mem dc dz → M.mem dcc dzz) :
    (ForestOrder.DepthEqAt M C X c z σ → ForestOrder.DepthEqAt M C Y cc zz ρ) ∧
      (ForestOrder.DepthLtAt M C X c z σ → ForestOrder.DepthLtAt M C Y cc zz ρ) := by
  have hdcNat : M.mem dc C.omega := by obtain ⟨_,_,_,hD⟩ := hDC; exact hD.1
  have hdzNat : M.mem dz C.omega := by obtain ⟨_,_,_,hD⟩ := hDZ; exact hD.1
  have hdccNat : M.mem dcc C.omega := by obtain ⟨_,_,_,hD⟩ := hDCC; exact hD.1
  have hdzzNat : M.mem dzz C.omega := by obtain ⟨_,_,_,hD⟩ := hDZZ; exact hD.1
  constructor
  · intro hEq a _ b _ ha hb
    have h1 := canon_depth_at_unique_d hM hC hY ha hDCC
    have h2 := canon_depth_at_unique_d hM hC hY hb hDZZ
    subst a
    subst b
    exact hEqImp (hEq dc hdcNat dz hdzNat hDC hDZ)
  · rintro ⟨a,_,b,_,ha,hb,hab⟩
    have h1 := canon_depth_at_unique_d hM hC hX ha hDC
    have h2 := canon_depth_at_unique_d hM hC hX hb hDZ
    subst a
    subst b
    exact ⟨dcc,hdccNat,dzz,hdzzNat,hDCC,hDZZ,hLtImp hab⟩

/-- 通用首差运输：目标每一行对应一个源行；Eq逐行运输，严格首差处取最小原像。 -/
theorem canon_key_transfer_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X Y : Data M.Domain} {c z cc zz tX tY : M.Domain}
    (Rows : M.Domain → M.Domain → Prop)
    (hTotal : ∀ ρ, M.mem ρ C.omega → (tY=ρ ∨ M.mem tY ρ) → ∃ σ, M.mem σ C.omega ∧ (tX=σ ∨ M.mem tX σ) ∧ Rows ρ σ)
    (hEq : ∀ ρ σ, M.mem ρ C.omega → (tY=ρ ∨ M.mem tY ρ) → M.mem σ C.omega → (tX=σ ∨ M.mem tX σ) → Rows ρ σ →
      (∀ q, M.mem q σ → (tX=q ∨ M.mem tX q) → ForestOrder.DepthEqAt M C X c z q) →
      ForestOrder.DepthEqAt M C X c z σ → ForestOrder.DepthEqAt M C Y cc zz ρ)
    (hLt : ∀ σ, M.mem σ C.omega → (tX=σ ∨ M.mem tX σ) →
      (∀ q, M.mem q σ → (tX=q ∨ M.mem tX q) → ForestOrder.DepthEqAt M C X c z q) →
      ForestOrder.DepthLtAt M C X c z σ → ∃ ρ, M.mem ρ C.omega ∧ (tY=ρ ∨ M.mem tY ρ) ∧
        ForestOrder.DepthLtAt M C Y cc zz ρ ∧ ∀ ρ', M.mem ρ' ρ → (tY=ρ' ∨ M.mem tY ρ') → ∀ σ', Rows ρ' σ' → M.mem σ' σ) :
    (ForestOrder.DepthEqFrom M C X c z tX → ForestOrder.DepthEqFrom M C Y cc zz tY) ∧
      (ForestOrder.DepthLtFrom M C X c z tX → ForestOrder.DepthLtFrom M C Y cc zz tY) := by
  constructor
  · intro hEqX ρ hρ hTρ
    obtain ⟨σ,hσ,hTσ,hR⟩ := hTotal ρ hρ hTρ
    exact hEq ρ σ hρ hTρ hσ hTσ hR (fun q hq hTq => hEqX q (nat_mem_omega hM hC hσ hq) hTq) (hEqX σ hσ hTσ)
  · rintro ⟨r,hr,hTr,hBefore,hLtr⟩
    obtain ⟨ρ,hρ,hTρ,hLtY,hEarlier⟩ := hLt r hr hTr hBefore hLtr
    refine ⟨ρ,hρ,hTρ,?_,hLtY⟩
    intro ρ' hρ' hTρ'
    have hρ'Nat := nat_mem_omega hM hC hρ hρ'
    obtain ⟨σ',hσ',hTσ',hR'⟩ := hTotal ρ' hρ'Nat hTρ'
    have hσ'r := hEarlier ρ' hρ' hTρ' σ' hR'
    exact hEq ρ' σ' hρ'Nat hTρ' hσ' hTσ' hR'
      (fun q hq hTq => hBefore q (nat_lt_trans hM hC hr hq hσ'r) hTq) (hBefore σ' hσ'r hTσ')

/-- KeyLE 的Eq/Lt两部分加上Top条件的组合。 -/
theorem canon_key_of_parts {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {X Y : Data M.Domain}
    {c z cc zz tX tY tc tz tcc tzz : M.Domain}
    (hParts : (ForestOrder.DepthEqFrom M C X c z tX → ForestOrder.DepthEqFrom M C Y cc zz tY) ∧
      (ForestOrder.DepthLtFrom M C X c z tX → ForestOrder.DepthLtFrom M C Y cc zz tY))
    (hTop : ForestOrder.DepthEqFrom M C X c z tX → (tc=tz ∨ M.mem tc tz) → (tcc=tzz ∨ M.mem tcc tzz))
    (hKey : ForestOrder.KeyLE M C X c z tX tc tz) : ForestOrder.KeyLE M C Y cc zz tY tcc tzz := by
  rcases hKey with hLess | ⟨hEqual,hTopLe⟩
  · exact Or.inl (hParts.2 hLess)
  · exact Or.inr ⟨hParts.1 hEqual,hTop hEqual hTopLe⟩

/-- 在前一行深度相等时，把Key起点前移一行。 -/
theorem canon_key_prepend_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} {c z r s tc tz : M.Domain}
    (hr : M.mem r C.omega) (hs : M.SuccessorOf s r)
    (hCurrent : ForestOrder.DepthEqAt M C X c z r) (hNext : ForestOrder.KeyLE M C X c z s tc tz) :
    ForestOrder.KeyLE M C X c z r tc tz := by
  rcases hNext with ⟨q,hq,hSQ,hEarlier,hLess⟩ | ⟨hEq,hTop⟩
  · have hrq : M.mem r q := nat_lt_of_lt_of_le hM hC hq hs.predecessor_mem hSQ
    refine Or.inl ⟨q,hq,Or.inr hrq,?_,hLess⟩
    intro p hp hRP
    rcases hRP with he | hrp
    · exact he ▸ hCurrent
    · exact hEarlier p hp (nat_succ_le_of_lt hM hC hr (nat_mem_omega hM hC hq hp) hs hrp)
  · refine Or.inr ⟨?_,hTop⟩
    intro q hq hRQ
    rcases hRQ with he | hrq
    · exact he ▸ hCurrent
    · exact hEq q hq (nat_succ_le_of_lt hM hC hr hq hs hrq)

/-- 若从起点起两列每行的源深度都蕴含目标深度，则Key以相同Top读数运输。 -/
theorem canon_key_of_depth_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {c z cc zz t tc tz : M.Domain} (hc : M.mem c X.width) (hz : M.mem z X.width)
    (hDC : ∀ r, M.mem r C.omega → (t=r ∨ M.mem t r) → ∀ d, ForestOrder.DepthAt M C X c r d → ForestOrder.DepthAt M C Y cc r d)
    (hDZ : ∀ r, M.mem r C.omega → (t=r ∨ M.mem t r) → ∀ d, ForestOrder.DepthAt M C X z r d → ForestOrder.DepthAt M C Y zz r d)
    (hKey : ForestOrder.KeyLE M C X c z t tc tz) : ForestOrder.KeyLE M C Y cc zz t tc tz := by
  have hRow (r : M.Domain) (hr : M.mem r C.omega) (hT : t=r ∨ M.mem t r) :
      (ForestOrder.DepthEqAt M C X c z r → ForestOrder.DepthEqAt M C Y cc zz r) ∧
        (ForestOrder.DepthLtAt M C X c z r → ForestOrder.DepthLtAt M C Y cc zz r) := by
    obtain ⟨dc,_,hDc⟩ := canon_depth_at_exists_d hM hC hX hr hc
    obtain ⟨dz,_,hDz⟩ := canon_depth_at_exists_d hM hC hX hr hz
    exact canon_row_transfer_d hM hC hX hY hDc hDz (hDC r hr hT dc hDc) (hDZ r hr hT dz hDz) id id
  apply canon_key_of_parts (canon_key_transfer_d hM hC (fun ρ σ => σ=ρ) (fun ρ hρ hT => ⟨ρ,hρ,hT,rfl⟩) ?_ ?_)
    (fun _ h => h) hKey
  · intro ρ σ hρ hT _ _ hR _ hEqX
    subst σ
    exact (hRow ρ hρ hT).1 hEqX
  · intro σ hσ hT _ hLtX
    refine ⟨σ,hσ,hT,(hRow σ hσ hT).2 hLtX,?_⟩
    intro ρ' hρ' _ σ' hR
    exact hR ▸ hρ'

private def rowsPropEnv {M : SetTheory.Structure.{u}} (u σ parents c z : M.Domain) : Env M 5 :=
  ((((oneEnv u).push σ).push parents).push c).push z

private def rowsPropSchema : Project.UnarySchema 5 where
  body := .imp (.disj (Project.Formula.extensionalEq (.bound 5) (.bound 0)) (.mem (.bound 5) (.bound 0)))
    (.imp (.mem (.bound 0) (.bound 4))
      (.forallE (.imp (memPairFormula (.bound 4) (.bound 1) (.bound 0))
        (parentRowsEqualFormula (.bound 0) (.bound 3) (.bound 2)))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,memPairFormula,codeFormula,pairFormula,
      parentRowsEqualFormula,Project.Formula.forallMem,Project.Formula.existsMem]

private theorem rowsPropSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (u σ parents c z q : M.Domain) :
    Project.Formula.satisfies ((rowsPropEnv u σ parents c z).push q) rowsPropSchema.body ↔
      ((u=q ∨ M.mem u q) → M.mem q σ → ∀ F, MemPair M parents q F → ParentRowsEqual M F c z) := by
  simp only [rowsPropSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forall_iff,memPairFormula_iff he,parentRowsEqualFormula_iff he]
  rfl

/-- 共同父行u以后各行深度相等时，直到σ前每一行的父行仍相同（源实际行运行的深度正规性）。 -/
theorem canon_parent_rows_propagate_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X)
    {u σ c z : M.Domain} (hσ : M.mem σ C.omega) (hc : M.mem c X.width) (hz : M.mem z X.width)
    (hInit : ∀ F, MemPair M X.parents u F → ParentRowsEqual M F c z)
    (hEq : ∀ q, M.mem q σ → M.mem u q → ForestOrder.DepthEqAt M C X c z q) :
    ∀ q, M.mem q C.omega → (u=q ∨ M.mem u q) → M.mem q σ → ∀ F, MemPair M X.parents q F → ParentRowsEqual M F c z := by
  have hAll := natural_induction_d hM rowsPropSchema (rowsPropEnv u σ X.parents c z) hC.omega
    (fun e he => (rowsPropSchema_iff hM.1 u σ X.parents c z e).mpr (by
      intro hUE _ F hF
      rcases hUE with heq | hlt
      · subst heq
        exact hInit F hF
      · exact False.elim (he u hlt)))
    (fun p hp ih s hs => (rowsPropSchema_iff hM.1 u σ X.parents c z s).mpr (by
      intro hUS hSσ Q hQ
      rcases hUS with heq | hlt
      · subst heq
        exact hInit Q hQ
      · have hUP : u=p ∨ M.mem u p := (nat_lt_succ_iff hM hs).mp hlt
        obtain ⟨F,_,hF⟩ := hX.parents.total p hp
        have hPσ : M.mem p σ := ((omega_isOrdinal_d hM hC.omega).mem hσ).transitive s hSσ p hs.predecessor_mem
        have hSame := (rowsPropSchema_iff hM.1 u σ X.parents c z p).mp ih hUP hPσ F hF
        obtain ⟨dc,hDc⟩ := depth_exists_d hM hC (hX.forest s Q hQ) hc
        obtain ⟨dz,hDz⟩ := depth_exists_d hM hC (hX.forest s Q hQ) hz
        have hEqS := hEq s hSσ hlt dc hDc.1 dz hDz.1 ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hDc⟩ ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hDz⟩
        subst dz
        exact source_parent_rows_of_previous_depth_eq_d hM hC hRun hX hFrom hs hF hQ hSame hDc hDz))
  intro q hq
  exact (rowsPropSchema_iff hM.1 u σ X.parents c z q).mp (hAll q hq)


/-- 共同父行u之后深度全等，则两列高度相同且伪父相同。 -/
theorem canon_pseudo_rows_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X)
    {Pseudo u t c z : M.Domain} (hPseudo : GraphPseudoForest M C X Pseudo)
    (hu : M.mem u C.omega) (ht : M.SuccessorOf t u) (hc : M.mem c X.width) (hz : M.mem z X.width)
    (hInit : ∀ F, MemPair M X.parents u F → ParentRowsEqual M F c z)
    (hcLive : ∃ p, ParentAt M X u c p)
    (hEqFrom : ForestOrder.DepthEqFrom M C X c z t) : ParentRowsEqual M Pseudo c z := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨hcH,hcHNat,hHC⟩ := hX.heights.total c hc
  obtain ⟨hzH,hzHNat,hHZ⟩ := hX.heights.total z hz
  obtain ⟨F0,_,hF0⟩ := hX.parents.total u hu
  have hzLive : ∃ p, ParentAt M X u z p := by
    obtain ⟨p,hP⟩ := hcLive
    have hPF := (canon_row_parent_iff hM.1 hX hF0).mp hP
    exact ⟨p,(canon_row_parent_iff hM.1 hX hF0).mpr ((hInit F0 hF0 p).mp hPF)⟩
  have hUC := (hX.source u c hcH hHC).mp hcLive
  have hUZ := (hX.source u z hzH hHZ).mp hzLive
  have hStart (q : M.Domain) (hq : M.mem q C.omega) (huq : M.mem u q) : t=q ∨ M.mem t q :=
    nat_succ_le_of_lt hM hC hu hq ht huq
  have hNoGap (a b ha hb : M.Domain) (hA : MemPair M X.heights a ha) (hB : MemPair M X.heights b hb)
      (hUA : M.mem u ha) (hab : M.mem ha hb) (hEqAB : ForestOrder.DepthEqAt M C X a b ha) : False := by
    have haNat := (hX.heights.bounds hM.1 hA).2
    obtain ⟨Q,_,hQ⟩ := hX.parents.total ha haNat
    have hQF := hX.forest ha Q hQ
    obtain ⟨da,hDa⟩ := depth_exists_d hM hC hQF (hX.heights.bounds hM.1 hA).1
    obtain ⟨db,hDb⟩ := depth_exists_d hM hC hQF (hX.heights.bounds hM.1 hB).1
    have hEqd := hEqAB da hDa.1 db hDb.1 ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hDa⟩ ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hDb⟩
    subst db
    have hNoA : NoParent M X.width Q a := canon_no_parent_of_height hM.1 hX hQ hA (nat_irrefl hM ha)
    have hZeroA := (depth_zero_iff_d hM hC hQF hDa).mpr hNoA
    have hNoB := (depth_zero_iff_d hM hC hQF hDb).mp hZeroA
    obtain ⟨p,hP⟩ := (hX.source ha b hb hB).mpr hab
    have hPQ := (canon_row_parent_iff hM.1 hX hQ).mp hP
    exact hNoB p (hQF.bounds hM.1 hPQ).2 hPQ
  have hEqAt (q : M.Domain) (hq : M.mem q C.omega) (huq : M.mem u q) : ForestOrder.DepthEqAt M C X c z q :=
    hEqFrom q hq (hStart q hq huq)
  have hSwap (q : M.Domain) (h : ForestOrder.DepthEqAt M C X c z q) : ForestOrder.DepthEqAt M C X z c q :=
    fun a ha b hb hA hB => (h b hb a ha hB hA).symm
  have hHeq : hcH=hzH := by
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare hcH hcHNat hzH hzHNat with he | hlt | hgt
    · exact hM.1.eq_of_same_members _ _ he
    · exact False.elim (hNoGap c z hcH hzH hHC hHZ hUC hlt (hEqAt hcH hcHNat hUC))
    · exact False.elim (hNoGap z c hzH hcH hHZ hHC hUZ hgt (hSwap hzH (hEqAt hzH hzHNat hUZ)))
  subst hzH
  rcases natural_cases hM hC.omega hcHNat with hEmpty | ⟨r,hr,hRS⟩
  · exact False.elim (hEmpty u hUC)
  · have hUR : u=r ∨ M.mem u r := (nat_lt_succ_iff hM hRS).mp hUC
    have hSameR := canon_parent_rows_propagate_d hM hC hRun hX hFrom hcHNat hc hz hInit
      (fun q hq huq => hEqAt q (nat_mem_omega hM hC hcHNat hq) huq) r hr hUR hRS.predecessor_mem
    have hCand (a b : M.Domain) (hA : MemPair M X.heights a hcH) (hB : MemPair M X.heights b hcH)
        (hSame : ∀ F, MemPair M X.parents r F → ParentRowsEqual M F a b) (p : M.Domain) :
        GraphPseudoCandidate M C X a p → GraphPseudoCandidate M C X b p := by
      rintro ⟨ha',ha'Nat,hp,hpNat,r',hr',hHA',hHP,hSucc',F,hFm,hF,hAnc,hRel⟩
      have hh := hX.heights.unique a ha' hcH hHA' hA
      subst ha'
      have hrr := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hr') hSucc' hRS
      subst r'
      exact ⟨hcH,ha'Nat,hp,hpNat,r,hr',hB,hHP,hSucc',F,hFm,hF,
        (ancestor_iff_of_parent_rows_eq_d hM hC (hX.forest r F hF) (hSame F hF) p).mp hAnc,hRel⟩
    have hCandIff (p : M.Domain) : GraphPseudoCandidate M C X c p ↔ GraphPseudoCandidate M C X z p :=
      ⟨hCand c z hHC hHZ hSameR p,hCand z c hHZ hHC (fun F hF q => (hSameR F hF q).symm) p⟩
    intro p
    rw [hPseudo.rows c p,hPseudo.rows z p]
    constructor
    · rintro ⟨hP,hMax⟩
      exact ⟨(hCandIff p).mp hP,fun q _ hQ => hMax q ((hCandIff q).mpr hQ |>.bounds hM.1).2.2 ((hCandIff q).mpr hQ)⟩
    · rintro ⟨hP,hMax⟩
      exact ⟨(hCandIff p).mpr hP,fun q _ hQ => hMax q ((hCandIff q).mp hQ |>.bounds hM.1).2.2 ((hCandIff q).mp hQ)⟩

/-- 深度全等时由上层UpperOrder读出复制Top的弱序。 -/
theorem canon_upper_top_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {D : Context M.Domain}
    (hD : D.Valid M C) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Pseudo oldTop newTop u t c z b cc zz tc tz tcc tzz : M.Domain}
    (hUpper : UpperOrder M C T D Pseudo oldTop newTop) (hPseudo : GraphPseudoForest M C D.mountain Pseudo)
    (hu : M.mem u C.omega) (ht : M.SuccessorOf t u)
    (hRootZ : M.mem D.coordinates.root z) (hzc : M.mem z c) (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hInit : ∀ F, MemPair M D.mountain.parents u F → ParentRowsEqual M F c z)
    (hcLive : ∃ p, ParentAt M D.mountain u c p)
    (hEqFrom : ForestOrder.DepthEqFrom M C D.mountain c z t)
    (hTC : MemPair M oldTop c tc) (hTZ : MemPair M oldTop z tz) (hLe : tc=tz ∨ M.mem tc tz)
    (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hNTC : MemPair M newTop cc tcc) (hNTZ : MemPair M newTop zz tzz) : tcc=tzz ∨ M.mem tcc tzz := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hcX : M.mem c D.mountain.width := hcLast.elim (fun he => he ▸ hD.last)
    (fun h => (hw.mem hD.mountain.width).transitive _ hD.last c h)
  have hzX : M.mem z D.mountain.width := (hw.mem hD.mountain.width).transitive c hcX z hzc
  exact hUpper z c hRootZ hzc hcLast
    (canon_pseudo_rows_eq_d hM hC hRun hD.mountain hFrom hPseudo hu ht hcX hzX hInit hcLive hEqFrom)
    tc tz hTC hTZ hLe b cc zz tcc tzz hMapC hMapZ hNTC hNTZ

end KP1Y.OneYFinite.CopiedMountain.Lower
