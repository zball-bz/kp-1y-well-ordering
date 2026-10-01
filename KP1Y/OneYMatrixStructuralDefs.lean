import KP1Y.OneYMatrixExpansion

/-! 有限矩阵列后缀次序及相对结构条件的公共定义；帧行不被要求满足 S。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def ColumnEqAt (M : SetTheory.Structure.{u}) (w z : M.Domain) (A B : FiniteMatrix M.Domain) (c d r : M.Domain) : Prop :=
  ∀ x, M.mem x w → ∀ y, M.mem y w → PaddedEntry M z A r c x → PaddedEntry M z B r d y → x=y

def ColumnLtAt (M : SetTheory.Structure.{u}) (w z : M.Domain) (A B : FiniteMatrix M.Domain) (c d r : M.Domain) : Prop :=
  ∃ x, M.mem x w ∧ ∃ y, M.mem y w ∧ PaddedEntry M z A r c x ∧ PaddedEntry M z B r d y ∧ M.mem x y

def ColumnEqFrom (M : SetTheory.Structure.{u}) (w z : M.Domain) (A B : FiniteMatrix M.Domain) (c d start : M.Domain) : Prop :=
  ∀ r, M.mem r w → start=r ∨ M.mem start r → ColumnEqAt M w z A B c d r

def ColumnLtFrom (M : SetTheory.Structure.{u}) (w z : M.Domain) (A B : FiniteMatrix M.Domain) (c d start : M.Domain) : Prop :=
  ∃ r, M.mem r w ∧ (start=r ∨ M.mem start r) ∧
    (∀ q, M.mem q r → start=q ∨ M.mem start q → ColumnEqAt M w z A B c d q) ∧ ColumnLtAt M w z A B c d r

def ColumnLeFrom (M : SetTheory.Structure.{u}) (w z : M.Domain) (A B : FiniteMatrix M.Domain) (c d start : M.Domain) : Prop :=
  ColumnEqFrom M w z A B c d start ∨ ColumnLtFrom M w z A B c d start

def columnEqAtFormula {n : Nat} (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d r : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem w (Project.Formula.forallMem w.weaken
    (.imp (.conj (paddedEntryFormula z.weaken.weaken A.weaken.weaken r.weaken.weaken c.weaken.weaken (.bound 1))
      (paddedEntryFormula z.weaken.weaken B.weaken.weaken r.weaken.weaken d.weaken.weaken (.bound 0)))
      (Project.Formula.extensionalEq (.bound 1) (.bound 0))))

def columnLtAtFormula {n : Nat} (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d r : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem w (Project.Formula.existsMem w.weaken
    (.conj (paddedEntryFormula z.weaken.weaken A.weaken.weaken r.weaken.weaken c.weaken.weaken (.bound 1))
      (.conj (paddedEntryFormula z.weaken.weaken B.weaken.weaken r.weaken.weaken d.weaken.weaken (.bound 0))
        (.mem (.bound 1) (.bound 0)))))

def columnEqFromFormula {n : Nat} (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d start : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem w (.imp (.disj (Project.Formula.extensionalEq start.weaken (.bound 0)) (.mem start.weaken (.bound 0)))
    (columnEqAtFormula w.weaken z.weaken A.weaken B.weaken c.weaken d.weaken (.bound 0)))

def columnLtFromFormula {n : Nat} (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d start : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem w (.conj (.disj (Project.Formula.extensionalEq start.weaken (.bound 0)) (.mem start.weaken (.bound 0)))
    (.conj (Project.Formula.forallMem (.bound 0)
      (.imp (.disj (Project.Formula.extensionalEq start.weaken.weaken (.bound 0)) (.mem start.weaken.weaken (.bound 0)))
        (columnEqAtFormula w.weaken.weaken z.weaken.weaken A.weaken.weaken B.weaken.weaken c.weaken.weaken d.weaken.weaken (.bound 0))))
      (columnLtAtFormula w.weaken z.weaken A.weaken B.weaken c.weaken d.weaken (.bound 0))))

def columnLeFromFormula {n : Nat} (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d start : Project.Term n) : Project.Formula 1 n :=
  .disj (columnEqFromFormula w z A B c d start) (columnLtFromFormula w z A B c d start)

theorem columnEqAtFormula_delta0 {n : Nat} (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d r : Project.Term n) :
    (columnEqAtFormula w z A B c d r).IsDelta0 := .forallMem _ (.forallMem _
      (.imp (.conj (paddedEntryFormula_delta0 _ _ _ _ _) (paddedEntryFormula_delta0 _ _ _ _ _)) (.atom _ _ _)))

theorem columnLtAtFormula_delta0 {n : Nat} (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d r : Project.Term n) :
    (columnLtAtFormula w z A B c d r).IsDelta0 := .existsMem _ (.existsMem _
      (.conj (paddedEntryFormula_delta0 _ _ _ _ _) (.conj (paddedEntryFormula_delta0 _ _ _ _ _) (.mem _ _))))

theorem columnEqFromFormula_delta0 {n : Nat} (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d start : Project.Term n) :
    (columnEqFromFormula w z A B c d start).IsDelta0 := .forallMem _
      (.imp (.disj (.atom _ _ _) (.mem _ _)) (columnEqAtFormula_delta0 _ _ _ _ _ _ _))

theorem columnLtFromFormula_delta0 {n : Nat} (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d start : Project.Term n) :
    (columnLtFromFormula w z A B c d start).IsDelta0 := .existsMem _ (.conj (.disj (.atom _ _ _) (.mem _ _))
      (.conj (.forallMem _ (.imp (.disj (.atom _ _ _) (.mem _ _)) (columnEqAtFormula_delta0 _ _ _ _ _ _ _)))
        (columnLtAtFormula_delta0 _ _ _ _ _ _ _)))

theorem columnLeFromFormula_delta0 {n : Nat} (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d start : Project.Term n) :
    (columnLeFromFormula w z A B c d start).IsDelta0 :=
  .disj (columnEqFromFormula_delta0 _ _ _ _ _ _ _) (columnLtFromFormula_delta0 _ _ _ _ _ _ _)

theorem columnEqAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d r : Project.Term n) :
    Project.Formula.satisfies env (columnEqAtFormula w z A B c d r) ↔
      ColumnEqAt M (w.eval env) (z.eval env) (A.eval env) (B.eval env) (c.eval env) (d.eval env) (r.eval env) := by
  simp only [columnEqAtFormula,ColumnEqAt,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,paddedEntryFormula_iff he,
    FiniteMatrix.eval_weaken,Term.eval_weaken]
  simp only [and_imp]
  rfl

theorem columnLtAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d r : Project.Term n) :
    Project.Formula.satisfies env (columnLtAtFormula w z A B c d r) ↔
      ColumnLtAt M (w.eval env) (z.eval env) (A.eval env) (B.eval env) (c.eval env) (d.eval env) (r.eval env) := by
  simp only [columnLtAtFormula,ColumnLtAt,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,paddedEntryFormula_iff he,FiniteMatrix.eval_weaken,Term.eval_weaken]
  rfl

theorem columnEqFromFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d start : Project.Term n) :
    Project.Formula.satisfies env (columnEqFromFormula w z A B c d start) ↔
      ColumnEqFrom M (w.eval env) (z.eval env) (A.eval env) (B.eval env) (c.eval env) (d.eval env) (start.eval env) := by
  simp only [columnEqFromFormula,ColumnEqFrom,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,
    columnEqAtFormula_iff he,FiniteMatrix.eval_weaken,Term.eval_weaken]
  rfl

theorem columnLtFromFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d start : Project.Term n) :
    Project.Formula.satisfies env (columnLtFromFormula w z A B c d start) ↔
      ColumnLtFrom M (w.eval env) (z.eval env) (A.eval env) (B.eval env) (c.eval env) (d.eval env) (start.eval env) := by
  simp only [columnLtFromFormula,ColumnLtFrom,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,columnEqAtFormula_iff he,
    columnLtAtFormula_iff he,FiniteMatrix.eval_weaken,Term.eval_weaken]
  rfl

theorem columnLeFromFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (w z : Project.Term n) (A B : FiniteMatrix (Project.Term n)) (c d start : Project.Term n) :
    Project.Formula.satisfies env (columnLeFromFormula w z A B c d start) ↔
      ColumnLeFrom M (w.eval env) (z.eval env) (A.eval env) (B.eval env) (c.eval env) (d.eval env) (start.eval env) := by
  simp only [columnLeFromFormula,ColumnLeFrom,Project.Formula.satisfies_disj_iff,
    columnEqFromFormula_iff he,columnLtFromFormula_iff he]

theorem column_eq_from_refl {M : SetTheory.Structure.{u}} (he : Extensional M) {w z : M.Domain}
    {A : FiniteMatrix M.Domain} (hA : A.Valid M w) (c start : M.Domain) : ColumnEqFrom M w z A A c c start :=
  fun _ _ _ _ _ _ _ hx hy => hA.padded_unique he hx hy

theorem column_lt_from_irrefl_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {w z : M.Domain}
    {A : FiniteMatrix M.Domain} (hA : A.Valid M w) (c start : M.Domain) : ¬ColumnLtFrom M w z A A c c start := by
  rintro ⟨_,_,_,_,x,_,y,_,hx,hy,hxy⟩
  have he := hA.padded_unique hM.1 hx hy
  subst y
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) x hxy

theorem column_le_from_congr {M : SetTheory.Structure.{u}} {w z c d c' d' start : M.Domain}
    {A B A' B' : FiniteMatrix M.Domain}
    (hA : ∀ r x, PaddedEntry M z A r c x ↔ PaddedEntry M z A' r c' x)
    (hB : ∀ r x, PaddedEntry M z B r d x ↔ PaddedEntry M z B' r d' x) :
    ColumnLeFrom M w z A B c d start ↔ ColumnLeFrom M w z A' B' c' d' start := by
  simp only [ColumnLeFrom,ColumnEqFrom,ColumnLtFrom,ColumnEqAt,ColumnLtAt,hA,hB]

theorem column_eq_at_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain} (hB : B.Valid M C.omega)
    {a b d r : M.Domain} (hAB : ColumnEqAt M C.omega C.zero A B a b r) (hBD : ColumnEqAt M C.omega C.zero B D b d r) :
    ColumnEqAt M C.omega C.zero A D a d r := by
  intro x hx y hy hAx hDy
  obtain ⟨z,hz,hBz⟩ := hB.padded_total_d hM hC r b
  exact (hAB x hx z hz hAx hBz).trans (hBD z hz y hy hBz hDy)

theorem column_eq_lt_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {a b d r : M.Domain} (hAB : ColumnEqAt M C.omega C.zero A B a b r) (hBD : ColumnLtAt M C.omega C.zero B D b d r) :
    ColumnLtAt M C.omega C.zero A D a d r := by
  obtain ⟨y,hy,z,hz,hBy,hDz,hyz⟩ := hBD
  obtain ⟨x,hx,hAx⟩ := hA.padded_total_d hM hC r a
  have hxy := hAB x hx y hy hAx hBy
  exact ⟨x,hx,z,hz,hAx,hDz,hxy.symm ▸ hyz⟩

theorem column_lt_eq_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain} (hD : D.Valid M C.omega)
    {a b d r : M.Domain} (hAB : ColumnLtAt M C.omega C.zero A B a b r) (hBD : ColumnEqAt M C.omega C.zero B D b d r) :
    ColumnLtAt M C.omega C.zero A D a d r := by
  obtain ⟨x,hx,y,hy,hAx,hBy,hxy⟩ := hAB
  obtain ⟨z,hz,hDz⟩ := hD.padded_total_d hM hC r d
  have hyz := hBD y hy z hz hBy hDz
  exact ⟨x,hx,z,hz,hAx,hDz,hyz ▸ hxy⟩

theorem column_lt_at_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain} (hB : B.Valid M C.omega)
    {a b d r : M.Domain} (hAB : ColumnLtAt M C.omega C.zero A B a b r) (hBD : ColumnLtAt M C.omega C.zero B D b d r) :
    ColumnLtAt M C.omega C.zero A D a d r := by
  obtain ⟨x,hx,y,hy,hAx,hBy,hxy⟩ := hAB
  obtain ⟨y',_,z,hz,hBy',hDz,hyz⟩ := hBD
  have he := hB.padded_unique hM.1 hBy hBy'
  subst y'
  exact ⟨x,hx,z,hz,hAx,hDz,(omega_isOrdinal_d hM hC.omega).wellOrder.linear.trans x hx y hy z hz hxy hyz⟩

theorem column_eq_from_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain} (hB : B.Valid M C.omega)
    {a b d start : M.Domain} (hAB : ColumnEqFrom M C.omega C.zero A B a b start) (hBD : ColumnEqFrom M C.omega C.zero B D b d start) :
    ColumnEqFrom M C.omega C.zero A D a d start :=
  fun r hr hs => column_eq_at_trans_d hM hC hB (hAB r hr hs) (hBD r hr hs)

theorem column_eq_lt_from_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain}
    (hA : A.Valid M C.omega) (hB : B.Valid M C.omega)
    {a b d start : M.Domain} (hAB : ColumnEqFrom M C.omega C.zero A B a b start) (hBD : ColumnLtFrom M C.omega C.zero B D b d start) :
    ColumnLtFrom M C.omega C.zero A D a d start := by
  obtain ⟨r,hr,hs,hEarlier,hAt⟩ := hBD
  refine ⟨r,hr,hs,?_,column_eq_lt_at_d hM hC hA (hAB r hr hs) hAt⟩
  intro q hq hStart
  exact column_eq_at_trans_d hM hC hB (hAB q ((omega_isOrdinal_d hM hC.omega).transitive r hr q hq) hStart) (hEarlier q hq hStart)

theorem column_lt_eq_from_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain}
    (hB : B.Valid M C.omega) (hD : D.Valid M C.omega)
    {a b d start : M.Domain} (hAB : ColumnLtFrom M C.omega C.zero A B a b start) (hBD : ColumnEqFrom M C.omega C.zero B D b d start) :
    ColumnLtFrom M C.omega C.zero A D a d start := by
  obtain ⟨r,hr,hs,hEarlier,hAt⟩ := hAB
  refine ⟨r,hr,hs,?_,column_lt_eq_at_d hM hC hD hAt (hBD r hr hs)⟩
  intro q hq hStart
  exact column_eq_at_trans_d hM hC hB (hEarlier q hq hStart) (hBD q ((omega_isOrdinal_d hM hC.omega).transitive r hr q hq) hStart)

theorem column_lt_from_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain}
    (hA : A.Valid M C.omega) (hB : B.Valid M C.omega) (hD : D.Valid M C.omega)
    {a b d start : M.Domain} (hAB : ColumnLtFrom M C.omega C.zero A B a b start) (hBD : ColumnLtFrom M C.omega C.zero B D b d start) :
    ColumnLtFrom M C.omega C.zero A D a d start := by
  obtain ⟨r,hr,hStartR,hEarlierR,hAtR⟩ := hAB
  obtain ⟨s,hs,hStartS,hEarlierS,hAtS⟩ := hBD
  have hw := omega_isOrdinal_d hM hC.omega
  rcases hw.wellOrder.linear.compare r hr s hs with he | hrs | hsr
  · have heq := hM.1.eq_of_same_members r s he
    subst s
    exact ⟨r,hr,hStartR,fun q hq hStart => column_eq_at_trans_d hM hC hB (hEarlierR q hq hStart) (hEarlierS q hq hStart),
      column_lt_at_trans_d hM hC hB hAtR hAtS⟩
  · refine ⟨r,hr,hStartR,?_,column_lt_eq_at_d hM hC hD hAtR (hEarlierS r hrs hStartR)⟩
    intro q hq hStart
    exact column_eq_at_trans_d hM hC hB (hEarlierR q hq hStart) (hEarlierS q ((hw.mem hs).transitive r hrs q hq) hStart)
  · refine ⟨s,hs,hStartS,?_,column_eq_lt_at_d hM hC hA (hEarlierR s hsr hStartS) hAtS⟩
    intro q hq hStart
    exact column_eq_at_trans_d hM hC hB (hEarlierR q ((hw.mem hr).transitive s hsr q hq) hStart) (hEarlierS q hq hStart)

theorem column_le_from_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain}
    (hA : A.Valid M C.omega) (hB : B.Valid M C.omega) (hD : D.Valid M C.omega)
    {a b d start : M.Domain} (hAB : ColumnLeFrom M C.omega C.zero A B a b start) (hBD : ColumnLeFrom M C.omega C.zero B D b d start) :
    ColumnLeFrom M C.omega C.zero A D a d start := by
  rcases hAB with hAB | hAB <;> rcases hBD with hBD | hBD
  · exact Or.inl (column_eq_from_trans_d hM hC hB hAB hBD)
  · exact Or.inr (column_eq_lt_from_d hM hC hA hB hAB hBD)
  · exact Or.inr (column_lt_eq_from_d hM hC hB hD hAB hBD)
  · exact Or.inr (column_lt_from_trans_d hM hC hA hB hD hAB hBD)

def RowBlocker (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (previous current start : M.Domain) : Prop :=
  ∀ c, M.mem c A.width → ∀ q, M.mem q A.width → ∀ p, M.mem p A.width →
    MemPair M previous c q → MemPair M current c p → p≠q →
      ∃ z, M.mem z A.width ∧ (z=q ∨ Ancestor M C A.width current z q) ∧ MemPair M current z p ∧
        ColumnLeFrom M C.omega C.zero A A c z start

def PreviousMatrixForest (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (height Forests Rows L r P : M.Domain) : Prop :=
  (r=C.zero ∧ P=L) ∨ ∃ j, M.mem j height ∧ M.SuccessorOf r j ∧ M.mem P Forests ∧ MemPair M Rows j P

def AboveS (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (Forests Rows L base : M.Domain) : Prop :=
  ∀ r, M.mem r A.height → base=r ∨ M.mem base r → ∀ P, PreviousMatrixForest M C A.height Forests Rows L r P →
    ∀ Q, M.mem Q Forests → MemPair M Rows r Q → ∀ start, M.mem start C.omega → M.SuccessorOf start r → RowBlocker M C A P Q start

def MatrixDepthRegular (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (Forests Rows : M.Domain) : Prop :=
  ∀ r, M.mem r A.height → ∀ P, M.mem P Forests → MemPair M Rows r P →
    ∀ c, M.mem c A.width → ∀ d, M.mem d C.omega → MatrixEntry M A r c d →
      (NoParent M A.width P c → d=C.zero) ∧ ∀ p, M.mem p A.width → MemPair M P c p →
        ∀ e, M.mem e C.omega → MatrixEntry M A r p e → M.SuccessorOf d e

end KP1Y.OneYFinite
