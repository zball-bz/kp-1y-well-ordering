import KP1Y.OneYMatrixExpansion

/-! 1-Y 的 (y,x] 源列与 BM4 的 [root,last) 地址之间的精确桥。
保留区 c≤y 的原始 source=y+1、block=0；仅 c>y 断言 encode 反解。
-/
namespace KP1Y.OneYFinite.CopyCoordinates
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite
universe u v

structure Context (α : Type u) where
  last : α
  root : α
  length : α
  first : α

def Context.map {α : Type u} {β : Type v} (A : Context α) (f : α → β) : Context β :=
  ⟨f A.last,f A.root,f A.length,f A.first⟩

def Context.eval {M : SetTheory.Structure.{u}} {n : Nat} (A : Context (Project.Term n)) (e : Env M n) : Context M.Domain := A.map (fun t => t.eval e)
def Context.weaken {n : Nat} (A : Context (Project.Term n)) : Context (Project.Term (n+1)) := A.map (fun t => t.weaken)

theorem Context.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat}
    (A : Context (Project.Term n)) (e : Env M n) (x : M.Domain) : A.weaken.eval (e.push x)=A.eval e := by
  cases A
  simp [Context.weaken,Context.eval,Context.map,Term.eval_weaken]

structure Context.Closed {n : Nat} (A : Context (Project.Term n)) : Prop where
  last : A.last.freeSupport=[]
  root : A.root.freeSupport=[]
  length : A.length.freeSupport=[]
  first : A.first.freeSupport=[]

structure ArithmeticClosed {n : Nat} (T : MatrixArithmetic (Project.Term n)) : Prop where
  addPairs : T.addPairs.freeSupport=[]
  plus : T.plus.freeSupport=[]
  mulPairs : T.mulPairs.freeSupport=[]
  times : T.times.freeSupport=[]
  diffPairs : T.diffPairs.freeSupport=[]
  difference : T.difference.freeSupport=[]

theorem Context.Closed.weaken {n : Nat} {A : Context (Project.Term n)} (h : A.Closed) : A.weaken.Closed := by
  rcases h with ⟨hx,hy,hL,hFirst⟩
  constructor <;> simp_all [Context.weaken,Context.map]

theorem ArithmeticClosed.weaken {n : Nat} {T : MatrixArithmetic (Project.Term n)} (h : ArithmeticClosed T) : ArithmeticClosed T.weaken := by
  rcases h with ⟨hAP,hPlus,hMP,hTimes,hDP,hDiff⟩
  constructor <;> simp_all [MatrixArithmetic.weaken,MatrixArithmetic.map]

structure Context.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : Context M.Domain) : Prop where
  last : M.mem A.last C.omega
  root : M.mem A.root C.omega
  below : M.mem A.root A.last
  difference : TruncatedDifference M C.omega C.zero A.last A.root A.length
  first : M.SuccessorOf A.first A.root

theorem context_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {x y : M.Domain}
    (hx : M.mem x C.omega) (hy : M.mem y C.omega) (hyx : M.mem y x) :
    ∃ A : Context M.Domain, A.last=x ∧ A.root=y ∧ A.Valid M C := by
  obtain ⟨L,_,hL⟩ := truncated_difference_exists_d hM hC hx hy
  obtain ⟨first,hFirst,_⟩ := hC.omega.1.2 y hy
  exact ⟨⟨x,y,L,first⟩,rfl,rfl,hx,hy,hyx,hL,hFirst⟩

theorem Context.Valid.length_nat {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {A : Context M.Domain} (hA : A.Valid M C) : M.mem A.length C.omega :=
  truncated_difference_natural he hA.difference

theorem Context.Valid.first_nat_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : Context M.Domain} (hA : A.Valid M C) : M.mem A.first C.omega :=
  natural_successor_mem_d hM hC hA.root hA.first

theorem Context.Valid.length_positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : Context M.Domain} (hA : A.Valid M C) : M.mem C.zero A.length :=
  (truncated_difference_positive_iff_d hM hC hA.difference).mpr hA.below

theorem Context.Valid.root_add_length_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : Context M.Domain} (hA : A.Valid M C) : Sum M A.root A.length A.last :=
  truncated_difference_add_inverse_d hM hC hA.difference (Or.inr hA.below)

private theorem successor_le_of_lt {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a s b : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hs : M.SuccessorOf s a) (hab : M.mem a b) : s=b ∨ M.mem s b := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hSub : M.MemberSubset s b := by
    intro x hx
    rcases (hs x).mp hx with hxa | hxa
    · exact (hw.mem hb).transitive a hab x hxa
    · exact hM.1.eq_of_same_members x a hxa ▸ hab
  exact ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC ha hs)) (hw.mem hb) hSub

def Source (M : SetTheory.Structure.{u}) (A : Context M.Domain) (s : M.Domain) : Prop :=
  M.mem A.root s ∧ (s=A.last ∨ M.mem s A.last)

def SourceSlot (M : SetTheory.Structure.{u}) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (s slot : M.Domain) : Prop :=
  M.mem slot A.length ∧ AddAt M T.addPairs T.plus A.first slot s

theorem source_slot_bounds_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {s slot : M.Domain} (hSlot : SourceSlot M T A s slot) : Source M A s := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hSlotNat := hw.transitive A.length (hA.length_nat hM.1) slot hSlot.1
  have hFirstNat := hA.first_nat_d hM hC
  have hS := (hT.add.add_iff_sum hM hFirstNat hSlotNat).mp hSlot.2
  have hRootS := sum_base_subset_d hM (hw.mem hFirstNat) hS A.root hA.first.predecessor_mem
  obtain ⟨u,hu,hU⟩ := natural_sum_exists_d hM hC.omega hA.root hSlotNat
  have hSucc := natural_sum_left_successor_d hM hC hSlotNat hA.first hU hS
  have huLast := sum_strict_right_d hM (hw.mem hA.root) hU (hA.root_add_length_d hM hC) hSlot.1
  exact ⟨hRootS,successor_le_of_lt hM hC hu hA.last hSucc huLast⟩

theorem source_slot_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {s : M.Domain} (hSource : Source M A s) : ∃ slot, SourceSlot M T A s slot := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hs : M.mem s C.omega := by
    rcases hSource.2 with he | hsx
    · exact he ▸ hA.last
    · exact hw.transitive A.last hA.last s hsx
  have hFirstNat := hA.first_nat_d hM hC
  have hFirstLe := successor_le_of_lt hM hC hA.root hs hA.first hSource.1
  obtain ⟨slot,hSlot,hDiff⟩ := truncated_difference_exists_d hM hC hs hFirstNat
  have hFirstSlot := truncated_difference_add_inverse_d hM hC hDiff hFirstLe
  obtain ⟨u,hu,hRootSlot⟩ := natural_sum_exists_d hM hC.omega hA.root hSlot
  have hSU := natural_sum_left_successor_d hM hC hSlot hA.first hRootSlot hFirstSlot
  have huLast : M.mem u A.last := by
    rcases hSource.2 with he | hsx
    · exact he ▸ hSU.predecessor_mem
    · exact (hw.mem hA.last).transitive s hsx u hSU.predecessor_mem
  have hSlotL : M.mem slot A.length := by
    rcases hw.wellOrder.linear.compare slot hSlot A.length (hA.length_nat hM.1) with he | hlt | hgt
    · have hEq := hM.1.eq_of_same_members slot A.length he
      subst slot
      have hUX := sum_unique_d hM hRootSlot (hA.root_add_length_d hM hC)
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.last (hUX ▸ huLast))
    · exact hlt
    · have hLastU := sum_strict_right_d hM (hw.mem hA.root) (hA.root_add_length_d hM hC) hRootSlot hgt
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) u ((hw.mem hu).transitive A.last hLastU u huLast))
  exact ⟨slot,hSlotL,(hT.add.add_iff_sum hM hFirstNat hSlot).mpr hFirstSlot⟩

def Encode (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (s b target : M.Domain) : Prop :=
  M.mem s C.omega ∧ M.mem b C.omega ∧ ∃ offset, M.mem offset C.omega ∧
    MulAt M T.mulPairs T.times b A.length offset ∧ AddAt M T.addPairs T.plus s offset target

def encodeFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (s b target : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem s C.omega) (.conj (.mem b C.omega) (Project.Formula.existsMem C.omega
    (.conj (mulAtFormula T.mulPairs.weaken T.times.weaken b.weaken A.length.weaken (.bound 0))
      (addAtFormula T.addPairs.weaken T.plus.weaken s.weaken (.bound 0) target.weaken))))

theorem encodeFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (s b target : Project.Term n) : (encodeFormula C T A s b target).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.existsMem _ (.conj (mulAtFormula_delta0 _ _ _ _ _) (addAtFormula_delta0 _ _ _ _ _))))

theorem encodeFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {A : Context (Project.Term n)} (hA : A.Closed)
    (s b target : Project.Term n) (hs : s.freeSupport=[]) (hb : b.freeSupport=[])
    (ht : target.freeSupport=[]) : (encodeFormula C T A s b target).FreeClosed := by
  simp [encodeFormula,mulAtFormula,addAtFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hT.mulPairs,hT.times,hT.addPairs,hT.plus,hA.length,hs,hb,ht]

theorem encodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : Context (Project.Term n))
    (s b target : Project.Term n) : Project.Formula.satisfies e (encodeFormula C T A s b target) ↔
      Encode M (C.eval e) (T.eval e) (A.eval e) (s.eval e) (b.eval e) (target.eval e) := by
  simp only [encodeFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,mulAtFormula_iff he,addAtFormula_iff he,Term.eval_weaken]
  rfl

theorem encode_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {s b : M.Domain} (hs : M.mem s C.omega) (hb : M.mem b C.omega) :
    ∃ target, M.mem target C.omega ∧ Encode M C T A s b target := by
  obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hb (hA.length_nat hM.1)
  obtain ⟨target,hTarget,hAdd⟩ := hT.add.add_exists_d hM hC hs hOff
  exact ⟨target,hTarget,hs,hb,off,hOff,hTimes,hAdd⟩

theorem encode_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} {s b x y : M.Domain} (hx : Encode M C T A s b x) (hy : Encode M C T A s b y) : x=y := by
  obtain ⟨_,_,off,_,hTimes,hX⟩ := hx
  obtain ⟨_,_,off',_,hTimes',hY⟩ := hy
  have hOff := hT.mul.mul_unique he hTimes hTimes'
  subst off'
  exact hT.add.add_unique he hX hY

theorem encode_at_base_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} {base slot s b target : M.Domain}
    (hBase : M.mem base C.omega) (hSlot : M.mem slot C.omega) (hb : M.mem b C.omega)
    (hSource : AddAt M T.addPairs T.plus base slot s) :
    Encode M C T A s b target ↔ CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times base A.length b slot target := by
  have hs := (hSource.bounds hM.1 hT.add).2.2
  have hSourceSum := (hT.add.add_iff_sum hM hBase hSlot).mp hSource
  constructor
  · rintro ⟨_,_,off,hOff,hTimes,hTarget⟩
    obtain ⟨start,hStart,hStartAdd⟩ := hT.add.add_exists_d hM hC hBase hOff
    obtain ⟨t,_,hTAdd⟩ := hT.add.add_exists_d hM hC hStart hSlot
    have hEq := natural_sum_shuffle_d hM hC hSlot hOff hSourceSum
      ((hT.add.add_iff_sum hM hs hOff).mp hTarget) ((hT.add.add_iff_sum hM hBase hOff).mp hStartAdd)
      ((hT.add.add_iff_sum hM hStart hSlot).mp hTAdd)
    subst t
    exact ⟨off,hOff,start,hStart,hTimes,hStartAdd,hTAdd⟩
  · rintro ⟨off,hOff,start,hStart,hTimes,hStartAdd,hTarget⟩
    obtain ⟨t,_,hTAdd⟩ := hT.add.add_exists_d hM hC hs hOff
    have hEq := natural_sum_shuffle_d hM hC hSlot hOff hSourceSum
      ((hT.add.add_iff_sum hM hs hOff).mp hTAdd) ((hT.add.add_iff_sum hM hBase hOff).mp hStartAdd)
      ((hT.add.add_iff_sum hM hStart hSlot).mp hTarget)
    subst t
    exact ⟨hs,hb,off,hOff,hTimes,hTAdd⟩

theorem source_encode_injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {s t b d target : M.Domain}
    (hs : Source M A s) (ht : Source M A t) (hS : Encode M C T A s b target) (hTgt : Encode M C T A t d target) : s=t ∧ b=d := by
  obtain ⟨slot,hSlot⟩ := source_slot_exists_d hM hC hT hA hs
  obtain ⟨slot',hSlot'⟩ := source_slot_exists_d hM hC hT hA ht
  have hw := omega_isOrdinal_d hM hC.omega
  have hPos := (encode_at_base_iff_d hM hC hT (hA.first_nat_d hM hC)
    (hw.transitive A.length (hA.length_nat hM.1) slot hSlot.1) hS.2.1 hSlot.2).mp hS
  have hPos' := (encode_at_base_iff_d hM hC hT (hA.first_nat_d hM hC)
    (hw.transitive A.length (hA.length_nat hM.1) slot' hSlot'.1) hTgt.2.1 hSlot'.2).mp hTgt
  obtain ⟨hbd,hSlots⟩ := copy_position_injective_d hM hC hT.add hT.mul (hA.first_nat_d hM hC)
    (hA.length_nat hM.1) hS.2.1 hTgt.2.1 hSlot.1 hSlot'.1 hPos hPos'
  subst slot'
  exact ⟨hT.add.add_unique hM.1 hSlot.2 hSlot'.2,hbd⟩

private theorem active_coverage_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c : M.Domain} (hc : M.mem c C.omega) (hAfter : M.mem A.root c) :
    ∃ b, M.mem b C.omega ∧ ∃ slot, M.mem slot A.length ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times A.first A.length b slot c := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨count,hCount,hCountNat⟩ := hC.omega.1.2 c hc
  obtain ⟨oneProduct,_,hOneProduct⟩ := natural_product_exists_d hM hC hCountNat hC.one_nat
  have hOneEq := natural_product_one_right_d hM hC hCountNat hOneProduct
  subst oneProduct
  obtain ⟨total,hTotalNat,hTotal⟩ := natural_product_exists_d hM hC hCountNat (hA.length_nat hM.1)
  have hOneL : M.MemberSubset C.one A.length := by
    intro i hi
    rcases (hC.one_succ i).mp hi with hi | hi
    · exact False.elim (hC.zero_empty i hi)
    · exact hM.1.eq_of_same_members i C.zero hi ▸ hA.length_positive_d hM hC
  have hCountSub := product_mono_right_d hM ⟨c,hCount.predecessor_mem⟩ hOneProduct hTotal hOneL
  obtain ⟨width,_,hWidth⟩ := natural_sum_exists_d hM hC.omega (hA.first_nat_d hM hC) hTotalNat
  have hTarget := sum_right_subset_d hM (hw.mem (hA.first_nat_d hM hC)) hWidth c
    (hCountSub c hCount.predecessor_mem)
  have hFirstLe := successor_le_of_lt hM hC hA.root hc hA.first hAfter
  obtain ⟨b,hb,slot,hSlot,hPos⟩ := copy_interval_coverage_d hM hC hT.add hT.mul
    (hA.first_nat_d hM hC) (hA.length_nat hM.1) hCountNat hTotal hWidth hTarget hFirstLe
  exact ⟨b,hw.transitive count hCountNat b hb,slot,hSlot,hPos⟩

/-- 原始 source/block 的总定义。保留区不回填 source=c，而保留原实现的 (y+1,0)。 -/
def RawDecoded (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (c s b : M.Domain) : Prop :=
  M.mem s C.omega ∧ M.mem b C.omega ∧
    ((¬M.mem A.root c ∧ s=A.first ∧ b=C.zero) ∨
      (M.mem A.root c ∧ Source M A s ∧ Encode M C T A s b c))

def rawDecodedFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (c s b : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem s C.omega) (.conj (.mem b C.omega)
    (.disj (.conj (.neg (.mem A.root c)) (.conj (Project.Formula.extensionalEq s A.first) (Project.Formula.extensionalEq b C.zero)))
      (.conj (.mem A.root c) (.conj (.conj (.mem A.root s)
        (.disj (Project.Formula.extensionalEq s A.last) (.mem s A.last))) (encodeFormula C T A s b c)))))

theorem rawDecodedFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (c s b : Project.Term n) : (rawDecodedFormula C T A c s b).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.disj (.conj (.neg (.mem _ _)) (.conj (.atom _ _ _) (.atom _ _ _)))
    (.conj (.mem _ _) (.conj (.conj (.mem _ _) (.disj (.atom _ _ _) (.mem _ _))) (encodeFormula_delta0 _ _ _ _ _ _)))))

theorem rawDecodedFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {A : Context (Project.Term n)} (hA : A.Closed)
    (c s b : Project.Term n) (hc : c.freeSupport=[]) (hs : s.freeSupport=[])
    (hb : b.freeSupport=[]) : (rawDecodedFormula C T A c s b).FreeClosed := by
  have hEncode := encodeFormula_freeClosed hC hT hA s b c hs hb hc
  simp [rawDecodedFormula,Definitional.Formula.FreeClosed,hC.omega,hC.zero,hA.root,hA.first,hA.last,hc,hs,hb,hEncode]

theorem rawDecodedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : Context (Project.Term n))
    (c s b : Project.Term n) : Project.Formula.satisfies e (rawDecodedFormula C T A c s b) ↔
      RawDecoded M (C.eval e) (T.eval e) (A.eval e) (c.eval e) (s.eval e) (b.eval e) := by
  simp only [rawDecodedFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,encodeFormula_iff he]
  rfl

theorem raw_decode_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c : M.Domain} (hc : M.mem c C.omega) :
    ∃ s b, RawDecoded M C T A c s b := by
  classical
  by_cases hAfter : M.mem A.root c
  · obtain ⟨b,hb,slot,hSlot,hPos⟩ := active_coverage_d hM hC hT hA hc hAfter
    have hSlotNat := (omega_isOrdinal_d hM hC.omega).transitive A.length (hA.length_nat hM.1) slot hSlot
    obtain ⟨s,hs,hSourceAdd⟩ := hT.add.add_exists_d hM hC (hA.first_nat_d hM hC) hSlotNat
    have hSource := source_slot_bounds_d hM hC hT hA ⟨hSlot,hSourceAdd⟩
    have hEncode := (encode_at_base_iff_d hM hC hT (hA.first_nat_d hM hC) hSlotNat hb hSourceAdd).mpr hPos
    exact ⟨s,b,hs,hb,Or.inr ⟨hAfter,hSource,hEncode⟩⟩
  · exact ⟨A.first,C.zero,hA.first_nat_d hM hC,hC.zero_nat,Or.inl ⟨hAfter,rfl,rfl⟩⟩

theorem raw_decode_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b s' b' : M.Domain}
    (h : RawDecoded M C T A c s b) (h' : RawDecoded M C T A c s' b') : s=s' ∧ b=b' := by
  rcases h.2.2 with ⟨hNot,hs,hb⟩ | ⟨hAfter,hSource,hEncode⟩ <;>
    rcases h'.2.2 with ⟨hNot',hs',hb'⟩ | ⟨hAfter',hSource',hEncode'⟩
  · exact ⟨hs.trans hs'.symm,hb.trans hb'.symm⟩
  · exact False.elim (hNot hAfter')
  · exact False.elim (hNot' hAfter)
  · exact source_encode_injective_d hM hC hT hA hSource hSource' hEncode hEncode'

theorem raw_decoded_retained_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {A : Context M.Domain} (hA : A.Valid M C) {c s b : M.Domain} (hNot : ¬M.mem A.root c) :
    RawDecoded M C T A c s b ↔ s=A.first ∧ b=C.zero := by
  constructor
  · intro h
    rcases h.2.2 with ⟨_,hs,hb⟩ | ⟨hAfter,_⟩
    · exact ⟨hs,hb⟩
    · exact False.elim (hNot hAfter)
  · rintro ⟨rfl,rfl⟩
    exact ⟨hA.first_nat_d hM hC,hC.zero_nat,Or.inl ⟨hNot,rfl,rfl⟩⟩

theorem raw_decoded_active_iff {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {T : MatrixArithmetic M.Domain} {A : Context M.Domain} {c s b : M.Domain} (hAfter : M.mem A.root c) :
    RawDecoded M C T A c s b ↔ Source M A s ∧ Encode M C T A s b c := by
  constructor
  · intro h
    rcases h.2.2 with ⟨hNot,_⟩ | ⟨_,hS,hE⟩
    · exact False.elim (hNot hAfter)
    · exact ⟨hS,hE⟩
  · rintro ⟨hS,hE⟩
    exact ⟨hE.1,hE.2.1,Or.inr ⟨hAfter,hS,hE⟩⟩

theorem raw_decoded_source_bounds_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {A : Context M.Domain} (hA : A.Valid M C) {c s b : M.Domain} (h : RawDecoded M C T A c s b) : Source M A s := by
  rcases h.2.2 with ⟨_,hs,_⟩ | ⟨_,hS,_⟩
  · subst s
    exact ⟨hA.first.predecessor_mem,successor_le_of_lt hM hC hA.root hA.last hA.first hA.below⟩
  · exact hS

theorem encode_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {s : M.Domain} (hs : M.mem s C.omega) : Encode M C T A s C.zero s := by
  obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hC.zero_nat (hA.length_nat hM.1)
  have hz := natural_product_zero_left_d hM hC (hA.length_nat hM.1)
    ((hT.mul.mul_iff_product hM hC.zero_nat (hA.length_nat hM.1)).mp hTimes)
  subst off
  exact ⟨hs,hC.zero_nat,C.zero,hC.zero_nat,hTimes,
    (hT.add.add_iff_sum hM hs hC.zero_nat).mpr (sum_zero_d hM s hC.zero_empty)⟩

theorem raw_original_coordinates_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c : M.Domain} (hc : Source M A c) : RawDecoded M C T A c c C.zero := by
  have hcNat : M.mem c C.omega := by
    rcases hc.2 with he | hcx
    · exact he ▸ hA.last
    · exact (omega_isOrdinal_d hM hC.omega).transitive A.last hA.last c hcx
  exact (raw_decoded_active_iff hc.1).mpr ⟨hc,encode_zero_d hM hC hT hA hcNat⟩

private def coordinateEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain) (A : Context M.Domain) : Env M 15 :=
  let e := ((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions
  let e' := (((((e.push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference
  (((e'.push A.last).push A.root).push A.length).push A.first

private def rawGraphSchema : Project.Delta0BinarySchema 15 where
  body := Project.Formula.existsMem (.bound 16) (Project.Formula.existsMem (.bound 17)
    (.conj (rawDecodedFormula ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩
      ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ ⟨.bound 7,.bound 6,.bound 5,.bound 4⟩
      (.bound 3) (.bound 1) (.bound 0)) (codeFormula (.bound 2) (.bound 1) (.bound 0))))
  freeClosed := by
    have hRaw := rawDecodedFormula_freeClosed
      (show (⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ : ExpressionData (Project.Term 19)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (show ArithmeticClosed (⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ : MatrixArithmetic (Project.Term 19)) from ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩)
      (show (⟨.bound 7,.bound 6,.bound 5,.bound 4⟩ : Context (Project.Term 19)).Closed from ⟨rfl,rfl,rfl,rfl⟩)
      (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl
    simp [Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,codeFormula,pairFormula,hRaw]
  delta0 := .existsMem _ (.existsMem _ (.conj (rawDecodedFormula_delta0 _ _ _ _ _ _) (codeFormula_delta0 _ _ _)))

private theorem rawGraphSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (c key : M.Domain) :
    Project.Formula.satisfies (((coordinateEnv C T A).push c).push key) rawGraphSchema.body ↔
      ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧ RawDecoded M C T A c s b ∧ Codes M key s b := by
  simp only [rawGraphSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    rawDecodedFormula_iff he,codeFormula_iff he]
  rfl

structure CoordinateGraph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (G : M.Domain) : Prop where
  graph : Graph M G C.omega T.addPairs
  rows : ∀ c s b key, Codes M key s b → (MemPair M G c key ↔ M.mem c C.omega ∧ RawDecoded M C T A c s b)

theorem coordinate_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) : ∃ G, CoordinateGraph M C T A G := by
  obtain ⟨G,hSupport,hG⟩ := relation_comprehension_d hM rawGraphSchema (coordinateEnv C T A) C.omega T.addPairs
  have hRaw : ∀ c key, MemPair M G c key ↔ M.mem c C.omega ∧ M.mem key T.addPairs ∧
      ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧ RawDecoded M C T A c s b ∧ Codes M key s b := by
    intro c key
    simpa only [rawGraphSchema_iff hM.1] using hG c key
  have hRows : ∀ c s b key, Codes M key s b → (MemPair M G c key ↔ M.mem c C.omega ∧ RawDecoded M C T A c s b) := by
    intro c s b key hCode
    constructor
    · intro hAt
      obtain ⟨hc,_,s',_,b',_,hRaw,hCode'⟩ := (hRaw c key).mp hAt
      obtain ⟨hss,hbb⟩ := codes_injective hM.1 hCode hCode'
      subst s'
      subst b'
      exact ⟨hc,hRaw⟩
    · rintro ⟨hc,hDecode⟩
      exact (hRaw c key).mpr ⟨hc,(hT.add.pairs key).mpr ⟨s,hDecode.1,b,hDecode.2.1,hCode⟩,
        s,hDecode.1,b,hDecode.2.1,hDecode,hCode⟩
  refine ⟨G,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨s,b,hDecode⟩ := raw_decode_exists_d hM hC hT hA hc
    obtain ⟨key,hCode⟩ := codes_total hM s b
    exact ⟨key,(hT.add.pairs key).mpr ⟨s,hDecode.1,b,hDecode.2.1,hCode⟩,(hRows c s b key hCode).mpr ⟨hc,hDecode⟩⟩
  · intro c key key' hAt hAt'
    obtain ⟨_,_,s,_,b,_,hDecode,hCode⟩ := (hRaw c key).mp hAt
    obtain ⟨_,_,s',_,b',_,hDecode',hCode'⟩ := (hRaw c key').mp hAt'
    obtain ⟨hss,hbb⟩ := raw_decode_unique_d hM hC hT hA hDecode hDecode'
    subst s'
    subst b'
    exact codes_unique hM.1 hCode hCode'

theorem CoordinateGraph.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} {G J : M.Domain} (hG : CoordinateGraph M C T A G) (hJ : CoordinateGraph M C T A J) : G=J := by
  apply hG.graph.ext he hJ.graph
  intro c _ key
  constructor
  · intro hAt
    obtain ⟨s,_,b,_,hCode⟩ := (hT.add.pairs key).mp (hG.graph.bounds he hAt).2
    exact (hJ.rows c s b key hCode).mpr ((hG.rows c s b key hCode).mp hAt)
  · intro hAt
    obtain ⟨s,_,b,_,hCode⟩ := (hT.add.pairs key).mp (hJ.graph.bounds he hAt).2
    exact (hG.rows c s b key hCode).mpr ((hJ.rows c s b key hCode).mp hAt)

def Width (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (N width : M.Domain) : Prop := Encode M C T A A.last N width

/-- 1-Y 的 N 份额外复制，对应 BM4 的 count=N+1 份完整坏块。 -/
theorem width_as_bms_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {N width : M.Domain} (hWidth : Width M C T A N width) :
    ∃ count, M.mem count C.omega ∧ M.SuccessorOf count N ∧ ∃ total, M.mem total C.omega ∧
      Product M count A.length total ∧ Sum M A.root total width := by
  obtain ⟨_,hN,off,hOff,hTimes,hAdd⟩ := hWidth
  obtain ⟨count,hCount,hCountNat⟩ := hC.omega.1.2 N hN
  obtain ⟨total,hTotalNat,hTotal⟩ := natural_product_exists_d hM hC hCountNat (hA.length_nat hM.1)
  have hOld := (hT.mul.mul_iff_product hM hN (hA.length_nat hM.1)).mp hTimes
  have hSuccProd := natural_product_left_successor_d hM hC hN (hA.length_nat hM.1) hCount hOld hTotal
  have hLOff := natural_sum_comm_d hM hC hOff (hA.length_nat hM.1) hSuccProd
  obtain ⟨w,_,hW⟩ := natural_sum_exists_d hM hC.omega hA.root hTotalNat
  have hWidthEq := natural_sum_assoc_d hM hC (hA.length_nat hM.1) hOff (hA.root_add_length_d hM hC)
    ((hT.add.add_iff_sum hM hA.last hOff).mp hAdd) hLOff hW
  subst w
  exact ⟨count,hCountNat,hCount,total,hTotalNat,hTotal,hW⟩

theorem encode_seam_bms_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b target : M.Domain} (hEncode : Encode M C T A A.last b target) :
    ∃ next, M.mem next C.omega ∧ M.SuccessorOf next b ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times A.root A.length next C.zero target := by
  obtain ⟨next,hNext,hs,total,hTotal,hTimes,hAdd⟩ := width_as_bms_d hM hC hT hA hEncode
  have hTarget := natural_sum_closed_d hM hC.omega hA.root hTotal hAdd
  exact ⟨next,hNext,hs,total,hTotal,target,hTarget,(hT.mul.mul_iff_product hM hNext (hA.length_nat hM.1)).mpr hTimes,
    (hT.add.add_iff_sum hM hA.root hTotal).mpr hAdd,
    (hT.add.add_iff_sum hM hTarget hC.zero_nat).mpr (sum_zero_d hM target hC.zero_empty)⟩

private theorem nonseam_slot_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {s : M.Domain} (hy : M.mem A.root s) (hs : M.mem s A.last) :
    ∃ slot, M.mem slot A.length ∧ M.mem C.zero slot ∧ AddAt M T.addPairs T.plus A.root slot s := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hsω := hw.transitive A.last hA.last s hs
  obtain ⟨slot,hSlot,hDiff⟩ := truncated_difference_exists_d hM hC hsω hA.root
  have hSum := truncated_difference_add_inverse_d hM hC hDiff (Or.inr hy)
  have hSlotL : M.mem slot A.length := by
    rcases hw.wellOrder.linear.compare slot hSlot A.length (hA.length_nat hM.1) with he | hlt | hgt
    · have hEq := hM.1.eq_of_same_members slot A.length he
      subst slot
      have hSX := sum_unique_d hM hSum (hA.root_add_length_d hM hC)
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.last (hSX ▸ hs))
    · exact hlt
    · have hXS := sum_strict_right_d hM (hw.mem hA.root) (hA.root_add_length_d hM hC) hSum hgt
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s ((hw.mem hsω).transitive A.last hXS s hs))
  exact ⟨slot,hSlotL,(truncated_difference_positive_iff_d hM hC hDiff).mpr hy,(hT.add.add_iff_sum hM hA.root hSlot).mpr hSum⟩

theorem encode_nonseam_bms_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {s b target : M.Domain}
    (hy : M.mem A.root s) (hs : M.mem s A.last) (hEncode : Encode M C T A s b target) :
    ∃ slot, M.mem slot A.length ∧ M.mem C.zero slot ∧ AddAt M T.addPairs T.plus A.root slot s ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times A.root A.length b slot target := by
  obtain ⟨slot,hSlot,hPos,hSource⟩ := nonseam_slot_exists_d hM hC hT hA hy hs
  have hSlotNat := (omega_isOrdinal_d hM hC.omega).transitive A.length (hA.length_nat hM.1) slot hSlot
  exact ⟨slot,hSlot,hPos,hSource,(encode_at_base_iff_d hM hC hT hA.root hSlotNat hEncode.2.1 hSource).mp hEncode⟩

theorem raw_decoded_seam_bms_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c b : M.Domain}
    (hAfter : M.mem A.root c) (h : RawDecoded M C T A c A.last b) :
    ∃ next, M.mem next C.omega ∧ M.SuccessorOf next b ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times A.root A.length next C.zero c :=
  encode_seam_bms_d hM hC hT hA ((raw_decoded_active_iff hAfter).mp h).2

theorem raw_decoded_nonseam_bms_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b : M.Domain}
    (hAfter : M.mem A.root c) (h : RawDecoded M C T A c s b) (hs : M.mem s A.last) :
    ∃ slot, M.mem slot A.length ∧ M.mem C.zero slot ∧ AddAt M T.addPairs T.plus A.root slot s ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times A.root A.length b slot c := by
  obtain ⟨hSource,hEncode⟩ := (raw_decoded_active_iff hAfter).mp h
  exact encode_nonseam_bms_d hM hC hT hA hSource.1 hs hEncode

/-- 由现成覆盖和单射推出范围的双向刻画；不重做重复块归纳。 -/
theorem copy_position_lt_width_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {root L count total width b slot target : M.Domain}
    (hRoot : M.mem root C.omega) (hL : M.mem L C.omega) (hCount : M.mem count C.omega) (hb : M.mem b C.omega)
    (hTotal : Product M count L total) (hWidth : Sum M root total width) (hSlot : M.mem slot L)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times root L b slot target) :
    M.mem target width ↔ M.mem b count := by
  constructor
  · intro hTarget
    have hw := omega_isOrdinal_d hM hC.omega
    have hSlotNat := hw.transitive L hL slot hSlot
    obtain ⟨off,hOff,start,hStart,hTimes,hStartAdd,hTargetAdd⟩ := hPos
    have hS := (hT.add.add_iff_sum hM hRoot hOff).mp hStartAdd
    have hTgt := (hT.add.add_iff_sum hM hStart hSlotNat).mp hTargetAdd
    have hTargetNat := (hTargetAdd.bounds hM.1 hT.add).2.2
    have hSub : M.MemberSubset root target := fun x hx => sum_base_subset_d hM (hw.mem hStart) hTgt x
      (sum_base_subset_d hM (hw.mem hRoot) hS x hx)
    have hAfter := ordinal_subset_cases_d hM (hw.mem hRoot) (hw.mem hTargetNat) hSub
    obtain ⟨b',hb',slot',hSlot',hPos'⟩ := copy_interval_coverage_d hM hC hT.add hT.mul hRoot hL hCount hTotal hWidth hTarget hAfter
    obtain ⟨hbb,_⟩ := copy_position_injective_d hM hC hT.add hT.mul hRoot hL hb
      (hw.transitive count hCount b' hb') hSlot hSlot' ⟨off,hOff,start,hStart,hTimes,hStartAdd,hTargetAdd⟩ hPos'
    exact hbb.symm ▸ hb'
  · intro hbCount
    exact copy_position_bounded_d hM hC hT.add hT.mul hRoot hL hCount hTotal hWidth hbCount hSlot hPos

theorem encoded_lt_width_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {s b target N width : M.Domain}
    (hSource : Source M A s) (hEncode : Encode M C T A s b target) (hWidth : Width M C T A N width) :
    M.mem target width ↔ M.mem b N ∨ (b=N ∧ M.mem s A.last) := by
  have hb := hEncode.2.1
  have hN := hWidth.2.1
  obtain ⟨count,hCount,hCountSucc,total,_,hTotal,hWidthBMS⟩ := width_as_bms_d hM hC hT hA hWidth
  rcases hSource.2 with he | hs
  · subst s
    obtain ⟨next,hNext,hNextSucc,hSeam⟩ := encode_seam_bms_d hM hC hT hA hEncode
    have hCmp := (copy_position_lt_width_iff_d hM hC hT hA.root (hA.length_nat hM.1) hCount hNext
      hTotal hWidthBMS (hA.length_positive_d hM hC) hSeam).trans
        (natural_successor_lt_iff hM hC hN hb hCountSucc hNextSucc)
    refine hCmp.trans ⟨Or.inl,?_⟩
    rintro (hbN | ⟨_,hSelf⟩)
    · exact hbN
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.last hSelf)
  · obtain ⟨slot,hSlot,_,_,hPos⟩ := encode_nonseam_bms_d hM hC hT hA hSource.1 hs hEncode
    have hCmp := copy_position_lt_width_iff_d hM hC hT hA.root (hA.length_nat hM.1) hCount hb hTotal hWidthBMS hSlot hPos
    refine hCmp.trans ⟨?_,?_⟩
    · intro hbCount
      rcases (hCountSucc b).mp hbCount with hbN | hbEq
      · exact Or.inl hbN
      · exact Or.inr ⟨hM.1.eq_of_same_members b N hbEq,hs⟩
    · rintro (hbN | ⟨he,_⟩)
      · exact (hCountSucc b).mpr (Or.inl hbN)
      · exact he.symm ▸ hCountSucc.predecessor_mem

theorem raw_decoded_block_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b N width : M.Domain}
    (hAfter : M.mem A.root c) (hDecode : RawDecoded M C T A c s b)
    (hWidth : Width M C T A N width) (hc : M.mem c width) : b=N ∨ M.mem b N := by
  obtain ⟨hSource,hEncode⟩ := (raw_decoded_active_iff hAfter).mp hDecode
  rcases (encoded_lt_width_iff_d hM hC hT hA hSource hEncode hWidth).mp hc with hb | ⟨he,_⟩
  · exact Or.inr hb
  · exact Or.inl he

theorem seam_lt_width_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b target N width : M.Domain}
    (hEncode : Encode M C T A A.last b target) (hWidth : Width M C T A N width) :
    M.mem target width ↔ M.mem b N := by
  have h := encoded_lt_width_iff_d hM hC hT hA ⟨hA.below,Or.inl rfl⟩ hEncode hWidth
  exact h.trans ⟨fun h => h.elim id (fun h => False.elim
    (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.last h.2)),Or.inl⟩

theorem width_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {width : M.Domain} (h : Width M C T A C.zero width) : width=A.last :=
  encode_unique hM.1 hT h (encode_zero_d hM hC hT hA hA.last)

theorem width_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {N next width width' : M.Domain} (hs : M.SuccessorOf next N)
    (hW : Width M C T A N width) (hW' : Width M C T A next width') : Sum M width A.length width' := by
  obtain ⟨_,hN,off,hOff,hTimes,hAdd⟩ := hW
  obtain ⟨_,hNext,off',hOff',hTimes',hAdd'⟩ := hW'
  have hOffSum := natural_product_left_successor_d hM hC hN (hA.length_nat hM.1) hs
    ((hT.mul.mul_iff_product hM hN (hA.length_nat hM.1)).mp hTimes)
    ((hT.mul.mul_iff_product hM hNext (hA.length_nat hM.1)).mp hTimes')
  obtain ⟨u,_,hU⟩ := natural_sum_exists_d hM hC.omega (hAdd.bounds hM.1 hT.add).2.2 (hA.length_nat hM.1)
  have hEq := natural_sum_assoc_d hM hC hOff (hA.length_nat hM.1)
    ((hT.add.add_iff_sum hM hA.last hOff).mp hAdd) hU hOffSum ((hT.add.add_iff_sum hM hA.last hOff').mp hAdd')
  exact hEq ▸ hU

/-- 原定义的商余数规格：d=c−y，q=pred(d)，q=b·L+slot，s=(y+1)+slot。 -/
def RemainderSpec (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (c s b : M.Domain) : Prop :=
  M.mem b C.omega ∧ ∃ d, TruncatedDifference M C.omega C.zero c A.root d ∧
    ∃ q, PreviousLength M C.omega C.zero d q ∧ ∃ slot, M.mem slot A.length ∧
      AddAt M T.addPairs T.plus A.first slot s ∧ ∃ offset, M.mem offset C.omega ∧
        Product M b A.length offset ∧ Sum M offset slot q

private theorem remainder_position_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b slot off q : M.Domain}
    (hb : M.mem b C.omega) (hSlot : M.mem slot A.length) (hOff : M.mem off C.omega)
    (hP : Product M b A.length off) (hQ : Sum M off slot q) :
    CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times C.zero A.length b slot q := by
  have hSlotNat := (omega_isOrdinal_d hM hC.omega).transitive A.length (hA.length_nat hM.1) slot hSlot
  have hZeroOff := natural_sum_comm_d hM hC hOff hC.zero_nat (sum_zero_d hM off hC.zero_empty)
  exact ⟨off,hOff,off,hOff,(hT.mul.mul_iff_product hM hb (hA.length_nat hM.1)).mpr hP,
    (hT.add.add_iff_sum hM hC.zero_nat hOff).mpr hZeroOff,(hT.add.add_iff_sum hM hOff hSlotNat).mpr hQ⟩

theorem remainder_spec_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b s' b' : M.Domain}
    (h : RemainderSpec M C T A c s b) (h' : RemainderSpec M C T A c s' b') : s=s' ∧ b=b' := by
  obtain ⟨hb,d,hd,q,hq,slot,hSlot,hSource,off,hOff,hProd,hSum⟩ := h
  obtain ⟨hb',d',hd',q',hq',slot',hSlot',hSource',off',hOff',hProd',hSum'⟩ := h'
  have hdd := truncated_difference_unique_d hM hC hd hd'
  subst d'
  have hqq := previous_length_unique_d hM hC hq hq'
  subst q'
  have hPos := remainder_position_d hM hC hT hA hb hSlot hOff hProd hSum
  have hPos' := remainder_position_d hM hC hT hA hb' hSlot' hOff' hProd' hSum'
  obtain ⟨hbb,hSlots⟩ := copy_position_injective_d hM hC hT.add hT.mul hC.zero_nat (hA.length_nat hM.1)
    hb hb' hSlot hSlot' hPos hPos'
  subst slot'
  exact ⟨hT.add.add_unique hM.1 hSource hSource',hbb⟩

theorem raw_decoded_remainder_spec_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b : M.Domain} (hc : M.mem c C.omega)
    (h : RawDecoded M C T A c s b) : RemainderSpec M C T A c s b := by
  have hb := h.2.1
  obtain ⟨d,hdNat,hDiff⟩ := truncated_difference_exists_d hM hC hc hA.root
  rcases h.2.2 with ⟨hNot,hs,hbz⟩ | ⟨hAfter,hSource,hEncode⟩
  · subst s
    subst b
    have hdz := (truncated_difference_eq_zero_iff_d hM hC hDiff).mpr hNot
    subst d
    have hProd : Product M C.zero A.length C.zero := natural_product_comm_d hM hC (hA.length_nat hM.1) hC.zero_nat
      (product_zero_d hM ((omega_isOrdinal_d hM hC.omega).mem (hA.length_nat hM.1)) hC.zero_empty)
    exact ⟨hC.zero_nat,C.zero,hDiff,C.zero,⟨hC.zero_nat,Or.inl ⟨rfl,rfl⟩⟩,
      C.zero,hA.length_positive_d hM hC,(hT.add.add_iff_sum hM (hA.first_nat_d hM hC) hC.zero_nat).mpr
        (sum_zero_d hM A.first hC.zero_empty),C.zero,hC.zero_nat,hProd,sum_zero_d hM C.zero hC.zero_empty⟩
  · obtain ⟨q,hq⟩ := previous_length_exists_d hM hC hdNat
    have hDPos := (truncated_difference_positive_iff_d hM hC hDiff).mpr hAfter
    have hDQ : M.SuccessorOf d q := by
      rcases hq.2 with ⟨hdz,_⟩ | hs
      · exact False.elim (hC.zero_empty C.zero (hdz ▸ hDPos))
      · exact hs
    have hRootD := truncated_difference_add_inverse_d hM hC hDiff (Or.inr hAfter)
    obtain ⟨u,hu,hRootQ⟩ := natural_sum_exists_d hM hC.omega hA.root hq.1
    obtain ⟨c',_,hFirstQ⟩ := natural_sum_exists_d hM hC.omega (hA.first_nat_d hM hC) hq.1
    have hCU := sum_successor_d hM hDQ hRootQ hRootD
    have hC'U := natural_sum_left_successor_d hM hC hq.1 hA.first hRootQ hFirstQ
    have hcc := Structure.SuccessorOf.eq hM.1 hC'U hCU
    subst c'
    obtain ⟨slot,hSlot,hFirstSlot⟩ := source_slot_exists_d hM hC hT hA hSource
    have hSlotNat := (omega_isOrdinal_d hM hC.omega).transitive A.length (hA.length_nat hM.1) slot hSlot
    have hPos := (encode_at_base_iff_d hM hC hT (hA.first_nat_d hM hC) hSlotNat hb hFirstSlot).mp hEncode
    obtain ⟨off,hOff,start,hStart,hTimes,hStartAdd,hTargetAdd⟩ := hPos
    obtain ⟨q',hq',hOffSlot⟩ := natural_sum_exists_d hM hC.omega hOff hSlotNat
    obtain ⟨c',_,hRootQ'⟩ := natural_sum_exists_d hM hC.omega (hA.first_nat_d hM hC) hq'
    have hcc' := natural_sum_assoc_d hM hC hOff hSlotNat
      ((hT.add.add_iff_sum hM (hA.first_nat_d hM hC) hOff).mp hStartAdd)
      ((hT.add.add_iff_sum hM hStart hSlotNat).mp hTargetAdd) hOffSlot hRootQ'
    subst c'
    have hqq' := natural_sum_cancel_left_d hM hC (hA.first_nat_d hM hC) hq.1 hq' hFirstQ hRootQ'
    subst q'
    exact ⟨hb,d,hDiff,q,hq,slot,hSlot,hFirstSlot,off,hOff,
      (hT.mul.mul_iff_product hM hb (hA.length_nat hM.1)).mp hTimes,hOffSlot⟩

theorem raw_decoded_iff_remainder_spec_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b : M.Domain} (hc : M.mem c C.omega) :
    RawDecoded M C T A c s b ↔ RemainderSpec M C T A c s b := by
  constructor
  · exact raw_decoded_remainder_spec_d hM hC hT hA hc
  · intro hSpec
    obtain ⟨s',b',hRaw⟩ := raw_decode_exists_d hM hC hT hA hc
    obtain ⟨hss,hbb⟩ := remainder_spec_unique_d hM hC hT hA hSpec (raw_decoded_remainder_spec_d hM hC hT hA hc hRaw)
    subst s'
    subst b'
    exact hRaw

theorem encoded_decodes_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} {s b c : M.Domain} (hSource : Source M A s) (hEncode : Encode M C T A s b c) :
    RawDecoded M C T A c s b := by
  have hCopy := hEncode
  obtain ⟨hs,_,off,hOff,_,hAdd⟩ := hCopy
  have hAfter := sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hs)
    ((hT.add.add_iff_sum hM hs hOff).mp hAdd) A.root hSource.1
  exact (raw_decoded_active_iff hAfter).mpr ⟨hSource,hEncode⟩

theorem first_seam_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) : RawDecoded M C T A A.last A.last C.zero :=
  raw_original_coordinates_d hM hC hT hA ⟨hA.below,Or.inl rfl⟩

theorem seam_decodes_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b c : M.Domain} (hEncode : Encode M C T A A.last b c) :
    RawDecoded M C T A c A.last b := encoded_decodes_d hM hC hT ⟨hA.below,Or.inl rfl⟩ hEncode

private def encodeGraphSchema : Project.Delta0BinarySchema 15 where
  body := Project.Formula.existsMem (.bound 16) (Project.Formula.existsMem (.bound 17)
    (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0))
      (encodeFormula ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩
        ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ ⟨.bound 7,.bound 6,.bound 5,.bound 4⟩
        (.bound 1) (.bound 0) (.bound 2))))
  freeClosed := by
    have hEnc := encodeFormula_freeClosed
      (show (⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ : ExpressionData (Project.Term 19)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (show ArithmeticClosed (⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ : MatrixArithmetic (Project.Term 19)) from ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩)
      (show (⟨.bound 7,.bound 6,.bound 5,.bound 4⟩ : Context (Project.Term 19)).Closed from ⟨rfl,rfl,rfl,rfl⟩)
      (.bound 1) (.bound 0) (.bound 2) rfl rfl rfl
    simp [Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,codeFormula,pairFormula,hEnc]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (encodeFormula_delta0 _ _ _ _ _ _)))

private theorem encodeGraphSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (key target : M.Domain) :
    Project.Formula.satisfies (((coordinateEnv C T A).push key).push target) encodeGraphSchema.body ↔
      ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧ Codes M key s b ∧ Encode M C T A s b target := by
  simp only [encodeGraphSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,encodeFormula_iff he]
  rfl

structure EncoderGraph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (E : M.Domain) : Prop where
  graph : Graph M E T.addPairs C.omega
  rows : ∀ s b key, Codes M key s b → ∀ target, MemPair M E key target ↔ Encode M C T A s b target

theorem encoder_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) : ∃ E, EncoderGraph M C T A E := by
  obtain ⟨E,hSupport,hE⟩ := relation_comprehension_d hM encodeGraphSchema (coordinateEnv C T A) T.addPairs C.omega
  have hRaw : ∀ key target, MemPair M E key target ↔ M.mem key T.addPairs ∧ M.mem target C.omega ∧
      ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧ Codes M key s b ∧ Encode M C T A s b target := by
    intro key target
    simpa only [encodeGraphSchema_iff hM.1] using hE key target
  have hRows : ∀ s b key, Codes M key s b → ∀ target, MemPair M E key target ↔ Encode M C T A s b target := by
    intro s b key hCode target
    constructor
    · intro hAt
      obtain ⟨_,_,s',_,b',_,hCode',hEncode⟩ := (hRaw key target).mp hAt
      obtain ⟨hss,hbb⟩ := codes_injective hM.1 hCode hCode'
      subst s'
      subst b'
      exact hEncode
    · intro hEncode
      have ht : M.mem target C.omega := by
        obtain ⟨_,_,_,_,_,hAdd⟩ := hEncode
        exact (hAdd.bounds hM.1 hT.add).2.2
      exact (hRaw key target).mpr ⟨(hT.add.pairs key).mpr ⟨s,hEncode.1,b,hEncode.2.1,hCode⟩,
        ht,s,hEncode.1,b,hEncode.2.1,hCode,hEncode⟩
  refine ⟨E,⟨hSupport,?_,?_⟩,hRows⟩
  · intro key hk
    obtain ⟨s,hs,b,hb,hCode⟩ := (hT.add.pairs key).mp hk
    obtain ⟨target,ht,hEncode⟩ := encode_exists_d hM hC hT hA hs hb
    exact ⟨target,ht,(hRows s b key hCode target).mpr hEncode⟩
  · intro key x y hx hy
    obtain ⟨_,_,s,_,b,_,hCode,hEncode⟩ := (hRaw key x).mp hx
    exact encode_unique hM.1 hT hEncode ((hRows s b key hCode y).mp hy)

def shiftColumnFormula {n : Nat} (Pairs Plus root offset p target : Project.Term n) : Project.Formula 1 n :=
  .disj (.conj (.mem p root) (Project.Formula.extensionalEq target p))
    (.conj (.neg (.mem p root)) (addAtFormula Pairs Plus p offset target))

theorem shiftColumnFormula_delta0 {n : Nat} (Pairs Plus root offset p target : Project.Term n) :
    (shiftColumnFormula Pairs Plus root offset p target).IsDelta0 :=
  .disj (.conj (.mem _ _) (.atom _ _ _)) (.conj (.neg (.mem _ _)) (addAtFormula_delta0 _ _ _ _ _))

theorem shiftColumnFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (Pairs Plus root offset p target : Project.Term n) :
    Project.Formula.satisfies e (shiftColumnFormula Pairs Plus root offset p target) ↔
      ShiftColumn M (Pairs.eval e) (Plus.eval e) (root.eval e) (offset.eval e) (p.eval e) (target.eval e) := by
  simp only [shiftColumnFormula,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,addAtFormula_iff he]
  rfl

private def globalShiftSchema : Project.Delta0BinarySchema 4 where
  body := shiftColumnFormula (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [shiftColumnFormula,addAtFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,
      Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := shiftColumnFormula_delta0 _ _ _ _ _ _

private theorem globalShiftSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (Pairs Plus root offset p target : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv Pairs).push Plus).push root).push offset).push p).push target) globalShiftSchema.body ↔
      ShiftColumn M Pairs Plus root offset p target := by
  rw [globalShiftSchema,shiftColumnFormula_iff he]
  rfl

/-- 将既有有限前缀嵌入统一为整个内部ω上的实际平移图；保序性复用有限嵌入。 -/
theorem global_shift_map_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {root offset : M.Domain} (hRoot : M.mem root C.omega) (hOffset : M.mem offset C.omega) :
    ∃ J, ColumnEmbedding M C.omega C.omega J ∧
      ∀ p target, MemPair M J p target ↔ M.mem p C.omega ∧ ShiftColumn M T.addPairs T.plus root offset p target := by
  obtain ⟨J,hSupport,hJ⟩ := relation_comprehension_d hM globalShiftSchema
    ((((oneEnv T.addPairs).push T.plus).push root).push offset) C.omega C.omega
  have hRows : ∀ p target, MemPair M J p target ↔ M.mem p C.omega ∧ ShiftColumn M T.addPairs T.plus root offset p target := by
    intro p target
    rw [hJ p target,globalShiftSchema_iff hM.1]
    refine ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,?_,h.2⟩⟩
    rcases h.2 with ⟨_,he⟩ | ⟨_,hAdd⟩
    · exact he ▸ h.1
    · exact (hAdd.bounds hM.1 hT.add).2.2
  have hGraph : Graph M J C.omega C.omega := by
    refine ⟨hSupport,?_,?_⟩
    · intro p hp
      classical
      by_cases hGood : M.mem p root
      · exact ⟨p,hp,(hRows p p).mpr ⟨hp,Or.inl ⟨hGood,rfl⟩⟩⟩
      · obtain ⟨x,hx,hAdd⟩ := hT.add.add_exists_d hM hC hp hOffset
        exact ⟨x,hx,(hRows p x).mpr ⟨hp,Or.inr ⟨hGood,hAdd⟩⟩⟩
    · intro p x y hx hy
      rcases ((hRows p x).mp hx).2 with ⟨hGood,hx⟩ | ⟨hNot,hx⟩ <;>
        rcases ((hRows p y).mp hy).2 with ⟨hGood',hy⟩ | ⟨hNot',hy⟩
      · exact hx.trans hy.symm
      · exact False.elim (hNot' hGood)
      · exact False.elim (hNot hGood')
      · exact hT.add.add_unique hM.1 hx hy
  refine ⟨J,⟨hGraph,?_⟩,hRows⟩
  intro a ha c hc hac x y hax hcy
  obtain ⟨m,hm,hmNat⟩ := hC.omega.1.2 c hc
  obtain ⟨off,F,hOff,hTimes,hF,hFRows⟩ := copy_column_map_exists_d hM hC hmNat hRoot hC.one_nat hOffset hT.add hT.mul
  have hOffEq := natural_product_one_left_d hM hC hOffset ((hT.mul.mul_iff_product hM hC.one_nat hOffset).mp hTimes)
  subst off
  have ham := (hm a).mpr (Or.inl hac)
  exact hF.strict a ham c hm.predecessor_mem hac x y
    ((hFRows a x).mpr ⟨ham,((hRows a x).mp hax).2⟩)
    ((hFRows c y).mpr ⟨hm.predecessor_mem,((hRows c y).mp hcy).2⟩)

def ParentCopy (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (b p target : M.Domain) : Prop :=
  M.mem p C.omega ∧ M.mem b C.omega ∧
    ((M.mem p A.root ∧ target=p) ∨ (¬M.mem p A.root ∧ Encode M C T A p b target))

def parentCopyFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (b p target : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem p C.omega) (.conj (.mem b C.omega)
    (.disj (.conj (.mem p A.root) (Project.Formula.extensionalEq target p))
      (.conj (.neg (.mem p A.root)) (encodeFormula C T A p b target))))

theorem parentCopyFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (b p target : Project.Term n) : (parentCopyFormula C T A b p target).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.disj (.conj (.mem _ _) (.atom _ _ _))
    (.conj (.neg (.mem _ _)) (encodeFormula_delta0 _ _ _ _ _ _))))

theorem parentCopyFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {A : Context (Project.Term n)} (hA : A.Closed)
    (b p target : Project.Term n) (hb : b.freeSupport=[]) (hp : p.freeSupport=[])
    (ht : target.freeSupport=[]) : (parentCopyFormula C T A b p target).FreeClosed := by
  have hEnc := encodeFormula_freeClosed hC hT hA p b target hp hb ht
  simp [parentCopyFormula,Definitional.Formula.FreeClosed,hC.omega,hA.root,hb,hp,ht,hEnc]

theorem parentCopyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : Context (Project.Term n))
    (b p target : Project.Term n) : Project.Formula.satisfies e (parentCopyFormula C T A b p target) ↔
      ParentCopy M (C.eval e) (T.eval e) (A.eval e) (b.eval e) (p.eval e) (target.eval e) := by
  simp only [parentCopyFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_neg_iff,encodeFormula_iff he]
  rfl

theorem parent_copy_shift_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} {b p off target : M.Domain} (hb : M.mem b C.omega) (hp : M.mem p C.omega)
    (hOff : M.mem off C.omega) (hTimes : MulAt M T.mulPairs T.times b A.length off) :
    ParentCopy M C T A b p target ↔ ShiftColumn M T.addPairs T.plus A.root off p target := by
  constructor
  · intro h
    rcases h.2.2 with ⟨hGood,ht⟩ | ⟨hNot,hEnc⟩
    · exact Or.inl ⟨hGood,ht⟩
    · obtain ⟨_,_,off',_,hTimes',hAdd⟩ := hEnc
      have hEq := hT.mul.mul_unique he hTimes' hTimes
      subst off'
      exact Or.inr ⟨hNot,hAdd⟩
  · rintro (⟨hGood,ht⟩ | ⟨hNot,hAdd⟩)
    · exact ⟨hp,hb,Or.inl ⟨hGood,ht⟩⟩
    · exact ⟨hp,hb,Or.inr ⟨hNot,hp,hb,off,hOff,hTimes,hAdd⟩⟩

theorem parent_copy_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b : M.Domain} (hb : M.mem b C.omega) :
    ∃ J, ColumnEmbedding M C.omega C.omega J ∧ ∀ p target, MemPair M J p target ↔ ParentCopy M C T A b p target := by
  obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hb (hA.length_nat hM.1)
  obtain ⟨J,hJ,hRows⟩ := global_shift_map_exists_d hM hC hT hA.root hOff
  refine ⟨J,hJ,fun p target => ?_⟩
  rw [hRows p target]
  exact ⟨fun h => (parent_copy_shift_iff hM.1 hT hb h.1 hOff hTimes).mpr h.2,
    fun h => ⟨h.1,(parent_copy_shift_iff hM.1 hT hb h.1 hOff hTimes).mp h⟩⟩

theorem parent_copy_below_encode_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b p s u target : M.Domain}
    (hAfter : M.mem A.root s) (hps : M.mem p s) (hParent : ParentCopy M C T A b p u)
    (hEncode : Encode M C T A s b target) : M.mem u target := by
  have hNot : ¬M.mem s A.root := by
    intro hs
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
      (((omega_isOrdinal_d hM hC.omega).mem hA.root).transitive s hs A.root hAfter)
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hParent.2.1
  exact hJ.strict p hParent.1 s hEncode.1 hps u target ((hRows p u).mpr hParent)
    ((hRows s target).mpr ⟨hEncode.1,hEncode.2.1,Or.inr ⟨hNot,hEncode⟩⟩)

theorem parent_copy_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {p : M.Domain} (hp : M.mem p C.omega) : ParentCopy M C T A C.zero p p := by
  classical
  by_cases hGood : M.mem p A.root
  · exact ⟨hp,hC.zero_nat,Or.inl ⟨hGood,rfl⟩⟩
  · exact ⟨hp,hC.zero_nat,Or.inr ⟨hGood,encode_zero_d hM hC hT hA hp⟩⟩

theorem parent_copy_good_iff {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {T : MatrixArithmetic M.Domain} {A : Context M.Domain} {b p target : M.Domain}
    (hb : M.mem b C.omega) (hp : M.mem p C.omega) (hGood : M.mem p A.root) :
    ParentCopy M C T A b p target ↔ target=p := by
  constructor
  · intro h
    exact h.2.2.elim And.right (fun h => False.elim (h.1 hGood))
  · intro he
    exact ⟨hp,hb,Or.inl ⟨hGood,he⟩⟩

theorem parent_copy_bad_iff {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {T : MatrixArithmetic M.Domain} {A : Context M.Domain} {b p target : M.Domain} (hBad : ¬M.mem p A.root) :
    ParentCopy M C T A b p target ↔ Encode M C T A p b target := by
  constructor
  · intro h
    exact h.2.2.elim (fun h => False.elim (hBad h.1)) And.right
  · intro h
    exact ⟨h.1,h.2.1,Or.inr ⟨hBad,h⟩⟩

/-- 这里只读取共享差表的有序对键，不再构造另一套减法。 -/
def DifferenceRead (M : SetTheory.Structure.{u}) (T : MatrixArithmetic M.Domain) (a b d : M.Domain) : Prop :=
  ∃ key, M.mem key T.diffPairs ∧ Codes M key a b ∧ MemPair M T.difference key d

def differenceReadFormula {n : Nat} (T : MatrixArithmetic (Project.Term n)) (a b d : Project.Term n) : Project.Formula 1 n :=
  addAtFormula T.diffPairs T.difference a b d

theorem differenceReadFormula_delta0 {n : Nat} (T : MatrixArithmetic (Project.Term n)) (a b d : Project.Term n) :
    (differenceReadFormula T a b d).IsDelta0 := addAtFormula_delta0 _ _ _ _ _

theorem differenceReadFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (T : MatrixArithmetic (Project.Term n)) (a b d : Project.Term n) :
    Project.Formula.satisfies e (differenceReadFormula T a b d) ↔ DifferenceRead M (T.eval e) (a.eval e) (b.eval e) (d.eval e) := by
  rw [differenceReadFormula,addAtFormula_iff he]
  rfl

theorem difference_read_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {a b d : M.Domain} (ha : M.mem a C.omega) (hb : M.mem b C.omega) :
    DifferenceRead M T a b d ↔ TruncatedDifference M C.omega C.zero a b d := by
  constructor
  · rintro ⟨key,_,hCode,hAt⟩
    exact (hT.diff.rows a ha b hb key hCode d).mp hAt
  · intro hDiff
    obtain ⟨key,hCode⟩ := codes_total hM a b
    exact ⟨key,(hT.diff.pairs key).mpr ⟨a,ha,b,hb,hCode⟩,hCode,(hT.diff.rows a ha b hb key hCode d).mpr hDiff⟩

theorem difference_read_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {a b : M.Domain} (ha : M.mem a C.omega) (hb : M.mem b C.omega) :
    ∃ d, M.mem d C.omega ∧ DifferenceRead M T a b d := by
  obtain ⟨key,hCode⟩ := codes_total hM a b
  have hk := (hT.diff.pairs key).mpr ⟨a,ha,b,hb,hCode⟩
  obtain ⟨d,hd,hAt⟩ := hT.diff.graph.total key hk
  exact ⟨d,hd,key,hk,hCode,hAt⟩

theorem difference_read_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {a b d e : M.Domain} (hd : DifferenceRead M T a b d) (he' : DifferenceRead M T a b e) : d=e := by
  obtain ⟨key,_,hCode,hAt⟩ := hd
  obtain ⟨key',_,hCode',hAt'⟩ := he'
  have hkk := codes_unique he hCode hCode'
  subst key'
  exact hT.diff.graph.unique key d e hAt hAt'

/-- 原拼接坐标：i<cut 时不动，否则 n+(i−cut)。无效几何参数仍给实际总函数。 -/
def MoveColumn (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (n cut i target : M.Domain) : Prop :=
  M.mem n C.omega ∧ M.mem cut C.omega ∧ M.mem i C.omega ∧
    ((M.mem i cut ∧ target=i) ∨ (¬M.mem i cut ∧ ∃ d, M.mem d C.omega ∧ DifferenceRead M T i cut d ∧ AddAt M T.addPairs T.plus n d target))

def moveColumnFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (size cut i target : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem size C.omega) (.conj (.mem cut C.omega) (.conj (.mem i C.omega)
    (.disj (.conj (.mem i cut) (Project.Formula.extensionalEq target i))
      (.conj (.neg (.mem i cut)) (Project.Formula.existsMem C.omega
        (.conj (differenceReadFormula T.weaken i.weaken cut.weaken (.bound 0))
          (addAtFormula T.addPairs.weaken T.plus.weaken size.weaken (.bound 0) target.weaken)))))))

theorem moveColumnFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (size cut i target : Project.Term n) : (moveColumnFormula C T size cut i target).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.disj (.conj (.mem _ _) (.atom _ _ _))
    (.conj (.neg (.mem _ _)) (.existsMem _ (.conj (differenceReadFormula_delta0 _ _ _ _) (addAtFormula_delta0 _ _ _ _ _)))))))

theorem moveColumnFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) (size cut i target : Project.Term n)
    (hn : size.freeSupport=[]) (hc : cut.freeSupport=[]) (hi : i.freeSupport=[])
    (ht : target.freeSupport=[]) : (moveColumnFormula C T size cut i target).FreeClosed := by
  simp [moveColumnFormula,differenceReadFormula,addAtFormula,MatrixArithmetic.weaken,MatrixArithmetic.map,
    memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hC.omega,hT.addPairs,hT.plus,hT.diffPairs,hT.difference,hn,hc,hi,ht]

theorem moveColumnFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (size cut i target : Project.Term n) :
    Project.Formula.satisfies e (moveColumnFormula C T size cut i target) ↔
      MoveColumn M (C.eval e) (T.eval e) (size.eval e) (cut.eval e) (i.eval e) (target.eval e) := by
  simp only [moveColumnFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_existsMem_iff,
    differenceReadFormula_iff he,addAtFormula_iff he,MatrixArithmetic.eval_weaken,Term.eval_weaken]
  rfl

theorem move_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {n cut i : M.Domain} (hn : M.mem n C.omega) (hCut : M.mem cut C.omega) (hi : M.mem i C.omega) :
    ∃ target, M.mem target C.omega ∧ MoveColumn M C T n cut i target := by
  classical
  by_cases hGood : M.mem i cut
  · exact ⟨i,hi,hn,hCut,hi,Or.inl ⟨hGood,rfl⟩⟩
  · obtain ⟨d,hd,hRead⟩ := difference_read_exists_d hM hT hi hCut
    obtain ⟨target,ht,hAdd⟩ := hT.add.add_exists_d hM hC hn hd
    exact ⟨target,ht,hn,hCut,hi,Or.inr ⟨hGood,d,hd,hRead,hAdd⟩⟩

theorem move_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {n cut i x y : M.Domain} (hx : MoveColumn M C T n cut i x) (hy : MoveColumn M C T n cut i y) : x=y := by
  rcases hx.2.2.2 with ⟨hGood,hx⟩ | ⟨hNot,d,_,hD,hX⟩ <;>
    rcases hy.2.2.2 with ⟨hGood',hy⟩ | ⟨hNot',e,_,hE,hY⟩
  · exact hx.trans hy.symm
  · exact False.elim (hNot' hGood)
  · exact False.elim (hNot hGood')
  · have hde := difference_read_unique he hT hD hE
    subst e
    exact hT.add.add_unique he hX hY

private def moveEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (n cut : M.Domain) : Env M 13 :=
  let e := ((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions
  let e' := (((((e.push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference
  (e'.push n).push cut

private def moveSchema : Project.Delta0BinarySchema 13 where
  body := moveColumnFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩
    ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5,.bound 4⟩ (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := moveColumnFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ rfl rfl rfl rfl
  delta0 := moveColumnFormula_delta0 _ _ _ _ _ _

private theorem moveSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (n cut i target : M.Domain) :
    Project.Formula.satisfies (((moveEnv C T n cut).push i).push target) moveSchema.body ↔ MoveColumn M C T n cut i target := by
  rw [moveSchema,moveColumnFormula_iff he]
  rfl

theorem move_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {n cut : M.Domain} (hn : M.mem n C.omega) (hCut : M.mem cut C.omega) :
    ∃ J, Graph M J C.omega C.omega ∧ ∀ i target, MemPair M J i target ↔ MoveColumn M C T n cut i target := by
  obtain ⟨J,hSupport,hJ⟩ := relation_comprehension_d hM moveSchema (moveEnv C T n cut) C.omega C.omega
  have hRows : ∀ i target, MemPair M J i target ↔ MoveColumn M C T n cut i target := by
    intro i target
    rw [hJ i target,moveSchema_iff hM.1]
    refine ⟨fun h => h.2.2,fun h => ⟨h.2.2.1,?_,h⟩⟩
    rcases h.2.2.2 with ⟨_,he⟩ | ⟨_,_,_,_,hAdd⟩
    · exact he ▸ h.2.2.1
    · exact (hAdd.bounds hM.1 hT.add).2.2
  refine ⟨J,⟨hSupport,?_,?_⟩,hRows⟩
  · intro i hi
    obtain ⟨target,ht,hMove⟩ := move_exists_d hM hC hT hn hCut hi
    exact ⟨target,ht,(hRows i target).mpr hMove⟩
  · intro i x y hx hy
    exact move_unique hM.1 hT ((hRows i x).mp hx) ((hRows i y).mp hy)

theorem move_as_shift_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {n cut d i target : M.Domain} (hDiff : TruncatedDifference M C.omega C.zero n cut d)
    (hCutLe : cut=n ∨ M.mem cut n) (hi : M.mem i C.omega) :
    MoveColumn M C T n cut i target ↔ ShiftColumn M T.addPairs T.plus cut d i target := by
  have hn := hDiff.1
  have hCut := hDiff.2.1
  have hd := truncated_difference_natural hM.1 hDiff
  have hCutD := truncated_difference_add_inverse_d hM hC hDiff hCutLe
  have hCutI : ¬M.mem i cut → cut=i ∨ M.mem cut i := by
    intro hNot
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare cut hCut i hi with he | hlt | hgt
    · exact Or.inl (hM.1.eq_of_same_members cut i he)
    · exact Or.inr hlt
    · exact False.elim (hNot hgt)
  constructor
  · intro hMove
    rcases hMove.2.2.2 with ⟨hGood,ht⟩ | ⟨hNot,e,he,hRead,hAdd⟩
    · exact Or.inl ⟨hGood,ht⟩
    · have hE := (difference_read_iff_d hM hT hi hCut).mp hRead
      have hCutE := truncated_difference_add_inverse_d hM hC hE (hCutI hNot)
      obtain ⟨x,_,hX⟩ := hT.add.add_exists_d hM hC hi hd
      have hEq := natural_sum_shuffle_d hM hC he hd hCutE ((hT.add.add_iff_sum hM hi hd).mp hX)
        hCutD ((hT.add.add_iff_sum hM hn he).mp hAdd)
      subst x
      exact Or.inr ⟨hNot,hX⟩
  · rintro (⟨hGood,ht⟩ | ⟨hNot,hAdd⟩)
    · exact ⟨hn,hCut,hi,Or.inl ⟨hGood,ht⟩⟩
    · obtain ⟨e,he,hRead⟩ := difference_read_exists_d hM hT hi hCut
      have hE := (difference_read_iff_d hM hT hi hCut).mp hRead
      have hCutE := truncated_difference_add_inverse_d hM hC hE (hCutI hNot)
      obtain ⟨x,_,hX⟩ := hT.add.add_exists_d hM hC hn he
      have hEq := natural_sum_shuffle_d hM hC he hd hCutE ((hT.add.add_iff_sum hM hi hd).mp hAdd)
        hCutD ((hT.add.add_iff_sum hM hn he).mp hX)
      subst x
      exact ⟨hn,hCut,hi,Or.inr ⟨hNot,e,he,hRead,hX⟩⟩

theorem move_embedding_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {n cut : M.Domain} (hn : M.mem n C.omega) (hCut : M.mem cut C.omega) (hLe : cut=n ∨ M.mem cut n) :
    ∃ J, ColumnEmbedding M C.omega C.omega J ∧ ∀ i target, MemPair M J i target ↔ MoveColumn M C T n cut i target := by
  obtain ⟨d,hd,hRead⟩ := difference_read_exists_d hM hT hn hCut
  have hDiff := (difference_read_iff_d hM hT hn hCut).mp hRead
  obtain ⟨J,hJ,hRows⟩ := global_shift_map_exists_d hM hC hT hCut hd
  refine ⟨J,hJ,fun i target => ?_⟩
  rw [hRows i target]
  exact ⟨fun h => (move_as_shift_d hM hC hT hDiff hLe h.1).mpr h.2,
    fun h => ⟨h.2.2.1,(move_as_shift_d hM hC hT hDiff hLe h.2.2.1).mp h⟩⟩

theorem move_prefix_fixed {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {n cut i : M.Domain} (hn : M.mem n C.omega) (hCut : M.mem cut C.omega) (hi : M.mem i C.omega)
    (hBefore : M.mem i cut) : MoveColumn M C T n cut i i := ⟨hn,hCut,hi,Or.inl ⟨hBefore,rfl⟩⟩

theorem move_cut_to_size_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {n cut : M.Domain} (hn : M.mem n C.omega) (hCut : M.mem cut C.omega) : MoveColumn M C T n cut cut n := by
  obtain ⟨d,_,hRead⟩ := difference_read_exists_d hM hT hCut hCut
  have hDiff := (difference_read_iff_d hM hT hCut hCut).mp hRead
  have hZero := truncated_difference_diagonal_d hM hC hDiff
  subst d
  exact ⟨hn,hCut,hCut,Or.inr ⟨SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) cut,
    C.zero,hC.zero_nat,hRead,
    (hT.add.add_iff_sum hM hn hC.zero_nat).mpr (sum_zero_d hM n hC.zero_empty)⟩⟩

theorem EncoderGraph.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} {E F : M.Domain} (hE : EncoderGraph M C T A E) (hF : EncoderGraph M C T A F) : E=F := by
  apply hE.graph.ext he hF.graph
  intro key hk target
  obtain ⟨s,_,b,_,hCode⟩ := (hT.add.pairs key).mp hk
  exact (hE.rows s b key hCode target).trans (hF.rows s b key hCode target).symm

private def widthSchema : Project.Delta0BinarySchema 15 where
  body := encodeFormula ⟨.bound 16,.bound 15,.bound 14,.bound 13,.bound 12⟩
    ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ ⟨.bound 5,.bound 4,.bound 3,.bound 2⟩
    (.bound 5) (.bound 1) (.bound 0)
  freeClosed := encodeFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ _ _ _ rfl rfl rfl
  delta0 := encodeFormula_delta0 _ _ _ _ _ _

private theorem widthSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (N width : M.Domain) :
    Project.Formula.satisfies (((coordinateEnv C T A).push N).push width) widthSchema.body ↔ Width M C T A N width := by
  rw [widthSchema,encodeFormula_iff he]
  rfl

theorem width_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) :
    ∃ W, Graph M W C.omega C.omega ∧ ∀ N width, MemPair M W N width ↔ Width M C T A N width := by
  obtain ⟨W,hSupport,hW⟩ := relation_comprehension_d hM widthSchema (coordinateEnv C T A) C.omega C.omega
  have hRows : ∀ N width, MemPair M W N width ↔ Width M C T A N width := by
    intro N width
    rw [hW N width,widthSchema_iff hM.1]
    refine ⟨fun h => h.2.2,fun h => ⟨h.2.1,?_,h⟩⟩
    obtain ⟨_,_,_,_,_,hAdd⟩ := h
    exact (hAdd.bounds hM.1 hT.add).2.2
  refine ⟨W,⟨hSupport,?_,?_⟩,hRows⟩
  · intro N hN
    obtain ⟨w,hw,hWidth⟩ := encode_exists_d hM hC hT hA hA.last hN
    exact ⟨w,hw,(hRows N w).mpr hWidth⟩
  · intro N w w' hw hw'
    exact encode_unique hM.1 hT ((hRows N w).mp hw) ((hRows N w').mp hw')

theorem retained_in_width_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c N width : M.Domain}
    (hc : c=A.root ∨ M.mem c A.root) (hWidth : Width M C T A N width) : M.mem c width := by
  obtain ⟨_,_,off,hOff,_,hAdd⟩ := hWidth
  have hw := omega_isOrdinal_d hM hC.omega
  have hcx : M.mem c A.last := by
    rcases hc with he | hcy
    · exact he.symm ▸ hA.below
    · exact (hw.mem hA.last).transitive A.root hA.below c hcy
  exact sum_base_subset_d hM (hw.mem hA.last) ((hT.add.add_iff_sum hM hA.last hOff).mp hAdd) c hcx

/-- 下一次cut y+(b+1)L就是本次宽度x+bL。 -/
theorem width_is_next_cut_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b next width : M.Domain}
    (hs : M.SuccessorOf next b) (hWidth : Width M C T A b width) : Encode M C T A A.root next width := by
  obtain ⟨count,hCount,hCountSucc,total,hTotalNat,hTotal,hSum⟩ := width_as_bms_d hM hC hT hA hWidth
  have hCounts := Structure.SuccessorOf.eq hM.1 hCountSucc hs
  subst count
  exact ⟨hA.root,hCount,total,hTotalNat,(hT.mul.mul_iff_product hM hCount (hA.length_nat hM.1)).mpr hTotal,
    (hT.add.add_iff_sum hM hA.root hTotalNat).mpr hSum⟩

theorem width_minus_cut_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b width cut : M.Domain}
    (hWidth : Width M C T A b width) (hCut : Encode M C T A A.root b cut) :
    TruncatedDifference M C.omega C.zero width cut A.length := by
  obtain ⟨_,_,off,hOff,hTimes,hWidthAdd⟩ := hWidth
  obtain ⟨_,_,off',_,hTimes',hCutAdd⟩ := hCut
  have hOffEq := hT.mul.mul_unique hM.1 hTimes' hTimes
  subst off'
  have hCutNat := (hCutAdd.bounds hM.1 hT.add).2.2
  obtain ⟨w,_,hW⟩ := natural_sum_exists_d hM hC.omega hCutNat (hA.length_nat hM.1)
  have hEq := natural_sum_shuffle_d hM hC (hA.length_nat hM.1) hOff (hA.root_add_length_d hM hC)
    ((hT.add.add_iff_sum hM hA.last hOff).mp hWidthAdd) ((hT.add.add_iff_sum hM hA.root hOff).mp hCutAdd) hW
  subst w
  exact truncated_difference_of_sum_d hM hC hCutNat (hA.length_nat hM.1) hW

theorem cut_lt_width_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b width cut : M.Domain}
    (hWidth : Width M C T A b width) (hCut : Encode M C T A A.root b cut) : M.mem cut width :=
  (truncated_difference_positive_iff_d hM hC (width_minus_cut_d hM hC hT hA hWidth hCut)).mp (hA.length_positive_d hM hC)

theorem move_column_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {n cut d i target bound : M.Domain} (hDiff : TruncatedDifference M C.omega C.zero n cut d)
    (hCutLe : cut=n ∨ M.mem cut n) (hBound : Sum M n d bound) (hi : M.mem i n)
    (hMove : MoveColumn M C T n cut i target) : M.mem target bound := by
  have hShift := (move_as_shift_d hM hC hT hDiff hCutLe hMove.2.2.1).mp hMove
  have hd := truncated_difference_natural hM.1 hDiff
  rcases hShift with ⟨_,he⟩ | ⟨_,hAdd⟩
  · subst target
    exact sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hDiff.1) hBound i hi
  · exact natural_sum_strict_left_d hM hC hMove.2.2.1 hDiff.1 hd
      ((hT.add.add_iff_sum hM hMove.2.2.1 hd).mp hAdd) hBound hi

/-- BM4 的下一副本首列等于当前 1-Y seam 的 last+bL 平移。 -/
theorem seam_bms_shift_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b next off c : M.Domain}
    (hb : M.mem b C.omega) (hs : M.SuccessorOf next b) (hOff : M.mem off C.omega)
    (hTimes : MulAt M T.mulPairs T.times b A.length off) :
    CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times A.root A.length next C.zero c ↔
      ShiftColumn M T.addPairs T.plus A.root off A.last c := by
  have hNot : ¬M.mem A.last A.root := by
    intro hLastRoot
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
      (((omega_isOrdinal_d hM hC.omega).mem hA.root).transitive A.last hLastRoot A.root hA.below)
  constructor
  · intro hPos
    obtain ⟨c',_,hEncode⟩ := encode_exists_d hM hC hT hA hA.last hb
    obtain ⟨next',_,hs',hPos'⟩ := encode_seam_bms_d hM hC hT hA hEncode
    have hNext := Structure.SuccessorOf.eq hM.1 hs' hs
    subst next'
    have hTarget := copy_position_unique hM.1 hT.add hT.mul hPos' hPos
    subst c'
    obtain ⟨_,_,off',_,hTimes',hAdd⟩ := hEncode
    have hOffsets := hT.mul.mul_unique hM.1 hTimes' hTimes
    subst off'
    exact Or.inr ⟨hNot,hAdd⟩
  · intro hShift
    rcases hShift with ⟨hGood,_⟩ | ⟨_,hAdd⟩
    · exact False.elim (hNot hGood)
    · have hEncode : Encode M C T A A.last b c := ⟨hA.last,hb,off,hOff,hTimes,hAdd⟩
      obtain ⟨next',_,hs',hPos⟩ := encode_seam_bms_d hM hC hT hA hEncode
      exact Structure.SuccessorOf.eq hM.1 hs' hs ▸ hPos

end KP1Y.OneYFinite.CopyCoordinates
