import KP1Y.OneYCopyDiagramAtoms

/-! 复制塔的层高度界和按(k,column,row)稳定过滤的实际根图列表。 -/
namespace KP1Y.OneYFinite.CopyDiagram
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u v

def LayerBound (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (I : Input M.Domain) (k b : M.Domain) : Prop :=
  ∃code, M.mem code I.codes ∧ MemPair M I.tower k code ∧ ∃heights parents, Codes M code heights parents ∧ SequenceBound M C I.width heights b

theorem LayerBound.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} {I : Input M.Domain}
    (hI : I.Valid M C) {k b : M.Domain} (h : LayerBound M C I k b) : M.mem k I.horizon ∧ M.mem b C.omega := by
  obtain ⟨code,_,hCode,_,_,_,hBound⟩ := h
  exact ⟨(hI.tower.bounds he hCode).1,hBound.1.1⟩

theorem layer_bound_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {I : Input M.Domain} (hI : I.Valid M C) {k : M.Domain} (hk : M.mem k I.horizon) :
    ∃b, LayerBound M C I k b := by
  obtain ⟨code,hc,hAt⟩ := hI.tower.total k hk
  obtain ⟨heights,parents,hCode,hX⟩ := hI.values k code hAt
  obtain ⟨b,hB⟩ := sequence_bound_exists_d hM hC hI.width hX.heights
  exact ⟨b,code,hc,hAt,heights,parents,hCode,hB⟩

theorem LayerBound.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {I : Input M.Domain} (hI : I.Valid M C) {k b b' : M.Domain}
    (h : LayerBound M C I k b) (h' : LayerBound M C I k b') : b=b' := by
  obtain ⟨code,_,hAt,heights,parents,hCode,hB⟩ := h
  obtain ⟨code',_,hAt',heights',parents',hCode',hB'⟩ := h'
  have he := hI.tower.unique k code code' hAt hAt'
  subst code'
  obtain ⟨hh,hp⟩ := codes_injective hM.1 hCode hCode'
  subst heights'
  exact hB.unique_d hM hC hB'

def layerBoundFormula {n : Nat} (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) (k b : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem I.codes (.conj (memPairFormula I.tower.weaken k.weaken (.bound 0))
    (CopiedMountain.withCodeFormula (.bound 0) (sequenceBoundFormula C.omega.weaken.weaken.weaken.weaken C.zero.weaken.weaken.weaken.weaken
      I.width.weaken.weaken.weaken.weaken (.bound 1) b.weaken.weaken.weaken.weaken)))

theorem layerBoundFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) (k b : Project.Term n) :
    (layerBoundFormula C I k b).IsDelta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _)
      (CopiedMountain.withCodeFormula_delta0 _ (sequenceBoundFormula_delta0 _ _ _ _ _)))

theorem layerBoundFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {I : Input (Project.Term n)} (hI : I.Closed) (k b : Project.Term n) (hk : k.freeSupport=[]) (hb : b.freeSupport=[]) :
    (layerBoundFormula C I k b).FreeClosed := by
  have hBound := sequenceBoundFormula_freeClosed C.omega.weaken.weaken.weaken.weaken C.zero.weaken.weaken.weaken.weaken
    I.width.weaken.weaken.weaken.weaken (.bound 1) b.weaken.weaken.weaken.weaken
    (by simpa using hC.omega) (by simpa using hC.zero) (by simpa using hI.width) rfl (by simpa using hb)
  have hCode := CopiedMountain.withCodeFormula_freeClosed (.bound 0) rfl hBound
  simp [layerBoundFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hI.codes,hI.tower,hk,hCode]

theorem layerBoundFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) (k b : Project.Term n) :
    Project.Formula.satisfies e (layerBoundFormula C I k b) ↔ LayerBound M (C.eval e) (I.eval e) (k.eval e) (b.eval e) := by
  have hBody (code : M.Domain) : Project.Formula.satisfies (e.push code) (CopiedMountain.withCodeFormula (.bound 0)
      (sequenceBoundFormula C.omega.weaken.weaken.weaken.weaken C.zero.weaken.weaken.weaken.weaken I.width.weaken.weaken.weaken.weaken (.bound 1) b.weaken.weaken.weaken.weaken)) ↔
      ∃heights parents, Codes M code heights parents ∧ SequenceBound M (C.eval e) (I.eval e).width heights (b.eval e) := by
    apply CopiedMountain.withCodeFormula_iff_exists he (e.push code) (.bound 0) _ _
    intro container heights parents
    simpa only [ExpressionData.eval,ExpressionData.weaken,ExpressionData.map,Input.eval,Input.map,Term.eval_weaken,
      Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using sequenceBoundFormula_iff he ((((e.push code).push container).push heights).push parents)
        C.weaken.weaken.weaken.weaken I.width.weaken.weaken.weaken.weaken (.bound 1) b.weaken.weaken.weaken.weaken
  simp only [layerBoundFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Term.eval_weaken,hBody]
  rfl

structure LayerBounds (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (I : Input M.Domain) (H : M.Domain) : Prop where
  graph : Graph M H I.horizon C.omega
  rows : ∀k b, MemPair M H k b ↔ LayerBound M C I k b

private def layerBoundSchema : Project.Delta0BinarySchema 10 where
  body := layerBoundFormula ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ ⟨.bound 6,.bound 5,.bound 4,.bound 3,.bound 2⟩ (.bound 1) (.bound 0)
  freeClosed := layerBoundFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl⟩ _ _ rfl rfl
  delta0 := layerBoundFormula_delta0 _ _ _ _

private def inputEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (I : Input M.Domain) : Env M 10 :=
  (((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push I.horizon).push I.width).push I.forests).push I.codes).push I.tower

theorem layer_bounds_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {I : Input M.Domain} (hI : I.Valid M C) : ∃H, LayerBounds M C I H := by
  obtain ⟨H,hSupport,hRaw⟩ := relation_comprehension_d hM layerBoundSchema (inputEnv C I) I.horizon C.omega
  have hRows (k b : M.Domain) : MemPair M H k b ↔ LayerBound M C I k b := by
    have hφ : Project.Formula.satisfies (((inputEnv C I).push k).push b) layerBoundSchema.body ↔ LayerBound M C I k b := layerBoundFormula_iff hM.1 _ _ _ _ _
    rw [hRaw k b,hφ]
    exact ⟨fun h => h.2.2,fun h => ⟨(h.bounds hM.1 hI).1,(h.bounds hM.1 hI).2,h⟩⟩
  refine ⟨H,⟨hSupport,?_,?_⟩,hRows⟩
  · intro k hk
    obtain ⟨b,hB⟩ := layer_bound_exists_d hM hC hI hk
    exact ⟨b,(hB.bounds hM.1 hI).2,(hRows k b).mpr hB⟩
  · exact fun k b b' hb hb' => ((hRows k b).mp hb).unique_d hM hC hI ((hRows k b').mp hb')

theorem LayerBounds.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} {I : Input M.Domain} {H H' : M.Domain}
    (h : LayerBounds M C I H) (h' : LayerBounds M C I H') : H=H' := h.graph.ext he h'.graph (fun k _ b => (h.rows k b).trans (h'.rows k b).symm)

theorem RowAtom.row_lt_layer_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {I : Input M.Domain} (hI : I.Valid M C) {k r q p c b : M.Domain}
    (h : RowAtom M C I k r q p c) (hBound : LayerBound M C I k b) : M.mem r b := by
  obtain ⟨code,_,hCode,heights,parents,hDecode,F,hF,hRow,hParent,_⟩ := h
  obtain ⟨code',_,hCode',heights',parents',hDecode',hBound⟩ := hBound
  have he := hI.tower.unique k code code' hCode hCode'
  subst code'
  obtain ⟨hh,hp⟩ := codes_injective hM.1 hDecode hDecode'
  subst heights'
  have hX := (hI.values k code hCode).read hM.1 hDecode
  have hP : CopiedMountain.ParentAt M ⟨I.width,heights,I.forests,parents⟩ r c p := ⟨F,hF,hRow,hParent⟩
  obtain ⟨height,_,hHeight⟩ := hX.heights.total c (hP.bounds hM.1 hX).2.1
  have hrh := (hX.source r c height hHeight).mp ⟨p,hP⟩
  exact ((omega_isOrdinal_d hM hC.omega).mem hBound.1.1).transitive height (hBound.value_lt hM.1 hX.heights hHeight) r hrh

structure Layout (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (I : Input M.Domain) (Bounds rowLimit budget slotCount slotSize : M.Domain) : Prop where
  bounds : LayerBounds M C I Bounds
  rowBound : SequenceBound M C I.horizon Bounds rowLimit
  padding : AddAt M T.addPairs T.plus I.horizon rowLimit budget
  slots : MulAt M T.mulPairs T.times budget I.width slotCount
  size : MulAt M T.mulPairs T.times slotCount budget slotSize

theorem Layout.naturals {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {I : Input M.Domain} {H R B S N : M.Domain} (h : Layout M C T I H R B S N) :
    M.mem R C.omega ∧ M.mem B C.omega ∧ M.mem S C.omega ∧ M.mem N C.omega :=
by
  have hS : M.mem S C.omega := by
    obtain ⟨_,_,_,hAt⟩ := h.slots
    exact (hT.mul.graph.bounds he hAt).2
  have hN : M.mem N C.omega := by
    obtain ⟨_,_,_,hAt⟩ := h.size
    exact (hT.mul.graph.bounds he hAt).2
  exact ⟨h.rowBound.1.1,(h.padding.bounds he hT.add).2.2,hS,hN⟩

theorem layout_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {I : Input M.Domain} (hI : I.Valid M C) : ∃H R B S N, Layout M C T I H R B S N := by
  obtain ⟨H,hH⟩ := layer_bounds_exists_d hM hC hI
  obtain ⟨R,hR⟩ := sequence_bound_exists_d hM hC hI.horizon hH.graph
  obtain ⟨B,hB,hPad⟩ := hT.add.add_exists_d hM hC hI.horizon hR.1.1
  obtain ⟨S,hS,hSlots⟩ := hT.mul.mul_exists_d hM hC hB hI.width
  obtain ⟨N,_,hSize⟩ := hT.mul.mul_exists_d hM hC hS hB
  exact ⟨H,R,B,S,N,hH,hR,hPad,hSlots,hSize⟩

theorem Layout.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {I : Input M.Domain} {H R B S N H' R' B' S' N' : M.Domain} (h : Layout M C T I H R B S N) (h' : Layout M C T I H' R' B' S' N') :
    H=H' ∧ R=R' ∧ B=B' ∧ S=S' ∧ N=N' := by
  have hHH := h.bounds.unique hM.1 h'.bounds
  subst H'
  have hRR := h.rowBound.unique_d hM hC h'.rowBound
  subst R'
  have hBB := hT.add.add_unique hM.1 h.padding h'.padding
  subst B'
  have hSS := hT.mul.mul_unique hM.1 h.slots h'.slots
  subst S'
  exact ⟨rfl,rfl,rfl,rfl,hT.mul.mul_unique hM.1 h.size h'.size⟩

theorem Layout.index_bounds_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {I : Input M.Domain} (hI : I.Valid M C) {H R B S N k r q p c : M.Domain}
    (h : Layout M C T I H R B S N) (hAtom : RowAtom M C I k r q p c) : M.mem k B ∧ M.mem r B := by
  have hAB := hAtom.bounds_d hM hC hI
  have hOrd := omega_isOrdinal_d hM hC.omega
  have hSum := (hT.add.add_iff_sum hM hI.horizon h.rowBound.1.1).mp h.padding
  have hHB := KP1Y.Arithmetic.sum_base_subset_d hM (hOrd.mem hI.horizon) hSum
  have hRB := KP1Y.Arithmetic.sum_base_subset_d hM (hOrd.mem h.rowBound.1.1) (natural_sum_comm_d hM hC hI.horizon h.rowBound.1.1 hSum)
  obtain ⟨b,_,hAt⟩ := h.bounds.graph.total k hAB.1
  have hrb := hAtom.row_lt_layer_bound_d hM hC hI ((h.bounds.rows k b).mp hAt)
  have hbR := h.rowBound.value_lt hM.1 h.bounds.graph hAt
  exact ⟨hHB k hAB.1,hRB r ((hOrd.mem h.rowBound.1.1).transitive b hbR r hrb)⟩

def IndexedAtom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (I : Input M.Domain) (budget slots Pairs i e : M.Domain) : Prop :=
  ∃k, M.mem k I.horizon ∧ ∃c, M.mem c I.width ∧ ∃r, M.mem r budget ∧ ∃q, M.mem q I.width ∧ ∃p, M.mem p I.width ∧
    ExpressionDiagram.Position M C T I.width budget slots i k c r ∧ RowAtom M C I k r q p c ∧ KP1Y.Reflection.Quad M Pairs e k q p c

def indexedAtomFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (I : Input (Project.Term n))
    (budget slots Pairs i e : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem I.horizon (Project.Formula.existsMem I.width.weaken (Project.Formula.existsMem budget.weaken.weaken
    (Project.Formula.existsMem I.width.weaken.weaken.weaken (Project.Formula.existsMem I.width.weaken.weaken.weaken.weaken
      (.conj (ExpressionDiagram.positionFormula C.weaken.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken.weaken
        I.width.weaken.weaken.weaken.weaken.weaken budget.weaken.weaken.weaken.weaken.weaken slots.weaken.weaken.weaken.weaken.weaken
        i.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2))
        (.conj (rowAtomFormula C.weaken.weaken.weaken.weaken.weaken I.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2) (.bound 1) (.bound 0) (.bound 3))
          (KP1Y.Reflection.quadFormula Pairs.weaken.weaken.weaken.weaken.weaken e.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 1) (.bound 0) (.bound 3))))))))

theorem indexedAtomFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (I : Input (Project.Term n))
    (budget slots Pairs i e : Project.Term n) : (indexedAtomFormula C T I budget slots Pairs i e).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (ExpressionDiagram.positionFormula_delta0 _ _ _ _ _ _ _ _ _)
    (.conj (rowAtomFormula_delta0 _ _ _ _ _ _ _) (KP1Y.Reflection.quadFormula_delta0 _ _ _ _ _ _)))))))

theorem indexedAtomFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {I : Input (Project.Term n)} (hI : I.Closed)
    (budget slots Pairs i e : Project.Term n) (hB : budget.freeSupport=[]) (hS : slots.freeSupport=[]) (hPairs : Pairs.freeSupport=[])
    (hi : i.freeSupport=[]) (he : e.freeSupport=[]) : (indexedAtomFormula C T I budget slots Pairs i e).FreeClosed := by
  have hPosition := ExpressionDiagram.positionFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken hT.weaken.weaken.weaken.weaken.weaken
    I.width.weaken.weaken.weaken.weaken.weaken budget.weaken.weaken.weaken.weaken.weaken slots.weaken.weaken.weaken.weaken.weaken
    i.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2)
    (by simpa using hI.width) (by simpa using hB) (by simpa using hS) (by simpa using hi) rfl rfl rfl
  have hAtom := rowAtomFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken hI.weaken.weaken.weaken.weaken.weaken
    (.bound 4) (.bound 2) (.bound 1) (.bound 0) (.bound 3) rfl rfl rfl rfl rfl
  have hQuad := KP1Y.Reflection.quadFormula_freeClosed Pairs.weaken.weaken.weaken.weaken.weaken e.weaken.weaken.weaken.weaken.weaken
    (.bound 4) (.bound 1) (.bound 0) (.bound 3) (by simpa using hPairs) (by simpa using he) rfl rfl rfl rfl
  simp [indexedAtomFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hI.horizon,hI.width,hB,hPosition,hAtom,hQuad]

theorem indexedAtomFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (I : Input (Project.Term n)) (budget slots Pairs i code : Project.Term n) :
    Project.Formula.satisfies e (indexedAtomFormula C T I budget slots Pairs i code) ↔ IndexedAtom M (C.eval e) (T.eval e) (I.eval e)
      (budget.eval e) (slots.eval e) (Pairs.eval e) (i.eval e) (code.eval e) := by
  simp only [indexedAtomFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    ExpressionDiagram.positionFormula_iff he,rowAtomFormula_iff he,KP1Y.Reflection.quadFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Input.eval_weaken,Term.eval_weaken]
  rfl

private theorem quad_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {Pairs e e' k q p c : M.Domain}
    (h : KP1Y.Reflection.Quad M Pairs e k q p c) (h' : KP1Y.Reflection.Quad M Pairs e' k q p c) : e=e' := by
  obtain ⟨u,_,v,_,hE,hU,hV⟩ := h
  obtain ⟨u',_,v',_,hE',hU',hV'⟩ := h'
  have huu := codes_unique he hU hU'
  have hvv := codes_unique he hV hV'
  subst u'
  subst v'
  exact codes_unique he hE hE'

theorem IndexedAtom.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {I : Input M.Domain} (hI : I.Valid M C) {B S Pairs i e e' : M.Domain} (hB : M.mem B C.omega) (hS : M.mem S C.omega)
    (h : IndexedAtom M C T I B S Pairs i e) (h' : IndexedAtom M C T I B S Pairs i e') : e=e' := by
  obtain ⟨k,_,c,_,r,_,q,_,p,_,hPos,hAtom,hQuad⟩ := h
  obtain ⟨k',_,c',_,r',_,q',_,p',_,hPos',hAtom',hQuad'⟩ := h'
  obtain ⟨hkk,hcc,hrr⟩ := hPos.injective_d hM hC hT hI.width hB hS hPos'
  subst k'
  subst c'
  subst r'
  obtain ⟨hqq,hpp⟩ := hAtom.unique_d hM hC hI hAtom'
  subst q'
  subst p'
  exact quad_unique hM.1 hQuad hQuad'

structure AtomMap (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (I : Input M.Domain) (B S N Pairs Codes Map : M.Domain) : Prop where
  graph : Filter.PartialGraph M Map N Codes
  rows : ∀i e, MemPair M Map i e ↔ M.mem i N ∧ M.mem e Codes ∧ IndexedAtom M C T I B S Pairs i e

private def atomSchema : Project.Delta0BinarySchema 19 where
  body := indexedAtomFormula ⟨.bound 20,.bound 19,.bound 18,.bound 17,.bound 16⟩ ⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩
    ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := indexedAtomFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := indexedAtomFormula_delta0 _ _ _ _ _ _ _ _

private def atomEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (I : Input M.Domain) (B S Pairs : M.Domain) : Env M 19 :=
  ((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push I.horizon).push I.width).push I.forests).push I.codes).push I.tower).push B).push S).push Pairs

theorem atom_map_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {I : Input M.Domain} (hI : I.Valid M C) {B S N Pairs Codes : M.Domain} (hB : M.mem B C.omega) (hS : M.mem S C.omega) :
    ∃Map, AtomMap M C T I B S N Pairs Codes Map := by
  obtain ⟨Map,hSupport,hRaw⟩ := relation_comprehension_d hM atomSchema (atomEnv C T I B S Pairs) N Codes
  have hRows (i e : M.Domain) : MemPair M Map i e ↔ M.mem i N ∧ M.mem e Codes ∧ IndexedAtom M C T I B S Pairs i e := by
    have hφ : Project.Formula.satisfies (((atomEnv C T I B S Pairs).push i).push e) atomSchema.body ↔ IndexedAtom M C T I B S Pairs i e := indexedAtomFormula_iff hM.1 _ _ _ _ _ _ _ _ _
    rw [hRaw i e,hφ]
  exact ⟨Map,⟨hSupport,fun i e e' hAt hAt' => ((hRows i e).mp hAt).2.2.unique_d hM hC hT hI hB hS ((hRows i e').mp hAt').2.2⟩,hRows⟩

theorem AtomMap.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {I : Input M.Domain} {B S N Pairs Codes Map Map' : M.Domain} (h : AtomMap M C T I B S N Pairs Codes Map) (h' : AtomMap M C T I B S N Pairs Codes Map') : Map=Map' :=
  relation_ext he h.graph.support h'.graph.support (fun i e => (h.rows i e).trans (h'.rows i e).symm)

def Enumerated (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : KP1Y.Reflection.Data M.Domain) (I : Input M.Domain) (A : M.Domain) : Prop :=
  ∃H R B S N Map len Indices, Layout M C T I H R B S N ∧ AtomMap M C T I B S N D.pairs D.edgeCodes Map ∧
    Filter.Filtered M C.omega Map N D.edgeCodes len A Indices

theorem enumerated_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    (D : KP1Y.Reflection.Data M.Domain) {I : Input M.Domain} (hI : I.Valid M C) : ∃A, Enumerated M C T D I A := by
  obtain ⟨H,R,B,S,N,hLayout⟩ := layout_exists_d hM hC hT hI
  have hNat := hLayout.naturals hM.1 hT
  obtain ⟨Map,hMap⟩ := atom_map_exists_d (N := N) (Pairs := D.pairs) (Codes := D.edgeCodes) hM hC hT hI hNat.2.1 hNat.2.2.1
  obtain ⟨len,A,Indices,hFilter⟩ := Filter.filtered_exists_d hM hC hNat.2.2.2 hMap.graph
  exact ⟨A,H,R,B,S,N,Map,len,Indices,hLayout,hMap,hFilter⟩

theorem Enumerated.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} {I : Input M.Domain} {A A' : M.Domain}
    (h : Enumerated M C T D I A) (h' : Enumerated M C T D I A') : A=A' := by
  obtain ⟨H,R,B,S,N,Map,len,Indices,hLayout,hMap,hFilter⟩ := h
  obtain ⟨H',R',B',S',N',Map',len',Indices',hLayout',hMap',hFilter'⟩ := h'
  obtain ⟨hHH,hRR,hBB,hSS,hNN⟩ := hLayout.unique_d hM hC hT hLayout'
  subst H'
  subst R'
  subst B'
  subst S'
  subst N'
  have hMM := hMap.unique hM.1 hMap'
  subst Map'
  exact (hFilter.unique_d hM hC (hLayout.naturals hM.1 hT).2.2.2 hMap.graph hFilter').2.1

theorem RowAtom.indexed_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega) {I : Input M.Domain} (hI : I.Valid M C)
    {H R B S N k r q p c : M.Domain} (hLayout : Layout M C T I H R B S N) (hAtom : RowAtom M C I k r q p c) :
    ∃i e, M.mem i N ∧ M.mem e D.edgeCodes ∧ ExpressionDiagram.Position M C T I.width B S i k c r ∧
      KP1Y.Reflection.Quad M D.pairs e k q p c ∧ IndexedAtom M C T I B S D.pairs i e := by
  have hBound := hAtom.bounds_d hM hC hI
  have hNat := hLayout.naturals hM.1 hT
  have hIndices := hLayout.index_bounds_d hM hC hT hI hAtom
  have hS := (hT.mul.mul_iff_product hM hNat.2.1 hI.width).mp hLayout.slots
  have hN := (hT.mul.mul_iff_product hM hNat.2.2.1 hNat.2.1).mp hLayout.size
  obtain ⟨i,hi,hPos⟩ := ExpressionDiagram.position_exists_d hM hC hT hI.width hNat.2.1 hS hN hIndices.1 hBound.2.2.1 hIndices.2
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨e,he,hQuad⟩ := KP1Y.Reflection.quad_code_exists_d hM hD
    (hOmega.symm ▸ hw.transitive I.horizon hI.horizon k hBound.1)
    (hOmega.symm ▸ hw.transitive I.width hI.width q hBound.2.2.2.2.1)
    (hOmega.symm ▸ hw.transitive I.width hI.width p hBound.2.2.2.1)
    (hOmega.symm ▸ hw.transitive I.width hI.width c hBound.2.2.1)
  exact ⟨i,e,hi,he,hPos,hQuad,k,hBound.1,c,hBound.2.2.1,r,hIndices.2,q,hBound.2.2.2.2.1,p,hBound.2.2.2.1,hPos,hAtom,hQuad⟩

theorem filtered_edges_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega) {I : Input M.Domain} (hI : I.Valid M C)
    {H R B S N Map len A Indices k q p c : M.Domain} (hLayout : Layout M C T I H R B S N)
    (hMap : AtomMap M C T I B S N D.pairs D.edgeCodes Map) (hFilter : Filter.Filtered M C.omega Map N D.edgeCodes len A Indices) :
    KP1Y.Reflection.EdgeAt M D A k q p c ↔ Atom M C I k q p c := by
  constructor
  · rintro ⟨j,_,e,_,hAt,hQuad⟩
    obtain ⟨i,_,hMapAt⟩ := (hFilter.range_iff hM.1 hMap.graph).mp ⟨j,(hFilter.output.bounds hM.1 hAt).1,hAt⟩
    obtain ⟨_,_,k',hk,c',_,r,_,q',_,p',_,_,hAtom,hQuad'⟩ := (hMap.rows i e).mp hMapAt
    obtain ⟨hkk,hqq,hpp,hcc⟩ := hQuad.injective hM.1 hQuad'
    subst k'
    subst q'
    subst p'
    subst c'
    exact ⟨hk,r,(hAtom.bounds_d hM hC hI).2.1,hAtom⟩
  · rintro ⟨_,r,_,hAtom⟩
    obtain ⟨i,e,hi,he,_,hQuad,hIndexed⟩ := hAtom.indexed_exists_d hM hC hT hD hOmega hI hLayout
    have hMapAt := (hMap.rows i e).mpr ⟨hi,he,hIndexed⟩
    obtain ⟨j,hj,hAt⟩ := (hFilter.range_iff hM.1 hMap.graph).mpr ⟨i,hi,hMapAt⟩
    exact ⟨j,hOmega.symm ▸ (omega_isOrdinal_d hM hC.omega).transitive len hFilter.length j hj,e,he,hAt,hQuad⟩

theorem Enumerated.edges_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega) {I : Input M.Domain} (hI : I.Valid M C)
    {A k q p c : M.Domain} (h : Enumerated M C T D I A) : KP1Y.Reflection.EdgeAt M D A k q p c ↔ Atom M C I k q p c := by
  obtain ⟨_,_,_,_,_,_,_,_,hLayout,hMap,hFilter⟩ := h
  exact filtered_edges_iff_d hM hC hT hD hOmega hI hLayout hMap hFilter

theorem Enumerated.diagram_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega) {I : Input M.Domain} (hI : I.Valid M C)
    {A : M.Domain} (h : Enumerated M C T D I A) : KP1Y.Reflection.Diagram M D I.width A := by
  have hEdges := fun k q p c => h.edges_iff_d hM hC hT hD hOmega hI (k := k) (q := q) (p := p) (c := c)
  obtain ⟨_,_,_,_,_,_,len,_,_,_,hFilter⟩ := h
  refine ⟨hOmega.symm ▸ hI.width,(hD.edgeLists A).mpr ⟨len,hOmega.symm ▸ hFilter.length,hFilter.output⟩,?_⟩
  intro k _ q _ p _ c _ hEdge
  obtain ⟨_,r,_,hAtom⟩ := (hEdges k q p c).mp hEdge
  have hb := hAtom.bounds_d hM hC hI
  exact ⟨hb.2.2.2.2.2.2,hb.2.2.2.2.2.1,hb.2.2.1⟩

abbrev Occurrence (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : KP1Y.Reflection.Data M.Domain) (I : Input M.Domain) (B S len A Indices k r q p c : M.Domain) : Prop :=
  ExpressionDiagram.FilteredRowOccurrence M C T D I.width B S len A Indices k r q p c

theorem occurrence_iff_row_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega) {I : Input M.Domain} (hI : I.Valid M C)
    {H R B S N Map len A Indices k r q p c : M.Domain} (hLayout : Layout M C T I H R B S N)
    (hMap : AtomMap M C T I B S N D.pairs D.edgeCodes Map) (hFilter : Filter.Filtered M C.omega Map N D.edgeCodes len A Indices) :
    Occurrence M C T D I B S len A Indices k r q p c ↔ RowAtom M C I k r q p c := by
  constructor
  · rintro ⟨i,j,e,hPos,hj,hIndex,hAt,hQuad⟩
    have hMapAt := (hFilter.entry_iff hM.1 hMap.graph).mpr ⟨j,hj,hIndex,hAt⟩
    obtain ⟨_,_,k',_,c',_,r',_,q',_,p',_,hPos',hAtom,hQuad'⟩ := (hMap.rows i e).mp hMapAt
    have hNat := hLayout.naturals hM.1 hT
    obtain ⟨hkk,hcc,hrr⟩ := hPos.injective_d hM hC hT hI.width hNat.2.1 hNat.2.2.1 hPos'
    subst k'
    subst c'
    subst r'
    obtain ⟨_,hqq,hpp,_⟩ := hQuad.injective hM.1 hQuad'
    subst q'
    subst p'
    exact hAtom
  · intro hAtom
    obtain ⟨i,e,hi,he,hPos,hQuad,hIndexed⟩ := hAtom.indexed_exists_d hM hC hT hD hOmega hI hLayout
    obtain ⟨j,hj,hIndex,hAt⟩ := (hFilter.entry_iff hM.1 hMap.graph).mp ((hMap.rows i e).mpr ⟨hi,he,hIndexed⟩)
    exact ⟨i,j,e,hPos,hj,hIndex,hAt,hQuad⟩

theorem occurrence_index_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {I : Input M.Domain} {B S N Map Codes len A Indices i i' j j' k c r : M.Domain}
    (hFilter : Filter.Filtered M C.omega Map N Codes len A Indices)
    (hPos : ExpressionDiagram.Position M C T I.width B S i k c r) (hPos' : ExpressionDiagram.Position M C T I.width B S i' k c r)
    (hIndex : MemPair M Indices j i) (hIndex' : MemPair M Indices j' i') : j=j' :=
  ExpressionDiagram.filtered_occurrence_index_unique_d hM hC hT hFilter hPos hPos' hIndex hIndex'

theorem occurrence_distinct_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {I : Input M.Domain} (hI : I.Valid M C) {H R B S N Map Codes len A Indices i i' j j' k c r r' : M.Domain}
    (hLayout : Layout M C T I H R B S N) (hFilter : Filter.Filtered M C.omega Map N Codes len A Indices)
    (hPos : ExpressionDiagram.Position M C T I.width B S i k c r) (hPos' : ExpressionDiagram.Position M C T I.width B S i' k c r')
    (hIndex : MemPair M Indices j i) (hIndex' : MemPair M Indices j' i') (hDifferent : r≠r') : j≠j' :=
  ExpressionDiagram.filtered_occurrence_distinct_rows_d hM hC hT hI.width (hLayout.naturals hM.1 hT).2.1 (hLayout.naturals hM.1 hT).2.2.1
    hFilter hPos hPos' hIndex hIndex' hDifferent

theorem Enumerated.empty_width_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {D : KP1Y.Reflection.Data M.Domain} {I : Input M.Domain}
    {A : M.Domain} (h : Enumerated M C T D I A) (hEmpty : I.width=C.zero) : A=C.zero := by
  obtain ⟨_,_,_,_,_,Map,_,_,_,hMap,hFilter⟩ := h
  exact (hFilter.empty_d hM hC (fun i e hAt => by
    obtain ⟨_,_,_,_,c,hc,_⟩ := (hMap.rows i e).mp hAt
    exact hC.zero_empty c (hEmpty ▸ hc))).2.1

theorem Enumerated.empty_horizon_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {D : KP1Y.Reflection.Data M.Domain} {I : Input M.Domain}
    {A : M.Domain} (h : Enumerated M C T D I A) (hEmpty : I.horizon=C.zero) : A=C.zero := by
  obtain ⟨_,_,_,_,_,Map,_,_,_,hMap,hFilter⟩ := h
  exact (hFilter.empty_d hM hC (fun i e hAt => by
    obtain ⟨_,_,k,hk,_⟩ := (hMap.rows i e).mp hAt
    exact hC.zero_empty k (hEmpty ▸ hk))).2.1

theorem tower_input_valid {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {H K level B n Forests Codes G : M.Domain}
    (h : CopyTower.Tower M C T A m L H K level B n Forests Codes G) : (⟨B,n,Forests,Codes,G⟩ : Input M.Domain).Valid M C :=
  ⟨h.bound,h.width,h.graph,fun _ _ hAt => h.code_valid hAt⟩

theorem tower_diagram_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {H K level B n Forests Codes G : M.Domain}
    (hTower : CopyTower.Tower M C T A m L H K level B n Forests Codes G) :
    ∃edges, Enumerated M C T D ⟨B,n,Forests,Codes,G⟩ edges ∧ KP1Y.Reflection.Diagram M D n edges ∧
      ∀k q p c, KP1Y.Reflection.EdgeAt M D edges k q p c ↔ M.mem k B ∧ ∃r, M.mem r C.omega ∧ RowAtom M C ⟨B,n,Forests,Codes,G⟩ k r q p c := by
  have hI := tower_input_valid hTower
  obtain ⟨edges,hEdges⟩ := enumerated_exists_d hM hC hT D hI
  exact ⟨edges,hEdges,hEdges.diagram_d hM hC hT hD hOmega hI,fun k q p c => hEdges.edges_iff_d hM hC hT hD hOmega hI (k := k) (q := q) (p := p) (c := c)⟩

def inputFormula {n : Nat} (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) : Project.Formula 1 n :=
  .conj (.mem I.horizon C.omega) (.conj (.mem I.width C.omega) (.conj (graphFormula I.tower I.horizon I.codes)
    (Project.Formula.forallMem I.horizon (Project.Formula.forallMem I.codes.weaken (.imp (memPairFormula I.tower.weaken.weaken (.bound 1) (.bound 0))
      (CopiedMountain.codeValidFormula C.weaken.weaken I.width.weaken.weaken I.forests.weaken.weaken (.bound 0)))))))

theorem inputFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) : (inputFormula C I).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.imp (memPairFormula_delta0 _ _ _) (CopiedMountain.codeValidFormula_delta0 _ _ _ _))))))

theorem inputFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed) {I : Input (Project.Term n)} (hI : I.Closed) :
    (inputFormula C I).FreeClosed := by
  have hCode := CopiedMountain.codeValidFormula_freeClosed hC.weaken.weaken I.width.weaken.weaken I.forests.weaken.weaken (.bound 0)
    (by simpa using hI.width) (by simpa using hI.forests) rfl
  simp [inputFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hI.horizon,hI.width,hI.tower,hI.codes,hC.omega,hCode]

theorem inputFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) (hC : (C.eval e).Valid M) :
    Project.Formula.satisfies e (inputFormula C I) ↔ (I.eval e).Valid M (C.eval e) := by
  have hCode (k code : M.Domain) := CopiedMountain.codeValidFormula_iff hM ((e.push k).push code) C.weaken.weaken
    I.width.weaken.weaken I.forests.weaken.weaken (.bound 0) (by simpa only [ExpressionData.eval_weaken] using hC)
  simp only [inputFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,graphFormula_iff hM.1,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff hM.1,hCode,ExpressionData.eval_weaken,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,fun k code hAt => h.2.2.2 k (h.2.2.1.bounds hM.1 hAt).1 code (h.2.2.1.bounds hM.1 hAt).2 hAt⟩,
    fun h => ⟨h.horizon,h.width,h.tower,fun k _ code _ hAt => h.values k code hAt⟩⟩

def layerBoundsFormula {n : Nat} (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) (H : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula H I.horizon C.omega) (Project.Formula.forallMem I.horizon (Project.Formula.forallMem C.omega.weaken
    (.iff (memPairFormula H.weaken.weaken (.bound 1) (.bound 0)) (layerBoundFormula C.weaken.weaken I.weaken.weaken (.bound 1) (.bound 0)))))

theorem layerBoundsFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) (H : Project.Term n) :
    (layerBoundsFormula C I H).IsDelta0 := .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
      (.iff (memPairFormula_delta0 _ _ _) (layerBoundFormula_delta0 _ _ _ _))))

theorem layerBoundsFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {I : Input (Project.Term n)} (hI : I.Closed) (H : Project.Term n) (hH : H.freeSupport=[]) : (layerBoundsFormula C I H).FreeClosed := by
  have hBound := layerBoundFormula_freeClosed hC.weaken.weaken hI.weaken.weaken (.bound 1) (.bound 0) rfl rfl
  simp [layerBoundsFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hI.horizon,hC.omega,hH,hBound]

theorem layerBoundsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) (H : Project.Term n) (hI : (I.eval e).Valid M (C.eval e)) :
    Project.Formula.satisfies e (layerBoundsFormula C I H) ↔ LayerBounds M (C.eval e) (I.eval e) (H.eval e) := by
  simp only [layerBoundsFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff he,layerBoundFormula_iff he,ExpressionData.eval_weaken,Input.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨hG,hRows⟩
    exact ⟨hG,fun k b => ⟨fun hAt => (hRows k (hG.bounds he hAt).1 b (hG.bounds he hAt).2).mp hAt,
      fun hBound => (hRows k (hBound.bounds he hI).1 b (hBound.bounds he hI).2).mpr hBound⟩⟩
  · exact fun h => ⟨h.graph,fun k _ b _ => h.rows k b⟩

def layoutFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (I : Input (Project.Term n))
    (H R B S N : Project.Term n) : Project.Formula 1 n :=
  .conj (layerBoundsFormula C I H) (.conj (sequenceBoundFormula C.omega C.zero I.horizon H R)
    (.conj (addAtFormula T.addPairs T.plus I.horizon R B) (.conj (mulAtFormula T.mulPairs T.times B I.width S) (mulAtFormula T.mulPairs T.times S B N))))

theorem layoutFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (I : Input (Project.Term n))
    (H R B S N : Project.Term n) : (layoutFormula C T I H R B S N).IsDelta0 :=
  .conj (layerBoundsFormula_delta0 _ _ _) (.conj (sequenceBoundFormula_delta0 _ _ _ _ _)
    (.conj (addAtFormula_delta0 _ _ _ _ _) (.conj (mulAtFormula_delta0 _ _ _ _ _) (mulAtFormula_delta0 _ _ _ _ _))))

theorem layoutFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {I : Input (Project.Term n)} (hI : I.Closed)
    (H R B S N : Project.Term n) (hH : H.freeSupport=[]) (hR : R.freeSupport=[]) (hB : B.freeSupport=[]) (hS : S.freeSupport=[]) (hN : N.freeSupport=[]) :
    (layoutFormula C T I H R B S N).FreeClosed := by
  have hBounds := layerBoundsFormula_freeClosed hC hI H hH
  have hRows := sequenceBoundFormula_freeClosed C.omega C.zero I.horizon H R hC.omega hC.zero hI.horizon hH hR
  simp [layoutFormula,addAtFormula,mulAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hT.addPairs,hT.plus,hT.mulPairs,hT.times,hI.horizon,hI.width,hR,hB,hS,hN,hBounds,hRows]

theorem layoutFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (I : Input (Project.Term n)) (H R B S N : Project.Term n)
    (hI : (I.eval e).Valid M (C.eval e)) : Project.Formula.satisfies e (layoutFormula C T I H R B S N) ↔
      Layout M (C.eval e) (T.eval e) (I.eval e) (H.eval e) (R.eval e) (B.eval e) (S.eval e) (N.eval e) := by
  simp only [layoutFormula,Project.Formula.satisfies_conj_iff,layerBoundsFormula_iff he e C I H hI,sequenceBoundFormula_iff he e C,
    addAtFormula_iff he,mulAtFormula_iff he]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,fun h => ⟨h.bounds,h.rowBound,h.padding,h.slots,h.size⟩⟩

def atomMapFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (I : Input (Project.Term n))
    (B S N Pairs Codes Map : Project.Term n) : Project.Formula 1 n :=
  .conj (Filter.partialGraphFormula Map N Codes) (Project.Formula.forallMem N (Project.Formula.forallMem Codes.weaken
    (.iff (memPairFormula Map.weaken.weaken (.bound 1) (.bound 0)) (indexedAtomFormula C.weaken.weaken T.weaken.weaken I.weaken.weaken
      B.weaken.weaken S.weaken.weaken Pairs.weaken.weaken (.bound 1) (.bound 0)))))

theorem atomMapFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (I : Input (Project.Term n))
    (B S N Pairs Codes Map : Project.Term n) : (atomMapFormula C T I B S N Pairs Codes Map).IsDelta0 :=
  .conj (Filter.partialGraphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _) (indexedAtomFormula_delta0 _ _ _ _ _ _ _ _))))

theorem atomMapFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {I : Input (Project.Term n)} (hI : I.Closed)
    (B S N Pairs Codes Map : Project.Term n) (hB : B.freeSupport=[]) (hS : S.freeSupport=[]) (hN : N.freeSupport=[])
    (hPairs : Pairs.freeSupport=[]) (hCodes : Codes.freeSupport=[]) (hMap : Map.freeSupport=[]) : (atomMapFormula C T I B S N Pairs Codes Map).FreeClosed := by
  have hPartial := Filter.partialGraphFormula_freeClosed Map N Codes hMap hN hCodes
  have hIndexed := indexedAtomFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hI.weaken.weaken B.weaken.weaken S.weaken.weaken Pairs.weaken.weaken (.bound 1) (.bound 0)
    (by simpa using hB) (by simpa using hS) (by simpa using hPairs) rfl rfl
  simp [atomMapFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hMap,hN,hCodes,hPartial,hIndexed]

theorem atomMapFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (I : Input (Project.Term n)) (B S N Pairs Codes Map : Project.Term n) :
    Project.Formula.satisfies e (atomMapFormula C T I B S N Pairs Codes Map) ↔
      AtomMap M (C.eval e) (T.eval e) (I.eval e) (B.eval e) (S.eval e) (N.eval e) (Pairs.eval e) (Codes.eval e) (Map.eval e) := by
  simp only [atomMapFormula,Project.Formula.satisfies_conj_iff,Filter.partialGraphFormula_iff he,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff he,indexedAtomFormula_iff he,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Input.eval_weaken,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,fun i code => ⟨fun hAt => ⟨(h.1.bounds he hAt).1,(h.1.bounds he hAt).2,
    (h.2 i (h.1.bounds he hAt).1 code (h.1.bounds he hAt).2).mp hAt⟩,fun hAt => (h.2 i hAt.1 code hAt.2.1).mpr hAt.2.2⟩⟩,
    fun h => ⟨h.graph,fun i hi code hc => (h.rows i code).trans ⟨fun hAt => hAt.2.2,fun hAt => ⟨hi,hc,hAt⟩⟩⟩⟩

def InputCode (M : SetTheory.Structure.{u}) (code : M.Domain) (I : Input M.Domain) : Prop :=
  ∃dims tail, Codes M code dims tail ∧ Codes M dims I.horizon I.width ∧ ∃rest, Codes M tail I.forests rest ∧ Codes M rest I.codes I.tower

theorem input_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (I : Input M.Domain) : ∃code, InputCode M code I := by
  obtain ⟨dims,hDims⟩ := codes_total hM I.horizon I.width
  obtain ⟨rest,hRest⟩ := codes_total hM I.codes I.tower
  obtain ⟨tail,hTail⟩ := codes_total hM I.forests rest
  obtain ⟨code,hCode⟩ := codes_total hM dims tail
  exact ⟨code,dims,tail,hCode,hDims,rest,hTail,hRest⟩

theorem InputCode.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {code : M.Domain} {I J : Input M.Domain}
    (h : InputCode M code I) (h' : InputCode M code J) : I=J := by
  obtain ⟨dims,tail,hCode,hDims,rest,hTail,hRest⟩ := h
  obtain ⟨dims',tail',hCode',hDims',rest',hTail',hRest'⟩ := h'
  obtain ⟨hd,ht⟩ := codes_injective he hCode hCode'
  subst dims'
  subst tail'
  obtain ⟨hh,hw⟩ := codes_injective he hDims hDims'
  obtain ⟨hf,hr⟩ := codes_injective he hTail hTail'
  subst rest'
  obtain ⟨hc,hg⟩ := codes_injective he hRest hRest'
  cases I
  cases J
  simp_all

def inputCodeFormula {n : Nat} (code : Project.Term n) (I : Input (Project.Term n)) : Project.Formula 1 n :=
  CopiedMountain.withCodeFormula code (.conj (codeFormula (.bound 1) I.horizon.weaken.weaken.weaken I.width.weaken.weaken.weaken)
    (CopiedMountain.withCodeFormula (.bound 0) (.conj (Project.Formula.extensionalEq (.bound 1) I.forests.weaken.weaken.weaken.weaken.weaken.weaken)
      (codeFormula (.bound 0) I.codes.weaken.weaken.weaken.weaken.weaken.weaken I.tower.weaken.weaken.weaken.weaken.weaken.weaken))))

theorem inputCodeFormula_delta0 {n : Nat} (code : Project.Term n) (I : Input (Project.Term n)) : (inputCodeFormula code I).IsDelta0 :=
  CopiedMountain.withCodeFormula_delta0 _ (.conj (codeFormula_delta0 _ _ _) (CopiedMountain.withCodeFormula_delta0 _ (.conj (.atom _ _ _) (codeFormula_delta0 _ _ _))))

theorem inputCodeFormula_freeClosed {n : Nat} {I : Input (Project.Term n)} (hI : I.Closed) (code : Project.Term n) (hc : code.freeSupport=[]) :
    (inputCodeFormula code I).FreeClosed := by
  simp [inputCodeFormula,CopiedMountain.withCodeFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hI.horizon,hI.width,hI.forests,hI.codes,hI.tower,hc]

theorem inputCodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (code : Project.Term n) (I : Input (Project.Term n)) : Project.Formula.satisfies e (inputCodeFormula code I) ↔ InputCode M (code.eval e) (I.eval e) := by
  have hTail (container dims tail : M.Domain) : Project.Formula.satisfies (((e.push container).push dims).push tail)
      (CopiedMountain.withCodeFormula (.bound 0) (.conj (Project.Formula.extensionalEq (.bound 1) I.forests.weaken.weaken.weaken.weaken.weaken.weaken)
        (codeFormula (.bound 0) I.codes.weaken.weaken.weaken.weaken.weaken.weaken I.tower.weaken.weaken.weaken.weaken.weaken.weaken))) ↔
      ∃rest, Codes M tail (I.eval e).forests rest ∧ Codes M rest (I.eval e).codes (I.eval e).tower := by
    have hRaw := CopiedMountain.withCodeFormula_iff_exists he (((e.push container).push dims).push tail) (.bound 0)
      (.conj (Project.Formula.extensionalEq (.bound 1) I.forests.weaken.weaken.weaken.weaken.weaken.weaken)
        (codeFormula (.bound 0) I.codes.weaken.weaken.weaken.weaken.weaken.weaken I.tower.weaken.weaken.weaken.weaken.weaken.weaken))
      (fun forests rest => forests=(I.eval e).forests ∧ Codes M rest (I.eval e).codes (I.eval e).tower) (by
        intro box forests rest
        simp only [Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,codeFormula_iff he,Term.eval_weaken]
        rfl)
    exact hRaw.trans ⟨fun ⟨forests,rest,hCode,hEq,hRest⟩ => ⟨rest,hEq ▸ hCode,hRest⟩,
      fun ⟨rest,hCode,hRest⟩ => ⟨(I.eval e).forests,rest,hCode,rfl,hRest⟩⟩
  apply CopiedMountain.withCodeFormula_iff_exists he e code _
    (fun dims tail => Codes M dims (I.eval e).horizon (I.eval e).width ∧ ∃rest, Codes M tail (I.eval e).forests rest ∧ Codes M rest (I.eval e).codes (I.eval e).tower)
  intro container dims tail
  simp only [Project.Formula.satisfies_conj_iff,codeFormula_iff he,Term.eval_weaken,hTail]
  rfl

def Calculation (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (Pairs Codes input A : M.Domain) (I : Input M.Domain) (H R B S N Map len Indices : M.Domain) : Prop :=
  InputCode M input I ∧ I.Valid M C ∧ Layout M C T I H R B S N ∧ AtomMap M C T I B S N Pairs Codes Map ∧ Filter.Filtered M C.omega Map N Codes len A Indices

def calculationFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (Pairs Codes input A : Project.Term n) (I : Input (Project.Term n)) (H R B S N Map len Indices : Project.Term n) : Project.Formula 1 n :=
  .conj (inputCodeFormula input I) (.conj (inputFormula C I) (.conj (layoutFormula C T I H R B S N)
    (.conj (atomMapFormula C T I B S N Pairs Codes Map) (Filter.filteredFormula C.omega Map N Codes len A Indices))))

theorem calculationFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (Pairs Codes input A : Project.Term n) (I : Input (Project.Term n)) (H R B S N Map len Indices : Project.Term n) :
    (calculationFormula C T Pairs Codes input A I H R B S N Map len Indices).IsDelta0 :=
  .conj (inputCodeFormula_delta0 _ _) (.conj (inputFormula_delta0 _ _) (.conj (layoutFormula_delta0 _ _ _ _ _ _ _ _)
    (.conj (atomMapFormula_delta0 _ _ _ _ _ _ _ _ _) (Filter.filteredFormula_delta0 _ _ _ _ _ _ _))))

theorem calculationFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {I : Input (Project.Term n)} (hI : I.Closed)
    (Pairs Codes input A H R B S N Map len Indices : Project.Term n)
    (hp : Pairs.freeSupport=[]) (hc : Codes.freeSupport=[]) (hi : input.freeSupport=[]) (ha : A.freeSupport=[]) (hh : H.freeSupport=[])
    (hr : R.freeSupport=[]) (hb : B.freeSupport=[]) (hs : S.freeSupport=[]) (hn : N.freeSupport=[]) (hm : Map.freeSupport=[])
    (hl : len.freeSupport=[]) (hx : Indices.freeSupport=[]) : (calculationFormula C T Pairs Codes input A I H R B S N Map len Indices).FreeClosed := by
  have hCode := inputCodeFormula_freeClosed hI input hi
  have hInput := inputFormula_freeClosed hC hI
  have hLayout := layoutFormula_freeClosed hC hT hI H R B S N hh hr hb hs hn
  have hMap := atomMapFormula_freeClosed hC hT hI B S N Pairs Codes Map hb hs hn hp hc hm
  have hFilter := Filter.filteredFormula_freeClosed C.omega Map N Codes len A Indices hC.omega hm hn hc hl ha hx
  simp [calculationFormula,Definitional.Formula.FreeClosed,hCode,hInput,hLayout,hMap,hFilter]

theorem calculationFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (Pairs Codes input A : Project.Term n)
    (I : Input (Project.Term n)) (H R B S N Map len Indices : Project.Term n) (hC : (C.eval e).Valid M) :
    Project.Formula.satisfies e (calculationFormula C T Pairs Codes input A I H R B S N Map len Indices) ↔
      Calculation M (C.eval e) (T.eval e) (Pairs.eval e) (Codes.eval e) (input.eval e) (A.eval e) (I.eval e)
        (H.eval e) (R.eval e) (B.eval e) (S.eval e) (N.eval e) (Map.eval e) (len.eval e) (Indices.eval e) := by
  simp only [calculationFormula,Project.Formula.satisfies_conj_iff,inputCodeFormula_iff hM.1,inputFormula_iff hM e C I hC,
    atomMapFormula_iff hM.1,Filter.filteredFormula_iff hM.1]
  exact ⟨fun h => ⟨h.1,h.2.1,(layoutFormula_iff hM.1 e C T I H R B S N h.2.1).mp h.2.2.1,h.2.2.2⟩,
    fun h => ⟨h.1,h.2.1,(layoutFormula_iff hM.1 e C T I H R B S N h.2.1).mpr h.2.2.1,h.2.2.2⟩⟩

def Computed (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : KP1Y.Reflection.Data M.Domain) (input A : M.Domain) : Prop := ∃I, InputCode M input I ∧ I.Valid M C ∧ Enumerated M C T D I A

theorem Computed.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} {input A A' : M.Domain} (h : Computed M C T D input A) (h' : Computed M C T D input A') : A=A' := by
  obtain ⟨I,hCode,_,hA⟩ := h
  obtain ⟨I',hCode',_,hA'⟩ := h'
  have he := hCode.unique hM.1 hCode'
  subst I'
  exact hA.unique_d hM hC hT hA'

def Certificate (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (Pairs Codes input A Box : M.Domain) : Prop :=
  ∃horizon, M.mem horizon Box ∧ ∃width, M.mem width Box ∧ ∃forests, M.mem forests Box ∧ ∃codes, M.mem codes Box ∧ ∃tower, M.mem tower Box ∧ ∃H, M.mem H Box ∧ ∃R, M.mem R Box ∧ ∃B, M.mem B Box ∧ ∃S, M.mem S Box ∧ ∃N, M.mem N Box ∧ ∃Map, M.mem Map Box ∧ ∃len, M.mem len Box ∧ ∃Indices, M.mem Indices Box ∧ Calculation M C T Pairs Codes input A ⟨horizon,width,forests,codes,tower⟩ H R B S N Map len Indices

theorem certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : KP1Y.Reflection.Data M.Domain} {input A : M.Domain}
    (h : Computed M C T D input A) : ∃Box, Certificate M C T D.pairs D.edgeCodes input A Box := by
  obtain ⟨I,hCode,hI,H,R,B,S,N,Map,len,Indices,hLayout,hMap,hFilter⟩ := h
  obtain ⟨Box,hBox⟩ := KP1Y.Ranking.finite_list_container_d hM [I.horizon,I.width,I.forests,I.codes,I.tower,H,R,B,S,N,Map,len,Indices]
  exact ⟨Box,I.horizon,hBox _ (by simp),I.width,hBox _ (by simp),I.forests,hBox _ (by simp),I.codes,hBox _ (by simp),I.tower,hBox _ (by simp),H,hBox _ (by simp),R,hBox _ (by simp),B,hBox _ (by simp),S,hBox _ (by simp),N,hBox _ (by simp),Map,hBox _ (by simp),len,hBox _ (by simp),Indices,hBox _ (by simp),hCode,hI,hLayout,hMap,hFilter⟩

theorem certificate_sound {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {D : KP1Y.Reflection.Data M.Domain} {input A Box : M.Domain} (h : Certificate M C T D.pairs D.edgeCodes input A Box) : Computed M C T D input A := by
  obtain ⟨horizon,_,width,_,forests,_,codes,_,tower,_,H,_,R,_,B,_,S,_,N,_,Map,_,len,_,Indices,_,hCode,hI,hLayout,hMap,hFilter⟩ := h
  exact ⟨⟨horizon,width,forests,codes,tower⟩,hCode,hI,H,R,B,S,N,Map,len,Indices,hLayout,hMap,hFilter⟩

private def calculationC : ExpressionData (Project.Term 29) := ⟨.bound 28,.bound 27,.bound 26,.bound 25,.bound 24⟩
private def calculationT : MatrixArithmetic (Project.Term 29) := ⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19,.bound 18⟩
private def calculationI : Input (Project.Term 29) := ⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩

def calculationMatrix : KP1Y.WitnessMatrix 13 where
  body := (Project.Formula.existsMem (.bound 0)
    (Project.Formula.existsMem (.bound 1)
    (Project.Formula.existsMem (.bound 2)
    (Project.Formula.existsMem (.bound 3)
    (Project.Formula.existsMem (.bound 4)
    (Project.Formula.existsMem (.bound 5)
    (Project.Formula.existsMem (.bound 6)
    (Project.Formula.existsMem (.bound 7)
    (Project.Formula.existsMem (.bound 8)
    (Project.Formula.existsMem (.bound 9)
    (Project.Formula.existsMem (.bound 10)
    (Project.Formula.existsMem (.bound 11)
    (Project.Formula.existsMem (.bound 12)
    (calculationFormula calculationC calculationT (.bound 17) (.bound 16) (.bound 15) (.bound 14) calculationI (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)))))))))))))))
  freeClosed := by
    have h := calculationFormula_freeClosed (C := calculationC) ⟨rfl,rfl,rfl,rfl,rfl⟩ (T := calculationT) ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (I := calculationI) ⟨rfl,rfl,rfl,rfl,rfl⟩ (.bound 17) (.bound 16) (.bound 15) (.bound 14) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    simpa [Project.Formula.existsMem,Definitional.Formula.FreeClosed] using h
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (calculationFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))))))))))))

private def calculationEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (Pairs Codes : M.Domain) : Env M 13 :=
  ((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push Pairs).push Codes

theorem calculationMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) (T : MatrixArithmetic M.Domain) (Pairs Codes input A Box : M.Domain) :
    Project.Formula.satisfies ((((calculationEnv C T Pairs Codes).push input).push A).push Box) calculationMatrix.body ↔ Certificate M C T Pairs Codes input A Box := by
  have hCalc (horizon width forests codes tower H R B S N Map len Indices : M.Domain) := calculationFormula_iff hM (((((((((((((((((calculationEnv C T Pairs Codes).push input).push A).push Box).push horizon).push width).push forests).push codes).push tower).push H).push R).push B).push S).push N).push Map).push len).push Indices)
    calculationC calculationT (.bound 17) (.bound 16) (.bound 15) (.bound 14) calculationI (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0) hC
  simp only [calculationMatrix,Project.Formula.satisfies_existsMem_iff,hCalc]
  rfl

theorem computed_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) (T : MatrixArithmetic M.Domain) (D : KP1Y.Reflection.Data M.Domain) (input A : M.Domain) :
    (∃Box, Project.Formula.satisfies ((((calculationEnv C T D.pairs D.edgeCodes).push input).push A).push Box) calculationMatrix.body) ↔ Computed M C T D input A := by
  constructor
  · rintro ⟨Box,hBox⟩
    exact certificate_sound ((calculationMatrix_iff hM hC T D.pairs D.edgeCodes input A Box).mp hBox)
  · intro h
    obtain ⟨Box,hBox⟩ := certificate_exists_d hM h
    exact ⟨Box,(calculationMatrix_iff hM hC T D.pairs D.edgeCodes input A Box).mpr hBox⟩

theorem Computed.at_input_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : KP1Y.Reflection.Data M.Domain} {input A : M.Domain} {I : Input M.Domain}
    (hCode : InputCode M input I) : Computed M C T D input A ↔ I.Valid M C ∧ Enumerated M C T D I A := by
  constructor
  · rintro ⟨J,hCode',hJ,hA⟩
    have hJI := hCode'.unique he hCode
    subst J
    exact ⟨hJ,hA⟩
  · exact fun h => ⟨I,hCode,h.1,h.2⟩

structure FunctionGraph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : KP1Y.Reflection.Data M.Domain) (Inputs F : M.Domain) : Prop where
  graph : Graph M F Inputs D.edgeLists
  rows : ∀input A, MemPair M F input A ↔ M.mem input Inputs ∧ Computed M C T D input A

/-- 给定实际输入代码集合上的唯一图值函数；不假设全部含ω父家族的输入构成集合。 -/
theorem function_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    (Inputs : M.Domain) (hInputs : ∀input, M.mem input Inputs → ∃I : Input M.Domain, InputCode M input I ∧ I.Valid M C) :
    ∃F, FunctionGraph M C T D Inputs F := by
  let e := calculationEnv C T D.pairs D.edgeCodes
  have hMeaning (input A : M.Domain) : (∃Box, Project.Formula.satisfies (((e.push input).push A).push Box) calculationMatrix.body) ↔ Computed M C T D input A :=
    computed_sigmaOne_iff_d hM hC T D input A
  have hBounds (input A : M.Domain) (h : Computed M C T D input A) : M.mem A D.edgeLists := by
    obtain ⟨I,_,hI,hA⟩ := h
    exact (hA.diagram_d hM hC hT hD hOmega hI).2.1
  obtain ⟨F,hGraph,hRaw⟩ := sigma_function_graph_d hM calculationMatrix e Inputs D.edgeLists
    (fun input hi => by
      obtain ⟨I,hCode,hI⟩ := hInputs input hi
      obtain ⟨A,hA⟩ := enumerated_exists_d hM hC hT D hI
      obtain ⟨Box,hBox⟩ := (hMeaning input A).mpr ⟨I,hCode,hI,hA⟩
      exact ⟨A,Box,hBox⟩)
    (fun input _ A Box hBox => hBounds input A ((hMeaning input A).mp ⟨Box,hBox⟩))
    (fun input _ A A' Box Box' hBox hBox' => ((hMeaning input A).mp ⟨Box,hBox⟩).unique_d hM hC hT ((hMeaning input A').mp ⟨Box',hBox'⟩))
  refine ⟨F,hGraph,fun input A => ?_⟩
  rw [hRaw input A,hMeaning input A]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hBounds input A h.2,h.2⟩⟩

theorem FunctionGraph.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : KP1Y.Reflection.Data M.Domain} {Inputs F G : M.Domain}
    (h : FunctionGraph M C T D Inputs F) (h' : FunctionGraph M C T D Inputs G) : F=G :=
  h.graph.ext he h'.graph (fun input _ A => (h.rows input A).trans (h'.rows input A).symm)

theorem FunctionGraph.at_input_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : KP1Y.Reflection.Data M.Domain} {Inputs F input A : M.Domain} {I : Input M.Domain}
    (h : FunctionGraph M C T D Inputs F) (hCode : InputCode M input I) : MemPair M F input A ↔ M.mem input Inputs ∧ I.Valid M C ∧ Enumerated M C T D I A :=
  (h.rows input A).trans (and_congr Iff.rfl (Computed.at_input_iff he hCode))

theorem FunctionGraph.diagram_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {Inputs F input A : M.Domain} {I : Input M.Domain} (h : FunctionGraph M C T D Inputs F) (hCode : InputCode M input I) (hAt : MemPair M F input A) :
    KP1Y.Reflection.Diagram M D I.width A := by
  obtain ⟨_,hI,hA⟩ := (h.at_input_iff hM.1 hCode).mp hAt
  exact hA.diagram_d hM hC hT hD hOmega hI

theorem FunctionGraph.edges_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {Inputs F input A k q p c : M.Domain} {I : Input M.Domain} (h : FunctionGraph M C T D Inputs F) (hCode : InputCode M input I) (hAt : MemPair M F input A) :
    KP1Y.Reflection.EdgeAt M D A k q p c ↔ M.mem k I.horizon ∧ ∃r, M.mem r C.omega ∧ RowAtom M C I k r q p c := by
  obtain ⟨_,hI,hA⟩ := (h.at_input_iff hM.1 hCode).mp hAt
  exact hA.edges_iff_d hM hC hT hD hOmega hI

theorem Layout.row_lt_uniform_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {I : Input M.Domain} (hI : I.Valid M C)
    {H R B S N k r q p c : M.Domain} (hLayout : Layout M C T I H R B S N) (hAtom : RowAtom M C I k r q p c) : M.mem r R := by
  obtain ⟨b,_,hAt⟩ := hLayout.bounds.graph.total k (hAtom.bounds_d hM hC hI).1
  have hrb := hAtom.row_lt_layer_bound_d hM hC hI ((hLayout.bounds.rows k b).mp hAt)
  exact ((omega_isOrdinal_d hM hC.omega).mem hLayout.rowBound.1.1).transitive b (hLayout.rowBound.value_lt hM.1 hLayout.bounds.graph hAt) r hrb

/-- 所有填充槽在实际部分原子图中无定义，并非仅忽略其证明义务。 -/
theorem padding_no_entry_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {I : Input M.Domain} (hI : I.Valid M C)
    {H R B S N Pairs Codes Map i k c r : M.Domain} (hLayout : Layout M C T I H R B S N) (hMap : AtomMap M C T I B S N Pairs Codes Map)
    (hPos : ExpressionDiagram.Position M C T I.width B S i k c r) (hPadding : ¬M.mem k I.horizon ∨ ¬M.mem r R) : ∀e, ¬MemPair M Map i e := by
  intro e hAt
  obtain ⟨_,_,k',hk,c',_,r',_,q,_,p,_,hPos',hAtom,_⟩ := (hMap.rows i e).mp hAt
  have hNat := hLayout.naturals hM.1 hT
  obtain ⟨hkk,hcc,hrr⟩ := hPos.injective_d hM hC hT hI.width hNat.2.1 hNat.2.2.1 hPos'
  subst k'
  subst c'
  subst r'
  exact hPadding.elim (fun h => h hk) (fun h => h (hLayout.row_lt_uniform_d hM hC hI hAtom))

theorem padding_no_output_index_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {I : Input M.Domain} (hI : I.Valid M C)
    {H R B S N Pairs Codes Map len A Indices i k c r : M.Domain} (hLayout : Layout M C T I H R B S N)
    (hMap : AtomMap M C T I B S N Pairs Codes Map) (hFilter : Filter.Filtered M C.omega Map N Codes len A Indices)
    (hPos : ExpressionDiagram.Position M C T I.width B S i k c r) (hPadding : ¬M.mem k I.horizon ∨ ¬M.mem r R) :
    ¬∃j, M.mem j len ∧ MemPair M Indices j i := by
  rintro ⟨j,hj,hIndex⟩
  obtain ⟨e,_,hAt⟩ := (hFilter.coverage i (hFilter.indices.bounds hM.1 hIndex).2).mpr ⟨j,hj,hIndex⟩
  exact padding_no_entry_d hM hC hT hI hLayout hMap hPos hPadding e hAt

theorem row_atom_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {I : Input M.Domain} (hI : I.Valid M C) {k r p c code heights parents : M.Domain}
    (hAt : MemPair M I.tower k code) (hDecode : Codes M code heights parents) :
    (∃q, RowAtom M C I k r q p c) ↔ CopiedMountain.ParentAt M ⟨I.width,heights,I.forests,parents⟩ r c p := by
  have hX := (hI.values k code hAt).read hM.1 hDecode
  constructor
  · rintro ⟨q,code',_,hAt',heights',parents',hDecode',F,hF,hRow,hParent,_⟩
    have he := hI.tower.unique k code' code hAt' hAt
    subst code'
    obtain ⟨hh,hp⟩ := codes_injective hM.1 hDecode' hDecode
    subst heights'
    subst parents'
    exact ⟨F,hF,hRow,hParent⟩
  · rintro ⟨F,hF,hRow,hParent⟩
    have hForest := hX.forest r F hRow
    obtain ⟨q,hRoot⟩ := root_exists_d hM hC hForest (hForest.bounds hM.1 hParent).1
    exact ⟨q,code,(hI.tower.bounds hM.1 hAt).2,hAt,heights,parents,hDecode,F,hF,hRow,hParent,hRoot⟩

theorem Enumerated.parent_edge_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega) {I : Input M.Domain} (hI : I.Valid M C)
    {A k r p c code heights parents : M.Domain} (h : Enumerated M C T D I A) (hAt : MemPair M I.tower k code) (hDecode : Codes M code heights parents)
    (hParent : CopiedMountain.ParentAt M ⟨I.width,heights,I.forests,parents⟩ r c p) : ∃q, KP1Y.Reflection.EdgeAt M D A k q p c := by
  obtain ⟨q,hAtom⟩ := (row_atom_parent_iff_d hM hC hI hAt hDecode).mpr hParent
  have hb := hAtom.bounds_d hM hC hI
  exact ⟨q,(h.edges_iff_d hM hC hT hD hOmega hI).mpr ⟨hb.1,r,hb.2.1,hAtom⟩⟩

end KP1Y.OneYFinite.CopyDiagram
