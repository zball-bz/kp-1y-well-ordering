import KP1Y.OneYCopyCoordinates
import KP1Y.OneYMatrixExpansionFacts

/-! 普通高层复制的 0-based 源坐标。源区间是 [root,last)，seam 使用后一块的 root。 -/
namespace KP1Y.OneYFinite.OrdinaryCoordinates
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopyCoordinates
universe u

/-- c<root 保留；其余坐标是标准 BMS 块地址，允许局部槽 0。 -/
def Decoded (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (c s b : M.Domain) : Prop :=
  M.mem c C.omega ∧ M.mem s C.omega ∧ M.mem b C.omega ∧
    ((M.mem c A.root ∧ s=c ∧ b=C.zero) ∨ (¬M.mem c A.root ∧ ∃ slot, M.mem slot A.length ∧
      AddAt M T.addPairs T.plus A.root slot s ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times A.root A.length b slot c))

def decodedFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (c s b : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem c C.omega) (.conj (.mem s C.omega) (.conj (.mem b C.omega)
    (.disj (.conj (.mem c A.root) (.conj (Project.Formula.extensionalEq s c) (Project.Formula.extensionalEq b C.zero)))
      (.conj (.neg (.mem c A.root)) (Project.Formula.existsMem A.length
        (.conj (addAtFormula T.addPairs.weaken T.plus.weaken A.root.weaken (.bound 0) s.weaken)
          (copyPositionFormula C.omega.weaken T.addPairs.weaken T.plus.weaken T.mulPairs.weaken T.times.weaken
            A.root.weaken A.length.weaken b.weaken (.bound 0) c.weaken)))))))

theorem decodedFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (c s b : Project.Term n) : (decodedFormula C T A c s b).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.disj (.conj (.mem _ _) (.conj (.atom _ _ _) (.atom _ _ _)))
    (.conj (.neg (.mem _ _)) (.existsMem _ (.conj (addAtFormula_delta0 _ _ _ _ _) (copyPositionFormula_delta0 _ _ _ _ _ _ _ _ _ _)))))))

theorem decodedFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {A : Context (Project.Term n)} (hA : A.Closed)
    (c s b : Project.Term n) (hc : c.freeSupport=[]) (hs : s.freeSupport=[]) (hb : b.freeSupport=[]) :
    (decodedFormula C T A c s b).FreeClosed := by
  simp [decodedFormula,copyPositionFormula,mulAtFormula,addAtFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.zero,
    hT.addPairs,hT.plus,hT.mulPairs,hT.times,hA.root,hA.length,hc,hs,hb]

theorem decodedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : Context (Project.Term n))
    (c s b : Project.Term n) : Project.Formula.satisfies e (decodedFormula C T A c s b) ↔
      Decoded M (C.eval e) (T.eval e) (A.eval e) (c.eval e) (s.eval e) (b.eval e) := by
  simp only [decodedFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,addAtFormula_iff he,copyPositionFormula_iff he,Term.eval_weaken]
  rfl

theorem decoded_good_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {A : Context M.Domain}
    (hA : A.Valid M C) {c : M.Domain} (hc : M.mem c A.root) : Decoded M C T A c c C.zero := by
  have hn := (omega_isOrdinal_d hM hC.omega).transitive A.root hA.root c hc
  exact ⟨hn,hn,hC.zero_nat,Or.inl ⟨hc,rfl,rfl⟩⟩

theorem decoded_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) : Decoded M C T A A.root A.root C.zero := by
  have hAdd := (hT.add.add_iff_sum hM hA.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM A.root hC.zero_empty)
  exact ⟨hA.root,hA.root,hC.zero_nat,Or.inr ⟨SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root,
    C.zero,hA.length_positive_d hM hC,hAdd,(copy_position_zero_iff_d hM hC hT hA.root (hA.length_nat hM.1)).mpr hAdd⟩⟩

theorem raw_nonseam_decoded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b : M.Domain}
    (hc : M.mem c C.omega) (hAfter : M.mem A.root c) (hRaw : RawDecoded M C T A c s b) (hs : M.mem s A.last) :
    Decoded M C T A c s b := by
  obtain ⟨slot,hSlot,_,hAdd,hPos⟩ := raw_decoded_nonseam_bms_d hM hC hT hA hAfter hRaw hs
  have hNot : ¬M.mem c A.root := fun hBack => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c
    (((omega_isOrdinal_d hM hC.omega).mem hc).transitive A.root hAfter c hBack)
  exact ⟨hc,hRaw.1,hRaw.2.1,Or.inr ⟨hNot,slot,hSlot,hAdd,hPos⟩⟩

/-- raw 首 seam 的 block=0，在普通复制中精确变成 source=root、block=1。 -/
theorem raw_seam_decoded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c b : M.Domain}
    (hc : M.mem c C.omega) (hAfter : M.mem A.root c) (hRaw : RawDecoded M C T A c A.last b) :
    ∃ next, M.SuccessorOf next b ∧ Decoded M C T A c A.root next := by
  obtain ⟨next,hNext,hs,hPos⟩ := raw_decoded_seam_bms_d hM hC hT hA hAfter hRaw
  have hNot : ¬M.mem c A.root := fun hBack => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c
    (((omega_isOrdinal_d hM hC.omega).mem hc).transitive A.root hAfter c hBack)
  have hAdd := (hT.add.add_iff_sum hM hA.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM A.root hC.zero_empty)
  exact ⟨next,hs,hc,hA.root,hNext,Or.inr ⟨hNot,C.zero,hA.length_positive_d hM hC,hAdd,hPos⟩⟩

theorem decoded_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c : M.Domain} (hc : M.mem c C.omega) :
    ∃ s b, Decoded M C T A c s b := by
  classical
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare c hc A.root hA.root with he | hBefore | hAfter
  · have heq := hM.1.eq_of_same_members c A.root he
    subst c
    exact ⟨A.root,C.zero,decoded_root_d hM hC hT hA⟩
  · exact ⟨c,C.zero,decoded_good_d hM hC hA hBefore⟩
  · obtain ⟨s,b,hRaw⟩ := raw_decode_exists_d hM hC hT hA hc
    rcases ((raw_decoded_active_iff hAfter).mp hRaw).1.2 with hs | hs
    · subst s
      obtain ⟨next,_,hNext⟩ := raw_seam_decoded_d hM hC hT hA hc hAfter hRaw
      exact ⟨A.root,next,hNext⟩
    · exact ⟨s,b,raw_nonseam_decoded_d hM hC hT hA hc hAfter hRaw hs⟩

theorem Decoded.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b s' b' : M.Domain}
    (h : Decoded M C T A c s b) (h' : Decoded M C T A c s' b') : s=s' ∧ b=b' := by
  rcases h.2.2.2 with ⟨hGood,hs,hb⟩ | ⟨hBad,slot,hSlot,hAdd,hPos⟩ <;>
    rcases h'.2.2.2 with ⟨hGood',hs',hb'⟩ | ⟨hBad',slot',hSlot',hAdd',hPos'⟩
  · exact ⟨hs.trans hs'.symm,hb.trans hb'.symm⟩
  · exact False.elim (hBad' hGood)
  · exact False.elim (hBad hGood')
  · obtain ⟨hbb,hss⟩ := copy_position_injective_d hM hC hT.add hT.mul hA.root (hA.length_nat hM.1) h.2.2.1 h'.2.2.1
      hSlot hSlot' hPos hPos'
    subst slot'
    exact ⟨hT.add.add_unique hM.1 hAdd hAdd',hbb⟩


theorem Decoded.source_lt_last_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b : M.Domain} (h : Decoded M C T A c s b) : M.mem s A.last := by
  have hw := omega_isOrdinal_d hM hC.omega
  rcases h.2.2.2 with ⟨hc,hs,_⟩ | ⟨_,slot,hSlot,hAdd,_⟩
  · exact hs.symm ▸ (hw.mem hA.last).transitive A.root hA.below c hc
  · exact KP1Y.Arithmetic.sum_strict_right_d hM (hw.mem hA.root)
      ((hT.add.add_iff_sum hM hA.root (hw.transitive A.length (hA.length_nat hM.1) slot hSlot)).mp hAdd)
      (hA.root_add_length_d hM hC) hSlot

theorem Decoded.parent_copy_reconstruct_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b : M.Domain} (h : Decoded M C T A c s b) :
    ParentCopy M C T A b s c := by
  rcases h.2.2.2 with ⟨_,hs,hb⟩ | ⟨_,slot,hSlot,hAdd,hPos⟩
  · subst s
    subst b
    exact parent_copy_zero_d hM hC hT hA h.1
  · have hw := omega_isOrdinal_d hM hC.omega
    have hSlotNat := hw.transitive A.length (hA.length_nat hM.1) slot hSlot
    have hSum := (hT.add.add_iff_sum hM hA.root hSlotNat).mp hAdd
    have hNot : ¬M.mem s A.root := fun hs => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s
      (KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hA.root) hSum s hs)
    exact ⟨h.2.1,h.2.2.1,Or.inr ⟨hNot,(encode_at_base_iff_d hM hC hT hA.root hSlotNat h.2.2.1 hAdd).mpr hPos⟩⟩

theorem Decoded.parent_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b p q : M.Domain}
    (h : Decoded M C T A c s b) (hParent : ParentCopy M C T A b p q) (hLeft : M.mem p s) : M.mem q c := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA h.2.2.1
  exact hJ.strict p hParent.1 s h.2.1 hLeft q c ((hRows p q).mpr hParent)
    ((hRows s c).mpr (h.parent_copy_reconstruct_d hM hC hT hA))

theorem decoded_original_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c : M.Domain} (hc : M.mem c A.last) : Decoded M C T A c c C.zero := by
  have hn := (omega_isOrdinal_d hM hC.omega).transitive A.last hA.last c hc
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare c hn A.root hA.root with he | hBefore | hAfter
  · have heq := hM.1.eq_of_same_members c A.root he
    subst c
    exact decoded_root_d hM hC hT hA
  · exact decoded_good_d hM hC hA hBefore
  · exact raw_nonseam_decoded_d hM hC hT hA hn hAfter (raw_original_coordinates_d hM hC hT hA ⟨hAfter,Or.inr hc⟩) hc

theorem Decoded.original_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b : M.Domain} (h : Decoded M C T A c s b) (hc : M.mem c A.last) : s=c ∧ b=C.zero :=
  h.unique_d hM hC hT hA (decoded_original_d hM hC hT hA hc)

private def coordinateEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain) (A : Context M.Domain) : Env M 15 :=
  let e := ((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions
  let e' := (((((e.push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference
  (((e'.push A.last).push A.root).push A.length).push A.first

private def graphSchema : Project.Delta0BinarySchema 15 where
  body := Project.Formula.existsMem (.bound 16) (Project.Formula.existsMem (.bound 17)
    (.conj (decodedFormula ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩
      ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ ⟨.bound 7,.bound 6,.bound 5,.bound 4⟩
      (.bound 3) (.bound 1) (.bound 0)) (codeFormula (.bound 2) (.bound 1) (.bound 0))))
  freeClosed := by
    have hDec := decodedFormula_freeClosed (C := ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩) ⟨rfl,rfl,rfl,rfl,rfl⟩
      (T := ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩) ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (A := ⟨.bound 7,.bound 6,.bound 5,.bound 4⟩) ⟨rfl,rfl,rfl,rfl⟩
      (Project.Term.bound (depth := 19) 3) (.bound 1) (.bound 0) rfl rfl rfl
    simp [Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,codeFormula,pairFormula,hDec]
  delta0 := .existsMem _ (.existsMem _ (.conj (decodedFormula_delta0 _ _ _ _ _ _) (codeFormula_delta0 _ _ _)))

private theorem graphSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (c key : M.Domain) :
    Project.Formula.satisfies (((coordinateEnv C T A).push c).push key) graphSchema.body ↔
      ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧ Decoded M C T A c s b ∧ Codes M key s b := by
  simp only [graphSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    decodedFormula_iff he,codeFormula_iff he]
  rfl

structure CoordinateGraph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (G : M.Domain) : Prop where
  graph : Graph M G C.omega T.addPairs
  rows : ∀ c s b key, Codes M key s b → (MemPair M G c key ↔ Decoded M C T A c s b)

theorem coordinate_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) : ∃ G, CoordinateGraph M C T A G := by
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM graphSchema (coordinateEnv C T A) C.omega T.addPairs
  have hExact (c key : M.Domain) : MemPair M G c key ↔ M.mem c C.omega ∧ M.mem key T.addPairs ∧
      ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧ Decoded M C T A c s b ∧ Codes M key s b := by
    simpa only [graphSchema_iff hM.1] using hRaw c key
  have hRows (c s b key : M.Domain) (hCode : Codes M key s b) : MemPair M G c key ↔ Decoded M C T A c s b := by
    constructor
    · intro hAt
      obtain ⟨_,_,s',_,b',_,hDecode,hCode'⟩ := (hExact c key).mp hAt
      obtain ⟨hss,hbb⟩ := codes_injective hM.1 hCode hCode'
      subst s'
      subst b'
      exact hDecode
    · intro hDecode
      exact (hExact c key).mpr ⟨hDecode.1,(hT.add.pairs key).mpr ⟨s,hDecode.2.1,b,hDecode.2.2.1,hCode⟩,
        s,hDecode.2.1,b,hDecode.2.2.1,hDecode,hCode⟩
  refine ⟨G,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨s,b,hDecode⟩ := decoded_exists_d hM hC hT hA hc
    obtain ⟨key,hCode⟩ := codes_total hM s b
    exact ⟨key,(hT.add.pairs key).mpr ⟨s,hDecode.2.1,b,hDecode.2.2.1,hCode⟩,(hRows c s b key hCode).mpr hDecode⟩
  · intro c key key' hAt hAt'
    obtain ⟨_,_,s,_,b,_,hDecode,hCode⟩ := (hExact c key).mp hAt
    obtain ⟨_,_,s',_,b',_,hDecode',hCode'⟩ := (hExact c key').mp hAt'
    obtain ⟨hss,hbb⟩ := hDecode.unique_d hM hC hT hA hDecode'
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


theorem decoded_encode_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {c s b : M.Domain}
    (hs : M.mem s A.last) (hNot : ¬M.mem s A.root) (hEncode : Encode M C T A s b c) : Decoded M C T A c s b := by
  have hOriginal := decoded_original_d hM hC hT hA hs
  rcases hOriginal.2.2.2 with ⟨hGood,_⟩ | ⟨_,slot,hSlot,hSource,_⟩
  · exact False.elim (hNot hGood)
  · have hw := omega_isOrdinal_d hM hC.omega
    have hSlotNat := hw.transitive A.length (hA.length_nat hM.1) slot hSlot
    have hPos := (encode_at_base_iff_d hM hC hT hA.root hSlotNat hEncode.2.1 hSource).mp hEncode
    obtain ⟨hsNat,hb,off,hOff,_,hAdd⟩ := hEncode
    have hcNat := (hAdd.bounds hM.1 hT.add).2.2
    have hSourceSum := (hT.add.add_iff_sum hM hA.root hSlotNat).mp hSource
    have hTargetSum := (hT.add.add_iff_sum hM hsNat hOff).mp hAdd
    have hcNot : ¬M.mem c A.root := fun hc => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c
      (KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hsNat) hTargetSum c
        (KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hA.root) hSourceSum c hc))
    exact ⟨hcNat,hsNat,hb,Or.inr ⟨hcNot,slot,hSlot,hSource,hPos⟩⟩

theorem decoded_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {p b c : M.Domain}
    (hp : M.mem p A.last) (hCopy : ParentCopy M C T A b p c) :
    ∃ block, Decoded M C T A c p block := by
  rcases hCopy.2.2 with ⟨hGood,hcp⟩ | ⟨hBad,hEncode⟩
  · subst c
    exact ⟨C.zero,decoded_good_d hM hC hA hGood⟩
  · exact ⟨b,decoded_encode_d hM hC hT hA hp hBad hEncode⟩

theorem Decoded.source_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {p b c s block : M.Domain}
    (hp : M.mem p A.last) (hCopy : ParentCopy M C T A b p c) (h : Decoded M C T A c s block) : s=p := by
  obtain ⟨block',h'⟩ := decoded_parent_copy_d hM hC hT hA hp hCopy
  exact (h.unique_d hM hC hT hA h').1

end KP1Y.OneYFinite.OrdinaryCoordinates
