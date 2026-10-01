import KP1Y.OneYLowerCanonPseudoLow

/-! Lower复制目标图伪父的统一公式（原 pseudo_parent_parentCopy）：对每个源列 root<s≤last 与块 b，
目标伪父恰为源伪父的 `PseudoCopy`（仅 H(s)=floor 且源伪父为root时收缩到root）。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

private theorem no_candidate_zero {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C) {c q : M.Domain}
    (hHZ : MemPair M X.heights c C.zero) : ¬GraphPseudoCandidate M C X c q := by
  rintro ⟨hc,_,_,_,r,_,hHC,_,hSucc,_⟩
  have he := hX.heights.unique c hc C.zero hHC hHZ
  subst he
  exact hC.zero_empty r hSucc.predecessor_mem

/-- 统一伪父公式。 -/
theorem Copies.canon_pseudo_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {s b c : M.Domain}
    (hRootS : M.mem D.coordinates.root s) (hsLast : s=D.coordinates.last ∨ M.mem s D.coordinates.last)
    (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c Y.width) (a : M.Domain) :
    GraphPseudoParent M C Y c a ↔ ∃ q, GraphPseudoParent M C D.mountain s q ∧ PseudoCopy M C T D s b q a := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hFloorNat := hD.floor_nat hM.1
  have hsX := canon_last_in_width hM hC hD hsLast
  obtain ⟨hs,hsNat,hHS⟩ := hD.mountain.heights.total s hsX
  have hRootNot : ¬M.mem D.coordinates.root D.coordinates.root := nat_irrefl hM _
  have hEncS := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMap.1 (Or.inr hRootS))).mp hMap
  have hCandNat (q : M.Domain) (h : GraphPseudoCandidate M C D.mountain s q) : M.mem q C.omega :=
    hw.transitive D.mountain.width hD.mountain.width q (h.bounds hM.1).1
  -- 非收缩：PseudoCopy 恰为 ParentCopy
  have hPlain (q a : M.Domain) (hNo : ¬MemPair M D.mountain.heights s D.floor) :
      PseudoCopy M C T D s b q a ↔ ParentCopy M C T D.coordinates b q a :=
    ⟨fun h => h.elim (fun h => False.elim (hNo h.2.1)) And.right,fun h => Or.inr ⟨fun h' => hNo h'.2,h⟩⟩
  have hTot : ∀ q, GraphPseudoCandidate M C D.mountain s q → ∃ a, PseudoCopy M C T D s b q a := by
    intro q hq
    classical
    by_cases hSp : q=D.coordinates.root ∧ MemPair M D.mountain.heights s D.floor
    · exact ⟨D.coordinates.root,Or.inl ⟨hSp.1,hSp.2,rfl⟩⟩
    · obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMap.2.1
      obtain ⟨a,_,hA⟩ := hJ.graph.total q (hCandNat q hq)
      exact ⟨a,Or.inr ⟨hSp,(hRows q a).mp hA⟩⟩
  have hCand : ∀ a, GraphPseudoCandidate M C Y c a ↔ ∃ q, GraphPseudoCandidate M C D.mountain s q ∧ PseudoCopy M C T D s b q a := by
    intro a
    classical
    by_cases hCone : InCone M C D s
    · have hFloorHs := hCone.height_strict_d hM hC hD hRootS hHS
      have hNo : ¬MemPair M D.mountain.heights s D.floor := fun h =>
        nat_irrefl hM D.floor ((hD.mountain.heights.unique s hs D.floor hHS h) ▸ hFloorHs)
      rw [hCopy.canon_pseudo_cand_lifted_d hM hC hT hD hY hRun hFrom hRootS hsLast hCone hEncS hc a]
      constructor
      · rintro ⟨q,hq,hEncQ⟩
        refine ⟨q,hq,(hPlain q a hNo).mpr ?_⟩
        obtain ⟨hs',_,_,_,r,hr,hHS',_,hSucc,F,_,hF,hAnc,_⟩ := hq
        have he := hD.mountain.heights.unique s hs' hs hHS' hHS
        subst he
        have hFloorR : D.floor=r ∨ M.mem D.floor r := (nat_lt_succ_iff hM hSucc).mp hFloorHs
        have hConeQ := (in_cone_ancestor_iff_d hM hC hD hRun hFrom hFloorR hF hAnc).mpr hCone
        exact (parent_copy_bad_iff (nat_not_lt_of_le hM hC hEncQ.1 (hConeQ.root_le hM.1 hD))).mpr hEncQ
      · rintro ⟨q,hq,hPC⟩
        have hMapQ := (hPlain q a hNo).mp hPC
        obtain ⟨hs',_,_,_,r,hr,hHS',_,hSucc,F,_,hF,hAnc,_⟩ := id hq
        have he := hD.mountain.heights.unique s hs' hs hHS' hHS
        subst he
        have hFloorR : D.floor=r ∨ M.mem D.floor r := (nat_lt_succ_iff hM hSucc).mp hFloorHs
        have hConeQ := (in_cone_ancestor_iff_d hM hC hD hRun hFrom hFloorR hF hAnc).mpr hCone
        exact ⟨q,hq,(parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapQ.1 (hConeQ.root_le hM.1 hD))).mp hMapQ⟩
    · have hsLast' : M.mem s D.coordinates.last := hsLast.resolve_left (fun he => hCone (he ▸ in_cone_last hD))
      rcases nat_le_or_lt hM hC hsNat hFloorNat with hle | hgt
      · rcases natural_cases hM hC.omega hsNat with hEmpty | ⟨_,_,_⟩
        · have hZ := hM.1.eq_of_same_members hs C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))
          subst hZ
          have hHCZ : MemPair M Y.heights c C.zero :=
            (hCopy.parent_copy_heights_d hM hC hT hD hsLast' (hCopy.width ▸ hc) hMap hHS).mpr (Or.inr ⟨hCone,rfl⟩)
          exact iff_of_false (no_candidate_zero hC hY hHCZ) (fun ⟨q,hq,_⟩ => no_candidate_zero hC hD.mountain hHS hq)
        · have hPos : M.mem C.zero hs := (hC.zero_mem_iff hM hsNat).mpr (by
            intro he
            subst he
            rename_i p _ hSucc
            exact hC.zero_empty p hSucc.predecessor_mem)
          rw [hCopy.canon_pseudo_cand_low_d hM hC hT hD hY hRun hFrom hRootS hsLast' hCone hHS hPos hle hMap hc a]
          have hEquiv (q : M.Domain) (hq : GraphPseudoCandidate M C D.mountain s q) :
              LowCopy M C T D.coordinates b q a ↔ PseudoCopy M C T D s b q a := by
            by_cases hqR : q=D.coordinates.root
            · subst hqR
              have hSp : MemPair M D.mountain.heights s D.floor := by
                obtain ⟨hs',_,hp,_,r,_,hHS',hHP,hSucc,_,_,_,_,hRel⟩ := hq
                have he1 := hD.mountain.heights.unique s hs' hs hHS' hHS
                subst he1
                have he2 := hD.mountain.heights.unique _ hp D.floor hHP hD.floor
                subst he2
                rcases hRel with he | he
                · exact he ▸ hHS
                · exact False.elim (nat_not_lt_of_le hM hC hFloorNat hle ((he ▸ hSucc).predecessor_mem |> fun _ =>
                    (hSucc D.floor).mpr (Or.inr (fun x => by rw [he])) ))
              exact ⟨fun h => h.elim (fun h => Or.inl ⟨rfl,hSp,h.2⟩) (fun h => False.elim (h.1 rfl)),
                fun h => h.elim (fun h => Or.inl ⟨rfl,h.2.2⟩) (fun h => False.elim (h.1 ⟨rfl,hSp⟩))⟩
            · exact ⟨fun h => h.elim (fun h => False.elim (hqR h.1)) (fun h => Or.inr ⟨fun h' => hqR h'.1,h.2⟩),
                fun h => h.elim (fun h => False.elim (hqR h.1)) (fun h => Or.inr ⟨hqR,h.2⟩)⟩
          exact ⟨fun ⟨q,hq,hL⟩ => ⟨q,hq,(hEquiv q hq).mp hL⟩,fun ⟨q,hq,hP⟩ => ⟨q,hq,(hEquiv q hq).mpr hP⟩⟩
      · have hNo : ¬MemPair M D.mountain.heights s D.floor := fun h =>
          nat_irrefl hM D.floor ((hD.mountain.heights.unique s hs D.floor hHS h) ▸ hgt)
        rw [hCopy.canon_pseudo_cand_out_d hM hC hT hD hY hRun hFrom hsLast' hCone hHS hgt hMap hc a]
        exact ⟨fun ⟨q,hq,h⟩ => ⟨q,hq,(hPlain q a hNo).mpr h⟩,fun ⟨q,hq,h⟩ => ⟨q,hq,(hPlain q a hNo).mp h⟩⟩
  exact canon_pseudo_parent_transfer_d hM hC hD.mountain hY (PseudoCopy M C T D s b)
    (fun q a a' h h' => canon_pseudo_copy_fun hM hC hT hD h h') hTot
    (fun q q' a a' h h' hqq => canon_pseudo_copy_mono hM hC hT hD h h' hqq) hCand a

/-- 以 Encode 给出新列、析取顺序同 helper `LowerHelp.PseudoCopyFormula M C T D Y` 定义体的形式（逐字同形）。 -/
theorem Copies.canon_pseudo_copy_formula_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) :
    ∀ s b c, M.mem D.coordinates.root s → (s=D.coordinates.last ∨ M.mem s D.coordinates.last) →
      Encode M C T D.coordinates s b c → M.mem c Y.width → M.mem D.coordinates.last c →
      ∀ q, GraphPseudoParent M C Y c q ↔ ∃ p, GraphPseudoParent M C D.mountain s p ∧
        ((MemPair M D.mountain.heights s D.floor ∧ p=D.coordinates.root ∧ q=D.coordinates.root) ∨
          (¬(MemPair M D.mountain.heights s D.floor ∧ p=D.coordinates.root) ∧ ParentCopy M C T D.coordinates b p q)) := by
  intro s b c hRootS hsLast hEnc hc _ q
  have hNot : ¬M.mem s D.coordinates.root := nat_not_lt_of_le hM hC hEnc.1 (Or.inr hRootS)
  rw [hCopy.canon_pseudo_copy_d hM hC hT hD hY hRun hFrom hRootS hsLast ((parent_copy_bad_iff hNot).mpr hEnc) hc q]
  constructor
  · rintro ⟨p,hp,h⟩
    exact ⟨p,hp,h.elim (fun ⟨h1,h2,h3⟩ => Or.inl ⟨h2,h1,h3⟩) (fun ⟨h1,h2⟩ => Or.inr ⟨fun ⟨a,b⟩ => h1 ⟨b,a⟩,h2⟩)⟩
  · rintro ⟨p,hp,h⟩
    exact ⟨p,hp,h.elim (fun ⟨h1,h2,h3⟩ => Or.inl ⟨h2,h1,h3⟩) (fun ⟨h1,h2⟩ => Or.inr ⟨fun ⟨a,b⟩ => h1 ⟨b,a⟩,h2⟩)⟩

end KP1Y.OneYFinite.CopiedMountain.Lower
