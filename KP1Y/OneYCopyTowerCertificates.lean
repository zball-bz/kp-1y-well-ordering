import KP1Y.OneYCopyTower

/-! 实际源山形/复制塔的有界证书。函数图总性与点结果唯一性恢复完整行规格；
不要求全部 ω 长度函数形成集合。 -/
namespace KP1Y.OneYFinite.CopyTower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

/-- 有界的图像证书：载域恰为图像，已列出的每一行满足点计算规格。 -/
structure ImageCertificate (M : SetTheory.Structure.{u}) (X Y F : M.Domain)
    (R : M.Domain → M.Domain → Prop) : Prop where
  graph : Graph M F X Y
  covered : ∀ y, M.mem y Y → ∃ x, M.mem x X ∧ MemPair M F x y
  sound : ∀ x, M.mem x X → ∀ y, M.mem y Y → MemPair M F x y → R x y

theorem ImageCertificate.rows {M : SetTheory.Structure.{u}} (he : Extensional M)
    {X Y F : M.Domain} {R : M.Domain → M.Domain → Prop}
    (h : ImageCertificate M X Y F R)
    (hUnique : ∀ x, M.mem x X → ∀ y z, R x y → R x z → y=z) (x y : M.Domain) :
    MemPair M F x y ↔ M.mem x X ∧ R x y := by
  constructor
  · intro hAt
    have hb := h.graph.bounds he hAt
    exact ⟨hb.1,h.sound x hb.1 y hb.2 hAt⟩
  · rintro ⟨hx,hR⟩
    obtain ⟨z,hz,hAt⟩ := h.graph.total x hx
    have hzy := hUnique x hx z y (h.sound x hx z hz hAt) hR
    exact hzy ▸ hAt

theorem ImageCertificate.range {M : SetTheory.Structure.{u}} (he : Extensional M)
    {X Y F : M.Domain} {R : M.Domain → M.Domain → Prop}
    (h : ImageCertificate M X Y F R)
    (hUnique : ∀ x, M.mem x X → ∀ y z, R x y → R x z → y=z) (y : M.Domain) :
    M.mem y Y ↔ ∃ x, M.mem x X ∧ R x y := by
  constructor
  · intro hy
    obtain ⟨x,hx,hAt⟩ := h.covered y hy
    exact ⟨x,hx,h.sound x hx y hy hAt⟩
  · rintro ⟨x,hx,hR⟩
    exact (h.graph.bounds he ((h.rows he hUnique x y).mpr ⟨hx,hR⟩)).2

theorem ImageCertificate.of_rows {M : SetTheory.Structure.{u}}
    {X Y F : M.Domain} {R : M.Domain → M.Domain → Prop}
    (hGraph : Graph M F X Y)
    (hRange : ∀ y, M.mem y Y ↔ ∃ x, M.mem x X ∧ R x y)
    (hRows : ∀ x y, MemPair M F x y ↔ M.mem x X ∧ R x y) : ImageCertificate M X Y F R := by
  refine ⟨hGraph,?_,fun x _ y _ hAt => ((hRows x y).mp hAt).2⟩
  intro y hy
  obtain ⟨x,hx,hR⟩ := (hRange y).mp hy
  exact ⟨x,hx,(hRows x y).mpr ⟨hx,hR⟩⟩

def imageCertificateFormula {n : Nat} (X Y F : Project.Term n) (body : Project.Formula 1 (n+2)) : Project.Formula 1 n :=
  .conj (graphFormula F X Y)
    (.conj (Project.Formula.forallMem Y (Project.Formula.existsMem X.weaken
      (memPairFormula F.weaken.weaken (.bound 0) (.bound 1))))
      (Project.Formula.forallMem X (Project.Formula.forallMem Y.weaken
        (.imp (memPairFormula F.weaken.weaken (.bound 1) (.bound 0)) body))))

theorem imageCertificateFormula_delta0 {n : Nat} (X Y F : Project.Term n)
    {body : Project.Formula 1 (n+2)} (hBody : body.IsDelta0) : (imageCertificateFormula X Y F body).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _)
    (.conj (.forallMem _ (.existsMem _ (memPairFormula_delta0 _ _ _)))
      (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) hBody))))

theorem imageCertificateFormula_freeClosed {n : Nat} {X Y F : Project.Term n}
    (hX : X.freeSupport=[]) (hY : Y.freeSupport=[]) (hF : F.freeSupport=[])
    {body : Project.Formula 1 (n+2)} (hBody : body.FreeClosed) : (imageCertificateFormula X Y F body).FreeClosed := by
  simp [imageCertificateFormula,graphFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.extensionalEq,hX,hY,hF,hBody]

theorem imageCertificateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {n : Nat} (e : Env M n) (X Y F : Project.Term n) (body : Project.Formula 1 (n+2)) :
    Project.Formula.satisfies e (imageCertificateFormula X Y F body) ↔
      ImageCertificate M (X.eval e) (Y.eval e) (F.eval e)
        (fun x y => Project.Formula.satisfies ((e.push x).push y) body) := by
  simp only [imageCertificateFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_imp_iff,memPairFormula_iff he,Term.eval_weaken,
    Project.Term.eval_bound_zero_push,Project.Term.eval_bound_one_push]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.graph,h.covered,h.sound⟩⟩

theorem ImageCertificate.congr {M : SetTheory.Structure.{u}} {X Y F : M.Domain}
    {R S : M.Domain → M.Domain → Prop}
    (h : ∀ x, M.mem x X → ∀ y, M.mem y Y → (R x y ↔ S x y)) :
    ImageCertificate M X Y F R ↔ ImageCertificate M X Y F S := by
  constructor
  · intro hR
    exact ⟨hR.graph,hR.covered,fun x hx y hy hAt => (h x hx y hy).mp (hR.sound x hx y hy hAt)⟩
  · intro hS
    exact ⟨hS.graph,hS.covered,fun x hx y hy hAt => (h x hx y hy).mpr (hS.sound x hx y hy hAt)⟩

def sourceGraphCertificateFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (States H B Histories Runs Sources SourceMap : Project.Term n) : Project.Formula 1 n :=
  imageCertificateFormula B Sources SourceMap
    (sourceFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken States.weaken.weaken H.weaken.weaken
      Histories.weaken.weaken Runs.weaken.weaken (.bound 1) (.bound 0))

theorem sourceGraphCertificateFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (States H B Histories Runs Sources SourceMap : Project.Term n) :
    (sourceGraphCertificateFormula C m R States H B Histories Runs Sources SourceMap).IsDelta0 :=
  imageCertificateFormula_delta0 _ _ _ (sourceFormula_delta0 _ _ _ _ _ _ _ _ _)

theorem sourceGraphCertificateFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m States H B Histories Runs Sources SourceMap : Project.Term n)
    (hm : m.freeSupport=[]) (hStates : States.freeSupport=[]) (hH : H.freeSupport=[]) (hB : B.freeSupport=[])
    (hHistories : Histories.freeSupport=[]) (hRuns : Runs.freeSupport=[]) (hSources : Sources.freeSupport=[])
    (hSourceMap : SourceMap.freeSupport=[]) :
    (sourceGraphCertificateFormula C m R States H B Histories Runs Sources SourceMap).FreeClosed := by
  apply imageCertificateFormula_freeClosed hB hSources hSourceMap
  exact sourceFormula_freeClosed hC.weaken.weaken hR.weaken.weaken _ _ _ _ _ _ _
    (by simpa using hm) (by simpa using hStates) (by simpa using hH)
    (by simpa using hHistories) (by simpa using hRuns) rfl rfl

theorem sourceGraphCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (e : Env M n) (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (States H B Histories Runs Sources SourceMap : Project.Term n)
    (hC : (C.eval e).Valid M) {V P : M.Domain}
    (hLayers : LayerRun M (C.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩ V P (H.eval e))
    (hFamily : ExpressionDiagram.RowFamily M (C.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩
      (H.eval e) (B.eval e) (Histories.eval e) (Runs.eval e)) :
    Project.Formula.satisfies e (sourceGraphCertificateFormula C m R States H B Histories Runs Sources SourceMap) ↔
      SourceGraph M (C.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩ (H.eval e) (B.eval e) (Sources.eval e) (SourceMap.eval e) := by
  rw [sourceGraphCertificateFormula,imageCertificateFormula_iff hM.1]
  have hBody (k code : M.Domain) := sourceFormula_iff hM ((e.push k).push code)
    C.weaken.weaken m.weaken.weaken R.weaken.weaken States.weaken.weaken H.weaken.weaken
    Histories.weaken.weaken Runs.weaken.weaken (.bound 1) (.bound 0)
    (by simpa only [ExpressionData.eval_weaken] using hC)
    (by simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken] using hLayers)
    (by simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken] using hFamily)
  have hCert := ImageCertificate.congr (M := M) (X := B.eval e) (Y := Sources.eval e) (F := SourceMap.eval e)
    (R := fun k code => Project.Formula.satisfies ((e.push k).push code)
      (sourceFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken States.weaken.weaken H.weaken.weaken
        Histories.weaken.weaken Runs.weaken.weaken (.bound 1) (.bound 0)))
    (S := SourceAt M (C.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩ (H.eval e))
    (fun k hk code _ => by simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken,
      Project.Term.eval_bound_zero_push,Project.Term.eval_bound_one_push,hk,true_and] using hBody k code)
  rw [hCert]
  constructor
  · intro h
    have hUnique : ∀ k, M.mem k (B.eval e) → ∀ a b,
        SourceAt M (C.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩ (H.eval e) k a →
        SourceAt M (C.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩ (H.eval e) k b → a=b :=
      fun _ _ _ _ ha hb => ha.unique_d hM hC hLayers hb
    exact ⟨h.graph,h.range hM.1 hUnique,h.rows hM.1 hUnique⟩
  · intro h
    exact ImageCertificate.of_rows h.graph h.range h.rows

def towerCertificateFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n))
    (m SourceForests K level B width Forests Sources SourceMap Codes G : Project.Term n) : Project.Formula 1 n :=
  imageCertificateFormula B Codes G
    (copiedFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken m.weaken.weaken SourceForests.weaken.weaken
      K.weaken.weaken level.weaken.weaken (.bound 1) width.weaken.weaken Forests.weaken.weaken
      Sources.weaken.weaken SourceMap.weaken.weaken (.bound 0))

theorem towerCertificateFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n))
    (m SourceForests K level B width Forests Sources SourceMap Codes G : Project.Term n) :
    (towerCertificateFormula C T A m SourceForests K level B width Forests Sources SourceMap Codes G).IsDelta0 :=
  imageCertificateFormula_delta0 _ _ _ (copiedFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem towerCertificateFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T)
    {A : CopyCoordinates.Context (Project.Term n)} (hA : A.Closed)
    (m SourceForests K level B width Forests Sources SourceMap Codes G : Project.Term n)
    (hm : m.freeSupport=[]) (hSF : SourceForests.freeSupport=[]) (hK : K.freeSupport=[])
    (hl : level.freeSupport=[]) (hB : B.freeSupport=[]) (hw : width.freeSupport=[])
    (hF : Forests.freeSupport=[]) (hS : Sources.freeSupport=[]) (hSM : SourceMap.freeSupport=[])
    (hCodes : Codes.freeSupport=[]) (hG : G.freeSupport=[]) :
    (towerCertificateFormula C T A m SourceForests K level B width Forests Sources SourceMap Codes G).FreeClosed := by
  apply imageCertificateFormula_freeClosed hB hCodes hG
  exact copiedFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken _ _ _ _ _ _ _ _ _ _
    (by simpa using hm) (by simpa using hSF) (by simpa using hK) (by simpa using hl) rfl
    (by simpa using hw) (by simpa using hF) (by simpa using hS) (by simpa using hSM) rfl

theorem towerCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : CopyCoordinates.Context (Project.Term n))
    (m SourceForests K level B width Forests Sources SourceMap Codes G : Project.Term n)
    (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e)) (hA : (A.eval e).Valid M (C.eval e))
    {L : LayerStateSpace M.Domain} {V P H : M.Domain}
    (hLayers : LayerRun M (C.eval e) (m.eval e) L V P H)
    (hBad : BadAt M (C.eval e) (m.eval e) L H (K.eval e) (level.eval e) (A.eval e).last (A.eval e).root)
    (hSources : SourceGraph M (C.eval e) (m.eval e) L H (B.eval e) (Sources.eval e) (SourceMap.eval e))
    (hSourceForests : SourceForests.eval e=L.rows.forests)
    (hForests : ∀ F, M.mem F (Forests.eval e) ↔ Forest M (C.eval e).omega (width.eval e) F)
    (hB : M.mem (B.eval e) (C.eval e).omega) (hWidth : M.mem (width.eval e) (C.eval e).omega) :
    Project.Formula.satisfies e (towerCertificateFormula C T A m SourceForests K level B width Forests Sources SourceMap Codes G) ↔
      Tower M (C.eval e) (T.eval e) (A.eval e) (m.eval e) L H (K.eval e) (level.eval e) (B.eval e)
        (width.eval e) (Forests.eval e) (Codes.eval e) (G.eval e) := by
  rw [towerCertificateFormula,imageCertificateFormula_iff hM.1]
  have hBody (k code : M.Domain) := copiedFormula_iff hM ((e.push k).push code)
    C.weaken.weaken T.weaken.weaken A.weaken.weaken m.weaken.weaken SourceForests.weaken.weaken
    K.weaken.weaken level.weaken.weaken (.bound 1) width.weaken.weaken Forests.weaken.weaken
    Sources.weaken.weaken SourceMap.weaken.weaken (.bound 0)
    (by simpa only [ExpressionData.eval_weaken] using hC)
    (by simpa only [ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken] using hT)
    (by simpa only [ExpressionData.eval_weaken,CopyCoordinates.Context.eval_weaken] using hA)
    (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hLayers)
    (by simpa only [ExpressionData.eval_weaken,CopyCoordinates.Context.eval_weaken,Term.eval_weaken] using hBad)
    (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hSources)
    (by simpa only [Term.eval_weaken] using hSourceForests)
    (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hForests)
  have hCert := ImageCertificate.congr (M := M) (X := B.eval e) (Y := Codes.eval e) (F := G.eval e)
    (R := fun k code => Project.Formula.satisfies ((e.push k).push code)
      (copiedFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken m.weaken.weaken SourceForests.weaken.weaken
        K.weaken.weaken level.weaken.weaken (.bound 1) width.weaken.weaken Forests.weaken.weaken
        Sources.weaken.weaken SourceMap.weaken.weaken (.bound 0)))
    (S := fun k code => ExpandedAt M (C.eval e) (T.eval e) (A.eval e) (m.eval e) L H (K.eval e) (level.eval e) k (width.eval e) (Forests.eval e) code)
    (fun k hk code _ => by simpa only [ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,
      CopyCoordinates.Context.eval_weaken,Term.eval_weaken,Project.Term.eval_bound_zero_push,
      Project.Term.eval_bound_one_push,hk,true_and] using hBody k code)
  rw [hCert]
  constructor
  · intro h
    have hK := (bad_indices_d hM hC hLayers hBad).1
    have hUnique : ∀ k, M.mem k (B.eval e) → ∀ a b,
        ExpandedAt M (C.eval e) (T.eval e) (A.eval e) (m.eval e) L H (K.eval e) (level.eval e) k (width.eval e) (Forests.eval e) a →
        ExpandedAt M (C.eval e) (T.eval e) (A.eval e) (m.eval e) L H (K.eval e) (level.eval e) k (width.eval e) (Forests.eval e) b → a=b :=
      fun _ _ _ _ ha hb => ha.unique_d hM hC hLayers hK hb
    exact ⟨hB,hWidth,hForests,h.graph,h.range hM.1 hUnique,h.rows hM.1 hUnique⟩
  · intro h
    exact ImageCertificate.of_rows h.graph h.range h.rows

end KP1Y.OneYFinite.CopyTower
