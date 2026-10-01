import KP1Y.ReflectionShapeEntries
import KP1Y.OneYFrameTransport

/-! 实际有限原子列表的逐位置坐标运输；层号保持，三个列坐标由同一个集合函数读取。 -/
namespace KP1Y.OneYFinite.CopyInvariant
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Assignments
open KP1Y.Reflection KP1Y.Ranking KP1Y.Bounded
universe u

theorem quad_mem_codes {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} (hD : D.Valid M)
    {e k q p c : M.Domain} (h : Quad M D.pairs e k q p c) : M.mem e D.edgeCodes := by
  obtain ⟨a,ha,b,hb,hCode,_,_⟩ := h
  exact (hD.edgeCodes e).mpr ⟨a,ha,b,hb,hCode⟩

theorem quad_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {Pairs e e' k q p c : M.Domain}
    (h : Quad M Pairs e k q p c) (h' : Quad M Pairs e' k q p c) : e=e' := by
  obtain ⟨a,_,b,_,hCode,hA,hB⟩ := h
  obtain ⟨a',_,b',_,hCode',hA',hB'⟩ := h'
  have haa := codes_unique he hA hA'
  have hbb := codes_unique he hB hB'
  subst a'
  subst b'
  exact codes_unique he hCode hCode'

def ReindexEdge (M : SetTheory.Structure.{u}) (w Pairs J e e' : M.Domain) : Prop :=
  ∃ k, M.mem k w ∧ ∃ q, M.mem q w ∧ ∃ p, M.mem p w ∧ ∃ c, M.mem c w ∧
  ∃ q', M.mem q' w ∧ ∃ p', M.mem p' w ∧ ∃ c', M.mem c' w ∧
    Quad M Pairs e k q p c ∧ MemPair M J q q' ∧ MemPair M J p p' ∧ MemPair M J c c' ∧ Quad M Pairs e' k q' p' c'

def reindexEdgeFormula {n : Nat} (w Pairs J e e' : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem w (Project.Formula.existsMem w.weaken (Project.Formula.existsMem w.weaken.weaken
    (Project.Formula.existsMem w.weaken.weaken.weaken (Project.Formula.existsMem w.weaken.weaken.weaken.weaken
      (Project.Formula.existsMem w.weaken.weaken.weaken.weaken.weaken (Project.Formula.existsMem w.weaken.weaken.weaken.weaken.weaken.weaken
        (.conj (quadFormula Pairs.weaken.weaken.weaken.weaken.weaken.weaken.weaken e.weaken.weaken.weaken.weaken.weaken.weaken.weaken
          (.bound 6) (.bound 5) (.bound 4) (.bound 3))
          (.conj (memPairFormula J.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 2))
            (.conj (memPairFormula J.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 1))
              (.conj (memPairFormula J.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 0))
                (quadFormula Pairs.weaken.weaken.weaken.weaken.weaken.weaken.weaken e'.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                  (.bound 6) (.bound 2) (.bound 1) (.bound 0))))))))))))

theorem reindexEdgeFormula_delta0 {n : Nat} (w Pairs J e e' : Project.Term n) : (reindexEdgeFormula w Pairs J e e').IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (quadFormula_delta0 _ _ _ _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (quadFormula_delta0 _ _ _ _ _ _)))))))))))

theorem reindexEdgeFormula_freeClosed {n : Nat} (w Pairs J e e' : Project.Term n)
    (hw : w.freeSupport=[]) (hPairs : Pairs.freeSupport=[]) (hJ : J.freeSupport=[]) (he : e.freeSupport=[]) (he' : e'.freeSupport=[]) :
    (reindexEdgeFormula w Pairs J e e').FreeClosed := by
  simp [reindexEdgeFormula,quadFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hw,hPairs,hJ,he,he']

theorem reindexEdgeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (w Pairs J e e' : Project.Term n) :
    Project.Formula.satisfies env (reindexEdgeFormula w Pairs J e e') ↔
      ReindexEdge M (w.eval env) (Pairs.eval env) (J.eval env) (e.eval env) (e'.eval env) := by
  simp only [reindexEdgeFormula,ReindexEdge,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    quadFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem reindex_edge_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {J e : M.Domain} (hJ : Graph M J D.omega D.omega)
    (he : M.mem e D.edgeCodes) : ∃ e', M.mem e' D.edgeCodes ∧ ReindexEdge M D.omega D.pairs J e e' := by
  obtain ⟨k,q,p,c,hQ⟩ := edge_code_decode hD he
  obtain ⟨hk,hq,hp,hc⟩ := hQ.bounds hM.1 hD.pairs
  obtain ⟨q',hq',hQ'⟩ := hJ.total q hq
  obtain ⟨p',hp',hP'⟩ := hJ.total p hp
  obtain ⟨c',hc',hC'⟩ := hJ.total c hc
  obtain ⟨e',he',hQuad⟩ := quad_code_exists_d hM hD hk hq' hp' hc'
  exact ⟨e',he',k,hk,q,hq,p,hp,c,hc,q',hq',p',hp',c',hc',hQ,hQ',hP',hC',hQuad⟩

theorem ReindexEdge.codes_mem {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} (hD : D.Valid M)
    {J e e' : M.Domain} (h : ReindexEdge M D.omega D.pairs J e e') : M.mem e D.edgeCodes ∧ M.mem e' D.edgeCodes := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hQ,_,_,_,hQ'⟩ := h
  exact ⟨quad_mem_codes hD hQ,quad_mem_codes hD hQ'⟩

theorem ReindexEdge.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {w Pairs J e e' e'' : M.Domain}
    (hJ : Graph M J w w) (h : ReindexEdge M w Pairs J e e') (h' : ReindexEdge M w Pairs J e e'') : e'=e'' := by
  obtain ⟨k,_,q,_,p,_,c,_,a,_,b,_,d,_,hQ,hA,hB,hD,hOut⟩ := h
  obtain ⟨k',_,q',_,p',_,c',_,a',_,b',_,d',_,hQ',hA',hB',hD',hOut'⟩ := h'
  obtain ⟨hk,hq,hp,hc⟩ := hQ.injective he hQ'
  subst k'; subst q'; subst p'; subst c'
  have ha := hJ.unique q a a' hA hA'
  have hb := hJ.unique p b b' hB hB'
  have hd := hJ.unique c d d' hD hD'
  subst a'; subst b'; subst d'
  exact quad_unique he hOut hOut'

theorem ReindexEdge.read {M : SetTheory.Structure.{u}} (he : Extensional M) {w Pairs J e e' k q p c : M.Domain}
    (h : ReindexEdge M w Pairs J e e') (hQuad : Quad M Pairs e k q p c) :
    ∃ a b d, MemPair M J q a ∧ MemPair M J p b ∧ MemPair M J c d ∧ Quad M Pairs e' k a b d := by
  obtain ⟨k',_,q',_,p',_,c',_,a,_,b,_,d,_,hQ,hA,hB,hD,hOut⟩ := h
  obtain ⟨hk,hq,hp,hc⟩ := hQ.injective he hQuad
  subst k'; subst q'; subst p'; subst c'
  exact ⟨a,b,d,hA,hB,hD,hOut⟩

private def edgeMapSchema : Project.Delta0BinarySchema 3 where
  body := reindexEdgeFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := reindexEdgeFormula_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := reindexEdgeFormula_delta0 _ _ _ _ _

theorem reindex_edge_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {J : M.Domain} (hJ : Graph M J D.omega D.omega) :
    ∃ F, Graph M F D.edgeCodes D.edgeCodes ∧ ∀ e e', MemPair M F e e' ↔ ReindexEdge M D.omega D.pairs J e e' := by
  let env := ((oneEnv D.omega).push D.pairs).push J
  have hφ (e e' : M.Domain) : Project.Formula.satisfies ((env.push e).push e') edgeMapSchema.body ↔ ReindexEdge M D.omega D.pairs J e e' := by
    rw [edgeMapSchema,reindexEdgeFormula_iff hM.1]
    rfl
  obtain ⟨F,hSupport,hRaw⟩ := relation_comprehension_d hM edgeMapSchema env D.edgeCodes D.edgeCodes
  have hRows (e e' : M.Domain) : MemPair M F e e' ↔ ReindexEdge M D.omega D.pairs J e e' := by
    rw [hRaw e e',hφ]
    exact ⟨fun h => h.2.2,fun h => ⟨(h.codes_mem hD).1,(h.codes_mem hD).2,h⟩⟩
  refine ⟨F,⟨hSupport,?_,?_⟩,hRows⟩
  · intro e he
    obtain ⟨e',he',h⟩ := reindex_edge_exists_d hM hD hJ he
    exact ⟨e',he',(hRows e e').mpr h⟩
  · intro e e' e'' hA hB
    exact ((hRows e e').mp hA).unique hM.1 hJ ((hRows e e'').mp hB)

theorem list_map_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {A len X Y F : M.Domain} (hA : Graph M A len X) (hF : Graph M F X Y) :
    ∃ B, Graph M B len Y ∧ ∀ i y, MemPair M B i y ↔ ∃ x, M.mem x X ∧ MemPair M A i x ∧ MemPair M F x y := by
  obtain ⟨B,hB⟩ := tuple_value_exists_d hM hA hF
  refine ⟨B,hB.values,?_⟩
  intro i y
  constructor
  · intro hAt
    have hi := (hB.values.bounds hM.1 hAt).1
    have hy := (hB.values.bounds hM.1 hAt).2
    obtain ⟨x,hx,hX⟩ := hA.total i hi
    exact ⟨x,hx,hX,(hB.rows i hi x hx y hy hX).mp hAt⟩
  · rintro ⟨x,hx,hX,hY⟩
    exact (hB.rows i (hA.bounds hM.1 hX).1 x hx y (hF.bounds hM.1 hY).2 hX).mpr hY

structure EdgeListTransport (M : SetTheory.Structure.{u}) (D : Reflection.Data M.Domain) (J len A B : M.Domain) : Prop where
  natural : M.mem len D.omega
  source : Graph M A len D.edgeCodes
  target : Graph M B len D.edgeCodes
  rows : ∀ i e', MemPair M B i e' ↔ ∃ e, M.mem e D.edgeCodes ∧ MemPair M A i e ∧ ReindexEdge M D.omega D.pairs J e e'

theorem edge_list_transport_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {J A : M.Domain} (hJ : Graph M J D.omega D.omega)
    (hA : M.mem A D.edgeLists) : ∃ len B, EdgeListTransport M D J len A B := by
  obtain ⟨len,hlen,hList⟩ := (hD.edgeLists A).mp hA
  obtain ⟨F,hF,hFRows⟩ := reindex_edge_graph_exists_d hM hD hJ
  obtain ⟨B,hB,hRows⟩ := list_map_graph_exists_d hM hList hF
  exact ⟨len,B,hlen,hList,hB,fun i e' => by simpa only [hFRows] using hRows i e'⟩

theorem EdgeListTransport.list_mem {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} (hD : D.Valid M)
    {J len A B : M.Domain} (h : EdgeListTransport M D J len A B) : M.mem B D.edgeLists :=
  (hD.edgeLists B).mpr ⟨len,h.natural,h.target⟩

theorem EdgeListTransport.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : Reflection.Data M.Domain} {J len len' A B B' : M.Domain}
    (h : EdgeListTransport M D J len A B) (h' : EdgeListTransport M D J len' A B') : B=B' := by
  have hLen := graph_domain_unique he h.source h'.source
  apply h.target.ext he (hLen.symm ▸ h'.target)
  intro i _ e'
  rw [h.rows i e',h'.rows i e']

theorem EdgeListTransport.entry_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : Reflection.Data M.Domain} {J len A B i k a b d : M.Domain}
    (hJ : Graph M J D.omega D.omega) (h : EdgeListTransport M D J len A B) :
    EdgeEntry M D B i k a b d ↔ ∃ q p c, EdgeEntry M D A i k q p c ∧ MemPair M J q a ∧ MemPair M J p b ∧ MemPair M J c d := by
  constructor
  · rintro ⟨e',he',hAt',hQ'⟩
    obtain ⟨e,hE,hAt,hTrans⟩ := (h.rows i e').mp hAt'
    obtain ⟨k',_,q,_,p,_,c,_,a',_,b',_,d',_,hQ,hA,hB,hD,hOut⟩ := hTrans
    obtain ⟨hk,ha,hb,hd⟩ := hOut.injective he hQ'
    subst k'; subst a'; subst b'; subst d'
    exact ⟨q,p,c,⟨e,hE,hAt,hQ⟩,hA,hB,hD⟩
  · rintro ⟨q,p,c,⟨e,hE,hAt,hQ⟩,hA,hB,hD⟩
    have hi := (h.source.bounds he hAt).1
    obtain ⟨e',he',hAt'⟩ := h.target.total i hi
    obtain ⟨f,_,hF,hTrans⟩ := (h.rows i e').mp hAt'
    have hfe := h.source.unique i f e hF hAt
    subst f
    obtain ⟨a',b',d',hA',hB',hD',hOut⟩ := hTrans.read he hQ
    have ha := hJ.unique q a' a hA' hA
    have hb := hJ.unique p b' b hB' hB
    have hd := hJ.unique c d' d hD' hD
    subst a'; subst b'; subst d'
    exact ⟨e',he',hAt',hOut⟩

theorem EdgeListTransport.edge_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : Reflection.Data M.Domain} {J len A B k a b d : M.Domain}
    (hJ : Graph M J D.omega D.omega) (h : EdgeListTransport M D J len A B) :
    EdgeAt M D B k a b d ↔ ∃ q p c, EdgeAt M D A k q p c ∧ MemPair M J q a ∧ MemPair M J p b ∧ MemPair M J c d := by
  constructor
  · rintro ⟨i,hi,hEntry⟩
    obtain ⟨q,p,c,hOld,hQ,hP,hC⟩ := (h.entry_iff he hJ).mp hEntry
    exact ⟨q,p,c,⟨i,hi,hOld⟩,hQ,hP,hC⟩
  · rintro ⟨q,p,c,⟨i,hi,hOld⟩,hQ,hP,hC⟩
    exact ⟨i,hi,(h.entry_iff he hJ).mpr ⟨q,p,c,hOld,hQ,hP,hC⟩⟩

theorem EdgeListTransport.diagram_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {J len A B m n : M.Domain}
    (hJ : ColumnEmbedding M D.omega D.omega J) (hn : M.mem n D.omega)
    (hRange : ∀ c, M.mem c m → ∀ c', MemPair M J c c' → M.mem c' n)
    (h : EdgeListTransport M D J len A B) (hA : Diagram M D m A) : Diagram M D n B := by
  refine ⟨hn,h.list_mem hD,?_⟩
  intro k _ a _ b _ d _ hEdge
  obtain ⟨q,p,c,hOld,hQ,hP,hC⟩ := (h.edge_iff hM.1 hJ.graph).mp hEdge
  obtain ⟨_,_,hc,hqp,hpc⟩ := hA.edge_columns_d hM hD hOld
  have hBounds := hOld.bounds hM.1 hD
  refine ⟨?_,hJ.strict p hBounds.2.2.1 c hBounds.2.2.2 hpc b d hP hC,hRange c hc d hC⟩
  rcases hqp with he | hqp
  · subst q
    exact Or.inl (hJ.graph.unique p a b hQ hP)
  · exact Or.inr (hJ.strict q hBounds.2.1 p hBounds.2.2.1 hqp a b hQ hP)

def ReindexNeed (M : SetTheory.Structure.{u}) (w J e e' : M.Domain) : Prop :=
  ∃ k, M.mem k w ∧ ∃ q, M.mem q w ∧ ∃ p, M.mem p w ∧ ∃ q', M.mem q' w ∧ ∃ p', M.mem p' w ∧
    Packet M e k q p ∧ MemPair M J q q' ∧ MemPair M J p p' ∧ Packet M e' k q' p'

def reindexNeedFormula {n : Nat} (w J e e' : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem w (Project.Formula.existsMem w.weaken (Project.Formula.existsMem w.weaken.weaken
    (Project.Formula.existsMem w.weaken.weaken.weaken (Project.Formula.existsMem w.weaken.weaken.weaken.weaken
      (.conj (packetFormula e.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2))
        (.conj (memPairFormula J.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (.conj (memPairFormula J.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
            (packetFormula e'.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 1) (.bound 0)))))))))

theorem reindexNeedFormula_delta0 {n : Nat} (w J e e' : Project.Term n) : (reindexNeedFormula w J e e').IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (packetFormula_delta0 _ _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (packetFormula_delta0 _ _ _ _))))))))

theorem reindexNeedFormula_freeClosed {n : Nat} (w J e e' : Project.Term n)
    (hw : w.freeSupport=[]) (hJ : J.freeSupport=[]) (he : e.freeSupport=[]) (he' : e'.freeSupport=[]) :
    (reindexNeedFormula w J e e').FreeClosed := by
  simp [reindexNeedFormula,packetFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hw,hJ,he,he']

theorem reindexNeedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (w J e e' : Project.Term n) : Project.Formula.satisfies env (reindexNeedFormula w J e e') ↔
      ReindexNeed M (w.eval env) (J.eval env) (e.eval env) (e'.eval env) := by
  simp only [reindexNeedFormula,ReindexNeed,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    packetFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem packet_mem_need_codes {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} (hD : D.Valid M)
    {e k q p : M.Domain} (hk : M.mem k D.omega) (hq : M.mem q D.omega) (hp : M.mem p D.omega)
    (h : Packet M e k q p) : M.mem e D.needCodes := by
  obtain ⟨pair,hCode,hPair⟩ := h
  exact (hD.needCodes e).mpr ⟨k,hk,pair,(hD.pairs pair).mpr ⟨q,hq,p,hp,hPair⟩,hCode⟩

theorem ReindexNeed.codes_mem {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} (hD : D.Valid M)
    {J e e' : M.Domain} (h : ReindexNeed M D.omega J e e') : M.mem e D.needCodes ∧ M.mem e' D.needCodes := by
  obtain ⟨_,hk,_,hq,_,hp,_,hq',_,hp',hOld,_,_,hNew⟩ := h
  exact ⟨packet_mem_need_codes hD hk hq hp hOld,packet_mem_need_codes hD hk hq' hp' hNew⟩

theorem reindex_need_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {J e : M.Domain} (hJ : Graph M J D.omega D.omega)
    (he : M.mem e D.needCodes) : ∃ e', M.mem e' D.needCodes ∧ ReindexNeed M D.omega J e e' := by
  obtain ⟨k,q,p,hPacket⟩ := need_code_decode hD he
  obtain ⟨pair,hCode,hPair⟩ := hPacket
  obtain ⟨k',hk,pair',hPairMem,hCode'⟩ := (hD.needCodes e).mp he
  obtain ⟨hkk,hpp⟩ := codes_injective hM.1 hCode hCode'
  subst k'; subst pair'
  obtain ⟨q',hq,p',hp,hPair'⟩ := (hD.pairs pair).mp hPairMem
  obtain ⟨hqq,hpp⟩ := codes_injective hM.1 hPair hPair'
  subst q'; subst p'
  obtain ⟨a,ha,hA⟩ := hJ.total q hq
  obtain ⟨b,hb,hB⟩ := hJ.total p hp
  obtain ⟨e',he',hNew⟩ := need_code_exists_d hM hD hk ha hb
  exact ⟨e',he',k,hk,q,hq,p,hp,a,ha,b,hb,⟨pair,hCode,hPair⟩,hA,hB,hNew⟩

theorem ReindexNeed.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {w J e e' e'' : M.Domain}
    (hJ : Graph M J w w) (h : ReindexNeed M w J e e') (h' : ReindexNeed M w J e e'') : e'=e'' := by
  obtain ⟨k,_,q,_,p,_,a,_,b,_,hQ,hA,hB,hOut⟩ := h
  obtain ⟨k',_,q',_,p',_,a',_,b',_,hQ',hA',hB',hOut'⟩ := h'
  obtain ⟨hk,hq,hp⟩ := hQ.injective he hQ'
  subst k'; subst q'; subst p'
  have ha := hJ.unique q a a' hA hA'
  have hb := hJ.unique p b b' hB hB'
  subst a'; subst b'
  exact hOut.unique he hOut'

theorem ReindexNeed.read {M : SetTheory.Structure.{u}} (he : Extensional M) {w J e e' k q p : M.Domain}
    (h : ReindexNeed M w J e e') (hPacket : Packet M e k q p) :
    ∃ a b, MemPair M J q a ∧ MemPair M J p b ∧ Packet M e' k a b := by
  obtain ⟨k',_,q',_,p',_,a,_,b,_,hQ,hA,hB,hOut⟩ := h
  obtain ⟨hk,hq,hp⟩ := hQ.injective he hPacket
  subst k'; subst q'; subst p'
  exact ⟨a,b,hA,hB,hOut⟩

private def needMapSchema : Project.Delta0BinarySchema 2 where
  body := reindexNeedFormula (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := reindexNeedFormula_freeClosed _ _ _ _ rfl rfl rfl rfl
  delta0 := reindexNeedFormula_delta0 _ _ _ _

theorem reindex_need_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {J : M.Domain} (hJ : Graph M J D.omega D.omega) :
    ∃ F, Graph M F D.needCodes D.needCodes ∧ ∀ e e', MemPair M F e e' ↔ ReindexNeed M D.omega J e e' := by
  let env := (oneEnv D.omega).push J
  have hφ (e e' : M.Domain) : Project.Formula.satisfies ((env.push e).push e') needMapSchema.body ↔ ReindexNeed M D.omega J e e' := by
    rw [needMapSchema,reindexNeedFormula_iff hM.1]
    rfl
  obtain ⟨F,hSupport,hRaw⟩ := relation_comprehension_d hM needMapSchema env D.needCodes D.needCodes
  have hRows (e e' : M.Domain) : MemPair M F e e' ↔ ReindexNeed M D.omega J e e' := by
    rw [hRaw e e',hφ]
    exact ⟨fun h => h.2.2,fun h => ⟨(h.codes_mem hD).1,(h.codes_mem hD).2,h⟩⟩
  refine ⟨F,⟨hSupport,?_,?_⟩,hRows⟩
  · intro e he
    obtain ⟨e',he',h⟩ := reindex_need_exists_d hM hD hJ he
    exact ⟨e',he',(hRows e e').mpr h⟩
  · intro e e' e'' hA hB
    exact ((hRows e e').mp hA).unique hM.1 hJ ((hRows e e'').mp hB)

structure NeedListTransport (M : SetTheory.Structure.{u}) (D : Reflection.Data M.Domain) (J len A B : M.Domain) : Prop where
  natural : M.mem len D.omega
  source : Graph M A len D.needCodes
  target : Graph M B len D.needCodes
  rows : ∀ i e', MemPair M B i e' ↔ ∃ e, M.mem e D.needCodes ∧ MemPair M A i e ∧ ReindexNeed M D.omega J e e'

theorem need_list_transport_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {J A : M.Domain} (hJ : Graph M J D.omega D.omega)
    (hA : M.mem A D.needLists) : ∃ len B, NeedListTransport M D J len A B := by
  obtain ⟨len,hlen,hList⟩ := (hD.needLists A).mp hA
  obtain ⟨F,hF,hFRows⟩ := reindex_need_graph_exists_d hM hD hJ
  obtain ⟨B,hB,hRows⟩ := list_map_graph_exists_d hM hList hF
  exact ⟨len,B,hlen,hList,hB,fun i e' => by simpa only [hFRows] using hRows i e'⟩

theorem NeedListTransport.list_mem {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} (hD : D.Valid M)
    {J len A B : M.Domain} (h : NeedListTransport M D J len A B) : M.mem B D.needLists :=
  (hD.needLists B).mpr ⟨len,h.natural,h.target⟩

theorem NeedListTransport.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : Reflection.Data M.Domain} {J len len' A B B' : M.Domain}
    (h : NeedListTransport M D J len A B) (h' : NeedListTransport M D J len' A B') : B=B' := by
  have hLen := graph_domain_unique he h.source h'.source
  apply h.target.ext he (hLen.symm ▸ h'.target)
  intro i _ e'
  rw [h.rows i e',h'.rows i e']

theorem NeedListTransport.entry_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : Reflection.Data M.Domain} {J len A B i k a b : M.Domain}
    (hJ : Graph M J D.omega D.omega) (h : NeedListTransport M D J len A B) :
    NeedEntry M D B i k a b ↔ ∃ q p, NeedEntry M D A i k q p ∧ MemPair M J q a ∧ MemPair M J p b := by
  constructor
  · rintro ⟨e',he',hAt',hQ'⟩
    obtain ⟨e,hE,hAt,hTrans⟩ := (h.rows i e').mp hAt'
    obtain ⟨k',_,q,_,p,_,a',_,b',_,hQ,hA,hB,hOut⟩ := hTrans
    obtain ⟨hk,ha,hb⟩ := hOut.injective he hQ'
    subst k'; subst a'; subst b'
    exact ⟨q,p,⟨e,hE,hAt,hQ⟩,hA,hB⟩
  · rintro ⟨q,p,⟨e,hE,hAt,hQ⟩,hA,hB⟩
    have hi := (h.source.bounds he hAt).1
    obtain ⟨e',he',hAt'⟩ := h.target.total i hi
    obtain ⟨f,_,hF,hTrans⟩ := (h.rows i e').mp hAt'
    have hfe := h.source.unique i f e hF hAt
    subst f
    obtain ⟨a',b',hA',hB',hOut⟩ := hTrans.read he hQ
    have ha := hJ.unique q a' a hA' hA
    have hb := hJ.unique p b' b hB' hB
    subst a'; subst b'
    exact ⟨e',he',hAt',hOut⟩

theorem NeedListTransport.need_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : Reflection.Data M.Domain} {J len A B k a b : M.Domain}
    (hJ : Graph M J D.omega D.omega) (h : NeedListTransport M D J len A B) :
    NeedAt M D B k a b ↔ ∃ q p, NeedAt M D A k q p ∧ MemPair M J q a ∧ MemPair M J p b := by
  constructor
  · rintro ⟨i,hi,hEntry⟩
    obtain ⟨q,p,hOld,hQ,hP⟩ := (h.entry_iff he hJ).mp hEntry
    exact ⟨q,p,⟨i,hi,hOld⟩,hQ,hP⟩
  · rintro ⟨q,p,⟨i,hi,hOld⟩,hQ,hP⟩
    exact ⟨i,hi,(h.entry_iff he hJ).mpr ⟨q,p,hOld,hQ,hP⟩⟩

theorem NeedListTransport.template_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {J len A B m n : M.Domain}
    (hJ : ColumnEmbedding M D.omega D.omega J) (hn : M.mem n D.omega)
    (hRange : ∀ p, M.mem p m → ∀ p', MemPair M J p p' → M.mem p' n)
    (h : NeedListTransport M D J len A B) (hA : Template M D m A) : Template M D n B := by
  refine ⟨hn,h.list_mem hD,?_⟩
  intro k _ a _ b _ hNeed
  obtain ⟨q,p,hOld,hQ,hP⟩ := (h.need_iff hM.1 hJ.graph).mp hNeed
  obtain ⟨_,hp,hqp⟩ := hA.need_columns_d hM hD hOld
  have hBounds := hOld.bounds hM.1 hD
  refine ⟨?_,hRange p hp b hP⟩
  rcases hqp with he | hqp
  · subst q
    exact Or.inl (hJ.graph.unique p a b hQ hP)
  · exact Or.inr (hJ.strict q hBounds.2.1 p hBounds.2.2 hqp a b hQ hP)

end KP1Y.OneYFinite.CopyInvariant
