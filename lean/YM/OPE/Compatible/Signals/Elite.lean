import YM.OPE.Compatible.Signals.Align
/-!
# Uniform authenticated point bounds on an outline atlas. Costs polylogs independent of layouts, *and grids* inside request. Exponent never inside a universal point statement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Lattice RG Wilson Cells Extraction Word Spec OPE.Allot
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Final C F S)
variable {X Cx J:Type}[Fintype X]{Q:Finset X}{Y:X→E4}{ψ: Filter Cx}{T:Cx→ℝ}
lemma mode_paid (P:Prescription U.sector.derivatives)(hp:P.Coherent)(h:Outward C F S U.sector.derivatives) (d:ℕ)(i: Mode U.sector.derivatives)(he:i.fst≤d): ∃ L:ℕ,∀ᶠ m:ℕ in atTop,∀ {X:Type}[Fintype X][DecidableEq X](A B:ℝ){n W:ℕ}{x:X→ Cover} {v:X→ C.book.Token}{q:C.label d}, Survival (C:=C) F n m W A B v x d q → ‖P.test i d (S.project d q)‖*C.S.a m^(d-i.fst) ≤ β C m^L*B:=by
   obtain ⟨L,hL⟩:= h.paper d i.fst he (P.test i d) (fun j hj hf v=>by rw [P.affinity U.room.kernel.laws.toSymmetric U.phase.transport.injection,Prescription.highVan _ _ hp _ hj]; exacts [U.room.kernel.laws.toSymmetric,U.phase.transport.injection])
   refine ⟨L,?_⟩; filter_upwards [hL] with m hm X _ _ A B n W x v q hs; obtain ⟨T,f,ht,hf,hy,_,hz⟩:=hs.wins; exact hm T ht hf f q B hy hz
namespace Arboreal
variable [PartialOrder X][OrderBot X]
variable {s:Cx→X→ℝ}{M η c:ℝ}
-- DecidableEq X affects neither geometry nor Survival? classical set
structure Address (C:Family G)(D:Origin X)(Q:Finset X)(v b:ℕ)(T:ℝ)(s:X→ℝ)(η M:ℝ)(y:X→ E4): Prop where
    ridge : Ridge s η M D Q y
    screen : Screen (picked (brim D Q) y)
    stops : ∀ i∈ allUp D Q, ∃ x, C.S.gridPoint (aperture D C b v η T s i) x = y i
-- issue requires coordinates all X including y outside possibly nongrid; set junk 0 and rest exact
variable (A:Allot C)(hG:G.Simple)(hI:Inward C F S)(h:Org.Grill C F)
variable (D:Origin X)(p:brim D Q → C.book.Token)
-- given allocation relative to S. Need arbitrary i. outputs identify all tests simultaneously
set_option quotPrecheck false
lemma Address.pack {q:X→ℝ}{b v j:ℕ}{t:ℝ}{z:X→E4}(hx : Address C D Q v b t q η M z)(hQ:Crown Q): ∃ W, ∃ y: X→ Cover, j≤W∧ (∀ i∈ allUp D Q, aperture D C b v η t q i ≤ W ∧ (C.S.gridPoint W ∘y) i = z i) ∧ y ⊥=0 :=by
    let f i:= aperture D C b v η t q i; let s:=allUp D Q
    let k:= j+ Finset.univ.sup f; have he(i:X): f i ≤ k:=le_trans (Finset.le_sup (Finset.mem_univ _)) (Nat.le_add_left ..); choose g hg using hx.stops
    let y (i:X):= if h:i∈s then if i=⊥ then (0:Cover) else zoom C.S (he i) (g i h) else 0; have hi:⊥∈s:= Finset.mem_union_left _ hQ.base
    refine ⟨k,y,Nat.le_add_right ..,fun i h=> ⟨he _,?_⟩,?_⟩
    · change C.S.gridPoint k (y i) = _; unfold y; rw [dif_pos h]; split; next hz=> rw [hz,grid_zero,hx.ridge.belly]
      rw [zoom_grid]; exact hg _ h
    simp [y,hi]
variable {n d b W k:ℕ}{x:X→ Cover}
variable (hΓ: Glowing D Q ψ T s η)(hM:0 ≤ M)(hd:1 ≤ b)
local notation "nJ"=>fun i=> schedule C b η (s i) ⊥-1
local notation "Ω"=> fun i=> volume D Q (fun a=> (p a).1) (s i)
local notation "R"=> fun i=> s i ⊥
include U A hG hΓ hM hI hd
lemma announce_here (v:ℕ)(hJ:Stock.Tabs.opens C.path.levels 1 k n)(he:C.ref d ≤ n) : ∃ B B' : Cx→ℝ, Round ψ T (fun i=> B i * Ω i / R i^d) ∧ Round ψ T (fun i=>B' i * Ω i / R i^d) ∧ ∀ᶠ i in ψ,∀ z:X→E4,Address C D Q v b (T i) (s i) η M z → ∃ W, ∃ (x:brim D Q→ Cover)(p':brim D Q→ C.book.Token) (q:C.label d), k≤ W ∧ C.S.gridPoint W ∘ x = picked (brim D Q) z ∧ (∀ a,S.classTokens (p' a)=S.classTokens (p a)) ∧ Survival (C:=C) F k (nJ i) W (B i) (B' i) p' x d q:=by
    obtain ⟨c,c',hP,hQ,hR⟩:= issued (d:=d) (v:=v) D A U.room.cutoff hG hΓ hM hI p hJ he hd; refine ⟨c,c',hP,hQ,?_⟩; filter_upwards [hR] with i hi z hZ
    obtain ⟨W,x,hx,hX,hβ⟩:= Address.pack D (j := k) hZ hΓ.crowned
    obtain ⟨w,hW,q,hq⟩:= hi W x (by
       refine ⟨?_,fun a u h hh hi=> ?_,fun a u ha hb hp hw=>?_⟩
       · rw [(hX _ (Finset.mem_union_left _ hΓ.crowned.base)).2]; exact hZ.ridge.belly
       · rw [(hX _ (Finset.mem_union_left _ h)).2,(hX _ hh).2]; exact hZ.ridge.near _ _ h hh hi
       rw [(hX _ ha).2,(hX _ hb).2]; exact hZ.ridge.span _ _ ha hb hp hw) hβ (fun a h=> ⟨(hX a h).1,(hZ.stops a h).imp fun b hb=>(hX a h).2.trans hb.symm⟩)
    refine ⟨W, x∘Subtype.val,_,_,hx,funext fun a=> (hX _ (Finset.mem_union_right _ a.2)).2,fun i=>?_,hq⟩
    change (⟨(p i).1, S.project _ (w i)⟩:S.Tag)=_; rw [hW]
end Arboreal
end YM.OPE
