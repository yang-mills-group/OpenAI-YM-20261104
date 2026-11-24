import YM.OPE.Portfolio.Billing
/-! # The carried price and exact complete-component trajectory after a capture -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float Labels Bid Extra.Histories.Relay
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{H:History G}{N p i j b k d :ℕ}{F:Labels.Frame G d}
    {D:∀ N p i:ℕ,i<N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i)}{ζ ψ w:ℕ→ℝ}
    {W:Worth}{L: Hol G}
local notation "T"=> H.rep N p
set_option quotPrecheck false
variable {X:∀ i:ℕ,Site (H.S.side i p)} {Y:∀ i:ℕ,Cup (H.rep N p i)}{E:Extra.Histories.Music F H N p}
-- True Edge path certificate (`Programs`): widths in provisional credits. Don't require
-- superpowers; can discount any (positive) fraction subsequently.
structure Program (H:History G)(N p i j:ℕ) (X:∀ i:ℕ,Site (H.S.side i p))(Y:∀ i:ℕ,Cup (H.rep N p i))(w:ℕ→ℝ) (D:∀ N p i:ℕ,i<N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i))(byLimit:j≤N): Prop where
    follows m : i ≤ m →∀ hm:m < j,∃ ξ:ℂ,Cup.Edge (H.levels.clock.op m p) (D N p m (hm.trans_le byLimit)) (Y (m+1)) (Y m) (X (m+1)) (X m) ξ (w (m+1))
namespace Program
variable {W':ℕ→ℝ}
lemma within {ht:i≤N} (h:Program H N p k i X Y w D ht) {a s:ℕ} (ha:k ≤ a)(he:s ≤ i)(hf:∀ i,a ≤ i → i ≤ s → 0 ≤ W' i)(hr:∀ i,a ≤ i→ i ≤ s→ W' i ≤ w i) : Program H N p a s X Y W' D (he.trans ht):= ⟨fun i hi hv=> let t:=hi.trans i.le_succ; (h.follows i (ha.trans hi) (hv.trans_le he)).elim (fun y hy=> ⟨y,hy.thin (hf _ t hv) (hr _ t hv)⟩)⟩
variable (B:SectionData F) (v:Motion) (h:H.Selected)(hp:B.Sound L)(Hc:Studio.Sessions B E b L W ψ D) (hj:b ≤ k) (hb:k ≤ i)(hi:i≤N)
    {P: ∀ m:ℕ,Coefficient F (H.S.side m p)}{c:ℕ→ℝ}
    (hr: Fiesta H F ζ ψ k)
    (he:∀ i':ℕ, k ≤ i'→i' ≤ i→ 0 < w i') (hx:∀ i':ℕ,k ≤ i'→ i' < i→ w (i'+1) ≤ w i') (hy: ∀ i':ℕ,k ≤ i'→ i' < i→ X (i'+1)=(H.levels.clock.op i' p).ratio.embed (X i'))
include hj hi he hx hy h hp hr Hc
local notation "Q"=> (H.S.side i p)
open Studio
lemma agenda (hc:Club H L B ζ ψ k i N p w D P c hi) : ∃ Y:∀ m,Cup (H.rep N p m), Program H N p k i X Y w D hi ∧ ∀ m,k ≤ m→m ≤ i→ Mantle H N p m B v (X m) (P m) (Y m):=by
    obtain ⟨g,hg,hf⟩:= chapter_units H L B ζ ψ k i N p v X w D P c h hp hi hc he hx hr hy (fun j hk ht=> (Hc.stamps _ (hj.trans hk) _).elim (fun _ h=>h.tuned.2.1))
    let F' := liftF H B N p v X P; let φ := liftK H N p v X P
    let y (j:ℕ) := if hi:k ≤ j∧ j ≤ i then Cup.book (T j) (F' j) (g j) (hg.stocked j hi.1 hi.2) else 0; have hf' (j)(hj:k ≤ j) (ht:j ≤ i): y j = Cup.book (T j) (F' j) (g j) (hg.stocked j hj ht):= dif_pos ⟨hj,ht⟩
    have hk(j)(hj:k ≤ j)(ht:j ≤ i): (y j).pays=coin (T j) (F' j) (g j):= Cup.booked (h.represents N p j (ht.trans hi)|>.good.labels) (y j) (F' j) (g j) _ (hf' j hj ht)
    refine ⟨y, ⟨fun j hj hx=> ?_⟩, fun j hj hk=> by rw [hf' j hj hk]; exact ⟨rfl,hf j hj hk⟩⟩
    obtain ⟨μ,v,u,C,hμ,hU,hC,hX,hξ⟩:= hg.sways j hj hx; let t:=hj.trans j.le_succ
    exact ⟨v,⟨by rw [hk j hj hx.le,hk (j+1) t hx]; exact (hg.feeds j hj hx).symm, μ,u,C,hμ,hU,hC,hX,by rw [hf' j hj hx.le,hf' (j+1) t hx]; exact hξ⟩⟩
-- obtain P. and Program.X with ledger. Two variants.
variable {V:Cup (H.rep N p i)} {R A e:ℝ}{F':Coefficient F (H.S.side i p)}
    (hc:Studio.Mantle H N p i B v (X i) F' V) (hV:F'.Format 0 L (H.rep N p i))(hR:F'.remBound 0 (H.rep N p i) (kappa H i) e)(hQ:F.coeffSize F'.x+e ≤ A)
    (hS:4*(1+(H.levels.params i).columns)*A ≤ R)
local notation "I"=> E.tone i
include hb hc hV hR hQ hS
-- compare any V at initial site (presumably on same layout)
lemma erased (hA:∀ j:ℕ,k ≤ j → j ≤ i→ w j*‖alto H j d‖*R ≤ ζ j) : ∃ a:F.Coeff, F.coeffSize ((I).index a) ≤ 2*R ∧ ∃ c Y P,
     Program H N p k i X Y w D hi ∧ Club H L B ζ ψ k i N p w D P c hi ∧
     (∀ m,k ≤ m→m ≤ i→ Mantle H N p m B v (X m) (P m) (Y m)) ∧ ∀ v':Cup (H.rep N p i), Mantle H N p i B v (X i) ((E.tone i).plays a) v'→ Y i=V+v':=by
   obtain ⟨Z,hZ,hψ,hY,hA',ht⟩:= commit B h Hc (hj.trans hb) hi hV hR hQ hS; let x:=-(Z b).a; let U:= dualize H N p E b i Z x; have hv:=Hc.reissue (v:=x) (w:=w) (t':=fun _=>R) B (hj.trans hb) hi hj hb hψ hY (fun i hi ht' => ht _ (hj.trans hi) ht') hA (fun j hj hv=>(he j hj hv).le)
   obtain ⟨Y',hy,hH⟩:= agenda B v h hp Hc hj hi hr he hx hy hv
   refine ⟨x,hA',U.cost,Y',U.voice,hy,hv,hH,fun p hP=>?_⟩
   have hp := (Hc.paidPastel B (hj.trans hb) hi hV hR v hc hP) -- edit (#check)
   exact (hH i hb le_rfl).same B v (by change Studio.Mantle _ _ _ _ _ _ _ ((Z i).bar E x) _; rw [hZ]; exact hp)
end Program
end YM.MergeProof.Ribbons.ManyCopies.Cadet
