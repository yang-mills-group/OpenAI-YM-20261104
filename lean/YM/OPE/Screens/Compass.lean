import YM.OPE.Screens.Deck
/-!
# Solving a generation. Assign the spectral matrix hypothesis
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Shuttle
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station Cells
open Book.Tariff Playout.Rake Rhythm.Store Rhythm Next.UVStress Spec Cards Payments
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G:Gauge}
    {H l m k b N p A t t' q d e:ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {F:Extraction.Order}{S:Table C.book}(U: Final C F S)
variable {Y:Type}{f:Filter Y}{X:Y→ I→ Cover}{T a c : Y→ℝ}{R r:Y→ℕ→ℝ}{α:ℕ→ℝ}{η M M':ℝ}
    {P:Y→Loom Q} {B:Border f T Q.limit R r α} (D:Oscars B M P C)
local notation "μ!"=> C.S.a
local notation "L!"=> (fun i=> (P i).launch Q.limit)
local notation "K"=> C.path.levels.budget
local notation "T!"=> C.S.gridPoint
variable {φ: Filter (ℕ×ℕ)}[φ.NeBot] (h:φ ≤ F.fuse)
variable {W r' D'}(L:LogPackage C W r' D')
variable (hG:G.Simple) (v:I→ C.book.Token) (V:MatrixTicket (C:=C) S U.sector.derivatives φ)
local notation "v'"=> (fun j=> (v j).1)
local notation "m!"=> (fun i=>(P i).below 0)
local notation "t!"=> (fun i=> (P i).below H)
local notation "μ"=> (fun i t=> (P i).launch t)
local notation "κ"=> Wallet f T
include D L
lemma piloting (A b k:ℕ) :∀ᶠ i in f, (let q:=Stock.Tabs.chosen C.path.levels 1 L.tabs b; q ≤ m! i ∧∀ m≥ m! i,A ≤ r' m) ∧ ∀ j,C.ref (v j).1≤ (P i).launch (Q.age j):= by
    have h':=(D.lower 0 (Nat.zero_le _)).grows; obtain ⟨t,ht⟩:= eventually_atTop.mp (L.spare.eventually_ge_atTop A); filter_upwards [h'.eventually_ge_atTop t,h'.eventually_ge_atTop (Stock.Tabs.chosen C.path.levels 1 L.tabs b),eventually_all.mpr (fun j:I=>(D.upper (Q.age j) (Q.bounded j)).grows.eventually_ge_atTop (C.ref (v j).1))] with i hi hh hp using ⟨⟨hh,fun m h=>ht m (hi.trans h)⟩,hp⟩
omit L in
lemma wholeRoom (b:ℕ)(H':H ≤ Q.age Q.star)(hm:0 ≤ M') (p: Y→ I→ E4) (he:∀ᶠ i in f,draft Q (R i) (r i) M' η H (p i)):∀ᶠ i in f,∀ j,8*‖p i j‖ ≤ μ! b:=by
    filter_upwards [B.envelope H' hm he (Nat.zero_le _), ((B.narrows 0 (Nat.zero_le _)).const_mul (16*M')).eventually (ge_mem_nhds (show (16*M')*0< μ! b from by rw [mul_zero]; exact C.S.a_pos _))] with i hi hh j; have ht:= hi j; rw [Q.lead_zero (Q.pinned_init j),sub_zero] at ht; linarith
local notation "Z'"=> (fun i=>priceSet Q univ v (R i))
local notation "Y'"=> (fun i=>priceSet Q (Q.focus H) v (R i))
include U V h hG
variable (he:C.ref 0<b) (hp:C.ref d ≤ b) (H':H ≤ Q.age Q.star)(hX:∀ᶠ i in f,Canvas (P i) C H b (X i))
    (hu:∀ᶠ i in f,draft Q (R i) (r i) M' η H (C.S.gridPoint ((P i).launch Q.limit) ∘ X i))
local notation "w!"=> Trunk.lens
include hX he hp H' hu
lemma ticks (hm:0 ≤ M'): ∃ a a' : Y→ℝ, ∃ z:Y→ C.label d, Wallet f T (fun i=> a i * priceSet Q univ v (R i)/ (R i 0)^d) ∧ Wallet f T (fun i=> a' i *priceSet Q univ v (R i)/(R i 0)^d)∧∀ᶠ i in f, Dir C S (L! i) b (m! i) d (a i) (a' i) (X i) v φ (z i):=by
    let Z'':= Z'; let A:= Fintype.card I+Fintype.card (C.labels.level d).Index; let q:=Stock.Tabs.chosen C.path.levels 1 L.tabs b; have hk : Stock.Tabs.opens C.path.levels 1 b q:= Stock.Tabs.opened ..; have hP:=hp.trans hk.1; have hξ:0<A:=(Fintype.card_pos_iff.mpr ⟨Q.star⟩).trans_le (Nat.le_add_right ..)
    obtain ⟨u,hU,hV⟩:= access D v V; let u' i:= Highest.base_price Q C (P i) v' (u i); have hh:= regWage D L hG hξ 0; obtain ⟨p,hQ,hπ⟩:=hh; let a i:= capBound (P i) 0 d A (p i) L (u' i); let c i:= rootBound (P i) 0 d b q A (p i) L (u' i); let t i z:= Dir C S (L! i) b (m! i) d (a i) (c i) (X i) v φ z; let y i:= if h:∃ z,t i z then h.choose else 0
    have hw: ValueStamp f T (fun i=> Z'' i/u' i):= routine D v hU univ; have hx:= hQ (0+1) (by omega)
    refine ⟨a,c,y,(cap_fuel D L (Nat.zero_le _) hξ hx hw d).congr ?_,(studioPrice D L (Nat.zero_le _) hξ hx hw d b q).congr ?_,?_⟩
    · filter_upwards with i; change Z'' i/R i 0^d* a i=a i*Z'' i/R i 0^d; ring
    · filter_upwards with i; change Z'' i/R i 0^d*c i=c i*Z'' i/R i 0^d; ring
    filter_upwards [hX,hV,piloting D L v A b b,wholeRoom D b H' hm _ hu, eventually_all.mpr (fun i=> (hU i).profit)] with i hi hV hT ha hS; have hh: ∃ z,t i z:= knock U h L hG (hπ _) hi he hP ha hk hT.1.1 le_rfl hT.1.2 hT.2 hS hV; rw [show y i=hh.choose from dif_pos hh]; exact hh.choose_spec
local notation "Ψ"=> (fun i=> priceSet Q univ v (R i)*fuel (R i) H l e)
omit H'
lemma responsible (hm:0 ≤ M') (hV:Q.Strike H l)(he':C.ref e ≤ b)(hη:0<η): ∃ (a a' c c':Y→ℝ)(z:Y→ C.label d)(y:Y→ C.label e), κ (fun i=> a i*Ψ i/R i 0^d)∧ κ (fun i=> a' i*Ψ i/R i 0^d) ∧ κ (fun i=>c i* Y' i/R i H^e) ∧ κ (fun i=> c' i*Y' i/R i H^e) ∧ ∀ᶠ i in f, SignDir C S (L! i) b (m! i) (t! i) d e (a i) (a' i) (c i) (c' i) (X i) v (Q.focus H) φ (z i) (y i):=by
    let Z'':= Z'; let A:= Fintype.card I+Fintype.card ((C.labels.level d).Index⊕ (C.labels.level e).Index); let q:=Stock.Tabs.chosen C.path.levels 1 L.tabs b; have hk : Stock.Tabs.opens C.path.levels 1 b q:= Stock.Tabs.opened ..; have hP:=hp.trans hk.1; have hξ:0<A:=(Fintype.card_pos_iff.mpr ⟨Q.star⟩).trans_le (Nat.le_add_right ..)
    obtain ⟨u,hU,hV₀⟩:= access D v V; let u' i:= Highest.base_price Q C (P i) v' (u i) * Variant.widen (P i) C H l e; let u'' i:= batchClock C (P i) v (u i) H; obtain ⟨p,hp₁,hπ⟩:= regWage D L hG hξ e
    let a i:=capBound (P i) 0 d A (p i) L (u' i); let c i:= rootBound (P i) 0 d b q A (p i) L (u' i); let a' i:=capBound (P i) H e A (p i) L (u'' i); let c' i:=rootBound (P i) H e b q A (p i) L (u'' i)
    let t i z y := SignDir C S (L! i) b (m! i) (t! i) d e (a i) (c i) (a' i) (c' i) (X i) v (Q.focus H) φ z y
    let Yp i:= if h:∃ z y,t i z y then h.choose else 0; let y i:= if h:∃ y,t i (Yp i) y then h.choose else 0; let Wow:= Ψ; let β:= Y'; have hH:= hV.atMost; have hZ:H ≤ Q.age Q.star:= hV.exists_.symm.le
    have hw:ValueStamp f T (fun i=> Wow i/u' i):= ((routine D v hU univ).mul (bonus D e (hV.before.le.trans hH) hH)).congr (Eventually.of_forall fun i=>div_mul_div_comm ..)
    have hw':ValueStamp f T (fun i=> β i/u'' i):= by simp_rw [u'',homeChart]; exact routine D v hU (Q.focus H); -- edit simp
    have hx:= hp₁ (0+1) (by omega); have hh:= hp₁ (H+1) (by omega)
    refine ⟨a,c,a',c',Yp,y,(cap_fuel D L (Nat.zero_le _) hξ hx hw d).congr ?_,(studioPrice D L (Nat.zero_le _) hξ hx hw d b q).congr ?_,(cap_fuel D L hH hξ hh hw' e).congr ?_,(studioPrice D L hH hξ hh hw' e b q).congr ?_,?_⟩
    · filter_upwards with i; change Wow i/R i 0^d* a i=a i*Wow i/R i 0^d; ring
    · filter_upwards with i; change Wow i/R i 0^d* c i=c i*Wow i/R i 0^d; ring
    · filter_upwards with i; change β i/R i H^e* a' i=a' i* β i/R i H^e; ring
    · filter_upwards with i; change β i/R i H^e*c' i=c' i*β i/R i H^e; ring
    have hf(i)(hi:i∉ Q.focus H) : ∀ᶠ p in f,∀ᶠ k in atTop,∀ m, (P p).below H ≤ m→(K m).B^2≤ separation (w! C (L! p) k (X p) m i) 0:=by
       let t:= Q.gap Q.star i; have h:t < H:= (by unfold t; rw [Q.flip]; exact (hV.reserve i hi).trans_lt hV.before); filter_upwards [B.ear hZ hm hu i hi rfl h hη,peep B hG D (t:=t) (h.le.trans hH) (half_pos hη),hX] with j hx hh hC using hC.extra_clear L i h hH (hh.trans_lt hx)
    filter_upwards [hX,hV₀,piloting D L v A b b,wholeRoom D b hZ hm _ hu,eventually_all.mpr (fun i=> (hU i).profit),eventually_all.mpr (fun i=> eventually_all.mpr (hf i))] with i hi hV hT ha hS hh;
    have hp:∃ z y,t i z y:= both U h L hG (hπ _) hi he hP (he'.trans hk.1) (mem_singleton_self _) ha hk hT.1.1 le_rfl hT.1.2 hT.2 hS hV ‹Q.Strike H l› (eventually_all.mpr (fun i' => eventually_all.mpr (hh i'))); have he: ∃ y,t i (Yp i) y:= (show Yp i= hp.choose from dif_pos hp).symm ▸hp.choose_spec; exact (show y i= he.choose from dif_pos he).symm ▸ he.choose_spec
end YM.OPE.Log.Trunk.Shuttle
