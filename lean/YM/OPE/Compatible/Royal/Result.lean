import YM.OPE.Compatible.Royal.Coupon
/-!
# Head transfer retaining explicit grade at pivot and root
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Arcade
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder
open scoped Topology BigOperators Classical
-- head buyer across certified root copies
variable {X:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F:Finset X}{m j:X→ℕ}
    {G:Gauge}{C:Family G}{p N J k b d u t:ℕ}{l:ℕ→ℕ}{A:Allot C}
    {a z:ℝ}
set_option quotPrecheck false
local notation "B"=> Site (C.side J p)
local notation "P"=> listP C p J
local notation "E"=> Mix.camp C p J
variable {o:X→ Track C.path (Site (C.side J p)) p}
variable (S: Series F m) (H:CutOrder C (listP C p J) D U m j N p (Mix.camp C p J) o b l)
   {f: Site (C.side J p)× (brim D F)→ Config G (C.side N p)→ℂ}
   (Q:Lights A (listP C p J) N p (fun i:brim D F=> finishAt D m i.val) k b (Mix.camp C p J) (fun i=>o i.val)) (y:Config G (C.side N p)→ℂ)
local notation "T!"=> birth (Names B (↥(brim D F))) (C.path.rep N p N) f
omit [Fintype X][PartialOrder X][OrderBot X] in
private lemma hat {V:Type}[Fintype V][DecidableEq V]{c0 b0:ℕ}{P':Ensemble V}{x y e0: Track C.path V p}{η:ℝ} {W:V→ Config G (C.S.side N p)→ℂ}{h' h''} (u:Finset X)
    (H: CutOrder.Head u A P' c0 N p b e0 x W η h')(he:x=y)(hv:c0=b0): CutOrder.Head u A P' b0 N p b e0 y W η h'':=by subst b0 x; exact H
include S A H
lemma finalUse (hz:m ⊥=u+1)(hv:k ≤ N)(hO:o ⊥=Mix.camp C p J)(hq:F⊆U)(hk:t ≤ u)(he:whenHigh F m < k)(hh:∀ i∈brim D F,k ≤ roof U m N i)
    (hR:Stock.Tabs.opens C.path.levels 1 J t)(hU:Expenses C D U m j l b a)(hw:∀ i,m ⊥ ≤ i→ places X ≤ A.r i)(hF:C.ref d ≤ t)
    (hV:LitUp Q (CutOrder.full (Site (C.side J p)) _) (gust C.path N p N (birth (Names (Site (C.side J p)) (↥(brim D F))) (C.path.rep N p N) f) k hv))(hT:Integrable (birth (Names (Site (C.side J p)) _) (C.path.rep N p N) f) (prior G _)) (hγ:GridApprox.room C.path.levels J u (lensScope C d))(hA:C.Makes)(hG:G.Simple) (hψ:Continuous y)(hE:m ⊥ ≤ N)
    (h':∀ i:Site (C.side J p), (center C.S p (le_trans hR.1 (hk.trans (u.le_succ.trans (hz.symm.trans_le hE)))) 0).copy i y= CutOrder.parcel (C:=C) (N:=N) (p:=p) f i)
    (hi: Interior ((center C.S p (le_trans hR.1 (hk.trans (u.le_succ.trans (hz.symm.trans_le hE)))) 0).chamber 0) y)(ht:∀ i:C.label d, Interior ((center C.S p (le_trans hR.1 (hk.trans (u.le_succ.trans (hz.symm.trans_le hE)))) 0).chamber 0) (C.O N p i 0)) (hd:0<z)(hc:z ≤ a^(F.card*(places X+places X))*∏ i,Q.bottom i) :
    ∃ Z':C.label d, Next.UVStress.quota C d u N p Z' ≤ 2*(owed C z d u) ∧ Interior ((center C.S p (le_trans hR.1 (hk.trans (u.le_succ.trans (hz.symm.trans_le hE)))) 0).chamber 0) (y-C.O N p Z' 0) ∧ (center C.S p (le_trans hR.1 (hk.trans (u.le_succ.trans (hz.symm.trans_le hE)))) 0).rootTest (C.beta N p) (y-C.O N p Z' 0) ≤ 2*(stakes C J t/rebate C z d t u):=by
    have hL := CutOrder.windfall D A H S hq f hh hv he hT Q hU hG hA hw hV
    refine draw (X:=X) (b:=b) A (show u < N from (hz.symm.trans_le hE : _+1 ≤ N)) hR hk y hF (by have ht:= H.head; omega) hG hA hγ hd hψ ht hi ?_
    -- edit
    rw [funext h']
    -- dependent index transport
    suffices he': Head ({⊥}:Finset X) A P (m ⊥) N p b E (o ⊥) (CutOrder.parcel (C:=C) (N:=N) (p:=p) f) z hE from by
       exact hat _ he' hO hz
    obtain ⟨V,hV,hU',hR⟩:= hL.ready; exact ⟨V,hV,hc.trans hU',hR⟩
end YM.OPE.Arboreal.Arcade
