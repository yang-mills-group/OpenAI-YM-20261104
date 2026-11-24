import YM.OPE.Compatible.Glades.Gust
/-! Event at highest active time. Uses only CutOrder for the n-ary planes (rather than pair elections). Simple variant buying all modes; later arbiter uses commissions (including Outgoing) directly. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.CutOrder
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset
open scoped Topology Classical
variable {X V:Type}[PartialOrder X][OrderBot X][Fintype X]
    (D:Origin X) {U Q:Finset X}{m j:X→ℕ}
open YM.OPE.Allot Series Lights
variable {G:Gauge}{C:Family G} (A:Allot C){P: Ensemble V}{l:ℕ→ℕ}
variable {N p b n:ℕ} {E:Track C.path V p}{o:X→Track C.path V p}
variable (h:CutOrder C P D U m j N p E o b l)(S:Series Q m)(hU:Q⊆U)
-- iteration billing temperatures
structure Expenses (C:Family G)(D: Origin X)(U:Finset X)(m j:X→ℕ)(l:ℕ→ℕ)(b:ℕ) (a:ℝ): Prop where
   good : 0 < a
   small : a ≤ 1
   price x : x∈ U→ a ≤ valve C (places X) b (l (m x)) (m x)
   rating x : x∈U→ a ≤ Run.Below C.path (sash C (m x)/2) (j x) (finishAt D m x)
set_option quotPrecheck false
local notation "i₀"=> whenHigh Q m
local notation "Δ"=> Series.crease D S
local notation "o₀"=>fun x : brim D Q=>o x.val
local notation "o₁"=>fun x : after D Q m=>o x.val
local notation "Χ"=> Names V ↥(brim D Q)
variable [Fintype V][DecidableEq V]
-- full Guard
variable (V) in
def full (I:Type)[Fintype I][DecidableEq I] : Guard (Names V I):=⟨fun _=>True,trivial,fun _=>trivial,fun _ _=>trivial⟩
omit [Fintype V] in
-- chordal condition
lemma full_rings (I:Type)[Fintype V][Fintype I][DecidableEq I] : (full V I).Chordal P.v P.perms:=by
   constructor; intros; simp [full]
include h hU S
lemma edges_ready (ht:∀ x∈brim D Q,n ≤ roof U m N x): Margins (full V ↥(brim D Q)) b (i₀+1) n (o₀):=by
   intro i he hi p' _ j _ k _ hj; rcases j,k with ⟨⟨j,x⟩,k,y⟩
   have hc(a : brim D Q): finishAt D m a.val < i:= lt_of_le_of_lt (high D S ((on_brim ..).mp a.2|>.2.2)) he
   have hd(a : brim D Q) :i ≤ roof U m N a.val:= hi.le.trans (ht _ a.2)
   by_cases hx:x.val=y.val
   · obtain rfl:x=y:= Subtype.ext hx; exact h.clear x.val (brim_under D U Q hU x.2) i (hc x) (hd x) j k (fun H=>hj (H ▸ rfl)) -- parser ..
   have hu' := brim_apart D Q S.base x.2 y.2 hx; exact h.gap x.val y.val (brim_under D U Q hU x.2) (brim_under D U Q hU y.2) hu' (brim_apart D Q S.base y.2 x.2 (Ne.symm hx)) i (lt_of_le_of_lt (high D S (S.base.roots (touch_par D (separate_left D hu')) ((on_brim D Q).mp x.2|>.2.2))) he) (hc x|>.le) (hc y|>.le) (hd x) (hd y) j k
omit h hU
-- reserve F facts and product formula
include S in
def attaches : Fibers (brim D Q) (after D Q m):= ⟨Series.chief D S,fun i=> (S.chef D i).choose,fun i=>(S.chef D i).choose_spec⟩
variable (f: V×(brim D Q)→ Config G (C.side N p)→ℂ)
-- name
include S in
def relayTo (i:V×(after D Q m))(W:Config G (C.side N p)) := ∏ j∈(attaches D S).contents i.2, f (i.1,j) W
-- earns lower cost and U. will reindex using frontier collapse.
include h hU
variable (ht: ∀ x∈brim D Q,n ≤ roof U m N x) (hn:n ≤ N) (hp:whenHigh Q m < n)(hF: Integrable (birth (Names V ↥(brim D Q)) (C.path.rep N p N) f) (prior G _))
variable (L : Lights A P N p (fun x:brim D Q=>finishAt D m x.val) n b E (fun x=>o x.val))
include ht hp hF
set_option maxHeartbeats 200000 in
lemma roll (hg:G.Simple)(hC:C.Makes)(hW:∀ i,m ⊥ ≤ i→ places X≤ A.r i)(hY:LitUp L (full V _) (gust C.path N p N (birth (Names V _) (C.path.rep N p N) f) n hn)) {a:ℝ}(hz:Expenses C D U m j l b a):
    let z:=i₀
    let y:=relayTo D (C:=C) S f
    Integrable (birth (Names V ↥(after D Q m)) (C.path.rep N p N) y) (prior G _)∧∃ R:Lights A P N p (fun u:after D Q m=>finishAt D m u.val) z b E (fun x=>o x.val),
       LitUp R (full V _) (gust C.path N p N (birth (Names V _) (C.path.rep N p N) y) z (hp.le.trans hn)) ∧
       (∀ i,¬ (crease D S).SingleFiber i→ let X:=R.tips i; Blade (C.path.rep N p z) (X.home P.v) (X.oil P.v) (profile (C.path.rep N p z).activities (X.gas P.v)) 0 (4*(1/R.asks i))) ∧
       a^(places X+places X)*(∏ i,L.bottom i) ≤ ∏ i,R.bottom i:=by
   intro z y; have hx:z<N:= hp.trans_le hn; have hd:= high D S S.base.base; have hh:C.ref 0 < z:= h.head.trans_le hd
   have hk(x:brim D Q):finishAt D m x.val ≤ z+1:= (high D S ((on_brim D Q).mp x.2|>.2.2)).trans z.le_succ
   have hA:= LitUp.descends L (full V _) hY hC hp hk hn (hh.trans_le z.le_succ|>.le) ⟨fun i hi hc=>h.moves.mare _ (hd.trans (z.le_succ.trans hi)) (hc.trans_le hn)⟩ (full_rings (P:=P) _) (fun i hb hc=> by
       have he : z ≤ i:=z.le_succ.trans hb; have hM:= hW i (hd.trans he)
       exact ⟨count_left D A h S hU (fun x hf=> (show i+1 ≤ n from hc).trans (ht _ hf)) (he.trans i.le_succ) hM,count_left D A h S hU (fun x hf=> hc.le.trans (ht _ hf)) he hM⟩) (edges_ready D h S hU ht)
   let L':= L.lowers hk hp; rw [drifting] at hA
   let ζ:=full V ↥(after D Q m); have hU': ∀ x∈brim D Q,z+1 ≤ roof U m N x:= fun x he=> Nat.le_trans hp (ht x he)
   have hK:= incoming D A h S hU hU' (hW _ hd); have hR:= bound D h S hU (fun x he=> z.le_succ.trans (hU' x he))
   obtain ⟨Q',hy,hLA⟩:= LitUp.event L' hA hC hg hx hh (h.moves.mare _ hd hx) hK hR (χ':=ζ) (fun _ _=>trivial)
   obtain ⟨hΩ,hZ⟩:= reuni_gust (A:=C.path) (crease D S) (attaches D S) (fun _=>rfl) hF hx.le
   rw [← gust_step _ _ _ _ _ hx,hZ] at hy
   obtain ⟨x,hX,hk'⟩:= exists_mem_eq_sup Q (begun D S) m
   refine ⟨hΩ,Q',hy,hLA.blades,bill_stock L' hLA hK.sizeP hh.le hR hz.good (show a ≤ _ from ?_) ?_ hK.sizes⟩
   · change a≤valve C _ b (l z) z; rw [show z= _ from hk']; exact hz.price x (hU hX)
   intro i hi
   have hh:=high_node D S _ hi; have hu:m i.val=z:=birth_stamp D S hh; nth_rw 1 [← hu]; exact hz.rating _ (hU (mem_inter.mp hh|>.2))
end YM.OPE.Arboreal.CutOrder
