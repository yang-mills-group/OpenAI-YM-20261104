import YM.FormalBulk08.Castor.Bouquet
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Castor
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G: Gauge}{K:KernelChoices}{I X:Type}{W:Lab G K X}{ρ:ChartRatio G}{d E R m l D e r:ℕ}{B:Frame G d}{Z:Frame G m}{o:Loc G 1}{P:SectionData B}{T:SectionData Z}{H:Hol G}
lemma postage [Fintype X] (F:Frame G d)(Y:X→ Anthem D G)(T:Matrix X I Pence)(hp:∀ i, Wade o (sliceM (Y i) E) l)(u:Letter F)(j:I): Through E (pantry F (larch Y T) u j) ((pantry F Y*T) u j):= by
   let M i:=sliceM (Y i) E
   have he i p n (hn:n≤E): Y i p n=M i p n:= (if_pos hn).symm
   refine Through.trans (label_reversed (fun p e hv=> district (U:=M) (P:=T) he (fun _ _=>Through.exact_eq _ _) j p e hv) u) ?_
   change Through E (pantry F (larch M T) u j) _; rw [pantry_handle F _ hp,Matrix.mul_apply,Matrix.mul_apply]; exact Through.finsetSum (fun i _=> (label_reversed (fun p j hj=> (he i p j hj).symm) u).mul (Through.exact_eq _ _))
lemma mints {Y: Roof.Plaza B D} (hp:∀ i,Wade o (sliceM (Y i) E) l)(hu:∀ i j,Through E (pantry B Y i j) ((1:Tilework B) i j))(M:Matrix (Letter B) I Pence)(x:Letter B)(p:I): Through E (pantry B (larch Y M) x p) (M x p):= by
   have hh:M x p=((1:Tilework B)* M) x p:=by rw [Matrix.one_mul]
   refine (postage B Y M hp x p).trans ?_
   rw [hh,Matrix.mul_apply,Matrix.mul_apply]; exact Through.finsetSum (fun _ _=> (hu x _).mul (Through.exact_eq _ _))
lemma larch_scale [Fintype X](Y:X→ Anthem D G)(T:Matrix X I Pence)(c:ℝ) (i:I):larch Y (C c • T) i=c • larch Y T i:=by unfold larch; rw [Finset.smul_sum];apply Finset.sum_congr rfl; intro j _; change launch (C c* T j i) _=_;rw [← launch_launch,launch_C]
variable (h:Quota B H W o D E R)(q:Quota Z H W o D E R)(u:Use W ρ E)(v:LocalRatio ρ) (a:hue G)(hg:G.Simple)(hp:P.Sound H)(hK:Bid.pop P)(ht:T.Sound H)(hb:Bid.pop T)(hk:m≤ d)(hr:d≤R)(x:Leaf W.scrolls)
include h q u v a hg hp hK ht hb hk hr
lemma curling (z y:Letter Z): Through E ((GateM W a ρ Z B P h.horizon x*GateM W a ρ B Z T q.horizon x) z y) ((1: Tilework Z) z y):= by
    let b:= x.b; let W':= issue W ρ a B P h.horizon x.a b;let T':= issue W ρ a Z T q.horizon x.a b; let L:= GateM W a ρ B Z T q.horizon x
    have hy p j (h':j≤ E): T' y p j=larch W' L y p j:= funext (nests h q u v a hg hp hK ht hb hk hr x y p h')
    exact (postage Z W' L (fun i => (rations_limit h u v a hg hp hK hr i x).1.through (slotsFits B i)) z y).symm.trans ((label_reversed hy z).symm.trans (stipulated q u v a hg ht hb (hk.trans hr) x z y))
omit h hp hK in
lemma turntable (p:Studio D)(i:Letter Z)(he:e≤E)(r) :
    let A:=issue W ρ a Z T q.horizon x.a (x.b+1) i
    let L:= (W.V x.a).S.block x.b; mover ρ a x m m A p e r=(smaller L m d • mover ρ a x d d A) p e r:= by
    intro A L; let f n:=destination (W.V x.a) (seqN x n) x.b
    let Q n := bornY ρ W a Z T q.horizon x.a (seqN x n) (x.b+1) i
    let V(n e):= migrates a (f n) (W.wood x.a x.b) K (nations ρ a x n) ρ (W.toEmpire.bill x.a x.b) (growL _ _) e e (Q n)
    have hx n : V n m= smaller L m d • V n d:= by
       refine points (o:=o) ρ _ _ _ _ _ _ _ v (genu (W.V x.a) (W.wood x.a) _ _ a v hg (N:=seqN x n) (i:=x.b+1) (by unfold seqN;omega)).toVivid hk (clef_through ?_ (slotsFits Z i)); exact (birth a v q hg ht hb x.a (x.b+1) (seqN x n) (x.zone.trans (Nat.le_succ _)) (by unfold seqN;omega)).officers i
    have hh t: Brass staticT o (fun _=>W.windowD x) (coinR x) (fun _=>1) (fun n p=>V n t p e r) (fun _ p=>mover ρ a x t t A p e r):= springL u v a hg x t _ _ (fun _ h r=> pantry_prices q u v a hg ht hb (hk.trans hr) h i r (porch x)) he r t
    ext w; exact tendsto_nhds_unique (sarking (hh m) p (u.zero x).le (coinD x) (coinP x)|>.shares w) ((((sarking (hh d) p (u.zero x).le (coinD x) (coinP x)|>.shares w).const_mul (smaller L m d))).congr' (.of_forall (fun n=>by dsimp only; rw [hx n];rfl))) -- may need change
lemma walk_diagram (i:Letter Z)(j:Letter B):
    let p:=GateM W a ρ B Z T q.horizon;let V:= p x; let Q:= p (porch x)
    Through E ((V*tableau Z a ρ T q.horizon x) j i) ((PowerSeries.C (smaller ((W.V x.a).S.block x.b) m d) • (tableau B a ρ P h.horizon x* Q.map (liquidate ρ a x))) j i):= by
   intro p V Q; let U:=issue W ρ a B P h.horizon x.a x.b; let Z' :=issue W ρ a B P h.horizon x.a (x.b+1)
   let T':=issue W ρ a Z T q.horizon x.a x.b; let W':=issue W ρ a Z T q.horizon x.a (x.b+1)
   let t:=tableau B a ρ P h.horizon x; let k:= tableau Z a ρ T q.horizon x;let y:= Q.map (liquidate ρ a x);let c:=smaller ((W.V x.a).S.block x.b) m d
   have he(φ:Studio D)(e:ℕ)(he:e≤E): larch U (V*k) i φ e=larch U (C c •(t*y)) i φ e:= by
       have hu j p k hk': T' j p k=larch U V j p k:= funext (nests h q u v a hg hp hK ht hb hk hr x j p hk')
       have hU i p k hP: W' i p k=larch Z' Q i p k:= funext (nests h q u v a hg hp hK ht hb hk hr (porch x) i p hP)
       have hh(j:Letter B)(p)(k)(hk:k≤E): (mover ρ a x d d ∘ Z') j p k=larch U t j p k:= funext (clapper h u v a hg hp hK hr x j p hk)
       rw [←larch_circuit,←district (U:=larch U V) (Y:=T') (P:=k) (Q:=k) hu (fun _ _=>Through.exact_eq _ _) i φ e he]
       ext1 r; rw [show larch T' k i φ e r=mover ρ a x m m (W' i) φ e r from (clapper q u v a hg ht hb (hk.trans hr) x i φ he r).symm]; rw [show mover ρ a x m m (W' i) φ e r=c • mover ρ a x d d (W' i) φ e r from turntable q u v a hg ht hb hk hr x φ i he r,larch_scale, ←larch_circuit, movie (W' i) _ ρ a x (hU i) φ d d he, show mover ρ a x d d _ φ e r=_ from scintillate h u v a hg hp hK hr x i Q φ he r, district (Q:=y) hh (fun _ _=> Through.exact_eq _ _) i φ e he]; rfl
   have hh i: Wade o (sliceM (U i) E) d:=(rations_limit h u v a hg hp hK hr i x).1.through (slotsFits B i)
   exact (mints hh (stipulated h u v a hg hp hK hr x) _ j i).symm.trans ((label_reversed he j).trans (mints hh (stipulated h u v a hg hp hK hr x) _ j i))
end YM.FormalBulk08.Castor
