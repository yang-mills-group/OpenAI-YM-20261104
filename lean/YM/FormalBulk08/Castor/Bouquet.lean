import YM.FormalBulk08.Castor.Vig
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Castor
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G: Gauge}{K:KernelChoices}{I X:Type}{W:Lab G K X}{ρ:ChartRatio G}{d E R m D e r:ℕ}{B:Frame G d}{Z:Frame G m}{o:Loc G 1}{P:SectionData B}{T:SectionData Z}{H:Hol G}

lemma label_reversed {U W: Anthem D G}(h:∀ p,∀ j≤ E, U p j=W p j)(k:Letter B): Through E (echo B U k) (echo B W k):= by
    intro i hi;rw [echoline,echoline]; apply Finset.sum_congr rfl; intro j _; rw [h _ _ (Nat.le_trans (Nat.sub_le ..) hi)]
lemma district [Fintype X] {Y U:X→ Anthem D G}{P Q:Matrix X I Pence}(h:∀ i p,∀ j≤ E,Y i p j= U i p j)(he:∀ i j,Through E (P i j) (Q i j))(x)(p)(j)(hp:j≤E): larch Y P x p j= larch U Q x p j:= by
    funext t; unfold larch; simp only [Finset.sum_apply,Kemp.launch,surf]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro a ha; rw [Finset.mem_antidiagonal] at ha; rw [h _ _ a.2 (by omega), he i x a.1 (by omega)]
lemma movie (X Y: Anthem D G)(ρ:ChartRatio G)(a:hue G)(x:Leaf W.scrolls)(h:∀ p,∀ j≤ E,X p j= Y p j)(p)(d t)(he:e≤E): mover ρ a x d t X p e=mover ρ a x d t Y p e:= by
   funext r; unfold mover stir Wine.stamp; apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi; exact congr_arg (_ • ·) (quo_eq x _ _ _ _ _ _ (fun _ _=> rfl) h p _ i r (by omega))
-- argument rescale across higher window

def liquidate (ρ:ChartRatio G)(a:hue G)(x:Leaf W.scrolls) (B:Pence):Pence:= B.subst (runic (haloO ρ a x))
lemma moves {P:Pence}(u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(x:Leaf W.scrolls):
     Priced staticT (coinR x) (fun i=> Roof.reborn a (destination (W.V x.a) (seqN x i) x.b) (W.wood x.a x.b) K (nations ρ a x i) ρ (W.toEmpire.bill x.a x.b) P) (fun _=> liquidate ρ a x P) E := by
   let S n:=scalar a (eating ρ a W (fun _=>seqN x n) x.a x.b); obtain ⟨hx,hw⟩:= (solar a u h hs x).goods (sunlight a h hs x) (fun _=> freshK a u h hs x)
   have hA i: Roof.reborn a (destination (W.V x.a) (seqN x i) x.b) (W.wood x.a x.b) K (nations ρ a x i) ρ (W.toEmpire.bill x.a x.b) P=P.subst (PowerSeries.X*bookH (S i)):= by rw [rele,mul_comm];rfl
   simp_rw [hA,liquidate,←forward_green];exact (Priced.constant staticT _ P E).by_order ((transit hx).le (Nat.le_succ _)) (fun i=>bottomless _) (fun i=>bottomless _)
variable (h:Quota B H W o D E R)(q:Quota Z H W o D E R)(u:Use W ρ E)(v:LocalRatio ρ) (a:hue G)(hg:G.Simple)(hp:P.Sound H)(hK:Bid.pop P)(ht:T.Sound H)(hb:Bid.pop T)(hk:m≤ d)(hr:d≤R)(x:Leaf W.scrolls)
-- Lift low matrix data through high graph using constant coupling resubstitution
include h u v hg hp hK hr
lemma scintillate (i:I)(U:Matrix (Letter B) I Pence)(p:Studio D)(he:e≤ E) (r):
     let Y:= issue W ρ a B P h.horizon x.a (x.b+1)
     mover ρ a x d d (larch Y U i) p e r=larch (mover ρ a x d d ∘ Y) (U.map (liquidate ρ a x)) i p e r:= by
   intro Y; let A n:=bornY ρ W a B P h.horizon x.a (seqN x n) (x.b+1); let Z(n:ℕ):= destination (W.V x.a) (seqN x n) x.b; let V:= W.wood x.a x.b; let Q n:=Roof.reborn a (Z n) V K (nations ρ a x n) ρ (W.toEmpire.bill x.a x.b); let f n:=migrates (D:=D) a (Z n) V K (nations ρ a x n) ρ (W.toEmpire.bill x.a x.b) (growL _ _) d d
   have hu n (j:Letter B): Wade o (A n j) d := ((birth a v h hg hp hK x.a (x.b+1) (seqN x n) (x.zone.trans (Nat.le_succ _)) (by unfold seqN;omega)).officers j).fare.through (slotsFits ..)
   have hh : Brass staticT o (fun _=>W.windowD x) (coinR x) (fun _=>1) (fun n p=>f n (larch (A n) U i) p e r) (fun _ p=>mover ρ a x d d (larch Y U i) p e r) := by refine springL u v a hg x d (fun n=>larch (A n) U i) _ (fun e ht r=>orbit_match (T:=A) i (fun _ ht r j=>pantry_prices h u v a hg hp hK hr ht j r (porch x)) (fun _=> Priced.constant _ _ _ E) ht) he r d
   have hx : Brass staticT o (fun _=>W.windowD x) (coinR x) (fun _=>1) (fun n p=> larch (f n∘ A n) (U.map (Q n)) i p e r) (fun _ p=> larch (mover ρ a x d d ∘ Y) (U.map (liquidate ρ a x)) i p e r):= orbit_match (S:=fun _=>mover ρ a x d d ∘ Y) i (fun _ he r j=>ruled h u v a hg hp hK hr x he j r d) (fun _=> Castor.moves u v a hg x) he
   have hz n : f n ∘ larch (A n) U=larch (f n ∘ A n) (U.map (Q n)) := by refine hammers ρ a _ _ _ _ _ _ _ _ _ _ (hu n) (genu (W.V x.a) (W.wood x.a) _ _ _ v hg (N:=seqN x n) (i:=x.b+1) (by unfold seqN;omega)).toStory ((W.V x.a).clock.adm _) v
   ext1 t; refine tendsto_nhds_unique (sarking hh p (u.zero x).le (coinD x) (coinP x)|>.shares t) ((sarking hx p (u.zero x).le (coinD x) (coinP x)|>.shares t).congr' (.of_forall fun n=>?_));rw [←hz];rfl
end YM.FormalBulk08.Castor
