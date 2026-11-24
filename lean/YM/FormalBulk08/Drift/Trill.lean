import YM.FormalBulk08.Drift.Evolve
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Drift
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{X:Type}{K:KernelChoices}{W:Lab G K X}{ρ:ChartRatio G}{E e r m d D j t R:ℕ}{o:Loc G 1}{F:Frame G d}{H:Hol G}{T:SectionData F}
def mover (ρ:ChartRatio G)(a:hue G)(x:Leaf W.scrolls)(d l:ℕ)(Y: Anthem D G) : Anthem D G:=
    stir (bookH (haloO ρ a x)) (bookU (haloO ρ a x)) (quickHat ρ x d l (heir a ρ W x.a (x.b+1)) Y)
-- cost static finite; horizon in charges
variable (q:Quota F H W o D E R)(u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb: Bid.pop T)(hr:d≤ R)(x:Leaf W.scrolls)
include q u h a hs ht hb hr
omit q ht hb hr in
lemma springL (d:ℕ)(p0:ℕ→ Anthem D G)(V0:Anthem D G)(H0:∀ j≤ E,∀ k,Brass staticT o (fun _=>W.windowU x) (coinR x) (fun _=>1) (fun m p=>p0 m p j k) (fun _ p=>V0 p j k))(he:e≤E)(r t:ℕ):
    let N:=fun j=>destination (W.V x.a) (seqN x j) x.b
    Brass staticT o (fun _=> W.windowD x) (coinR x) (fun _=>1)
       (fun n p=> migrates a (N n) (W.wood x.a x.b) K (nations ρ a x n) ρ (W.toEmpire.bill x.a x.b) (growL _ _) d t (p0 n) p e r) (fun _ p=> mover ρ a x d t V0 p e r):= by
    intro N; let f(i:ℕ):= scalar a (eating ρ a W (fun _=>seqN x i) x.a x.b); let g:= haloO ρ a x
    obtain ⟨hA,hP⟩:=Priced.goods (solar a u h hs x) (sunlight a h hs x) (fun _=> freshK a u h hs x)
    unfold Brass mover migrates stir Wine.stamp; apply matched_sums _; intro i' hi; rw [Finset.mem_range] at hi; exact Matched.amp (countedWing (e:=i') u h a hs (by omega) x d _ _ H0 t r) (hA.income hP _ _ r (by omega))
lemma ruled (he:e≤E)(i:Letter F)(r t:ℕ):
    let N:=fun j=>destination (W.V x.a) (seqN x j) x.b
    Brass staticT o (fun _=> W.windowD x) (coinR x) (fun _=>1)
       (fun n p=> migrates a (N n) (W.wood x.a x.b) K (nations ρ a x n) ρ (W.toEmpire.bill x.a x.b) (growL _ _) d t (bornY ρ W a F T q.horizon x.a (seqN x n) (x.b+1) i) p e r) (fun _ p=> mover ρ a x d t (issue W ρ a F T q.horizon x.a (x.b+1) i) p e r):= springL u h a hs x d _ _ (fun _ hj k=>pantry_prices q u h a hs ht hb hr hj i k (porch x)) he r t
omit q u h a hs ht hb hr
def tableau (F:Frame G d)(a:hue G)(ρ:ChartRatio G)(T:SectionData F)(hd:d+1≤D)(x:Leaf W.scrolls): Tilework F := pantry F (mover ρ a x d d ∘ issue W ρ a F T hd x.a (x.b+1))
include q u h a hs ht hb hr
lemma terraceF (i j:Letter F): Priced staticT (coinR x) (fun n=> bornM (ρ:=ρ) (T:=T) (W:=W) a q.horizon x.a (seqN x n) x.b i j) (fun _=> tableau F a ρ T q.horizon x i j) E:=
    mana (T:=fun n=> migrates a (destination (W.V x.a) (seqN x n) x.b) (W.wood x.a x.b) K (nations ρ a x n) ρ (W.toEmpire.bill x.a x.b) (growL _ _) d d (pinks (T:=T) (ρ:=ρ) q a x n j)) F (fun _ he r=>ruled q u h a hs ht hb hr x he j r d) (u.zero x) i -- Q
lemma origins (i: Letter F)(he:e≤ E)(r) : Brass staticT o (fun _=>W.windowD x) (coinR x) (fun _=>1) (fun n p=> bornY ρ W a F T q.horizon x.a (seqN x n) x.b i p e r) (fun _ p=>issue W ρ a F T q.horizon x.a x.b i p e r):= by
   have V:= pantry_prices q u h a hs ht hb hr he i r x; -- avoid W
   have hh (i:ℕ): fare_n x (i+1+x.b)≤coinR x i:=by
       rw [show i+1+x.b=seqN x i by unfold seqN;omega]; change ratioR _ (seqN x i) x.b targetPower≤ ratioR (W.V x.a).S (seqN x i) (x.b+1) targetPower; unfold ratioR;gcongr
       all_goals first|exact targetPower_pos.le| exact (W.V x.a).S.strictAnti.antitone (Nat.le_succ _)| exact div_nonneg (Schedule.a_pos ..).le (Schedule.a_pos ..).le|exact Schedule.a_pos ..| exact (Schedule.a_pos ..).le
   have H:=brass_fold (p:=fun i:ℕ=>i+1) (soft_coin staticT 1) V hh; simp_rw [show ∀ n,seqN x n=n+1+x.b from fun n=>by unfold seqN;omega]; exact H
lemma stipulated (i j:Letter F): Through E (pantry F (issue W ρ a F T q.horizon x.a x.b) i j) ((1:Tilework F) i j):= by
   let f n:= bornY ρ W a F T q.horizon x.a (seqN x n) x.b j
   have hh:Priced staticT (coinR x) (fun n=> echo F (f n) i) (fun _=> pantry F (issue W ρ a F T q.horizon x.a x.b) i j) E:= mana F (fun e he r=> origins q u h a hs ht hb hr x j he r) (u.zero x) i
   intro e he; refine tendsto_nhds_unique (quietP (coinD x) (coinP x) (hh _ he)) (tendsto_const_nhds.congr' (.of_forall fun n=>?_)); have he: echo F (f n) i=if i=j then 1 else 0:=(birth a h q hs ht hb _ _ (seqN x n) x.zone (by unfold seqN;omega)).city i j
   dsimp only; rw [he,Matrix.one_apply]
lemma clapper (i: Letter F)(p:Studio D)(he:e≤E)(r):
    mover ρ a x d d (issue W ρ a F T q.horizon x.a (x.b+1) i) p e r=larch (issue W ρ a F T q.horizon x.a x.b) (tableau F a ρ T q.horizon x) i p e r:= by
    let V N:= bornY ρ W a F T q.horizon x.a (seqN x N) x.b
    let U:=fun N=> bornM (T:=T) (W:=W) (ρ:=ρ) a q.horizon x.a (seqN x N) x.b
    have hz(v) := sarking (orbit_match (T:=V) (Q:=U) i (fun e he r y=> origins q u h a hs ht hb hr x y he r) (fun j=>terraceF q u h a hs ht hb hr x j i) (r:=r) he) p (u.zero x).le (coinD x) (coinP x)|>.shares v
    ext w; refine tendsto_nhds_unique (sarking (ruled q u h a hs ht hb hr x he i r d) p (u.zero x).le (coinD x) (coinP x)|>.shares w) ((hz w).congr' (.of_forall fun n=>?_));
    have hN:= mat_begins a h q hs ht hb x.a x.b (seqN x n) x.zone (by unfold seqN;omega); exact congr_fun (congr_fun (congr_fun (congr_fun (congr_fun hN.2 i) p) e) r) w
end YM.FormalBulk08.Drift
