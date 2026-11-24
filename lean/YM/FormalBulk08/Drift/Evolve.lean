import YM.FormalBulk08.Drift.Stout
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Drift
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{X:Type}{K:KernelChoices}{W: Lab G K X}{ρ:ChartRatio G}{E e r m n l d D R:ℕ}{o: Loc G 1}{F: Frame G d}{H:Hol G}{T:SectionData F}
-- limit post mean includes xy line. dictionary rooted at ancestor. no new Gaussian hypothesis

def liftHat (x:Leaf W.scrolls)(Z:Tile (edgeL G) r): Tile (Biglot (BoardL G (W.pat x) (W.wood x.a x.b))) r := pearl (lands (limY x)) (pearl (lands (pane G (W.pat x) (W.wood x.a x.b))) (pearl (lands (winging (Rim G (W.pat x)) (Loc G 1))) (jetty (Bank.scroll ((W.pat x).L) (Loc G 1)).symm Z)))
-- canon pivot fixed patch using count dimension, output root summation. use full M and stopper. read suppression hp independent.

def quickHat (ρ: ChartRatio G)(x:Leaf W.scrolls)(d l:ℕ)(M: Pot G)(Y: Anthem D G) : Anthem D G:= fun p e r=>
    let s:= (W.V x.a).S; let P:= destination (W.V x.a) x.b x.b
    aven (s.block x.b) d • ∑ i:Site (s.block x.b),∑ j∈Finset.range (l+3*e+1), jetty (coastRight _ _ _)
       (dipper (lands (limG x)) (swim (lands (limG x)) (camp ρ x M)) (fun e r=> liftHat x (stepsong P Y (growL (W.V x.a) x.b) p i e r)) j e r)
-- remove unused a
lemma quo_eq (x:Leaf W.scrolls)(d l)(M S:Pot G)(U Y: Anthem D G)(hm :∀ j≤ E,M j=S j)(hv:∀ p j,j≤E→ U p j= Y p j)(p)(ρ)(e r)(he:e≤ E): quickHat ρ x d l M U p e r=quickHat ρ x d l S Y p e r:= by
   dsimp only [quickHat]; apply congr_arg; apply Finset.sum_congr rfl;intro j _; refine Finset.sum_congr rfl fun i _=>?_; apply congr_arg (jetty _); apply congr_fun _ r; refine through_dip _ _ _ _ _ (fun n=> through_swim _ _ _ n E ?_) (fun e he=> ?_) i e he
   · intro i hi; funext r; unfold camp; split; rfl; unfold ouzo Bank.atlas altitude; rw [hm i hi]
   funext r; apply congr_arg; unfold stepsong Kemp.work; rw [hv _ _ ‹e ≤ E›] -- confusion

variable (q:Quota F H W o D E R)(u:Use W ρ E)(h: LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:d≤R)(he:e≤E)(i:Letter F)(x:Leaf W.scrolls)
abbrev pinks (m:ℕ):= bornY ρ W a F T q.horizon x.a (seqN x m) (x.b+1)
-- T implicit declaration maybe result inferred `i`
include q u h a hs ht hb hr he
omit q ht hb hr in
lemma countedWing (d:ℕ) (p0:ℕ→Anthem D G)(V0:Anthem D G)(H0:∀ j ≤ E,∀ k,Brass staticT o (fun _=>W.windowU x) (coinR x) (fun _=>1) (fun m p=>p0 m p j k) (fun _ p=> V0 p j k)) (t r:ℕ): Brass staticT o (fun _=> W.windowD x) (coinR x) (fun _=>1)
    (fun b p=> quick (destination (W.V x.a) (seqN x b) x.b) (W.wood x.a x.b) (nations ρ a x b) (p0 b) ρ (W.toEmpire.bill x.a x.b) (growL _ _) d t p e r) (fun _ p=> quickHat ρ x d t (heir a ρ W x.a (x.b+1)) V0 p e r):= by
    let L:= (W.pat x).L; let P m:= destination (W.V x.a) (seqN x m) x.b; let V:= W.wood x.a x.b; let Z (m:ℕ):= p0 m; let U:= V0; let o': Biglot (BoardL G (W.pat x) V) := coastRight _ _ _ (0,o);let M:=heir a ρ W x.a (x.b+1);let Q:=stopper M E
    have hx n : Vivid (nations ρ a x n):=(genu (W.V x.a) (W.wood x.a) _ ρ a h hs (N:= seqN x n) (i:=x.b+1) (by unfold seqN;omega)).toVivid
    have hv: Fiery (camp ρ x Q):= blizzard x (North.born a (porch x) u h hs) h
    let Y:= fun i:ℕ=>lands (booket x i); let g:=lands (limG x);let η:=W.windowD x;let σ:= W.windowU x
    have he'(_ :ℕ):0≤η := (u.zero x).le; have ht':= graspG x u
    have hh(t k) (hq:t≤ E)(v:Site L):
        Matched staticT (fun _=>fame _) (fun _ (_:Studio D)=>o') (fun _=> η) (coinR x) (fun _ p=>1*‖p‖) (fun m p=> coves K (P m) V (stepsong (P m) (Z m) (growL _ _) p v) t k) (fun _ p=> liftHat x (stepsong (P 0) U (growL _ _) p v t k)) := by
       let y:X:=x.a
       let G1:= winging (Rim G (W.pat x)) (Loc G 1); let G2:= pane G (W.pat x) V; let d' m p:= stepsong (P m) (Z m) (growL _ _) p v t k
       let D':=stepsong (P 0) U (growL _ _); let O:=scroll L (Loc G 1) (lift v,o)
       have H:= H0 t hq k
       -- build with leaner for fixed v; hp freeze
       have Hz: Matched staticT (fun _=>fame _) (fun _ _=>(lift v,o)) (fun _=> σ) (coinR x) (fun _ (p:Studio D)=>1*‖p‖) (fun m p=> stepsong (P m) (Z m) (growL _ _) p v t k) (fun _ (p:Studio D)=> stepsong (P 0) U (growL _ _) p v t k):= by
           let C:= destination (W.V x.a) x.b x.b; have hm : (P 0).patch=C.patch:=rfl
           let F : ℕ→Flight (W.upper x) (W.lower x):=fun _=>P 0
           have hw:=brass_at (F:=F) (T:=Z) (Y:=fun _=>U) (fun _=>(P 0).wing) (fun _=>(P 0).wing) (fun _=> growL _ _) H (fun _=>zero_le_one) (coinP x)
           obtain ⟨⟨A,p,t,M⟩,⟨B,b,r,R⟩,C,c,y,W⟩:=hw
           exact ⟨⟨_,p,t,fun i u=>M i (u,v)⟩,⟨_,b,r,fun i u=>R i (u,v)⟩,_,c,y,fun i u=>W i (u,v)⟩
       have h1:= (Hz.scrolls (P:=fun _=> L) he' (fun _=>(W.turn_whose u x).ship) (soft_coin _ _)); have h2:ease (V:=fun _=> Rim G (W.pat x)) staticT (fun _=>η) (fun _=> G1):=⟨_,soft_coin _ 1,fun _=>zero_le_one,fun _=>wing_strip η⟩; have h3:ease (V:=fun _=> Board G (W.pat x)) staticT (fun _=>η) (fun _=>G2):=⟨_,soft_coin _ 1,fun _=>zero_le_one,fun _=> pane_pay V η⟩
       have he: Matched staticT (fun _=>fame _) (fun _ (_:Studio D)=> (O.1,Sum.inr o)) (fun _=> η) (coinR x) (fun _ p=>1*‖p‖) (fun i p=> coves K (P i) V (stepsong (P i) (Z i) (growL _ _) p v) t k) (fun _ p=> liftHat x (D' p v t k)) := (((h1.gift he' (maori_constant h2) (soft_coin _ (Fintype.card (Board G (W.pat x)):ℝ)) (coinP x) (fun _ _=> Sum.inr o)).gift he' (maori_constant h3) (soft_coin _ (Fintype.card (BoardL G (W.pat x) V):ℝ)) (coinP x) (fun _ _=>Sum.inr o)).gift he' (meet_land x u) (soft_coin _ _) (coinP x) (fun _ _=>Sum.inr o))
       have hy : (O.1,Sum.inr o)=o' := congr_arg (coastRight _ _ _) (chief_h (P:=P 0) o v)
       rw [←hy]; exact he
    let w(t:Site L)p:=stepsong (P 0) U (growL _ _) p t
    have ht (v:Site L)(k:ℕ):Matched staticT (fun _=>fame _) (fun _ (_:Studio D)=>o') (fun _=>η) (coinR x) (fun _ p=>1*‖p‖) (fun m p=>border (P m) V (nations ρ a x m) (stepsong (P m) (Z m) (growL _ _) p v) ρ (W.toEmpire.bill x.a x.b) k e r) (fun _ p=> dipper g (swim g (camp ρ x Q)) (fun j r=> liftHat x (w v p j r)) k e r) := by
       by_cases hy:k=0
       · subst k; unfold border; simp_rw [dipper_first]; exact hh e r he v
       refine concentric (Z:= fun b=> cola (nations ρ a x b) ρ (P b) V K) (W:=fun _=>camp ρ x Q) (T:=fun i (p : Studio D)=> coves K (P i) V (stepsong (P i) (Z i) (growL _ _) p v)) (S:=fun _ p j r=> liftHat x (w v p j r)) (R:=fun _=>fame (BoardL G (W.pat x) V)) k e r (e:=e) (r:=r) (graspG x u) he' (fun i=>fairy _ _ (P i) V K (hx i) h) (fun _=>hv) (Or.inr ⟨rfl,rfl,Nat.pos_of_ne_zero hy⟩) ?hp (fun j k h=> hh _ _ (by unfold precede at h;omega) v)
       intro n i k hz Hk
       exact fares_hop he' (fun i=>fairy _ _ (P i) V K (hx i) h) ht' (fun _=>hv) (fun b r' a' z Hk' hQ=> stellar a x u h hs (show b≤ E from (show b≤ e by unfold precede at *;omega).trans he) (z:=⟨0,a'⟩)) n i k (orbit_access_e e i n k hz Hk) Hk -- define
    simp_rw [show ∀ p: Studio D,quickHat ρ x d t (heir a ρ W x.a (x.b+1)) V0 p e r=quickHat ρ x d t Q U p e r from fun p=>quo_eq x d t M Q U U (fun i hi=>(if_pos hi).symm) (fun _ _ _ =>rfl) p ρ e r he]
    unfold Brass quick quickHat; simp only [Pi.smul_apply, Finset.sum_apply,braise];
    let H  (i:ℕ) (v:Site L) m (p:Studio D):= jetty (coastRight _ _ _) (border (P m) V (nations ρ a x m) (stepsong (P m) (Z m) (growL _ _) p v) ρ (W.toEmpire.bill x.a x.b) i e r)
    let X i v (p:Studio D):= jetty (coastRight _ _ _) (dipper g (swim g (camp ρ x Q)) (fun j r=> liftHat x (w v p j r)) i e r)
    have hv: Matched staticT (fun _=>fame _) (fun _ _=>(0,o)) (fun _=>η) (coinR x) (fun _ p=>1*‖p‖) (fun i p=>∑ v:Site L,∑ k∈Finset.range (t+3*e+1),H k v i p) (fun _ p=> ∑ v:Site L,∑ k∈Finset.range (t+3*e+1),X k v p):= by
        apply matched_sums Finset.univ; intro v _; apply matched_sums _; intro i _; exact Matched.jet (o:=fun _ _=>(0,o)) (ht v i)
    exact hv.amp (Pact.coin staticT (coinR x) (aven L d))
where
    orbit_access_e (e i n k:ℕ)(hz:i≤ e)(hk:0<k): orbit_access e 0 i k n:= Or.inl (by unfold precede;omega)
lemma counted (t r:ℕ): Brass staticT o (fun _=> W.windowD x) (coinR x) (fun _=>1)
    (fun b p=> quick (destination (W.V x.a) (seqN x b) x.b) (W.wood x.a x.b) (nations ρ a x b) (bornY ρ W a F T q.horizon x.a (seqN x b) (x.b+1) i) ρ (W.toEmpire.bill x.a x.b) (growL _ _) d t p e r) (fun _ p=> quickHat ρ x d t (heir a ρ W x.a (x.b+1)) (issue W ρ a F T q.horizon x.a (x.b+1) i) p e r):= countedWing u h a hs he x _ _ _ (fun _ hj k=>pantry_prices q u h a hs ht hb hr hj i k (porch x)) t r
end YM.FormalBulk08.Drift
