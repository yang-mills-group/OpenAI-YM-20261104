import YM.OPE.Compatible.Pendulum.OpenAir
/-!
# Pick matching terms at one rooted layout with covered shifted view.

Validity in the p,N eventual sense (V_0 tilt verified *inside*
the common fixed mesh W, afterwards finer sites). Actual bounds
on BOTH balance norms for same choice of signed readout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open scoped Topology BigOperators Classical
variable {X I : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F K:Finset X}{m j s':X→ℕ}{l:ℕ→ℕ}
   {G:Gauge}{C:Family G}{p J s t k N b i n W d e:ℕ}{A:Allot C}
    {y:X→ Cover}(S:Wave m U K (k+1))(S':Wave m K F k)(x:brim D F)(hP:x.val∈brim D K)(hX:x.val∈U)
set_option quotPrecheck false
local notation "B"=> Site (C.side J p)
local notation "H!"=> places X+Fintype.card (C.labels.level d).Index
local notation "Z"=>fun N p i=>Cells.location C.S W N p (y i)
local notation "Ψ"=> fun (N p:ℕ)(i:X)=> Cells.location C.S W N p (y i - y x.val)
local notation "j'"=>fun a=>min (j a) (m a)
local notation "μ"=>fun i=>81*(l i+1)
variable (v:brim D U→ C.book.Token)(u:brim D U→ℝ){r Q a c z:ℝ}
local notation "Y"=>fun i:brim D U=>Run.Below C.path (u i) (s' i.val+1) (finishAt D m i.val)
local notation "q"=> fun i:brim D U=>(v i).1
local notation "F!"=>fun i:brim D U=>(v i).2
variable (h:Positioned C D U m j b J W l y)(hj:m x.val=k+1) (hh:j x.val≤ k) (hν:∀ a∈allUp D U,8*‖C.S.gridPoint W (y a-y x.val)‖≤ C.S.a J)
private lemma Interior.all {J:Type} (W:J→ Config G (C.S.side N p)→ℂ)(x: Finset J)(t: Set (Site (C.S.side N p)))(hp:∀ i∈ x,Interior t (W i)):Interior t (∏ i∈x,W i):=by rw [show (∏ i∈x,W i)=fun U=>∏ i∈x,W i U from funext fun _=>Finset.prod_apply ..]; exact Interior.combines W x hp
include S S' hP hX h hj hh hν
set_option maxHeartbeats 200000 in
lemma dual_marched (hA:C.Makes)(hg:G.Simple)
    (hk:C.ref d < j x.val)(hb:1≤ b)(ht':d ≤ b)(ht:∀ i,k ≤ i→ 2*(places X+Fintype.card (C.labels.level d).Index)≤ A.r i)
    (hT: Taxes C D U m (fun i=>min (j i) (m i)) (fun i=>81*(l i+1)) k H! b c)
    (hU:∀ i, 0<u i)(hU':∀ i:brim D U,C.ref (v i).1 ≤ s' i.val ∧ s' i.val+1=j i.val)
    (he:0<z)(hw:z≤ feedS D S Y H! c (⟨x.val,hP⟩:brim D K))
    (hK:Stock.Tabs.opens C.path.levels 1 J s)(hK':Stock.Tabs.opens C.path.levels 1 J t)(hz:m ⊥=n+1)(htN:t ≤ n)(hη:s<k)(hh₁ : C.ref d ≤ s)(hh': C.ref e ≤ t)
    (hx:0<r) (hxA:r ≤ c*badge_fee C z k)(hΦ:r*(2*owed C z d k) ≤ c^2 * ballot C k d)(hμ:r*‖alto C.path k d‖*owed C z d k ≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels d k)
    (hR: GridApprox.room C.path.levels J n (lensScope C e))(hM:Expenses C D U m (fun i=>min (j i) (m i)) (fun i=>81*(l i+1)) b a) (hl:∀ i,m ⊥ ≤ i→ places X ≤ A.r i)
    (ha:0 < Q)(hY: Q ≤ a^(F.card*(places X+places X))* (Run.Below C.path ((lantern C.path r d k (j x.val))/2) (j x.val) (finishAt D m x.val)*(∏ i∈univ.erase x,feedS D S' (feedS D S Y H! c) H! c i))) :
    ∀ᶠ p:ℕ in atTop,∀ᶠ N:ℕ in atTop,
     (∀ i:brim D U, 2*u i * Next.Rank.Spindle.paid C (v i).1 (j i.val) N p (v i).2 ≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels (v i).1 (j i.val)) →
     ∃ T:C.label d, Next.UVStress.quota C d k N p T ≤ 2*owed C z d k∧ Cards.PaidAt C.S N p J (C.beta N p) (stakes C J s/ lantern C.path r d k s) (shop D q F! x.val (Ψ N p) T) ∧ ∃ V:C.label e, Next.UVStress.quota C e n N p V ≤ 2*owed C Q e n∧ Cards.PaidAt C.S N p J (C.beta N p) (2*(stakes C J t / rebate C Q e t n)) ((shop D q F! x.val (Z N p) T*peers D (N:=N) q F! x.val (Z N p))-C.O N p V 0):=by
   filter_upwards [eventual_positioned D S.before h, eventually_all.mpr fun a:X=>faraway C W (y a-y x.val)] with p hL hθ
   filter_upwards [hL,(eventually_all.mpr fun i:brim D U=> near_center C J (v i|>.1) hA),near_center C J d hA,near_center C J e hA,eventually_gt_atTop (k+1),eventually_ge_atTop W] with N ⟨hD,hs,hQ,hx',hX'⟩ hc hd hε hn hw' he'
   let A':= intoSky C p J; let B':= clouds C p J; let ξ (i:X):=Z N p i; let O x:= axis C p N J (ξ x); let X₀:= rootTilt C p J N (ξ x.val); let T (a:X):=board C p J N (ξ x.val) (ξ a)
   have hp:= S'.after; have hi:= (Series.high D hp hp.base.base).trans S'.lower.le; have hN:= k.le_succ.trans hn.le; have hJ:J ≤ N:= h.live.trans (hi.trans hN); have hs(k'): Ψ N p k'=ξ k'-ξ x.val:=by
       have ha(x):Cells.location C.S W N p x=(C.S.toDepth hw' p).embed (wrap (C.S.side W p) x):=dif_pos hw'
       dsimp only; rw [ha, map_sub]; unfold ξ; dsimp only; rw [ha, ha]; exact map_sub (C.S.toDepth hw' p).root _ _
   have h0(Y':X)(hy:Y'∈allUp D U) : 8*‖C.S.place (ξ Y'-ξ x.val)‖≤ C.S.a J:=by
       rw [← hs Y']; dsimp only; rw [show Cells.location C.S W N p (y Y'-y x.val)=(C.S.toDepth hw' p).embed _ from dif_pos hw',C.S.embeds_place,hθ]; exact hν _ hy
   have h1(Y':X)(hy:Y'∈allUp D U) : 8*‖C.S.place (ξ Y')‖ ≤ C.S.a J:=by rw [show C.S.place (ξ Y')= C.S.gridPoint W (y Y') from hX' _ hy]; exact h.fit Y' hy
   have hf(i:brim D U):i.val∈ allUp D U:= mem_union_right _ i.2; have htX:x.val∈allUp D U:=mem_union_left _ hX
   have hW:∀ i:brim D U,C.ref (v i).1 ≤ s' i.val ∧ s' i.val < N ∧ finishAt D m i.val ≤ s' i.val+1 ∧ Migrating C.path (s' i.val+1) p N (O i.val)∧ 0<u i ∧ 2*u i*Spindle.paid C (v i).1 (s' i.val+1) N p (v i).2 ≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels (v i).1 (s' i.val+1):=by
       intro i; obtain ⟨ht,t,hT⟩:= hQ _ (hf i); refine ⟨(hU' i).1, (show s' i.val+1 ≤ N from (hU' i).2.le.trans ht), ?_⟩; rw [(hU' i).2]; refine ⟨h.ap _ (hf i),?_,hU i,he' i⟩
       rw [show O i.val=axis C p N J ((C.S.toDepth ht p).embed t) from congr_arg (axis C p N J) hT]; exact reel C p N J (h.live.trans ((lower_earliest D U m S.before _ (hf i)).trans (h.ap i.val (hf i)))) ht t
   obtain ⟨htx,t',hζ⟩:= hQ _ htX; obtain ⟨w,hω⟩:= tilted C p k N (ξ x.val) hh htx hN t' hζ
   let V':=center C.S p hJ 0; have hδ(v:Site (C.side J p)): T x.val k (A' false v)= Mix.camp C p J k v:=by
       change axis C p N J (ξ x.val-ξ x.val) k v= _; rw [sub_self,axis_zero]
   have hι: Arcade C B' (A' true) Prod.snd D U m j' N p (listP C p J) (Mix.camp C p J) O b (fun i=>81*(l i+1)) X₀ T k:=by
       apply breeze S.before hD hi hN _ hN _ hω; intro y hy; have he:=normC C N p (ξ y-ξ x.val)|>.1; change width C N p _ _ ≤ _ at he; exact he.trans (by have hy:= h0 y hy; linarith only [hy,C.S.a_pos J]) -- B token local notation p from global? fix
   have hhQ(L:C.label d): Interior (V'.chamber 0) (shop D q F! x.val (Ψ N p) L):=by
       refine Next.UVStress.minus (Interior.all _ _ _ (fun i _=>hc i hJ p (Ψ N p i.val) (by rw [hs]; exact h0 _ (hf i)) _)) (hd hJ p _ (by rw [hs]; exact h0 _ htX) _)
   have hμ(x':X)(a:Site (C.side J p))(b:Bool) : T x' N (A' b a)=affine (B'.move (A' b a)).1 (Mix.camp C p J N a) (signBase C p N (ξ x.val) (ξ x') b):=by
        let u:= signBase C p N (ξ x.val) (ξ x') b; let Q:=(hands C p J a).1; change axis C p N J u N a= affine Q _ u; rw [show axis C p N J u N a= affine Q _ _ from bit C J N p N u hJ a true,biteT C J N p N u hJ,Ribbons.same]
   have hxσ:min (j x.val) (m x.val)=j x.val:=min_eq_left (hh.trans (k.le_succ.trans hj.symm.le)); have hρ: Migrating C.path k p N (O x.val):=by unfold O;rw [hω]; exact reel C p N J (h.live.trans hi) hN _
   obtain ⟨T',hP',hq',Y',hs',hζ',hr'⟩:= Arcade.dual_end (f':=A' false) D hι S S' x hP hX (ξ) (Ψ N p) q F! u s' hA hg ((hxσ.symm) ▸ hk) hn ((hxσ.symm) ▸ hh) hb ht' (fun i hi=>by simpa using ht i hi) hT hW hρ he hw rfl rfl (fun i _ v=> hμ i v true) (fun i _ v=> by rw [hs]; exact hμ i v false) (funext hδ) (fun _ _=>rfl) (fun _ _=>rfl) hK hK' hz htN hη hh₁ hh' hx hxA hΦ (by assumption) hR ((congr_arg _ (show ξ ⊥=0 from hx')).trans (axis_zero ..)) hM hl ha (by rw [hxσ];exact hY) hJ (fun t=>by
       refine Interior.times (Next.UVStress.minus (Interior.all _ _ _ (fun i _=>hc i hJ p (ξ i.val) (h1 _ (hf i)) _)) (hd hJ p _ (h1 _ htX) _)) (Interior.all _ _ _ (fun i _=>hc i hJ p (ξ i.val) (h1 _ (hf i)) _))) (fun t=> hε hJ p _ (by rw [latzero]; simp [(C.S.a_pos J).le]) _)
   exact ⟨_,hP',⟨hJ,hhQ _,hq'⟩,Y',hs',⟨hJ,hζ',hr'⟩⟩
end YM.OPE.Arboreal.Pixel
