import YM.OPE.Compatible.Royal.Result
/-!
# Combine in both positions. End of polygonal lattice sweep.
Boundary alignment choices and Signed tiling angles certificated across P'.
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
variable {X V I G' T : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U F K:Finset X}{m j:X→ℕ}
   [Fintype T][DecidableEq T][Fintype G']
    {G:Gauge}{C:Family G}{p N b d k e J s t n:ℕ}{l:ℕ→ℕ}{A:Allot C} {z c r σ Q:ℝ}
variable {P':Ensemble T}{o:X→ Track C.path (Site (C.side J p)) p}
    {E':Track C.path T p}{o':X→Track C.path T p} {f f':Site (C.side J p) ↪ T}{a:T→G'}
variable (L:Arcade C P' f a D U m j N p (CutOrder.listP C p J) (Mix.camp C p J) o b l E' o' k)
    (S:Wave m U K (k+1))(S':Wave m K F k) (x:brim D F)(hP:x.val∈brim D K)(hX:x.val∈U)
    (V₀ V₁:X→ Site (C.side N p))
local notation "V!"=> Site (C.side J p)
set_option quotPrecheck false
local notation "J'"=> (C.labels.level d).Index
set_option quotPrecheck false
local notation "H!"=> places X+Fintype.card (C.labels.level d).Index
variable (q:brim D U→ℕ)(v:∀ i,C.label (q i))(u:brim D U→ℝ)(k':X→ℕ)
local notation "Y"=>fun i:brim D U=> Run.Below C.path (u i) (k' i.val+1) (finishAt D m i.val)
local notation "x'"=>(⟨x.val,hP⟩:brim D K)
local notation "Q!"=> (C.factory d N p).terminal
local notation "T'"=> C.path
local notation "Z"=> C.path.rep N p
local notation "ζ"=> PhysicalNext.Repeat.Legato.Bandage.fly (T').levels -- avoid token
local notation "O"=> lantern C.path r d k
local notation "E"=> Mix.camp C p J
private lemma cont_planar {I:Type}(L:Side)(v:I→ Config G L→ℂ)(s:Finset I)(h:∀ i∈s,Continuous (v i)):Continuous (∏ i∈s,v i):=by
    rw [show (∏ i∈s,v i)=fun x=>∏ i∈s,v i x from funext fun x=>Finset.prod_apply ..]; exact continuous_finsetProd _ h
lemma shop_cont (T:C.label d): Continuous (shop D q v x.val V₁ T):=by
    unfold shop; refine Continuous.sub ?_ (C.continuousO ..); exact cont_planar _ _ _ (fun i _=> C.continuousO ..) -- orientation
include S S' L hX hP
set_option maxHeartbeats 200000 in
lemma dual_end (hA:C.Makes)(hg:G.Simple)
    (hk:C.ref d < j x.val)(hn:k+1<N)(hm:j x.val≤ k)(hb:1≤ b)(ht':d ≤ b)(ht:∀ i,k ≤ i→ Fintype.card G'*(places X+Fintype.card (C.labels.level d).Index)≤ A.r i)
    (hT: Taxes C D U m j l k (places X+Fintype.card (C.labels.level d).Index) b c)
    (hy:∀ i:brim D U,C.ref (q i) ≤ k' i.val∧ k' i.val<N∧ finishAt D m i.val ≤ k' i.val+1 ∧ Migrating C.path (k' i.val+1) p N (o i.val)∧ 0<u i ∧2*u i* Spindle.paid C (q i) (k' i.val+1) N p (v i) ≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels (q i) (k' i.val+1))
    (hv:Migrating C.path k p N (o x.val))(he:0 < z)(hw:z≤ feedS D S (fun i:brim D U=> Run.Below C.path (u i) (k' i.val+1) (finishAt D m i.val)) H! c (⟨x.val,hP⟩:brim D K))
    (hc:P'.move ∘f=hands C p J)(hx':P'.move ∘f'=hands C p J)
    (hU:∀ i∈ allUp D U,∀ v:V!,o' i N (f v)=affine (P'.move (f v)).1 (Mix.camp C p J N v) (V₀ i))
    (hp:∀ i∈ allUp D U,∀ v:V!,o' i N (f' v)=affine (P'.move (f' v)).1 (Mix.camp C p J N v) (V₁ i))
    (hC: o' x.val k ∘f'= E k)(hF:∀ i j,a (f i)=a (f j))(hZ:∀ i j,a (f' i)=a (f' j))
    (hK:Stock.Tabs.opens C.path.levels 1 J s)(hK':Stock.Tabs.opens C.path.levels 1 J t)(hz:m ⊥=n+1)(htN:t ≤ n)(hη:s<k)(hh : C.ref d ≤ s)(hh': C.ref e ≤ t)
    (hx:0<r) (hxA:r ≤ c*badge_fee C z k)(hΦ:r*(2*owed C z d k) ≤ c^2 * ballot C k d)(hμ:r*‖alto C.path k d‖*owed C z d k ≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels d k)
    (hR: GridApprox.room C.path.levels J n (lensScope C e))(hV: o ⊥=Mix.camp C p J) (hM:Expenses C D U m j l b σ) (hl:∀ i,m ⊥ ≤ i→ places X ≤ A.r i)
    (ha:0 < Q)(hY: Q ≤ σ^(F.card*(places X+places X))* (Run.Below C.path ((lantern C.path r d k (j x.val))/2) (j x.val) (finishAt D m x.val)*(∏ i∈univ.erase x,feedS D S' (feedS D S Y H! c) H! c i)))
    (hJ:J ≤ N) (hL:∀ T:C.label d,Interior ((center C.S p hJ 0).chamber 0) (shop D q v x.val V₀ T* peers D (N:=N) q v x.val V₀))(hθ:∀ T:C.label e,Interior ((center C.S p hJ 0).chamber 0) (C.O N p T 0)):
    ∃ T:C.label d, Next.UVStress.quota C d k N p T ≤ 2*owed C z d k∧(center C.S p hJ 0).rootTest (C.beta N p) (shop D q v x.val V₁ T) ≤ stakes C J s/ lantern C.path r d k s ∧∃ V:C.label e, Next.UVStress.quota C e n N p V ≤ 2*owed C Q e n ∧ Interior ((center C.S p hJ 0).chamber 0) ((shop D q v x.val V₀ T*peers D (N:=N) q v x.val V₀)-C.O N p V 0) ∧ (center C.S p hJ 0).rootTest (C.beta N p) ((shop D q v x.val V₀ T*peers D (N:=N) q v x.val V₀)-C.O N p V 0) ≤ 2*(stakes C J t / rebate C Q e t n):=by
    have he':C.ref d < k:= lt_of_lt_of_le hk hm; have hlX :x.val∈allUp D U:=mem_union_left _ hX; have hi:k ≤ N:= k.le_succ.trans hn.le
    obtain ⟨Q',hQ⟩:= recital A p (he'.le.trans hi)
    obtain ⟨hv',y,hG,hV',hr,T₀,X',hP',hc',htE,hvS,hα⟩:= trained D Q' L S S' x hP hX q v u k' hQ hA hg he' hn hm hb ht hT hy hv he hw
    obtain ⟨Q'',h'',hz',hΦ',X₀,H,H',h''_,hU'⟩:= received_here D (Q:=Q') L S' x hQ hg hA hi he'.le hP' hv' hG hV' hr he htE hvS hα hx hxA hΦ hμ -- repeated shadow
    let s'':= (Q'' (C.ref d)).a; let z':= (Q!).toLinearMap s''; let Qc:=- (Q'.tone k).index s''; let f₀:= Deb.portion (atopBy T (foldTo (W:= (C.labels.level d).Index) x)) (spices P' (dyes (I:=brim D F) Qc)) (spurs D (spurs D (entered D q v o' P' x.val Q' k) S) S')
    let U':= shop D q v x.val V₁ z'; let V:= shop D q v x.val V₀ z'; let V'':= peers (N:=N) D q v x.val V₀
    have hξE:= filled_signed h'' hQ.pull A.buy.system hx (fun i _ hi => hμ.trans (fly_le hg d i k hi))|>.1
    have hY': ∀ i:V!, f₀ (f' i,x)=(center C.S p hJ 0).copy i U':= fun i=> speak_cost (k:=k) D S S' x hP Q' s'' q v o' P' V₁ hA hJ i (f' i) (congr_fun hx' _) (fun i' he=> hp i' he i) hlX|>.1
    refine ⟨z',?_,?_,?_⟩
    · unfold Next.UVStress.quota
      have he: (Q!).symm z'=s'':= (Q!).symm_apply_apply _
      rw [he,hQ.bank,show ((Q'.draft T').inits k s'').x=_ from (hQ.pull.earned k he'.le hi).currents s'']; exact bias_price Q' hQ.pull y h'' hr
    · let X₁ i:= (Q'' i).bar Q' (-s''); have hP: (X₀ x).home∘f'=E k:= by rw [h''_ x]; exact hC
      exact declare A hA hg x f' hZ f₀ U' (shop_cont ..) hK hη hi hh hx' hz' hY' (c:=X₁) H H' hP (update_self ..) hx hξE
    let D':= f₀ ∘ limb (brim D F) f; obtain ⟨hWW,M,hP₀,hζ,hε⟩:= recession D L S x hP hX f₀ hi H _ H' hΦ' hz' hx (h''_ _) (by intro i hi; rw [hU' i hi]; exact hP'.seen _) hF hm hk ht' hg hA
    have hM'(b:brim D F): k ≤ roof U m N b.val := upward D S' S.next N (fun i=> le_trans (k.le_succ) (upward D S (Finset.Subset.refl _) N (fun i=>(hn.le.trans (if_neg ((on_brim ..).mp i.2|>.1)|>.symm.le))) _)) b
    refine finalUse D S'.after L.bed M (V*V'') hz hi hV (S'.next.trans S.next) htN S'.lower (fun i hv=>hM' ⟨i,hv⟩) hK' hM hl hh' hP₀ hWW hR hA hg ?_ (le_trans (Series.high D L.bed.plan (L.bed.plan.base.base)) L.bed.next.le) ?_ (hL _) hθ ha ?_
    · refine (shop_cont D x V₀ q v _).mul ?_; unfold V'' peers; exact cont_planar _ _ _ (fun i _=> C.continuousO ..)
    · intro i; let W:=(center C.S p hJ 0); obtain ⟨hp,hx⟩:= speak_cost (k:=k) D S S' x hP Q' s'' q v o' P' V₀ hA hJ i (f i) (congr_fun hc _) (fun i' hp => hU i' hp _) hlX; funext y; change W.copy i (V*V'') y=∏ j,D' (i,j) y
      rw [← mul_prod_erase _ _ (mem_univ x)]; change W.copy _ _ _=f₀ (f i,x) y* _; have he: (∏ j∈univ.erase x,D' (i,j) y)= W.copy i V'' y:=(Finset.prod_apply ..|>.symm).trans (congr_fun hx _)
      rw [show f₀ (f i,x)= W.copy i V from hp,he]; unfold Tiling.copy; split_ifs <;> simp [star_mul']
    apply hY.trans; rw [← mul_prod_erase _ _ (mem_univ x),hζ]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg hM.good.le _); apply mul_le_mul_of_nonneg_left _ (Run.below_fee _ (div_pos (lan_pos C.path hx) zero_lt_two)|>.le)
    refine Finset.prod_le_prod (fun i _=> ?_) (fun i hi=> ?_)
    · exact (feed_pos D S' _ _ hT.start (fun i=> feed_pos D S _ _ hT.start (fun i=> Run.below_fee _ (hy i|>.2.2.2.2.1)))).le
    rw [hε i (mem_erase.mp hi|>.1)]; exact hc' _ (mem_erase.mp hi|>.1)
end YM.OPE.Arboreal.Arcade
