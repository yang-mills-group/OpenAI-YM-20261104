import YM.Contacts.Junction.Sunrise
/-! # per-station Rate-frame supplies aperture. Head pruned exact. Endowment.Card. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} (P : ChartRatio G) {σ C e v d t K:ℝ}{n k j:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current
open Sienna Lantern Planned.JetPort Dew
open Uniform
variable {U:Teller G}{D:ℕ→Dew G}{g v f K a w:ℕ→ℝ}{b:ℕ→BudgetPoint}{L:Side} {M:Uniform.ChartPrices}
variable {N:Meter} (hp:Pouch N (- (1/2:ℝ)) g)
local notation "Φ" => (fun i=>Dew.Q (D i))
local notation "E" => Frame.Port Φ (N.pow Capture.stashp)
variable (ht: ∀ᶠ i in atTop,Pearl U (v i) (f i) L σ C M n (b i) (D i)) (hv:N.Rush 0 v) (he: N.β=ᶠ[atTop] (fun i=> betaF G (f i) L)) (hh:Tendsto f atTop atTop)
local notation "u" => (fun i:ℕ=> ((Dew.ℓ (D i))))
lemma stencilA (D:Dew G)(x:D.X×D.Y) : ‖combineH D.B x‖ ≤ ‖x‖:= by
    let f:=(combineH (G:=G) D.B).toContinuousLinearMap; exact (f.le_of_opNorm_le (feesComb (G:=G) D.B) x).trans_eq (one_mul _)
include ht hv
lemma crest (hk:k≤n+3): Direct N k 0 (N.pow stashp) (fun i=> let d:=D i; Lapis.table d.B d.label d.T.up d.T.high ∘ d.ℓ) := by
   let Y i:= (D i).X × (D i).Y; let H(i:ℕ) := (D i).B; let p (i:ℕ):Y i→ℝ:= Lapis.table (H i) (D i).label (D i).T.up (D i).T.high; have hx:= (wordPos ht hv).2.2.2.1; apply rUse (f:=fun _=> M.initial) ?_ ((K_touch ht hv hx).mono fun i hi j=> mem_ball_zero_iff.mpr (hi _ j.property)) (ell_pole ht hv) le_rfl; let a i:=mineshaft n M (v i); have ha:= (chairCost ht hv M hv).2; refine ⟨_,ha,ht.mono fun i hi=>?_⟩; obtain ⟨A,hA,h⟩:= hi.service; let Hh(w:Y i)(hl: ‖w‖< M.initial): Brush k (a i) 1 (p i) w:= by
     let d:=D i; have he:= trench d.B d.label d.T.up d.T.high σ C _ A hi.stitches.large hi.staples _ hi.stitches.one hi.stitches.overall w (mem_ball_zero_iff.mpr (h.symm ▸ lt_of_le_of_lt (stencilA d w) hl)); rw [h] at he; exact he.smaller hk
   exact ⟨(Hh 0 (norm_zero.trans_lt hx)).nonneg,fun x=>Hh _ (mem_ball_zero_iff.mp x.property)⟩
variable (hP:LocalRatio P)
include he hh hP
lemma ember : Direct N k 0 (N.pow stashp) (fun i=> let d:=D i; Lapis.mist d.B P d.T.up ∘ d.ℓ) := by
   obtain ⟨Y,hY⟩:= paint_supply G k; let K:= Classical.choice (Planned.JetPort.purchase P hP k); let H i:= loopBill G L (f i); have hH := Meter.Rush.grounded (loopBill_rate G L) hh he;
   let p:=Uniform.shade G; have hp :0<p :=shade_pos G; have hw:= hP.patch;
   let d:= min 1 ((P.radius/2)/p); have hd : 0<d := lt_min zero_lt_one (div_pos (half_pos hw) hp); let r i:= atomW G k Y σ (H i) (v i) (v i)+ v i*taxR k K.cost G; have hr : N.Rush 0 r:= by
      have ha:= hH.bind (atomCost G Y σ k 2); have hz := hv.times ((Rush.zeroN  k hv).times ha (by norm_num : (0:ℝ)+0=0)) (by norm_num : (0:ℝ)+0=0); exact hz.blend (hv.bind _)
   apply rUse (f:=fun _=>d) ?_ ((K_touch ht hv hd).mono fun i hi j=> mem_ball_zero_iff.mpr (hi _ j.property)) (ell_pole ht hv) le_rfl; refine ⟨r,hr,ht.mono fun i hi=>?_⟩; let D':=D i; let q(w:D'.X×D'.Y)(hl:‖w‖<d): Brush k (r i) 1 (Lapis.mist D'.B P D'.T.up) w:= by
      refine pen D'.B P D'.T.up k hY hi.staples K hi.stitches.one hi.stitches.overall hi.stitches.finalP hi.stitches.lever w (lt_of_le_of_lt (stencilA D' w) (hl.trans_le (min_le_left ..))) ?_; let W:= weld (Precision.Key D'.B G); have hx:= ((W.toContinuousLinearMap.le_opNorm w.2).trans (le_trans (mul_le_of_le_one_left (norm_nonneg _) (Lapis.climb (Precision.Key D'.B G))) (norm_snd_le w))).trans (hl.le.trans (min_le_right ..)); rw [mul_comm]; exact (le_div_iff₀ hp).1 hx
   exact ⟨(q 0 (norm_zero.trans_lt hd)).nonneg,fun x=> q _ (mem_ball_zero_iff.mp x.property)⟩
omit he ht hv hh hP in
lemma clock_surge : Budget N (Frame.Port Φ (N.pow stashp)) k 0 (fun i _=>⇑(clockF (G:=G) (D i).B)):= by change Budget N E k 0 (fun i (_:Frame.Bank Φ (N.pow stashp) i) (x:(D i).Q)=> x.1.1); exact fstD (Q:=fun i (_:Frame.Bank Φ (N.pow stashp) i) (x:(D i).Q)=>x.1) (fstD (Q:=fun i (_:Frame.Bank Φ (N.pow stashp) i)=> (id (α:=(D i).Q) ·)) (Current.meetP (d:=stashp) Meter.Rush.any (by norm_num [stashp])))
lemma clearFan (hk:k≤n+3): Root N (fun i=> (D i).fan P) k 0 (N.pow stashp):= by
   let f:= fun i=> (D i).fan P; let θ: Mint _ _:= (fun i (_:Frame.Bank Φ (N.pow stashp) i)=>⇑(clockF (G:=G) (D i).B)); refine ⟨?_,ht.mono fun i hi=> ribbonH P _ _ _ _ hi.staples hi.stitches.large hP⟩; apply Arms.sum (crest ht hv hk); exact Budget.mul (θ^2) _ (Budget.power (k:=k) clock_surge 2) (ember P ht hv he hh hP) (by ring) -- p/q inferred first? not
omit he hh hP
omit ht hv in
private lemma bevelInside {m:Side}{x:Config G m}(h:∀ i,G.chord (x i)< Kale.charHeight G) : Kale.bevel m x= content x ∧ input G m (Kale.bevel m x)=x:= by
    let hp:= Kale.guardChar G; have hs:=hp.down; have he: Kale.bevel m x=content x:=congr_arg ((arm G m 1).symm) (funext fun i=> hp.kept _ _ (h (i.1,axisEquiv.symm i.2)).le); refine ⟨he,?_⟩; rw [he]; funext ⟨a,b⟩; rw [encode_link, content_at]; exact hp.right _ (le_of_lt (by linarith only [hs,h (a,b)]))
lemma branchInside : ∀ᶠ i in atTop, ∀ z∈Frame.Bank Φ (N.pow stashp) i, let d:= D i; let x:= d.ℓ z; (∀ e,G.chord (pul d.B x e)< Kale.charHeight G)∧ input G d.f (lane d.B x) = pul d.B x:= by
    obtain ⟨Z,hZ⟩:= paint_supply G 1; let c:= Inputs.variation G (fineCost G 1 Z); let θ:=Kale.charHeight G; have hp:= Kale.guardChar G; have hz:0<θ:=hp.down; let d:= min 1 (θ/(1+|c|)); have hd : 0<d:= lt_min zero_lt_one (div_pos hz (by positivity)); filter_upwards [K_touch ht hv hd] with i hi z hm D x; have hv: ‖combineH D.B (G:=G) x‖ <d := (stencilA D x).trans_lt (hi z hm); have hs(e) : G.chord (pul D.B x e)< θ:= by
         have hx:= ((fine_supply D.B hZ).chord le_rfl ((hv.le.trans (min_le_left ..))) e); let v:= ‖combineH D.B (G:=G) x‖; apply lt_of_le_of_lt hx; change c*v<_; have hl:= (lt_div_iff₀ (show 0<1+|c| by positivity)).1 (show v< θ/(1+|c|) from (hv.trans_le (min_le_right ..)));  rw [mul_comm]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_trans (le_abs_self c) (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _)) hl
    exact ⟨hs,(bevelInside hs).2⟩ -- shadow hv!
lemma propup : Direct N k 0 (N.pow stashp) (fun i z=> lane (D i).B ((D i).ℓ z)) := by
   obtain ⟨Z,hZ⟩:= paint_supply G k; let H:= composeCost k (Arbor.Logprice G k) (composeCost k (fineCost G k Z) 1); let A(i:ℕ)(z:Frame.Bank Φ (N.pow stashp) i):= (D i).ℓ z;
   refine Budget.graft (a:=fun i (_:Frame.Bank Φ (N.pow stashp) i)=> ⇑(D i).ℓ) (g:=fun i _=> lane (D i).B) ?_ (ell_pole ht hv) le_rfl; refine ⟨fun _=>|H|, Rush.settle (M:=N) _,?_ ⟩; filter_upwards [branchInside ht hv,K_touch ht hv zero_lt_one] with i hi hp using ⟨abs_nonneg _, fun j=> Brush.offer.2 ⟨((lane_price _ hZ (A i j) (hp _ j.property).le (hi _ j.property).1).analytic.of_le le_top), fun k h=> ((lane_price _ hZ (A i j) (hp _ j.property).le (hi _ j.property).1).norm_le k h).trans (le_abs_self _)⟩⟩
lemma winds : Direct N k 0 (N.pow stashp) (fun i=> shuttle (D i).B (D i).L):= Current.polar clock_surge (propup ht hv)
lemma smallLan : ∀ᶠ i in atTop,∀ z∈Frame.Bank Φ (N.pow stashp) i,‖(shuttle (D i).B (D i).L z).2‖ < Province.Costing.ripe (N.β i):= by
    let B := Frame.Bank Φ (N.pow stashp); let Z i z:Link G (D i).f:=lane (D i).B ((D i).ℓ z); obtain ⟨p,hp,H⟩:= (propup (k:=1) ht hv).cap;
    have hv i: Z i 0=0:=by unfold Z; rw [map_zero,lane0];
    have hh:= rush_lax (hp.times (Meter.Rush.any (p:=stashp)) (zero_add _)) (show stashp < - (2/5:ℝ) from by norm_num [stashp]); filter_upwards [H,N.eventual,hh] with i hi hp hh z hz;
    let d:=(N.pow stashp) i; have hj :∀ y∈B i, Brush 1 (p i) 1 (Z i) y:= fun y hy=> hi.2 ⟨y,hy⟩; have h0: (0:Φ i)∈ B i:= mem_ball_self (Real.rpow_pos_of_pos hp _); have h₁ : ‖Z i z‖ ≤ p i * ‖z‖:= by simpa only [hv,sub_zero] using Convex.norm_image_sub_le_of_norm_fderiv_le (fun y hy=> (hj y hy).smooth.differentiableAt (by decide)) (fun _ h=> (norm_iteratedFDeriv_one (𝕜:=ℝ) _).symm.trans_le ((Brush.offer.1 (hj _ h)).2 1 le_rfl)) (convex_ball _ _) h0 hz
    exact h₁.trans_lt ((mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hz).le hi.1).trans_lt ((le_abs_self _).trans_lt hh))
include hP
private lemma windowG (D':Dew G) {z: D'.Q} (h:‖D'.ℓ z‖<P.radius/(Uniform.shade G)) : Fare.windmill D'.B (D'.ℓ z).2 ∈ Next.SectorChange.mouth P:= by
    intro i _; let S:= weld (Key D'.B G); let q:=Uniform.shade G; have hp:0<q:= Uniform.shade_pos G; apply mem_ball_zero_iff.mpr; refine (Lapis.carries (G:=G) D'.B i _).trans_lt ?_; rw [mul_comm]; apply (lt_div_iff₀ hp).mp; apply (S.toContinuousLinearMap.le_opNorm _).trans_lt ((mul_le_of_le_one_left (norm_nonneg _) (Lapis.climb (Key D'.B G))).trans_lt ((norm_snd_le (D'.ℓ z)).trans_lt h)) -- needs annotation P.radius
lemma paid : ∀ᶠ i in atTop,∀ z∈Frame.Bank Φ (N.pow stashp) i,let D:=D i; let x:= D.ℓ z; Fare.windmill D.B x.2∈ Next.SectorChange.mouth P ∧ ∀ j:D.S.Choices,Lapis.table D.B j D.T.up D.T.high x=Lapis.table D.B D.label D.T.up D.T.high x:= by
   have hw:0<M.initial := (wordPos ht hv).2.2.2.1; filter_upwards [K_touch ht hv hw,K_touch ht hv (div_pos hP.patch (Uniform.shade_pos G)), ht] with i hi hr h z hz d x; obtain ⟨A,hA,ha⟩:= h.service; refine ⟨windowG P ht hv hP d (z:=z) (hr _ hz), fun j=>?_⟩; exact (A.receipt d.B d.label h.staples h.stitches.large rfl rfl).2 _ (mem_ball_zero_iff.mpr ((stencilA d x).trans_lt (ha.symm ▸ hi z hz))) j
omit hP
include he hh
open Next.Fluctuations ConnectedActivityE6.Coat
abbrev γC (D:ℕ→Dew G): ℕ→ℝ:= fun i=>(D i).grad
lemma volume_count : let W:= fun i=> (D i).β; (∀ᶠ i in atTop,0<W i ∧ W i∈ Set.Icc (N.β i / 2) (2*N.β i))∧ N.Rush 1 W ∧ Pouch N (-(1/2)) (γC D):= by
    intro W; let t:=γC D; have hz : ∀ᶠ i in atTop,0<W i ∧ W i∈Set.Icc (N.β i/2) (2*N.β i):= (ht.and he).mono fun i hi=> by obtain ⟨H,hh⟩:=hi; rw [hh,← H.patch]; exact ⟨H.intake.positive,H.intake.window⟩
    have ht': ∀ᶠ i in atTop,0<t i:= hz.mono fun i hi=> (gS _ hi.1).1;
    refine ⟨hz, Meter.Rush.view ((Meter.Rush.any (p:=1)).multiplier 2) (hz.mono fun i h=>?_), ht',?_,?_⟩
    · unfold pow; rw [Real.rpow_one]; exact (Real.norm_of_nonneg h.1.le).trans_le (h.2.2.trans (le_abs_self _))
    · have h:= Meter.Rush.grounded (Sienna.glim G L) hh he; refine h.view ?_; filter_upwards [he,N.eventual,hz,ht'] with i h hv hp h'; have hf:= Sienna.lamp G L (t:=f i) (show 0< betaF G (f i) L from h ▸ hv) (W i) (show betaF G (f i) L/2 ≤ W i from h ▸ hp.2.1); exact (Real.norm_of_nonneg h'.le).trans_le (hf.2.trans (le_abs_self _));
    · have h : - - (1/2:ℝ)=1/2:= by norm_num
      rw [h]; refine ((Meter.Rush.any (p:=1/2)).multiplier 2).view ?_; filter_upwards [N.eventual,hz,ht'] with i hx ht h'; unfold pow; rw [← Real.sqrt_eq_rpow]; erw [inv_inv]; have h:= ht.1; refine (Real.norm_of_nonneg (Real.sqrt_nonneg (W i))).trans_le ((?_ : Real.sqrt (W i) ≤ 2*Real.sqrt (N.β i)).trans (le_abs_self _)); nlinarith only [ht.2.2,Real.sq_sqrt hx.le,Real.sq_sqrt h.le,hx,Real.sqrt_nonneg (N.β i),Real.sqrt_nonneg (W i)]
end Provision
end YM.Contacts.Junction
