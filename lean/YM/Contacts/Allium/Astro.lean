import YM.Contacts.Allium.Flux
import YM.Contacts.Revest.Pales
/-!
# Controller. Real Tugs harvest on small prototypes. Does not use any rank‐zero funding premise,
 nor compare the partition scalar itself. Burn after clocks.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Allium
open Function Filter Finset Lattice Gauge RG Matrix  -- order
open Wilson Milling Pulse Loom Flux PhysicalNext.Repeat Pressure Precision -- errors
open Push.Uniform Pulse Spine Garf Steam House Exterior Model Model.Arbor Province.Costing PertExtension.Series Radial
open Lintel Lintel.Angle Lintel.Plata Loom Junction Junction.Current Junction.Buyer Junction.Provision ConnectedActivityE6 Blaze Blaze.March Coat Meter Capture YM.Stationary Cove Lumen
open scoped Topology ContDiff Classical NNReal BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {c:Side}
section operations
open Revest.Tucks
-- imply real sheet.PT minus flag‐free analytic.User.Deploy
abbrev physical (B:BudgetPoint) (p:Clip)(T:PathData G)(F:bore G)(k:ℕ)(u:ℝ)(V:Config G c):ℝ := u* mainTerm p T V+ Precision.loop T V+ Trio.froth (integrated B F p T k u) V
abbrev forecast (B:BudgetPoint)(p:Clip)(T:PathData G)(F:bore G)(k:ℕ): Milling.cap G c→ℝ:= enact (material p T)+ biomass k B F p T
lemma paneHolds (B:BudgetPoint) (p:Clip)(T:PathData G)(F:bore G)(k:ℕ)(u:ℝ)(hu:0<u)(x:Link G c): physical B p T F k u (input G c x)= u*forecast B p T F k (gStep u,x):= by
     let v:= input G c x; let g:=gStep u; let a:= g^ (2:ℕ); let f:= Trio.froth (c:=c) (integrated B F p T k u); have hf': f v=u* ∑ i∈Finset.range (k+1),g^i*plays (Buyer.book k B F p T i (f:=c)) x:= by
         unfold f Trio.froth integrated plays; simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; rw [sum_comm,mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [← mul_sum]; change (u*g^i)* _= _*(g^i * _); rw [mul_assoc]; rfl
     unfold physical; change u*mainTerm _ T v+Precision.loop _ v+ f v=u*((mainTerm _ _ v+ a*Precision.loop T v)+ (∑ i∈Finset.range (k+1),g^i* plays (Buyer.book k B F p T i (f:=c)) x)); rw [hf']; have he:u*a=1:= (mul_comm u a|>.trans (Fare.gS _ hu).2) -- shape?;
     rw [mul_add u, mul_add u, ← mul_assoc u,he,one_mul]
end operations
variable {V γ:ℕ→Type}[∀ i, NormedAddCommGroup (V i)][∀ i, NormedSpace ℝ (V i)] {x:Frame γ V}
variable {N:Meter} {X:G.ColorIndex}
variable {F:ℕ→bore G}{H:ℕ→Side}{Λ a d b:ℕ→ℝ}{B:ℕ→BudgetPoint}{η:ℕ→PathData G}{Y:ℕ→Bed} {ζ:ℕ→ℕ} {σ I v:ℝ}{p : Clip}{k n i j:ℕ}
local notation "Φ" => (fun l=> forecast (G:=G) (c:=H l) (B l) p (η l) (F l) k)
local notation "A" => (fun i=> Milling.cap G (H i))
local notation "K" => (fun i=> Link G (H i))
local notation "U" => (fun i=> hair (F i) (H i))
local notation "℘" => (fun i=>swell (U i) (k+3))
local notation "Ψ" => (fun i=>Buyer.boom k (B i) (F i) p (η i) (f:= H i))
-- shine ledger
structure Firm (X:G.ColorIndex)(p:Clip)(η:ℕ→PathData G)(Y:ℕ→Bed)(F:ℕ→bore G)(B:ℕ→BudgetPoint)(H:ℕ→Side)(N:Meter)(σ I:ℝ)(k n:ℕ) : Prop where
     paint : ∃ Λ a d:ℕ→ℝ,∃ ζ:ℕ→ℕ,N.Rush 0 Λ∧ (∀ r, N.Rush r (fun i=> N.pow (- (d i)) i)) ∧ N.Rush 0 (fun i=> N.pow (a i) i) ∧ ∀ᶠ i in atTop,(η i).Bounds p σ I (Λ i) ∧ n+3 ≤ ζ i∧ ∀ j≤k, Charted G k (N.β i) (B i) (η i) (F i) p (d i) (ripe (N.β i)) (a i) j (ζ i)
     wage : Spectrum N k (S:=fun i=> hair (F i) (H i)) 0
     census : N.Rush 0 (fun i=> (Fintype.card (Site (H i)):ℝ))
     sky : ∀ᶠ i in atTop, Aegis X (F i) (Y i)∧10*(B i).B < (H i).val
variable (w:Firm X p η Y F B H N σ I k n)(hG:G.Simple)(hk:2≤k) (hn:k≤n)
namespace Firm
section pathPow
variable (hΛ:N.Rush 0 Λ) (h:∀ᶠ i in atTop,(η i).Bounds p σ I (Λ i)) {C : Shelf V γ (fun i=> Milling.cap G (H i))}
variable (ht: Budget N x j 0 C) (hZ:∀ᶠ i in atTop,∀ y, ‖(C i y (x i y)).2‖<1)
include hΛ w h ht hZ hk
lemma skyway : Budget N x j 0 (fun i s=> (enact (f:=H i) (material p (η i))) ∘ C i s):= by
   obtain ⟨t,hh⟩:= paint_supply G j; let t' := outerCost G j t; let X' i:= sumFee G p t' σ I (Λ i) j; have hx:N.Rush 0 X':= by unfold X' sumFee; apply Meter.Rush.blend _ (Meter.Rush.settle _); exact (Meter.Rush.settle _).blend (Meter.absolute (hΛ.bind _));
   let L i:= (Fintype.card (Site (H i)):ℝ)* X' i; let S j i:= base p (η i) (H i) j ∘ input G (H i); refine Arms.confirm ?_ (forStake (k:=k) ht (P:=S) (fun p' hp=> rUse (L:=S p') (d:=0) (f:=1) ?_ (hZ.mono fun i hi j=> mem_ball_zero_iff.mpr (hi j)) (sndD ht) le_rfl));
   · apply Eventually.of_forall; intro i; change (fun s=> enact (material p (η i)) ∘ C i s)=_; rw [rear hk]; rfl -- order maybe first?
   refine ⟨_,w.census.times hx (by norm_num),?_⟩; filter_upwards [h] with i h; refine ⟨mul_nonneg (Nat.cast_nonneg _) (sumFee_nn p),fun u=>?_⟩; let z:= H i; let f:= S p' i; have hp : Allows j f u.val (L i):= by
       unfold f S; rw [← Model.uses]; exact Model.train _ (fun i'=>outerBrush p (η i) Metric.isOpen_ball (convex_ball _ _).isPreconnected u.property (fun i u hu=> Model.imprints hh (mem_ball_zero_iff.mp hu).le i) _ i' h p');
   exact Brush.offer.2 ⟨hp.analytic.of_le le_top,hp.norm_le⟩
end pathPow
local notation "s" => (N.pow stashp)
def projected (F E: Milling.cap G c→ℝ) := Radar.gap (F-E)
lemma shaded (F E:Milling.cap G c→ℝ): projected F E= Radar.gap F-Radar.gap E:=by ext1 y; unfold projected Radar.gap; simp only [Pi.sub_apply]; abel
lemma shadePlus (F E:Milling.cap G c→ℝ): Radar.gap (F+E)=Radar.gap F+Radar.gap E:= by ext1 y; unfold Radar.gap; simp only [Pi.add_apply]; abel
lemma graded {C:Milling.cap G c→ℝ}(hc: AnalyticAt ℝ C 0)(he: YM.Stationary.Rays n C): AnalyticAt ℝ (Radar.gap C) 0∧ YM.Stationary.Rays n (Radar.gap C):= by
   let X:= Link G c; let L: ℝ × X →L[ℝ] ℝ × X:= (ContinuousLinearMap.fst ℝ ℝ X).prod 0
   have hv : Radar.gap C = C-(C ∘ L):= rfl; rw [hv]; exact ⟨hc.sub (Forge.starts _ hc L), he.sub (Milling.merkin hc he L (L.analyticAt _) (map_zero _))⟩
local notation "A₀" => (Frame.Port A (N.pow stashp))
set_option quotPrecheck false
local notation "V₀" => (fun i j (x:A i)=> (x.1,(0:Link G (H i))))
local notation "Hm" => (fun i=> projected (c:=(H i)) (℘ i) (Φ i + Ψ i))
include w hk hG hn
lemma firth : ∀ᶠ i in atTop, AnalyticAt ℝ (Hm i) 0 ∧ YM.Stationary.Rays (k+3) (Hm i):= by
   obtain ⟨Λ,a,d,z,-,-,-,he⟩:= w.paint; filter_upwards [w.sky,he] with i hi hP; have h:=Buyer.asset hP.1 hP.2.2 hk hG (f:=H i) hi.1; exact graded h.1 h.2
-- radius relative.Field eval for snap.H price.
section relative
variable {X' : Shelf V γ (fun i=> Milling.cap G (H i))}
lemma reven (O:Lamp (fun i=> Milling.cap G (H i)))
   (hp:Budget N x j (v) (fun i z=>O i ∘ X' i z))(he:Budget N x j v (fun i z y=> O i ((X' i z y).1,0))) : Budget N x j v (fun i z=> Radar.gap (O i) ∘ X' i z):= Arms.sub hp he
lemma trivialBack (v:ℝ)(X':Shelf V γ (fun i=>Milling.cap G (H i)))(hX: Budget N x (n+3) 0 X'): Budget N x (n+3) v (fun i z=> (Radar.gap (Ψ i)) ∘ X' i z):= by
   let V' i z y:Milling.cap G (H i):=((X' i z y).1,0); have hv:Budget N x (n+3) 0 V':= Budget.stack (fstD hX) Budget.zero
   obtain ⟨Λ,a,d,z,h,hD,hA,H'⟩:=w.paint; have he (Z:Shelf V γ A) := Current.gleaming (Z:=Z) (Zr:=x) (n:= n+3) (p:=fun _=>p) (H'.mono (fun _ hi=> hi.1)) (H'.mono (fun _ hi=>hi.2.2)) (w.sky.mono (fun _ hi=> hi.1)) hG (hh:=w.sky.mono (fun _ hi=>hi.2)) w.census hD hk
   exact reven w hG hk hn (Ψ) (he X' hX v) (he V' hv v) -- binder order; implicit parameters nobodies
end relative
lemma tower : Root N Hm (n+3) 0 (s) := by
   obtain ⟨Λ,a,d,z,h,hD,hA,H'⟩:=w.paint; let L:=Frame.Port A s; let C i (_:↥(Frame.Bank (A) s i))(y:A i):=y; let D: Shelf A (fun i=>↥(Frame.Bank A s i)) A:= V₀ -- elaboration replace
   have he:Budget N L (n+3) 0 C := Budget.id (Frame.head (Meter.Rush.any.mono (by norm_num [stashp]))); have hg:Budget N L (n+3) 0 D:= Budget.stack (fstD he) Budget.zero
   have hx : ∀ᶠ i in atTop,s i<ripe (N.β i) ∧ ripe (N.β i) ≤ 1:= by
      filter_upwards [N.grows.eventually_gt_atTop 1] with i hi using ⟨Real.rpow_lt_rpow_of_exponent_lt hi (by norm_num [stashp]: stashp < -(2/5:ℝ)),Real.rpow_le_one_of_one_le_of_nonpos hi.le (by norm_num:(-(2/5):ℝ)≤0)⟩
   let V:= (fun i=>Radar.gap (Ψ i)); have hp : ∀ F:Shelf A (fun i=>↥(Frame.Bank A s i)) A,Budget N L (n+3) 0 F → (∀ᶠ i in atTop, ∀ j, ‖(F i j (L i j)).2‖<ripe (N.β i))→ Budget N L (n+3) 0 (fun i j=> Φ i ∘ F i j):= by
      intro F hF ht; apply Arms.sum (b:=fun i j=> Junction.Buyer.biomass k (B i) _ p (η i) ∘ F i j) (w.skyway hk h (H'.mono fun _ hi=>hi.1) hF ((hx.and ht).mono fun _ h' v=>(h'.2 v).trans_le h'.1.2)); exact Current.whirs (H'.mono fun _ hi=> hi.2.2) w.census hA hF (H'.mono fun _ hi=> hi.2.1) ht
   have ht: Budget N L (n+3) 0 (fun i j=> Radar.gap (Φ i) ∘ C i j):= reven w hG hk hn Φ (hp C he (hx.mono (fun i h j=> ((norm_snd_le (L i j)).trans_lt (mem_ball_zero_iff.mp j.property)).trans h.1))) (hp D hg ((N.eventual).mono fun i hi v=> (norm_zero (E:=Link G (H i))).trans_lt (Real.rpow_pos_of_pos hi _))) -- arguments expected
   have hw:= (gap_shield he w.wage); have hh:Budget N L (n+3) 0 (fun i j=> Radar.gap (℘ i) ∘ C i j):= hw;
   have h':= w.trivialBack hG hk hn 0 C he -- fill
   refine ⟨Arms.cheaper ?_ (Arms.sub hh (ht.sum h')), (w.firth hG hk hn|>.mono (fun i hi=> hi.1))⟩
   funext i j x; change (Radar.gap (℘ i)) x - ((Radar.gap (Φ i)) x + Radar.gap (Ψ i) x)= _; rw [← show Radar.gap (Φ i+Ψ i) x=Radar.gap (Φ i) x+Radar.gap (Ψ i) x from congr_fun (shadePlus (Φ i) (Ψ i)) x]; exact (congr_fun (shaded (℘ i) (Φ i + Ψ i)) x).symm
variable {C:Shelf V γ (fun i=> Milling.cap G (H i))}
lemma preflight (h:Budget N x (n+3) fit C): Budget N x (n+3) (stashp*(k+3:ℝ)) (fun i j=> projected (Φ i) (℘ i) ∘ C i j):= by
   have ht := (w.firth hG hk hn); let S:=Hm; let P:=Pouch.canon (N:=N) (p:=stashp); have hw:=P.bank h (by norm_num [fit,stashp]); have he : Budget N x (n+3) (stashp*(k+3:ℝ)) (fun i j=> S i ∘ C i j):= by
      apply Arms.lo (Root.application (S:=S) ((w.tower hG hk hn).snap P (j:=k+3) (by omega) (ht.mono (fun i hi=> (YM.Stationary.rays_jet hi.1 (k+3)).1 hi.2)) (by norm_num [stashp])) hw P h (by norm_num [fit,stashp])) _ le_rfl; push_cast; rw [zero_add]
   refine Arms.cheaper ?_ (Arms.opp (Arms.sum he (w.trivialBack hG hk hn (stashp*(k+3)) C (h.lo (by norm_num [fit]) le_rfl)))); funext i j x; unfold S projected Radar.gap; simp only [Function.comp_apply,Pi.neg_apply,Pi.sub_apply,Pi.add_apply]; abel
end Firm
section transition
open Resetter Firm
variable {u:ℕ→Resetter.Pow}{S T: ∀ i, House (Lines G (H i) 1)}{Z:Shelf V γ (fun i=> Link G (H i))}
local notation "f" => appeal b (k+3) u
local notation "z" => (gStep ∘ (appeal b (k+3) u))
variable (hb:Foil b N) (hv:Live u N (k+3))(hu:∀ᶠ i in atTop, Resetter.Uniform (u i)∧QuietPower (u i))
variable (hF: ∀ᶠ i in atTop,hair (F i) (H i)=lowerHouse (u i) (T i))
variable (hp: Spectrum N k (T-S) (fit*(k+3))) (hZ: Budget N x (n+3) fit Z)
-- craft.
def aperture (F:bore G)(B:BudgetPoint) (T:PathData G)(p:Clip)(k:ℕ)(β γ:ℝ)(S:House (Lines G c 1))(U': Config G c)(X:Link G c):= (physical (c:=c) B p T F k γ U'- physical (c:=c) B p T F k γ 1)- β* (Radar.gap (swell S (k+3)) (gStep β,X))
local notation "λ₀" => (fun i j x=> aperture (F i) (B i) (η i) p k (b i) (f i) (S i) (input G (H i) (Z i j x)) (Z i j x))
include w hG hk hn hb hv hu hF hp hZ
lemma strut : Budget N x (n+3) (1+stashp*(k+3)) λ₀:= by
   let X i j y:= (z i, Z i j y); have hx: Budget N x (n+3) fit X:= Budget.stack (Budget.tally z ((hb.born (k:=k+3) (by omega) hv hu).mono (by norm_num [fit]))) hZ
   have hp':0 ≤ (k+3:ℝ):= by positivity
   have ht:= ((preflight (C:=X) w hG hk hn hx).weighted (hb.trend (k:=k+3) (by omega) hv hu) (add_comm _ 1)); apply Arms.confirm _ (Arms.sum ht ((ringlet hb hv hu hZ w.wage hF hp).lo (add_le_add_right (mul_le_mul_of_nonneg_right (by norm_num [fit,stashp]) hp') _) le_rfl));
   filter_upwards [Foil.trans hb (k:=k+3) (by omega) hv hu] with i hi; funext j x; let y:= Z i j x; unfold aperture; rw [paneHolds _ _ _ _ _ _ hi.2.2.1, ← input_zero (G:=G) (m:= H i), paneHolds _ _ _ _ _ _ hi.2.2.1]; change f i* Φ i (z i,y)- f i* Φ i (z i,0) - _= (f i)* (Firm.projected (Φ i) (℘ i) (z i,y))+ ((f i)* Radar.gap _ (z i,y)- b i*_); rw [Firm.shaded]; simp only [Pi.sub_apply,put,Radar.gap,Function.comp_apply]; change _= _; ring
end transition
end YM.Contacts.Allium
