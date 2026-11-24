import YM.Contacts.Junction.Natural
/-! # shifting aperture around region. Transfers relat. `Ex..` -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω' s a:ℝ}{n k j r i:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform StagePort
open Push.AbsoluteSums SectorMeasure Presented Next.Fluctuations Next.Fluctuations.Sector
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => (fun i=> Dew.X (ι i))
local notation "Y" => (fun i=> Dew.Y (ι i))
local notation "μ" => (fun i=>StagePort.μ (Φ i))
local notation "γ" => γC (ι)
variable {N:Meter}{Q:ℝ→ℝ}
section global
local notation "η" => Real.exp 1
variable (p:StagePort G U P X k L σ C M n)
local notation "D" => (p.dew)
def windC (p:StagePort G U P X k L σ C M n) (d:ℝ) := wick G L d p.pearlRide
structure Quiescent (d q:ℝ)(x:(D).X):Prop where
    near : ‖x‖ < p.flag
    support (u:(D).B.Slice G): u∈ relative (D) (windC p d) x→ flags p.budget.threshold ((D).B.drape u)=∅
    outside : let Yz:= relative (D) (windC p d) x; let V:= p.notion x; let U:= (D).B.order G; (∫ z in Yzᶜ,V z ∂U)≤q*∫ z in Yz,V z ∂U
-- effective estimates Norm- unscaled
abbrev spare (p:StagePort G U P X k L σ C M n)(D':ℝ)(y:p.dew.X):= ∫ u in linearStay p.dew D' y,p.traceK y u ∂p.dew.B.order G
abbrev modest (A:ℝ)(x:(D).X):= ∫ z in closedBall 0 A,p.shadeV x z ∂p.μ
def allowancePin (x:(D).X):= p.push x / (p.dream x)
lemma reader {p:StagePort G U P X k L σ C M n}{z:p.dew.X} (h:Up p d a j) (he:Quiescent p t s z) (hh:∀ z:Config G p.dew.f, flags p.budget.threshold z=∅→|p.poll z|≤1) (hs:0 ≤ s)(hD:relative p.dew (windC p t) z⊆ linearStay p.dew K z) : (p.push z ≤ spare p K z+ η^2*s*spare p K z) ∧(∀ b:ℝ,spare p b z≤p.push z) := by
   let B:= relative p.dew (windC p t) z; let S':=linearStay p.dew K z; let V:=p.dew.B.order G; let f(w:p.dew.B.Slice G):= p.traceK z w; let u:=p.notion z; let a:=spare p K z; let b:=∫ y in B,f y ∂V; let c:=∫ y in B,u y ∂V; have hx:=he.outside; have hf: Integrable f V:= (StagePort.billsV h z).2.integrable _; have hu:Integrable u V:= (StagePort.billsV h z).1.integrable _; have hp:= StagePort.actual_both (p:=p) z; have hb: MeasurableSet B:= staying_meas ..; have hh':∀ y: p.dew.B.Slice G, u y≤ η*f y:= by
        intro y; have h:= (hp y).2.1; rw [Real.exp_neg] at h; exact (inv_mul_le_iff₀ (Real.exp_pos _)).1 h
   have hc : c≤ η*b:= (integral_mono hu.integrableOn (hf.integrableOn.const_mul η) hh').trans_eq (MeasureTheory.integral_const_mul ..); have hm : b ≤ a:= setIntegral_mono_set hf.integrableOn (Eventually.of_forall fun x=>(hp x).1) (Eventually.of_forall fun i=>show i∈B → i∈ S' from fun h=> hD h)
   rw [StagePort.fiscal h hh z]; constructor; swap; · intro k; exact setIntegral_le_integral hf (Eventually.of_forall fun i=> (hp i).1)
   erw [← integral_add_compl hb hf]; change b+(∫ y in Bᶜ,f y ∂V)≤ a+ _;
   have hℓ : (∫ y in Bᶜ,f y ∂V)≤ η*(s*c):= ( (integral_mono («μ»:=V.restrict Bᶜ) hf.integrableOn (hu.integrableOn.const_mul η) (fun i=> (hp i).2.2))).trans ((MeasureTheory.integral_const_mul ..).trans_le (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le)); apply add_le_add hm; apply hℓ.trans; have he:= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)) hs) (Real.exp_pos (1:ℝ)).le; change _ ≤ η^2*s*a; nlinarith only [he]
end global
namespace Travel
open Loom.Patch
variable (p:Travel N Q Φ)(hk:2≤k)(hn:k≤n)(hG:G.Simple)(hp:LocalRatio P)(hd:0<d)
local notation "g" => (arcCoast Φ d)
local notation "R" => (arcCoast Φ (2*d))
local notation "r" => (arcCoast Φ (d/2))
local notation "H₀" => Frame.Bank (fun i=>(Φ i).dew.X) (fun _=>1)
local notation "v₀" => Real.exp 1
-- single proof comparison.Des.State index call.
include p hk hn hG hp hd
-- inside.
lemma placed : ∀ᶠ i in atTop, let v:=Φ i; ∀ x∈ H₀ i, let y:= v.flag • x; spare v (g i) y=v.dream y * modest v (g i) x := by
    obtain ⟨d',a,j,_,_,H⟩:= p.ship; filter_upwards [H,p.seen hk hn hG hp hd] with i hi h v x hx y; exact transfer_c hi.2 hp (h x hx)
private lemma bill_tip (i:ℕ) : r i=g i/2∧ R i=2*g i ∧0<r i ∧ r i≤ R i:= by
    let v:= Delay.fineMonitor G L (Φ i).pearlRide; have hv:0<v:=Delay.monitor_pos ..; unfold arcCoast wick; change (d/2*v=d*v/2 ∧2*d*v=2*(d*v)∧ 0<d/2*v ∧ d/2*v≤2*d*v); refine ⟨by ring, by ring,mul_pos (half_pos hd) hv,mul_le_mul_of_nonneg_right (by linarith) hv.le⟩
def crestT (Φ:ℕ→StagePort G U P X k L σ C M n)(z:ℝ)(i:ℕ) :ℝ:= ((Φ i).μ).real (closedBall (0:(Φ i).dew.Y) (arcCoast Φ z i))ᶜ
lemma rent_pair (he:e<0): ∀ᶠ i in atTop, let v:= Φ i; let w:=R i; let t:=r i; let f:= summitK Φ (d/2); let a:= N.pow e i; ∀ x∈ H₀ i, let u:= v.flag • x; Quiescent v d a u→
    (‖modest v t x-f i x‖≤ v₀^2*a)∧
    (modest v w x≤ modest v t x+ v₀^2 * crestT Φ (d/2) i)∧ modest v w x ≤ v₀^2 := by
   have ht:= half_pos hd; have hh:= mul_pos (show (0:ℝ)<2 by norm_num) hd; filter_upwards [N.eventual, glow p hk hn hG hp hh,p.warm_precise hk hn hG hp hh he,p.travels hd] with i hi hk h hm v s t f a x hx u h';
   obtain ⟨hV,hF⟩:= hk.2 _ hx; obtain ⟨ht',hw,ht,h_l⟩:= bill_tip p (by assumption) hn hG hp hd i; let S:=closedBall (0:v.dew.Y) s; let T:=closedBall (0:v.dew.Y) t; let a':= modest v t x; let b':= modest v s x; have hTS:T ⊆ S := closedBall_subset_closedBall h_l; let O:= v.shadeV x; let f':= f i x
   have hr:S \ T ⊆ Tᶜ:= fun i hi=> hi.2; have hu : f'=∫ z in T, v.warmth x z ∂v.μ := rfl;
   have hX (z:v.dew.Y) (hz:z∈ S) : ‖O z‖≤v₀^2:= by unfold O shadeV; have ht:= h x hx z hz; split; exact (Real.norm_of_nonneg ht.1.le).trans_le ht.2.1; rw [norm_zero]; positivity
   refine ⟨?_,?_,?_⟩;
   · have hp':∀ y∈ T,‖O y-v.warmth x y‖≤ v₀^2*a:= by intro y hy; unfold O shadeV; rw [if_pos]; exact (h x hx y (hTS hy)).2.2; apply h'.support (v.stainP u y); apply (hm u h'.near).1; change _∈ linearStay v.dew (g i/2) u; rw [← ht']; exact ⟨_,⟨y,hy,rfl⟩,rfl⟩;
     change ‖a'-f'‖≤_; unfold a' modest; rw [hu,← MeasureTheory.integral_sub (hV.mono_set hTS) (hF.mono_set hTS)]; apply (norm_setIntegral_le_of_norm_le_const (measure_lt_top ..) hp').trans; apply mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hi.le _)); exact (measureReal_mono (Set.subset_univ _) (measure_ne_top v.μ _)).trans_eq probReal_univ
   · apply (sub_le_iff_le_add').1; change ((∫ y in S,O y ∂v.μ)-(∫ y in T,O y ∂v.μ))≤_; rw [← MeasureTheory.setIntegral_sdiff measurableSet_closedBall hV hTS]; exact (le_abs_self _).trans ((norm_setIntegral_le_of_norm_le_const (f:=O) (measure_lt_top ..) fun z hz=> hX z (sdiff_subset hz)).trans (mul_le_mul_of_nonneg_left (measureReal_mono hr (measure_ne_top v.μ (Tᶜ))) (sq_nonneg _))) -- real vs abs etc
   · unfold modest; apply (le_abs_self _).trans; apply (norm_setIntegral_le_of_norm_le_const («μ»:=v.μ) (measure_lt_top ..) hX).trans; exact mul_le_of_le_one_right (sq_nonneg _) ((measureReal_mono (Set.subset_univ _) (measure_ne_top v.μ _)).trans_eq probReal_univ)
-- refund raw log without statement of matching.Fence use. `Ticket.tail` price by calibration. Eventually p.L.R.WorkAdvance.Error.S.
def capT (Φ:ℕ→StagePort G U P X k L σ C M n)(y:ℝ) (i:ℕ)(x:(Φ i).dew.X) := Real.log ((Φ i).push x) - Real.log ((Φ i).dream x) - Real.log (summitK Φ (y/2) i (((Φ i).flag)⁻¹ • x))
lemma crest_moved (e:ℝ): N.Rush e (crestT Φ d):= by
   have he:=(p.heat hd).powers 0 e; simpa only [pow_zero,_root_.MeasureTheory.setIntegral_one_eq_measureReal] using! he -- notation power.s
lemma interlock (he:e<0) : N.Funds (fun i b=>∀ x∈ H₀ i, let u:=(Φ i).flag • x; Quiescent (Φ i) d (N.pow e i) u→
     ‖allowancePin (Φ i) u-summitK Φ (d/2) i x‖≤ b) e := by
   let Z i:= crestT Φ (d/2) i; let N' i:= N.pow e i; let V i:= v₀^2 * N' i; let H i:= (V i+ v₀^2 * Z i)+ V i*v₀^2; have hp' : N.Rush e V:= Meter.Rush.any (p:=e)|>.multiplier _; have h':N.Rush e H:= (hp'.blend (p.crest_moved hk hn hG hp (half_pos hd) e|>.multiplier _)).blend (hp'.bind _); obtain ⟨d',a,j,_,_,h⟩:=p.ship; refine ⟨H,h',?_⟩; -- d shadow notational hygiene
   filter_upwards [N.eventual,p.rent_pair hk hn hG hp hd he,p.placed hk hn hG hp (mul_pos (by norm_num : 0 < (2:ℝ)) hd), p.placed hk hn hG hp (half_pos hd), h,p.quake_model hk,p.travels hd] with i hi hp' hA ht hs hQ hw; let v:= Φ i; let q:= N' i; let g':= V i; let v':=H i; let D:=v.dew; have ht₀:0≤Z i:= measureReal_nonneg; have hq:0≤q:= Real.rpow_nonneg hi.le _; have hh:0≤V i:=by change 0 ≤ v₀^2*q; positivity
   refine ⟨add_nonneg (add_nonneg hh (mul_nonneg (sq_nonneg _) ht₀)) (mul_nonneg hh (sq_nonneg _)), ?_ ⟩
   intro x hx u h₀; let k:= summitK Φ (d/2) i x; obtain ⟨hpL,hpH,hpB⟩:= hp' x hx h₀; let K:=v.dream u; have hK: 0<K:=StagePort.matter hs.2.truePE hp _; obtain ⟨hF,hU⟩:= reader (K:=R i) hs.2 h₀ hQ hq (by have hh: (relative (Φ i).dew (g i) u⊆ linearStay (Φ i).dew (2*g i) u):= (hw u h₀.near).2; rw [(bill_tip p hk hn hG hp hd i).2.1]; exact hh); let V₀:=spare (Φ i) (R i) u; let Z₀:= modest (Φ i) (r i) x; let T:= modest (Φ i) (R i) x; let P:=allowancePin v u; have hp₁: v.push u=P*K:= by change _=v.push u/K*K; exact (div_mul_cancel₀ _ hK.ne').symm
   have heA:V₀=K*T:= hA x hx; have hpB: T ≤ v₀^2 := hpB; have hpH : T ≤ Z₀ + v₀^2 * Z i := hpH; change ‖P-k‖ ≤ v'; apply abs_le.mpr; change |Z₀-k| ≤ V i at hpL; have hL: Z₀ ≤ P:= by
      change Z₀ ≤ v.push u/K; rw [le_div_iff₀ hK]; rw [mul_comm]; exact (ht x hx).symm.le.trans (hU (r i));
   constructor; · unfold v' H; linarith only [(abs_le.mp hpL).1,hL,mul_nonneg (sq_nonneg (Real.exp 1)) ht₀,mul_nonneg hh (sq_nonneg (Real.exp 1))] -- commute
   change v.push u≤ V₀+ g' * V₀ at hF; rw [hp₁,heA, mul_comm P K] at hF; apply (sub_le_iff_le_add).mpr; unfold v' H; unfold g' at hF; have hl : P ≤ T+V i*T:= le_of_mul_le_mul_left (hF.trans_eq (by ring)) hK; nlinarith only [hl,hpH,(abs_le.mp hpL).2,mul_le_mul_of_nonneg_left hpB hh] -- g'.unfold
private lemma theft (x y:ℝ)(hx:1/2<y)(he:‖x-y‖<1/4): 0<x∧ ‖Real.log x-Real.log y‖≤4*‖x-y‖:= by
   have hv:1/4 < x:= by linarith only [(abs_lt.mp he).1,hx]
   refine ⟨by linarith only [hv],?_⟩; let S:=Set.Ioi (1/4:ℝ); apply (convex_Ioi (𝕜:=ℝ) _).norm_image_sub_le_of_norm_deriv_le (f:=Real.log) _ _ (show y∈S from (by change _<y; linarith)) hv; · exact fun i hi=> Real.differentiableAt_log (show i≠0 from (by have hh:1/4< i:=hi; linarith));
   intro i hi; have hp:1/4< i:= hi; have hx:0< i:=by linarith
   rw [Real.deriv_log, Real.norm_of_nonneg (inv_nonneg.mpr hx.le)]; exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
lemma log_sun (he:e<0): N.Funds (fun i b=>∀ x:(Φ i).dew.X,Quiescent (Φ i) d (N.pow e i) x→ 0<(Φ i).push x ∧ ‖capT Φ d i x‖≤ b) e:= by
   obtain ⟨f,hf,H⟩:= (interlock p hk hn hG hp hd he).cap; let t i:=4*f i; let a:ℝ:=-1/6; have ha: Capture.race < a:= by norm_num [Capture.race,a]
   have hu:a<0:=by norm_num [a]
   have h:= heard (Φ:=Φ) p hG hk hn hp (half_pos hd) ha hu; refine ⟨t,hf.multiplier 4,?_⟩; filter_upwards [H, Capture.Budget.limits h hu (1/2) (by norm_num),p.f_current.pos,Meter.sliding hf he _ (by norm_num: (0:ℝ)<1/4), p.dawn] with i hi hh hX hA hf; refine ⟨mul_nonneg (by norm_num) hi.1, fun x hq =>?_⟩;
   let v:= Φ i; let D:= v.dew; let u:v.dew.X:= v.flag⁻¹ • x; have hh': v.flag • u=x:= smul_inv_smul₀ hX.ne' x; let V:= allowancePin v x; let U := summitK Φ (d/2) i u; have hx : u∈ H₀ i := mem_ball_zero_iff.mpr (show ‖u‖<1 from (by unfold u; rw [norm_smul_of_nonneg (inv_pos.mpr (show 0<v.flag from hX)).le, inv_mul_lt_iff₀ (show 0<v.flag from hX)]; exact lt_of_lt_of_le hq.near (mul_one v.flag|>.symm.le) ))
   have hu : ‖V-U‖≤ f i:= by unfold V; rw [← hh']; exact hi.2 u hx (show Quiescent v d (N.pow e i) (v.flag • u) from hh'.symm ▸ hq)
   have hv : 1/2 < U:= by have ht: - (1/2:ℝ)< U-1:=(abs_lt.mp (show |U-1|<1/2 from hh ⟨u,hx⟩)).1; linarith only [ht]
   obtain ⟨hr,ht⟩:= theft p hk hn hG hp hd V U hv (hu.trans_lt ((le_abs_self _).trans_lt hA)); let P:=v.dream x; have hp :0<P := StagePort.matter hf hp x; have he : 0<v.push x:= by simpa using ((lt_div_iff₀ hp).1 (show 0<v.push x/P from hr))
   refine ⟨he,?_⟩; change ‖Real.log (v.push x)-Real.log P-Real.log U‖ ≤ _; rw [← Real.log_div he.ne' hp.ne']; apply ht.trans; exact mul_le_mul_of_nonneg_left hu (by norm_num)
end Travel
end Provision
end YM.Contacts.Junction
