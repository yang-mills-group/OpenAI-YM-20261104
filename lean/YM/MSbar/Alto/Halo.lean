import YM.MSbar.Alto.Post
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}
open Supply Input
variable {O:ChartRatio G}{K:MapPrices} {B: Sheet G}{D: Rolls B}{Θ:Protection D}{T0:Delays Θ}{W: Bar T0}{I:Wait W}{P:PostCost D}(A:Directed G I O K P)
local notation "λ'"=> A.kin
variable (p:ℕ)(m k:ℕ)
noncomputable def hat (m:Levels G)(k:ℕ):= flurry (m.clock.hatBeta k)
noncomputable def candles (m:Levels G)(k:ℕ):= cWidth (m.clock.hatBeta k)
lemma inK : 0≤ candles A.a k:=by unfold candles cWidth; positivity
variable (h:G.Simple)(hA : Reports K B O A.a) (hp:Merit A.a A.M)
set_option quotPrecheck false
local notation "ρ" x=> candles A.a x
local notation "μ" x=> hat A.a x
include h
lemma hats : Tendsto (hat A.a) atTop atTop:=broad.comp (show Tendsto A.a.clock.hatBeta atTop atTop from tendsto_atTop_add_const_left _ _ (A.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos h)))
variable (s i N:ℕ)
local notation "C!"=> A.a.clock.op m i
local notation "B!"=> (A.a.clock.op m i).ratio
variable (F:Forest (A.a.clock.op m i).ratio)
variable (v:G.ColorIndex)(hs:6≤ s) {M:ℕ}(T:Scene A.a i p)(ht: Realized A.kin N i M p (Lis.sun G v) T)
include hA hp ht
omit ht in
lemma chosen (x:G.ColorIndex)(p i:ℕ)(hm:M≤ N): ∃ T: Scene A.a i p,Realized A.kin N i M p (Lis.sun G x) T:=by -- unneeded h,ht
   apply freezes A.kin P N _ _ A.support _ (sunny ..) A.ratio _ hm -- args check
   intro j hj hk; exact ⟨hp.towns ..,(hA.pulse j i).1⟩
-- actual integrator step estimates
variable (hm:m<N)(hr:M ≤ m)(hq:max p s ≤ A.a.clock.J m)
include hs hm hr hq
lemma solitaire (hZ:Wedge (T.Poly (m+1)) Dean (hat A.a (m+1)) (candles A.a (m+1)) s p): Wedge (T.Poly m) Dean (hat A.a m) (candles A.a m) s p ∧ (∀ j≤p, |PowerSeries.coeff j (T.action m)|≤ purse Dean (hat A.a m) j) :=by
    let j:= A.a.clock.J (m+1); let j':=A.a.clock.J m; have hq:max p s ≤ j:=hq.trans (A.a.fits.mono (Nat.le_succ m));
    obtain ⟨Z,hR,hc,h₁,hB,hG⟩:=(hA.stage m i s p ((le_max_right ..).trans hq) ((le_max_left ..).trans hq) hs).1
    let C' := A.a.clock.hatBeta; have hv : countV G ((A.a.clock.op m i).patch.L) (A.a.clock.hatBeta m) = A.a.clock.hatBeta (m+1) :=by unfold countV Calendar.hatBeta; rw [Schedule.scale_succ]; change _ + _ *Real.log (A.a.S.block m).val = _+ _* _; unfold Levels.S; ring
    rw [hv] at hR h₁ hB; have hu:1≤ hat A.a m:=hR.wise.1; have hu':hat A.a m≤hat A.a (m+1):=hR.wise.2; have hh:0< μ m:=zero_lt_one.trans_le hu
    obtain ⟨F,y,hb,hA',hV⟩:= ht.step m hm hr; obtain ⟨hx,hk⟩:=ht.budget (m+1) hm (by omega); let κ:= A.kin; let X:=κ.path N (m+1); let Y:=κ.path N m; let u:=A.a.params (m+1); let U:=A.a.params m; let g:= κ.stationary N m i F; obtain ⟨M',v₀,v₁⟩:=(hA.pulse m i).1
    have h₀:= ready A m N p i s F hp hm Z v y hs hx.quiet (by omega) (inK A m) hc hG (hh.trans_le hu') hB h₁ v₀ v₁ -- k,p arguments
    have he:= hp.towns m i; let L:= A.a.clock.op m i; have hS : Rolling.Serves L G:=⟨he.1,(A.a.blocks ..).symmetric,(A.a.blocks ..).gauge,he⟩; have hp:Matrix.PosDef (Push.Uniform.block (priced F y u.clip X) 0):=blueprint F y X u.clip he.1 hx.quiet (P.price _) (A.support.gap N m i hm F)
    have ht':=newT F y X Y u.clip U.clip g O A.ratio (T.Poly (m+1)) (T.film (m+1)) p hS (A.support.critical N m i hm F).1 (A.support.classicalPart N m i hm F) hx hp
    have hy(j₀)(hj:j₀≤p):= paths F Dean ranked _ X u.clip g Y U.clip y _ O (T.Poly (m+1)) (T.film (m+1)) v hx h hk hR h₀ hZ hb (show Keeps _ _ _ from hV ▸ (ht.budget m hm.le hr).2) ht'.plane ht'.bond j₀ hj
    refine ⟨⟨fun r he=>?_⟩,fun j he=> hy j he|>.2.2⟩; rw [hV]; refine ⟨(hy r he).2.1.dec,fun i hi j=>?_⟩; -- replace constant
    exact ((hy r he).2.1.fan i hi j).trans (div_le_div_of_nonneg_left ((hy r he).2.1.dec) (pow_pos hh _) (pow_le_pow_left₀ hh.le hu' _))
end YM.MSbar.Alto
