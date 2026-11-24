import YM.SignedWilsonExpansion.Fire.Dues
import YM.ForFlash.F9.Oven

set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.Integration.Exporter
open Function Filter Finset Lattice RG Wilson Asymptotics Real
open Push.GridApprox YM.SignedWilsonExpansion.Commission
open OPE.Therm
open scoped Topology ENNReal BigOperators Classical
open YM.SignedWilsonExpansion.Purchases UVClock Schedules
open YM.SignedWilsonExpansion.Purchases.HalfRoof.Minty YM.SignedWilsonExpansion.Purchases.HalfRoof.Cooking
open WilsonCoeffUV.Bank PathCost WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa
open Logwood.HeatS
variable {G: Gauge}{ι:Type}{H:Family G}{J:Levels G}{j w v k x N p f r c b:ι→ℕ} -- ι order
variable {L:Filter ι}{ρ B T M D:ι→ℝ}{α d τ n a u h e:ℕ}
variable (g:G.Simple)(h':GentleS J)(vB:Rise B L) (pρ:∀ᶠ i in L,0<ρ i) (pB:B=ᶠ[L] βClock G ρ)
namespace Loans
include g vB pρ pB
local notation "S"=> LogLength ρ
local notation "Ξ"=> J.S.scale
local notation "℘₀"=> Spread B
structure AgeReadForFlash (α a D:ℕ)(L:Filter ι)(J:Levels G)(ρ B:ι→ℝ)(f k v r:ι→ℕ)(g₁:ι→ℝ): Prop where
    fast : hereD J ρ f ≤ᶠ[L] payD B (-1/2)
    far  : ∀ᶠ i in L,ρ i ≤ J.clock.hatBeta ( f i )^α * J.S.a (f i)
    owner : f ≤ᶠ[L] k
    -- from `WilsonAddressedCollarWindow` paid with arbitrary real `slop=1`
    sizeAt : ∀ᶠ i in L, let q:= J.S.a (f i) / J.S.a (k i); let Z:= J.clock.hatBeta (f i); Z^a ≤ q ∧ q≤ Z^(a+1)
    buried : (fun i=>v i+2) ≤ᶠ[L] f
    bought : Glow J ρ B L v
    -- true landing & given g₁ at capture (not v_age). Later use physical g at r_age endpoint.
    stop_age : r ≤ᶠ[L] v
    grasp : (Glow J ρ B L v) → IsEquivalent L g₁ (mark B)
    step     : ∀ᶠ i in L,J.S.a (v i)/J.S.a (r i) ≤ (g₁ i^D)^2 ∧ J.S.scale (v i)-J.S.scale (r i) ≤ 4*(2*(D:ℝ)+1)* log (g₁ i)⁻¹
variable (P: AgeReadForFlash α a d L J ρ B f k v r M)
include P
lemma AgeReadForFlash.reporter : Glow J ρ B L f:=by
    let K:= P.fast; have hp : hereD J ρ f ≤ᶠ[L] (1:ι→ℝ):= P.fast.trans ( ( payD_fee vB ( by norm_num: -(1:ℝ)/2 ≤ 0) ).trans ( Eventually.of_forall fun i=> Eq.le (congr_fun (payD_zero B) i) ) ); apply from_lag (a:=α) g vB pρ pB g hp; filter_upwards [P.far,pρ] with i hi hz; exact (div_le_div_iff₀ (pow_pos ( zero_lt_one.trans ( J.fits.delayed (f i) ) ) α) hz).mpr (by rw[one_mul,mul_comm]; exact hi)
lemma AgeReadForFlash.file : Glow J ρ B L k:=by
   have hp:= P.reporter g vB pρ pB; let X(i):= (J.clock.hatBeta ( f i)); have Hx:= spread_tie vB (epoch_wave vB pB hp); refine grown_cp g vB pρ pB hp P.owner ( ?_ ); apply IsBigO.trans (g:=fun i:ι=> ((a+1:ℕ):ℝ)*Spread X i) -- annotate field name wrong (uses y?)
   · apply IsBigO.of_norm_eventuallyLE; filter_upwards [P.sizeAt,P.owner] with i hi hk; rw [Real.norm_of_nonneg (sub_nonneg.mpr (scales J.S hk)), σStub]; apply le_trans (log_le_log ( div_pos (J.S.a_pos _) (J.S.a_pos _)) hi.2); exact Eq.le (log_pow ..)
   exact ( isBigO_const_mul_self _ _ _ ).trans Hx.isBigO
include h' in
lemma AgeReadForFlash.capture : Glow J ρ B L v:=by
    exact P.bought
include h'
lemma AgeReadForFlash.past : Glow J ρ B L r:=by
    let Q:= memo_log vB ( P.grasp (P.capture g h' vB pρ pB) ); refine grown_pc g vB pρ pB (P.capture g h' vB pρ pB) P.stop_age ( IsBigO.trans (?_) (( Q.2.const_mul_left (4*(2*(d:ℝ)+1))) ) ); apply IsBigO.of_norm_eventuallyLE; filter_upwards [P.stop_age,P.step] with i hi hx; rw [Real.norm_of_nonneg ( sub_nonneg.mpr (scales J.S hi) ) ]; exact hx.2
lemma AgeReadForFlash.camp : Camp J L ρ B f k r:=⟨vB,pB,P.owner,⟨1/2, by norm_num, by simpa only[neg_div] using P.fast⟩, P.stop_age.trans ((show v≤ᶠ[L]f from P.buried.mono fun i hi=> (Nat.le_add_right ..).trans hi).trans P.owner), P.file g vB pρ pB,P.past g h' vB pρ pB⟩ -- by norm_num builds inversion neg form?
lemma AgeReadForFlash.horizon : Consume B L (-(a:ℝ)) (fun i=>paceT J.S ( f i ) (k i)):=by
    refine IsBigO.trans (?_) ( money_curve vB ( epoch_wave vB pB (P.reporter g vB pρ pB)) a).2; apply IsBigO.of_norm_eventuallyLE; filter_upwards [ P.sizeAt ] with i h; unfold paceT; have p:(J.clock.hatBeta (f i))^a ≤ J.S.a (f i)/ J.S.a (k i):=h.1; rw [Real.norm_of_nonneg (div_nonneg (J.S.a_pos _).le (J.S.a_pos _).le)]; exact ((inv_div ..).symm.trans_le (inv_anti₀ ( pow_pos (zero_lt_one.trans ( J.fits.delayed _ )) _ ) p))
lemma AgeReadForFlash.lower : let T:ℕ:= α+a+2; payD B (-(T:ℝ)) ≤ᶠ[L] hereD J ρ k:=by
   intro T; let K:= J.clock.hatBeta ∘ f; let e:= α+(a+1); let E:=payD B T; have he:( fun i=> K i^e ) ≤ᶠ[L] E:= Consume.tuck vB ( money_curve vB (epoch_wave vB pB (P.reporter g vB pρ pB)) e ).1 (by exact_mod_cast ( show e<T by unfold e T; omega)); filter_upwards [he, pρ,P.far,P.sizeAt] with i he hp hf hv; rw [payD_inv,Pi.inv_apply, ←one_div, hereD,sizeT]; let p:=J.S.a_pos (k i); let F(i):=J.S.a (f i); let H:=zero_lt_one.trans (J.fits.delayed (f i))
   apply ( div_le_div_iff₀ (pay_pos .. ) hp ).mpr; rw [one_mul]; have hc: ( K i^e )* J.S.a ( k i )≤ payD B T i*J.S.a ( k i ) := mul_le_mul_of_nonneg_right he p.le; rw [mul_comm]; refine hf.trans (le_trans (?_) hc); change K i^α * F i≤ K i^e* _; unfold e; rw [pow_add,mul_assoc]; exact mul_le_mul_of_nonneg_left (( div_le_iff₀ p ).mp hv.2) ( pow_nonneg H.le _ )
variable {δ:ℝ}
lemma AgeReadForFlash.closes (h:-(a:ℝ)+(-1/2)< -δ) : hereD J ρ k ≤ᶠ[L] payD B (-δ) :=by
    let Q:=P.horizon g h' vB pρ pB -- replace h' omitted
    have hm:= Consume.tuck vB (Schedules.Consume.mul Q (Schedules.Consume.ordered (pρ.mono fun i hi=>sizeT_pos J hi ( f i)|>.le) P.fast)) h; filter_upwards [hm,pρ] with i hi ht; change _≤_; refine le_trans (le_of_eq ?_) hi; rw [Pi.mul_apply]; unfold hereD sizeT paceT; field_simp [(J.S.a_pos (f i)).ne']
lemma AgeReadForFlash.stop_time (h: -(d:ℝ)+1< -4*δ): Consume B L (-δ) (fun i=> trailC J.S ( r i ) (k i)):=by
    let Q:= ( Real.tendsto_log_atTop.comp vB ); let Ψ:= fun i=> M i^( d * 2 ); have ht:= (( P.grasp (P.capture g h' vB pρ pB) ).isBigO ).trans ( penMap vB (EventuallyEq.rfl)); have he : Consume B L (-(d:ℝ)) Ψ := by
        convert Schedules.Consume.power ht (n:= d*2) using 1; · push_cast; ring
        funext; rfl
    have hz: (fun i=>paceT J.S (r i) (k i)) ≤ᶠ[L] Ψ:=by
        filter_upwards [P.step,P.buried,P.owner] with i hi hx hw; exact le_trans (div_le_div_of_nonneg_right (J.S.strictAnti.antitone ((Nat.le_add_right ..|>.trans hx).trans hw)) (J.S.a_pos _).le) ( hi.1.trans (le_of_eq (pow_mul ..).symm ) )
    have hQ:= hz.trans ( Consume.tuck vB he (by linarith only [h]: -(d:ℝ) < -4*δ) ); apply Schedules.Consume.ordered (Eventually.of_forall fun i=> Real.exp_nonneg _) ; filter_upwards [hQ] with i hi; unfold payD; apply exp_le_exp.mpr; have hv:=Real.log_le_log ( div_pos (J.S.a_pos _) (J.S.a_pos _)) hi; simp only [paceT,payD,Real.log_exp] at hv; linarith only[hv, σStub J (r i) (k i)] -- extraction
end Loans
end YM.Integration.Exporter

end

set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.Integration.Exporter
open Function Filter Finset Lattice RG Wilson Asymptotics Real
open Push.GridApprox YM.SignedWilsonExpansion.Commission
open OPE.Therm
open scoped Topology ENNReal BigOperators Classical
open YM.SignedWilsonExpansion.Purchases UVClock Schedules
open YM.SignedWilsonExpansion.Purchases.HalfRoof.Minty YM.SignedWilsonExpansion.Purchases.HalfRoof.Cooking
open WilsonCoeffUV.Bank PathCost WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa
open Logwood.HeatS
variable {G: Gauge}{ι:Type}{H:Family G}{J:Levels G}{j w v k x N p f r c b:ι→ℕ} -- ι order
variable {L:Filter ι}{ρ B T M D:ι→ℝ}{α d τ n a u h e:ℕ}
variable (g:G.Simple)(h':GentleS J)(vB:Rise B L) (pρ:∀ᶠ i in L,0<ρ i) (pB:B=ᶠ[L] βClock G ρ)
namespace Loans
variable (P: AgeReadForFlash α a d L J ρ B f k v r M)
-- f-c width window via Visit.mesh from P grant.
include vB pB pρ P h' g
variable (R:Realm G (e+1) Credit.leanC)
lemma awakenGForFlash (h₁:R.draws=J) {δ ζ:ℝ}(p:δ≤(h:ℝ)*a)(q:δ ≤ (u:ℝ)/2)(b:0<ζ)(z:4*δ≤ ζ)(hx: -(d:ℝ)+1< -4*δ): Angles e R h u ρ (ell₁ J ρ B) f k r (corn J B ζ k) L B δ:=by
   subst J; refine ⟨(payD_move vB (by linarith: (u:ℝ)*(-1/2) ≤ -δ) ( Consume.powerReading vB P.fast ( pρ.mono fun i h'=> sizeT_pos _ h' _|>.le ) u )), payD_move vB (by linarith only [p]: (h:ℝ)*(-(a:ℝ))≤ -δ) (Schedules.Consume.power (P.horizon g h' vB pρ pB)), P.stop_time g h' vB pρ pB hx,( payD_move vB (by linarith only [z]:-ζ/4 ≤ -δ) ( Schedules.Consume.ordered ( Eventually.of_forall fun i=>trail_pos .. |>.le ) ( corn_trail vB h' g pB pρ b ) )) ⟩ -- unfold
end Loans
end YM.Integration.Exporter

end

set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.SignedWilsonExpansion.Fire
open Function Filter Asymptotics Gauge Wilson RG Real Lattice
open Purchases UVClock Schedules Dancer Dancer.Supper WilsonCoeffUV WilsonCoeffUV.Bank PathCost
open Commission Purchases.HalfRoof.Cooking Purchases.HalfRoof Purchases.HalfRoof.Minty
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ Stair PorchK Source
open Pert.Asymptotics Integration.Exporter.Loans
open XSpace FVA2 MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book
open WardBin
open scoped Classical BigOperators Topology
variable {G:Gauge} {ι κ: Type} {H:Levels G} {a b d n h u ξ q p K e V:ℕ}{U:Filter ι}{L:Filter κ}
variable {B r X A:ι→ℝ} {f y z c v N j l k:ι→ℕ} {s : κ→ι}
section

variable (w:G.Simple)(W:GentleS H)(g:Tendsto r U Trace.Pilot.trail) (Z:AgeReadForFlash a b ξ U H r (cck G ∘ r) f k v j B)
-- k reserved birthday. v capture. j older stop. horizon h & e modest. S issued
include w W g Z
lemma movesForFlash (hu:Tendsto s L U) : AgeReadForFlash a b ξ L H (r∘ s) (cck G∘r∘ s) (f∘s) (k∘s) (v∘s) (j∘s) (B ∘ s):=by
   exact ⟨hu.eventually Z.fast,hu.eventually Z.far,hu.eventually Z.owner, hu.eventually Z.sizeAt,hu.eventually Z.buried,Z.bought.comp_tendsto hu, hu.eventually Z.stop_age,fun _=>( Z.grasp ( Z.capture w W ( radius_clock w g ) (g.eventually self_mem_nhdsWithin) (EventuallyEq.rfl))).comp_tendsto hu,hu.eventually Z.step⟩
end
variable (R:Realm G (e+1) Credit.leanC){F:Labels.Frames G}{Ω : Council F}{F':Initialize G}{Q:∀h,Rays G h F'.hol}
variable (Y:Normalize.Store G)(Kb: Rose.Pick Y){T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S':Prescription (Press.portDeck G)}(M:Speed.Quoted F' Kb T S')
variable (headV:6≤d)
section
variable (w:G.Simple)(W:GentleS R.draws)(g:Tendsto r U Trace.Pilot.trail)(Z:AgeReadForFlash a b ξ U R.draws r (cck G ∘ r) f k v j B)
variable (pv:∀ i,0<r i)(s:Axis)
local notation "J" => R.draws
local notation "X₁" => cck G ∘ r
local notation "ξ₀"=> βNeed a b
local notation "Y₀"=> goalX p V d ξ₀
local notation "ℨ"=> demandΦ p V d a b
local notation "M₀"=> ℐ Y₀
local notation "ℓ₀"=> ell₁ J r X₁
local notation "m₀"=> m₁ J r X₁
local notation "C₁"=> corn J X₁ M₀ k
variable [U.NeBot](Pb:0<b)(ha:h=needH p V d a b)(ht:d≤h)(gp:(p:ℝ)/2<b)
variable (unit: u≤K)(tier:h+e≤K)(px: goalX p V d (βNeed a b)*2 ≤ u)(tu: (bankSize G F' Kb M w s h (headV.trans ht))*h ≤ u)(α:Ample h u (h+e))(b₁: target₀ p V d a b ≤ ξ)(he: demandΦ p V d a b ≤ e)
include Z g W M headV pv Pb ha ht gp unit tier px tu α b₁ he
lemma recruitmentForFlash {st:ℕ}(Φ:Hol G) (p₁:∀i,(Ω i).Sound Φ)(p₂:∀i,Bid.pop (Ω i))(P:Install Φ (Master.mk F.level Ω p₁ p₂) R K)(hZ:R.y= Ticket.zz R.draws)(Y': Campfire ι G e R.draws R.paid F' st)(z:IsEquivalent U X ( needle G ∘ r )) :
    ∃ (ℜ Y₁:ι→ℝ) (ζ: ι→ PorchK F' F Q Ω R h h u), Club Y Kb R ζ U ℓ₀ m₀ f k C₁ j X₁ Y₁ r ℜ X pv p d ℨ K (ξ₀:ℝ) (Y₀:ℝ) M s ∧ RoomForFlash R U X₁ ℓ₀ C₁ r pv F' Q F h h:=by
    let E:ℝ:=Y₀; have hp:0 < mildG:=MS.Tide.mild_p; have hu:0<M₀:=by unfold ℐ; positivity
    have hz:= radius_clock w g; let t:= Z.camp w W hz ( g.eventually self_mem_nhdsWithin ) (EventuallyEq.rfl); obtain ⟨U₁,Y₁,ζ,B'⟩:= raving R p₁ p₂ P pv W hZ Y' unit tier (le_refl h) α Q t M₀ hu
    let v':= g.eventually ( Trace.Pilot.trail |> fun _=> self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Set.Ioi 0) ); let r':= EventuallyEq.rfl (f:=cck G∘r) (l:=U)
    have E':0<E:=by unfold E goalX; positivity
    refine ⟨U₁,Y₁,ζ,⟨ B',headV,ht, le_rfl,tier,unit,tu,tu.trans unit,he,?_,⟨( isEquivalent_iff_tendsto_one ((hz.eventually_gt_atTop 0).mono fun i hi=> (inv_pos.mpr (sqrt_pos.mpr hi)).ne')).mp z⟩,⟨ b,gp,Z.closes w W hz v' r' (by linarith)⟩,Z.lower w W hz v' r', (?_:0<(ξ₀:ℝ)),E'.le,?_,?_⟩, roomForFlash R pv W Y' Q (b:=f) (F:=F) t M₀ hu⟩
    · unfold demandΦ; omega
    · unfold βNeed; positivity
    · refine awakenGForFlash (e:=e) w W hz v' r' Z R (δ:=Y₀) rfl ?_ ?_ hu ?_ ?_
      · apply le_trans _ (show (h:ℝ) ≤ (h:ℝ) * b from le_mul_of_one_le_right (Nat.cast_nonneg _) (Nat.one_le_cast.mpr Pb) ) -- name
        exact_mod_cast (show Y₀ ≤ h from (le_max_right d Y₀).trans_eq ha.symm)
      · have he : (Y₀:ℝ)*2 ≤ u:=by exact_mod_cast px
        linarith only [he]
      · unfold ℐ; have hv:0≤ E/MS.Tide.mildG:=(by positivity); change 4 * E ≤ 1 + 4 * E + E/MS.Tide.mildG; linarith only [hv]
      have hv: (4*(Y₀:ℝ)+2) ≤ ξ:= by exact_mod_cast ( (le_max_right (ℨ) (4*Y₀+2)).trans b₁ )
      linarith only [hv]
    · apply peerP_chip (z:=M₀) pv hz (corn_size hz W w r' v' ( campUnity R pv W t ) hu); unfold ℐ; have hv:E=E/MS.Tide.mildG * MS.Tide.mildG:= ( div_mul_cancel₀ E hp.ne' ).symm; change E ≤ (1 + 4 * E+ E/MS.Tide.mildG) * _; nlinarith only [ hv,E',hp,mul_pos hp E' ]
end
end YM.SignedWilsonExpansion.Fire

end