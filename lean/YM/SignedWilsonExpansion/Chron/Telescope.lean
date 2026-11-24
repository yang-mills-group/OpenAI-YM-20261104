import YM.SignedWilsonExpansion.Chron.Restitute
import YM.SignedWilsonExpansion.Purchase.Raving
/-!
# Campus' estimator budgeting from mixed book station pricing
Supports two homes. `ClockPort` stores sizes for gathered F. old & K ``Loans`` all REAL fittings derived later there. Coordinates crop power allowances *include* actual dimensions at K.
-/
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
lemma shutter (a: hereD J ρ f ≤ᶠ[L] (1:ι→ℝ)) : Rise ( J.clock.hatBeta ∘ f ) L:=by
     refine tendsto_atTop_mono' _ (?_) vB; filter_upwards [ a, pρ,pB ] with i hi hp hB; rw [hB]; unfold βClock; have hv:-(Ξ (f i)-S i)≤0:= Real.exp_le_one_iff.mp (by change exp _ ≤ _; rw [ ←pointD hp f ]; exact hi); simp only [Function.comp_apply,Calendar.hatBeta]; exact le_trans ( mul_le_mul_of_nonneg_left (sub_nonneg.mp (neg_nonpos.mp hv)) (Gauge.slopeConstant_pos g).le ) ( le_add_of_nonneg_left J.clock.bar_pos.le )
omit g vB pρ pB in
lemma subdued {U Z Y:ι→ℝ} (ht:∀ᶠ i in L,0≤Z i)(p:U≤ᶠ[L] Z)(w:∀ᶠ i in L,-(Y i)≤U i)(b:Z=O[L] B)(u:Y=O[L] B): U=O[L]B:=by
     apply IsBigO.trans _ ( b.norm_left.add u.norm_left ); apply IsBigO.of_norm_eventuallyLE; filter_upwards [ht,p,w] with i hp h hw; simp only[Real.norm_eq_abs, Pi.add_apply]; apply abs_le.mpr; constructor <;> linarith [abs_nonneg (Z i),abs_nonneg (Y i),le_abs_self (Z i),le_abs_self (Y i)]
-- above used irrelevant assumptions; remove
lemma star_path (x:Glow J ρ B L f)(w:j ≤ᶠ[L] f)(A:ℝ)(hp:1≤A)(z:∀ᶠ i in L, hereD J ρ j i≤ A) : Glow J ρ B L j:=by
    let V:= fun i=> Ξ (f i) - S i; let Y:= fun i=> Ξ ( j i )-S i; have hv: (fun _:ι=>log A)=O[L] ℘₀:= ( isLittleO_const_left.mpr ( Or.inr (tendsto_abs_atTop_atTop.comp (y_rise vB)) ) ).isBigO -- incorrect
    refine subdued (U:=Y) (B:=Spread B) (Z:=fun i=>|V i|) (Y:=fun i=>log A) (?_) (?_) (?_) x.norm_left hv
    · exact Eventually.of_forall fun i=> abs_nonneg _
    · exact w.mono fun i hi=> (sub_le_sub_right (scales J.S hi) _).trans (le_abs_self _)
    filter_upwards [pρ,z] with i hi hv; have ht:= log_le_log (sizeT_pos _ hi _) hv; rw [pointD_log hi j] at ht; linarith
lemma from_lag (g': G.Simple)(a0: hereD J ρ f ≤ᶠ[L] (1:ι→ℝ))(z: ∀ᶠ i in L,1/(J.clock.hatBeta (f i))^a ≤ hereD J ρ f i) : Glow J ρ B L f:=by
    let x (i):= Ξ (f i)- S i; let A:= J.clock.hatBeta ∘ f; let c := G.slopeConstant; have hp := shutter g vB pρ pB a0; have ht :(0:ι→ℝ)≤ᶠ[L] x :=by filter_upwards [a0,pρ] with i h hz; change hereD J ρ f i≤1 at h; rw [pointD hz f, exp_le_one_iff,neg_nonpos] at h; exact h
    have he: x ≤ᶠ[L] fun i=> a*Spread A i:=by filter_upwards [z,pρ] with i h hz; have p:= pow_pos ( zero_lt_one.trans ( J.fits.delayed (f i) ) ) a; have hh:=Real.log_le_log ( one_div_pos.mpr p ) h; rw [pointD_log hz f, Real.log_div (by norm_num: (1:ℝ)≠ 0) p.ne',log_pow,Real.log_one] at hh; change Ξ (f i)-S i ≤ a*log (J.clock.hatBeta (f i)); linarith
    have ha : x =O[L] (Spread A):=by apply IsBigO.trans _ (isBigO_const_mul_self (a:ℝ) (Spread A) L); exact IsBigO.of_norm_eventuallyLE (( he.and ht ).mono fun i h=> ( Real.norm_of_nonneg h.2 ).le.trans h.1 )
    have hm : Spread A =o[L] A:= ( show log=o[atTop] fun i=>i from by simpa using! isLittleO_log_rpow_atTop zero_lt_one ).comp_tendsto hp
    have hx : (B-A)=o[L] A:=by
       let hv:= ( ha.trans_isLittleO hm ).const_mul_left c |>.add (show (fun _=>J.clock.bar)=o[L] A from isLittleO_const_left.mpr (Or.inr (tendsto_abs_atTop_atTop.comp hp))) -- lemma inspect
       apply hv.neg_left.congr' (?_) (.refl ..); filter_upwards [pB] with i hi; unfold x c A; change -( _ + _) = B i-(J.clock.bar+_); rw [hi,βClock]; ring
    exact ha.trans (( spread_tie vB hx.isEquivalent.symm ).isBigO)
-- moves between stations
lemma grown_cp {Γ Γ':ι→ℕ} (h:Glow J ρ B L Γ)(q:Γ ≤ᶠ[L] Γ')(y: ((fun i=>Ξ (Γ' i)-Ξ (Γ i))=O[L] ℘₀)): Glow J ρ B L Γ':= (h.add y).congr_left fun i=> by ring
lemma grown_pc {Γ Γ':ι→ℕ} (h:Glow J ρ B L Γ')(q:Γ ≤ᶠ[L] Γ')(y:((fun i=>Ξ (Γ' i)-Ξ (Γ i))=O[L] ℘₀)): Glow J ρ B L Γ:= (h.sub y).congr_left fun i=> by ring
include h' in
lemma prev_cp (hp:Glow J ρ B L f)(q:∀ᶠ i in L,f i=x i+1): Glow J ρ B L x:= by
     have hx: x ≤ᶠ[L] f:= q.mono fun i t=> (x i |>.le_succ).trans_eq t.symm
     refine grown_pc g vB pρ pB hp hx ( (stairLimit vB J g h' ( epoch_wave vB pB hp ) hx ).isBigO.congr' (?_) (.refl ..) ); exact q.mono fun i h=>by dsimp only; rw [h]
omit g pρ pB
lemma money_curve (x: IsEquivalent L D B)(k:ℕ): Consume B L k (D^k) ∧ Consume B L (-(k:ℝ)) (D^k)⁻¹:=by
    have p:= beta_owe vB x; let K:=payD B 1; have hp:IsEquivalent L D K:=by refine x.trans_eventuallyEq (?_); exact (vB.eventually_gt_atTop 0).mono fun i hi=> by unfold K; rw [payD,one_mul]; exact (exp_log hi).symm; -- syntax
    constructor; · simpa using Consume.power (n:=k) p
    have hx : (D^k)⁻¹=O[L] ( (K^k)⁻¹ ):= ((hp.pow k).inv).isBigO; -- paren warning
    have hi:=payD_pow B 1 k; rw [mul_one] at hi; unfold Consume; rw [payD_inv,hi]; exact hx
variable {β ξ:ℝ}
lemma Consume.tuck (p:Consume B L β T)(t: β < ξ) : T ≤ᶠ[L] payD B ξ:= by
    filter_upwards [(p.trans_isLittleO ( payD_eps vB t )).bound (c:=1) zero_lt_one] with i hi; exact (le_abs_self _).trans (by rw [Real.norm_of_nonneg (pay_pos ..|>.le),one_mul] at hi; exact hi)
lemma Consume.powerReading (u:T ≤ᶠ[L] payD B β)(h:∀ᶠ i in L,0≤T i) (D:ℕ) : Consume B L (D*β) (T^D):= Schedules.Consume.power ( Schedules.Consume.ordered h u )
-- convert old clock quote at all regulators.Stretches. upper slack.
include g pρ pB
structure AgeRead (α a D:ℕ)(L:Filter ι)(J:Levels G)(ρ B:ι→ℝ)(f k v r:ι→ℕ)(g₁:ι→ℝ): Prop where
    fast : hereD J ρ f ≤ᶠ[L] payD B (-1/2)
    far  : ∀ᶠ i in L,ρ i ≤ J.clock.hatBeta ( f i )^α * J.S.a (f i)
    owner : f ≤ᶠ[L] k
    -- from `WilsonAddressedCollarWindow` paid with arbitrary real `slop=1`
    sizeAt : ∀ᶠ i in L, let q:= J.S.a (f i) / J.S.a (k i); let Z:= J.clock.hatBeta (f i); Z^a ≤ q ∧ q≤ Z^(a+1)
    buried : (fun i=>v i+2) ≤ᶠ[L] f
    bought : ∃ A > (1:ℝ), ∀ᶠ i in L,J.S.a (v i+1)≤ A*ρ i
    -- true landing & given g₁ at capture (not v_age). Later use physical g at r_age endpoint.
    stop_age : r ≤ᶠ[L] v
    grasp : (Glow J ρ B L v) → IsEquivalent L g₁ (mark B)
    step     : ∀ᶠ i in L,J.S.a (v i)/J.S.a (r i) ≤ (g₁ i^D)^2 ∧ J.S.scale (v i)-J.S.scale (r i) ≤ 4*(2*(D:ℝ)+1)* log (g₁ i)⁻¹
variable (P: AgeRead α a d L J ρ B f k v r M)
include P
lemma AgeRead.reporter : Glow J ρ B L f:=by
    let K:= P.fast; have hp : hereD J ρ f ≤ᶠ[L] (1:ι→ℝ):= P.fast.trans ( ( payD_fee vB ( by norm_num: -(1:ℝ)/2 ≤ 0) ).trans ( Eventually.of_forall fun i=> Eq.le (congr_fun (payD_zero B) i) ) ); apply from_lag (a:=α) g vB pρ pB g hp; filter_upwards [P.far,pρ] with i hi hz; exact (div_le_div_iff₀ (pow_pos ( zero_lt_one.trans ( J.fits.delayed (f i) ) ) α) hz).mpr (by rw[one_mul,mul_comm]; exact hi)
lemma AgeRead.file : Glow J ρ B L k:=by
   have hp:= P.reporter g vB pρ pB; let X(i):= (J.clock.hatBeta ( f i)); have Hx:= spread_tie vB (epoch_wave vB pB hp); refine grown_cp g vB pρ pB hp P.owner ( ?_ ); apply IsBigO.trans (g:=fun i:ι=> ((a+1:ℕ):ℝ)*Spread X i) -- annotate field name wrong (uses y?)
   · apply IsBigO.of_norm_eventuallyLE; filter_upwards [P.sizeAt,P.owner] with i hi hk; rw [Real.norm_of_nonneg (sub_nonneg.mpr (scales J.S hk)), σStub]; apply le_trans (log_le_log ( div_pos (J.S.a_pos _) (J.S.a_pos _)) hi.2); exact Eq.le (log_pow ..)
   exact ( isBigO_const_mul_self _ _ _ ).trans Hx.isBigO
include h' in
lemma AgeRead.capture : Glow J ρ B L v:=by
    obtain ⟨A,hp,hz⟩:= P.bought; apply prev_cp (f:=fun i=>v i+1) g h' vB pρ pB ( star_path g vB pρ pB (P.reporter g vB pρ pB) ( P.buried.mono fun i h=>le_trans (Nat.le_succ _) h ) A hp.le ( (hz.and pρ).mono fun i h=>(div_le_iff₀ h.2).mpr h.1 ) ) (Eventually.of_forall fun i=>rfl)
-- incomplete
omit g pρ pB P in
lemma memo_log (h:IsEquivalent L D (mark B)): (∀ᶠ i in L,0<D i) ∧ (fun i=>log (D i)⁻¹ )=O[L] (Spread B):=by
    let X:=mark B; have hp:Rise X⁻¹ L:= by
       let r:= mark_exp vB; apply ( payD_looms vB (by norm_num: (0:ℝ)<1/2)).congr'; refine r.mono (fun i hi=>?_); change payD B (1/2) i=(mark B i)⁻¹; rw [hi,payD,payD,←Real.exp_neg]; congr 1; ring
    have hx:= spread_tie hp h.inv
    let Y(i):= payD B (-1/2) i; have hw:Rise D⁻¹ L:= tends hp h.inv; have hy:= mark_exp vB
    refine ⟨(hw.eventually_gt_atTop 0).mono fun i h=> ( inv_pos ).mp h, ?_⟩; refine hx.isBigO.trans ( ( isBigO_const_mul_self (1/2:ℝ) (Spread B) L ).congr' (?_) (.refl ..) ); filter_upwards [hy] with i hi; change _=log ( UVClock.mark B i )⁻¹; rw [hi,log_inv,payD,log_exp]; ring
include h'
lemma AgeRead.past : Glow J ρ B L r:=by
    let Q:= memo_log vB ( P.grasp (P.capture g h' vB pρ pB) ); refine grown_pc g vB pρ pB (P.capture g h' vB pρ pB) P.stop_age ( IsBigO.trans (?_) (( Q.2.const_mul_left (4*(2*(d:ℝ)+1))) ) ); apply IsBigO.of_norm_eventuallyLE; filter_upwards [P.stop_age,P.step] with i hi hx; rw [Real.norm_of_nonneg ( sub_nonneg.mpr (scales J.S hi) ) ]; exact hx.2
lemma AgeRead.camp : Camp J L ρ B f k r:=⟨vB,pB,P.owner,⟨1/2, by norm_num, by simpa only[neg_div] using P.fast⟩, P.stop_age.trans ((show v≤ᶠ[L]f from P.buried.mono fun i hi=> (Nat.le_add_right ..).trans hi).trans P.owner), P.file g vB pρ pB,P.past g h' vB pρ pB⟩ -- by norm_num builds inversion neg form?
lemma AgeRead.horizon : Consume B L (-(a:ℝ)) (fun i=>paceT J.S ( f i ) (k i)):=by
    refine IsBigO.trans (?_) ( money_curve vB ( epoch_wave vB pB (P.reporter g vB pρ pB)) a).2; apply IsBigO.of_norm_eventuallyLE; filter_upwards [ P.sizeAt ] with i h; unfold paceT; have p:(J.clock.hatBeta (f i))^a ≤ J.S.a (f i)/ J.S.a (k i):=h.1; rw [Real.norm_of_nonneg (div_nonneg (J.S.a_pos _).le (J.S.a_pos _).le)]; exact ((inv_div ..).symm.trans_le (inv_anti₀ ( pow_pos (zero_lt_one.trans ( J.fits.delayed _ )) _ ) p))
lemma AgeRead.lower : let T:ℕ:= α+a+2; payD B (-(T:ℝ)) ≤ᶠ[L] hereD J ρ k:=by
   intro T; let K:= J.clock.hatBeta ∘ f; let e:= α+(a+1); let E:=payD B T; have he:( fun i=> K i^e ) ≤ᶠ[L] E:= Consume.tuck vB ( money_curve vB (epoch_wave vB pB (P.reporter g vB pρ pB)) e ).1 (by exact_mod_cast ( show e<T by unfold e T; omega)); filter_upwards [he, pρ,P.far,P.sizeAt] with i he hp hf hv; rw [payD_inv,Pi.inv_apply, ←one_div, hereD,sizeT]; let p:=J.S.a_pos (k i); let F(i):=J.S.a (f i); let H:=zero_lt_one.trans (J.fits.delayed (f i))
   apply ( div_le_div_iff₀ (pay_pos .. ) hp ).mpr; rw [one_mul]; have hc: ( K i^e )* J.S.a ( k i )≤ payD B T i*J.S.a ( k i ) := mul_le_mul_of_nonneg_right he p.le; rw [mul_comm]; refine hf.trans (le_trans (?_) hc); change K i^α * F i≤ K i^e* _; unfold e; rw [pow_add,mul_assoc]; exact mul_le_mul_of_nonneg_left (( div_le_iff₀ p ).mp hv.2) ( pow_nonneg H.le _ )
variable {δ:ℝ}
lemma AgeRead.closes (h:-(a:ℝ)+(-1/2)< -δ) : hereD J ρ k ≤ᶠ[L] payD B (-δ) :=by
    let Q:=P.horizon g h' vB pρ pB -- replace h' omitted
    have hm:= Consume.tuck vB (Schedules.Consume.mul Q (Schedules.Consume.ordered (pρ.mono fun i hi=>sizeT_pos J hi ( f i)|>.le) P.fast)) h; filter_upwards [hm,pρ] with i hi ht; change _≤_; refine le_trans (le_of_eq ?_) hi; rw [Pi.mul_apply]; unfold hereD sizeT paceT; field_simp [(J.S.a_pos (f i)).ne']
lemma AgeRead.stop_time (h: -(d:ℝ)+1< -4*δ): Consume B L (-δ) (fun i=> trailC J.S ( r i ) (k i)):=by
    let Q:= ( Real.tendsto_log_atTop.comp vB ); let Ψ:= fun i=> M i^( d * 2 ); have ht:= (( P.grasp (P.capture g h' vB pρ pB) ).isBigO ).trans ( penMap vB (EventuallyEq.rfl)); have he : Consume B L (-(d:ℝ)) Ψ := by
        convert Schedules.Consume.power ht (n:= d*2) using 1; · push_cast; ring
        funext; rfl
    have hz: (fun i=>paceT J.S (r i) (k i)) ≤ᶠ[L] Ψ:=by
        filter_upwards [P.step,P.buried,P.owner] with i hi hx hw; exact le_trans (div_le_div_of_nonneg_right (J.S.strictAnti.antitone ((Nat.le_add_right ..|>.trans hx).trans hw)) (J.S.a_pos _).le) ( hi.1.trans (le_of_eq (pow_mul ..).symm ) )
    have hQ:= hz.trans ( Consume.tuck vB he (by linarith only [h]: -(d:ℝ) < -4*δ) ); apply Schedules.Consume.ordered (Eventually.of_forall fun i=> Real.exp_nonneg _) ; filter_upwards [hQ] with i hi; unfold payD; apply exp_le_exp.mpr; have hv:=Real.log_le_log ( div_pos (J.S.a_pos _) (J.S.a_pos _)) hi; simp only [paceT,payD,Real.log_exp] at hv; linarith only[hv, σStub J (r i) (k i)] -- extraction
end Loans
end YM.Integration.Exporter
