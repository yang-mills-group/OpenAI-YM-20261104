import YM.SignedWilsonExpansion.Chron.Telescope
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
variable (P: AgeRead α a d L J ρ B f k v r M)
-- f-c width window via Visit.mesh from P grant.
include vB pB pρ P h' g
lemma phase_cost (h:∀ᶠ i in L,J.S.a (v i) / J.S.a (f i)≤ J.clock.hatBeta ( f i )^τ) (w':∀ᶠ i in L,v i=w i+1) : ∀ᶠ i in L,J.S.a ( w i )/ J.S.a ( k i )≤ J.clock.hatBeta (w i)^(τ+a+3):=by
    let x(i):=((J.S.block (w i)).val:ℝ); let t:=τ+(a+1); let V:= J.clock.hatBeta ∘ w; let F:= J.clock.hatBeta ∘ f; have p':Epoch L B J w:= epoch_wave vB pB ( prev_cp g h' vB pρ pB ( P.capture g h' vB pρ pB ) w' ); let E:= epoch_wave vB pB ( P.reporter g vB pρ pB ); have hv: Rise V L:= tends vB p'; have hG:= ( spread_cost vB J g h' p').trans_isLittleO ( show Spread B=o[L] B from ( show log=o[atTop] (fun i=>i) from by simpa using! isLittleO_log_rpow_atTop zero_lt_one ).comp_tendsto vB ); let u:= x*F^t; have hx : (F^t)=O[L] (V^t):= ( (E.trans p'.symm).pow t ).isBigO; have ht:u=o[L] (V^(t+1)):=by rw [pow_succ']; exact (hG.trans_isBigO p'.isBigO_symm).mul_isBigO hx
    filter_upwards [h,w',ht.bound zero_lt_one, P.sizeAt] with i hi hw hz hU; let A:=J.S.a ( v i ); let Y:=J.S.a (f i); let U:=J.S.a ( k i ); have h1:A=(x i)⁻¹ * J.S.a (w i):=by rw [show A=J.S.a (w i+1) from congr_arg J.S.a hw,J.S.a_step]; unfold x; ring -- x reduction wrong inv
    have h2: J.S.a (w i ) /U = x i * (A/Y) * ( Y/U ) :=by
        have t0:0<x i:= Nat.cast_pos.mpr (J.S.block (w i)).property; rw[h1]; have hp:0<Y:= J.S.a_pos _; have hz:0<U:= J.S.a_pos _; field_simp [t0.ne',(J.S.a_pos (f i)).ne',(J.S.a_pos (k i)).ne'] -- possible unknown
    rw [h2]; refine le_trans (mul_le_mul ( mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg ( (J.S.block (w i)).val )) ) hU.2 ( div_nonneg (J.S.a_pos _).le (J.S.a_pos _).le ) ( mul_nonneg (Nat.cast_nonneg _) ( pow_nonneg ( zero_lt_one.trans (J.fits.delayed _)).le _ ) )) (?_); let hp :1≤ V i:= (J.fits.delayed _).le; change x i * F i^τ * F i^(a+1) ≤ _; rw [mul_assoc,←pow_add]; refine le_trans (le_trans ( le_abs_self (u i) ) hz ) (?_); rw [ one_mul ]; change ‖V i^(t+1)‖ ≤ V i^_; rw [Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hp) _)]; exact pow_le_pow_right₀ hp (by unfold t; omega)
lemma phase_heat (w':∀ᶠ i in L,v i=w i+1): ∀ᶠ i in L,J.clock.hatBeta ( k i )≤ 2*J.clock.hatBeta ( w i ):=by
    have h :Epoch L B J w:= epoch_wave vB pB ( prev_cp g h' vB pρ pB ( P.capture g h' vB pρ pB ) w' ); let V:= J.clock.hatBeta; let K:= epoch_wave vB pB ( P.file g vB pρ pB ); let F:= K.trans h.symm; let p(i:ι):= ( zero_lt_one.trans ( J.fits.delayed (w i) ) ); have hx:= (isEquivalent_iff_tendsto_one (Eventually.of_forall (fun i=> (zero_lt_one.trans ( J.fits.delayed (w i))).ne'))).mp F; filter_upwards [hx.eventually (ge_mem_nhds (by norm_num: (1:ℝ)<2))] with i hi; exact ( div_le_iff₀ (p i)).mp hi
variable (R:Realm G (e+1) Credit.leanC)
lemma awakenG (h₁:R.draws=J) {δ ζ:ℝ}(p:δ≤(h:ℝ)*a)(q:δ ≤ (u:ℝ)/2)(b:0<ζ)(z:4*δ≤ ζ)(hx: -(d:ℝ)+1< -4*δ): Angles e R h u ρ (ell₁ J ρ B) f k r (corn J B ζ k) L B δ:=by
   subst J; refine ⟨(payD_move vB (by linarith: (u:ℝ)*(-1/2) ≤ -δ) ( Consume.powerReading vB P.fast ( pρ.mono fun i h'=> sizeT_pos _ h' _|>.le ) u )), payD_move vB (by linarith only [p]: (h:ℝ)*(-(a:ℝ))≤ -δ) (Schedules.Consume.power (P.horizon g h' vB pρ pB)), P.stop_time g h' vB pρ pB hx,( payD_move vB (by linarith only [z]:-ζ/4 ≤ -δ) ( Schedules.Consume.ordered ( Eventually.of_forall fun i=>trail_pos .. |>.le ) ( corn_trail vB h' g pB pρ b ) )) ⟩ -- unfold
end Loans
end YM.Integration.Exporter
