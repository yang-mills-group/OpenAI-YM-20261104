import YM.SignedWilsonExpansion.F9.Pedals
import YM.SignedWilsonExpansion.Purchase.Bullet
import YM.WilsonCoeffUV.Vacuum.UV.Budget
/-! # Geometry-clock appointment. Interpolation window selected at the cut filters.
Eclipsing IR bottom is not a physical cutoff.Owes Amount.PAprX.Reserve numbers below. -/
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.Schedules
open Asymptotics Wilson Gauge RG Push Lattice Source PriceCompiler UVClock WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa WilsonCoeffUV.Bank PathCost
open Set Filter Function Real Next.Rank Perch Commission
open RG.Supply
open scoped Topology Classical BigOperators
variable {G:Gauge} {M:Levels G}{ι:Type*}{B ρ:ι→ℝ}{N j k p i m:ℕ}{L:Filter ι}
variable (h:Rise B L)(b:GentleS M)(g:G.Simple) {i':ι} {Y Z:ι→ℝ}
abbrev hereD (M:Levels G)(ρ:ι→ℝ)(x:ι→ℕ):ι→ℝ:= fun i=> sizeT M (ρ i) (x i)
def ell₁ (M:Levels G)(ρ:ι→ℝ)(B:ι→ℝ):ι→ℕ:= fun i=> berthX M.S (LogLength ρ i-(Spread B i)^2)
def corn (M:Levels G)(B:ι→ℝ)(d:ℝ)(v:ι→ℕ):ι→ℕ:= fun i=> berthX M.S ( M.S.scale (v i)+d*Spread B i )
def m₁ (M:Levels G)(ρ:ι→ℝ)(B:ι→ℝ):ι→ℕ:= fun i=> berthX M.S ( LogLength ρ i+ Real.log (Spread B i) )
lemma pointD_log (q:0<ρ i') (w:ι→ℕ) : Real.log (hereD M ρ w i')= -(M.S.scale (w i')-LogLength ρ i'):=by rw [σIdentity M (w i') _ q,hereD,sizeT,Real.log_div (M.S.a_pos _).ne' q.ne',Real.log_div q.ne' (M.S.a_pos _).ne']; ring
lemma pointD (q:0<ρ i') (w:ι→ℕ) : hereD M ρ w i'= exp (-( M.S.scale (w i') - LogLength ρ i' )):=by rw [←pointD_log q, exp_log ( sizeT_pos _ q _ )]
local notation "σ" => LogLength ρ
local notation "U" => Spread B
variable (pM:B=ᶠ[L] βClock G ρ)(wet:∀ᶠ i in L,0<ρ i) {w v u t:ι→ℕ}
lemma wage_bias {Y:ι→ℝ} (v:Y=O[L] Spread B): Wage L (Spread B) 1 Y:= ⟨1,by simpa using v⟩
lemma wageSpread : Wage L (Spread B) (1:ι→ℝ) (Spread B):= wage_bias (isBigO_refl _ L)
local notation "W" => Wage L (Spread B) 1
include h b g pM
lemma σRate {s:ι→ℝ}(v:W (fun i=> s i -LogLength ρ i)): IsEquivalent L (fun i=>G.slopeConstant * s i) B:= by
    refine IsLittleO.isEquivalent ( (polyLittle h v).const_mul_left G.slopeConstant |>.congr' ( ?_ ) (.refl ..)); filter_upwards [pM] with i hi; simp only [Pi.sub_apply]; rw [hi]; unfold βClock; ring
lemma ell_epoch : Epoch L B M (ell₁ M ρ B) ∧ (fun i=> M.S.scale (ell₁ M ρ B i)-( LogLength ρ i-U i^2 ))=o[L] U:=by
    let t(i):= LogLength ρ i-( U i )^2; apply door h b g t (σRate h b g pM (?_)); simp only [t,sub_sub_cancel_left]; refine Wage.fix ((Wage.power (n:=2) ( wageSpread (B:=B) (L:=L) )).neg) (.refl ..) (Eventually.of_forall (fun i=>by simp))
include wet in
lemma eclipses : Eclipse L B (hereD M ρ (ell₁ M ρ B)):=by
     let s:=ell₁ M ρ B
     constructor; intro x; have hx:= (ell_epoch (M:=M) h b g pM).2.bound zero_lt_one
     filter_upwards [wet,hx,(y_rise h).eventually_gt_atTop 0,(y_rise h).eventually_ge_atTop (1+x)] with i hp hv hi hL; rw [pointD hp, payD]; apply exp_le_exp.mpr; rw [Real.norm_of_nonneg hi.le,one_mul] at hv; have h':M.S.scale ( s i )-(LogLength ρ i-U i^2)≤ U i:=(le_abs_self _).trans hv; change x*_≤ -( M.S.scale ( s i)-LogLength ρ i); nlinarith
lemma ell_old (v':Glow M ρ B L v): ∀ᶠ i in L, ell₁ M ρ B i< v i:=by
    obtain ⟨C,z,hz⟩:= v'.exists_pos; have hp:= (ell_epoch (M:=M) h b g pM).2.bound zero_lt_one
    let ℓ:=ell₁ M ρ B; filter_upwards [(y_rise h).eventually_gt_atTop (C+1), hz.bound, hp] with i hx hv hp; have hw:0<U i:=by linarith
    rw [Real.norm_of_nonneg hw.le] at hv hp; rw [one_mul] at hp; have hl: M.S.scale (ℓ i)-( LogLength ρ i- U i^2)≤ U i:= (le_abs_self _).trans hp; have h': M.S.scale ( v i )- LogLength ρ i ≥ -(C*U i):=( abs_le.mp hv ).1; by_contra! t; have hv: M.S.scale ( v i )≤ M.S.scale ( ℓ i ):= scales M.S t; nlinarith
variable {d d':ℝ}
include wet
lemma active_floor (wG: Glow M ρ B L w): ∃ u:ℝ,0<u ∧ payD B (-u) ≤ᶠ[L] hereD M ρ w ∧ hereD M ρ w≤ᶠ[L] payD B u:=by
    obtain ⟨C,v,hv⟩:= wG.exists_pos; refine ⟨C,v,?_⟩; apply eventually_and.mp; filter_upwards [wet,(y_rise h).eventually_ge_atTop 0,hv.bound] with i hi hu hx; rw [Real.norm_of_nonneg hu] at hx; have ⟨ha,hb⟩:= abs_le.mp hx; rw [pointD hi] -- replace simplicity
    unfold payD; constructor <;> ( first | linarith | apply exp_le_exp.mpr; linarith )
lemma dawnSpurt (v:Eclipse L B (hereD M ρ w)): (fun i=> hereD M ρ w i)⁻¹=o[L] (payD B (-d)):=by
    have h0:(fun i=> hereD M ρ w i)⁻¹=ᶠ[L] fun i=> hereD M ρ w i ^(-(1:ℝ)) := by simp only [Real.rpow_neg_one]; exact Eventually.of_forall fun i=>rfl
    exact (Consume.inc h (v:= -d-1) ( Eclipse.power_zone h v (-d-1) 1 (zero_lt_one) ) (by linarith: -d-1< -d)).congr' h0.symm (.refl ..)
omit wet pM
lemma corn_epoch (p:Epoch L B M v): Epoch L B M ( corn M B d v) ∧ (fun i=> M.S.scale ( corn M B d v i )-( M.S.scale (v i)+ d*U i ))=o[L] U:=by
     let x(i):= M.S.scale (v i)+d*U i; apply berthSketch h b g x p; unfold x; simpa using! (wage_bias (isBigO_const_mul_self d (Spread B) L))
lemma corn_top (p:0<d): ∀ᶠ i in L,v i< corn M B d v i:= by filter_upwards [( y_rise h ).eventually_gt_atTop 0] with i hi; by_contra! t; have ht:M.S.scale (v i)+d*U i≤ M.S.scale (v i) := (berth_yes _).trans (scales M.S t); linarith [mul_pos p hi]
include pM wet
lemma corn_glow (x:Glow M ρ B L v): Glow M ρ B L (corn M B d v):=by
    let p:= epoch_wave h pM x; have hx:=(corn_epoch (d:=d) h b g p).2.isBigO; refine ((hx.add x).add (isBigO_const_mul_self d _ L)).congr_left (fun i=>?_) ; ring
lemma corn_bill (p:0<d): hereD M ρ (corn M B d v) / hereD M ρ v ≤ᶠ[L] payD B (-d):=by
     filter_upwards [wet] with i hi; rw [Pi.div_apply, pointD hi,pointD hi,←exp_sub,payD]; have h':M.S.scale ( v i )+d*U i ≤ M.S.scale (corn M B d v i):= berth_yes _; exact exp_le_exp.mpr (by linarith)
lemma corn_trail (p:0<d): (fun i=> trailC M.S ( v i ) (corn M B d v i))≤ᶠ[L] payD B (-d/4):=by
     filter_upwards [wet] with i hi; dsimp only [trailC,payD]; apply exp_le_exp.mpr; have hw:M.S.scale (v i)+ d*Spread B i≤ M.S.scale (corn M B d v i):= berth_yes _; linarith
lemma corn_size (v₀: hereD M ρ v ≤ᶠ[L] (1:ι→ℝ))(p:0<d): hereD M ρ (corn M B d v) ≤ᶠ[L] payD B (-d):=by
    filter_upwards [wet, corn_bill (v:=v) h b g pM wet p,v₀] with i hi hx hz; exact le_trans ( ( div_le_iff₀ ( sizeT_pos _ hi (v i)) ).mp hx ) (( mul_le_of_le_one_right (pay_pos ..|>.le) hz ))
lemma logSpread : (fun i=>log ( Spread B i ))=o[L] Spread B:= (( show (log)=o[atTop] (fun i=>i) from by simpa using! (isLittleO_log_rpow_atTop zero_lt_one)).comp_tendsto ( y_rise h ))
lemma m_alpha : Epoch L B M (m₁ M ρ B) ∧ (fun i=> M.S.scale ( m₁ M ρ B i )- LogLength ρ i)=o[L] U:=by
    let s (i):= LogLength ρ i+ log (Spread B i); obtain ⟨hx,hh⟩:= door h b g s (σRate h b g pM (show W (fun i=> s i- LogLength ρ i) by simp_rw [s,add_sub_cancel_left]; exact wage_bias ( logSpread h b g pM wet ).isBigO)); refine ⟨hx,( hh.add (logSpread h b g pM wet) ).congr_left (fun i=>?_)⟩; unfold s m₁; ring -- unfold s conflicts index inside hh becomes ?
local notation "T"=> m₁ M ρ B
lemma m_late (p:0<d)(w:hereD M ρ v≤ᶠ[L] payD B (-d)): ∀ᶠ i in L, m₁ M ρ B i < v i:=by
    filter_upwards [wet,w, ( m_alpha h b g pM wet ).2.bound (half_pos p), ( y_rise h ).eventually_gt_atTop 0 ] with i hi hv hp hx; rw [Real.norm_of_nonneg hx.le] at hp; have hz:hereD M ρ v i ≤ _:= hv; rw [pointD hi,payD] at hz; let t:= Real.exp_le_exp.mp hz; have hw: M.S.scale (T i)- LogLength ρ i≤ d/2*U i := le_trans (le_abs_self _) hp; by_contra! y; have hv:=scales M.S y; linarith only [t,hv,hw,mul_pos p hx]
lemma m_owe : hereD M ρ (m₁ M ρ B) ≤ᶠ[L] U⁻¹∧ W ((hereD M ρ (m₁ M ρ B))⁻¹):=by
    let u(i):= LogLength ρ i+log (U i); let m(i):=berthX M.S (u i); have hy: Epoch L B M m:= ( m_alpha h b g pM wet ).1; let q:=fun i=> m i-1; let f(i):= (( M.S.block (q i) ).val:ℝ)
    refine ⟨(?_),?_⟩
    · filter_upwards [wet,(y_rise h).eventually_gt_atTop 0] with i hi hp; rw [Pi.inv_apply,pointD hi]; refine le_trans (b:=exp (-log (U i))) (exp_le_exp.mpr (?_)) (le_of_eq (by rw [ Real.exp_neg,Real.exp_log hp] )); have h': LogLength ρ i+ log ( U i )≤ M.S.scale (T i):= berth_yes _; linarith
    have hw:= Wage.mul ( Wage.enroll (u:=U) (spread_prev h M g b (x:=m) hy (a:=q) ( Eventually.of_forall fun i=>Nat.sub_le ..))) (wageSpread (B:=B) (L:=L) )
    refine Wage.rel (Wage.ascend (Wage.fix hw (.refl ..) (show U*1=ᶠ[L] U by rw [mul_one])) (wageSpread)) (?_); apply IsBigO.of_norm_eventuallyLE; filter_upwards [wet,(y_rise h).eventually_gt_atTop 0,( fee_Θ h M g hy ).eventually_gt_atTop 0] with i hi hp ht; change ‖(hereD M ρ m i)⁻¹‖≤ f i*U i; rw [Real.norm_of_nonneg (inv_nonneg.mpr (sizeT_pos _ hi _).le)]; change ( hereD M ρ m i)⁻¹ ≤ _; rw [pointD hi]; rw [← exp_neg, neg_neg]; have hv: M.S.scale (q i)< u i:= berth_no (by unfold q; omega: q i<m i); have H: M.S.scale (m i)= M.S.scale (q i)+log (f i):=by have U₁:= M.S.scale_succ (q i); rw [show q i+1=m i from Nat.sub_add_cancel ht] at U₁; exact U₁
    refine le_trans (exp_le_exp.mpr (?_:M.S.scale ( m i ) - LogLength ρ i ≤ log (f i) + log ( U i ))) (le_of_eq (by rw [exp_add,exp_log hp,exp_log (by unfold f; positivity)])); linarith only [hv,H]
-- Canopy funding on Room
lemma ell_wallet (vG: Glow M ρ B L v): hemisphere M L B (ell₁ M ρ B) v:=by
    let p:=wage_bias vG; have ht:=wage_bias ( ell_epoch h b g pM ).2.isBigO; refine Wage.fix (Wage.plus ((y_rise h).eventually_ge_atTop 1) (Wage.minus ((y_rise h).eventually_ge_atTop 1) p ht) ( show Wage _ _ 1 ( fun i=> U i^2 ) from Wage.fix (Wage.power (n:=2) ( wageSpread (B:=B) (L:=L) )) (.refl ..) (Eventually.of_forall fun i=>by simp))) (Eventually.of_forall (fun i=>?_)) (.refl ..); ring
omit pM wet in
lemma grantEllipse (R:Realm G N WilsonCoeffUV.Bank.Credit.leanC) (e:R.y = WilsonCoeffUV.Bank.Ticket.zz M)(p:R.draws=M)(u: hemisphere M L B w v) (p':Epoch L B M w)(q:w ≤ᶠ[L] v) : ∃ Z:ι→ℝ,W Z ∧ ∀ᶠ i in L,Canopy R (w i) (v i) (Z i):=by
    let s (i):=M.S.scale ( v i)- M.S.scale (w i); let t(i):= R.y (w i); let Z:=s+t; have ht:W t:= by unfold t; rw [e]; unfold WilsonCoeffUV.Bank.Ticket.zz; let q'(i):= M.clock.hatBeta (w i); have he :Rise q' L:= tends h p'; have hh:(fun i=> log (Spread q' i ))=o[L] Spread B:= ((show (log)=o[atTop] (fun i=>i) from by simpa using! (isLittleO_log_rpow_atTop zero_lt_one)).comp_tendsto (y_rise he)).trans_isBigO ( spread_tie h p' ).isBigO; exact Wage.plus (( y_rise h ).eventually_ge_atTop 1) ( Wage.unitC _ ) (wage_bias hh.isBigO)
    let x:= Wage.plus (( y_rise h ).eventually_ge_atTop 1) u ht; refine ⟨fun i=> 3*Z i,(?_),?_⟩
    · exact Wage.fix (Wage.mul ( Wage.unitC (3:ℝ)) x) ( EventuallyEq.rfl ) (show 1* (1:ι→ℝ)=ᶠ[L] 1 by rw [one_mul])
    filter_upwards [q,( fee_Θ h M g p' ).eventually_ge_atTop R.anchor] with i hi hv; have h':0 ≤ s i:= sub_nonneg.mpr ( scales M.S hi ); refine Canopy.advance hv hi (le_add_of_nonneg_left h') (?_); rw [p]; exact le_add_of_nonneg_right ( zero_le_one.trans ( R.depth _ hv ) )
end YM.SignedWilsonExpansion.Purchases.Schedules
