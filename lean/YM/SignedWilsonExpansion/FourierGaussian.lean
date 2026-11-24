import YM.SignedWilsonExpansion.KineticFee
namespace YM.SignedWilsonExpansion.FourierGaussian
/-! Explicit continuum interpretation of the Fourier-measure cutoff (here radian momentum);
complex signs throughout. Heat V requires moments with TWO insertions, and absolute dominator
 only at positive lengths, not at the face at zero. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset Complex
open MS MS.Plane MS.Plane.Flux MS.Landau MS.Landau.Detect MS.High MS.Tone
open FVA2 FVA2.Lambda Area Walk Bubble TreeLine TreeView HighRank HighScale PhasePair
open Gaussian
open scoped Classical Topology ContDiff BigOperators
variable (d:ℝ)
local notation "Z" => Momentum.sq
local notation "F" => FourP
local notation "Ω" => AxisChoice.disk
local notation "E" => Real.exp
local notation "μ" => covMeasure Axis
abbrev axis (d:ℝ) :F:= d • spike 3
def flag (d x:ℝ):ℂ:= Complex.exp (Complex.I*( d:ℂ )* (x:ℂ))
local notation "τ" => Tone.bill (axis d)
variable (p:F)
lemma flag_len (x:ℝ): ‖flag d x‖=1:= by unfold flag; rw [Complex.norm_exp]; simp
lemma bill_act : τ p=flag d (p 3):= by
    unfold Tone.bill flag; simp [ Momentum.pairing,axis,spike, Pi.single_apply, mul_ite,ite_mul ]; ring
def X (d:ℝ):= d^2/4
local notation "X₀" => X d
variable {R:ℝ}(hR:0<R)

def main (d R:ℝ)(x:ℝ):ℂ:= flag d x* E (-R*x^2)
def seat (n:ℕ)(R d:ℝ)(x:ℝ):ℂ:= (x:ℂ)^n * main d R x
variable (n:ℕ)
include hR
lemma seat_int : Integrable (seat n R d):= by
    refine ⟨ by unfold seat main flag; fun_prop,?_⟩; have he:= integrable_rpow_mul_exp_neg_mul_sq (show (0:ℝ)<R from hR) (show (-1:ℝ)<(n:ℝ) from lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (by positivity)); simp_rw [Real.rpow_natCast] at he
    rw [← hasFiniteIntegral_norm_iff]; convert! he.norm.hasFiniteIntegral using 1; ext x; simp only [ seat,main,norm_mul,norm_pow, flag_len,Complex.norm_real,one_mul ]
def tit (n:ℕ)(R d:ℝ):= ∫ x, seat n R d x
abbrev rock1 (R:ℝ):ℝ:=Real.sqrt (Real.pi/R)
local notation "S" => rock1 R
lemma cue : tit 0 R d=( ↑( S * E (-X₀/R) ) ):= by
    unfold tit seat; simp_rw [pow_zero,one_mul]; let A:= ( ( Real.pi:ℂ ) / R ) ^ ((1/2):ℂ)
    have ht(d:ℝ) : (∫ x,main d R x)= A*E (-X d/R):= by
       unfold main flag; unfold X; simp_rw [ Complex.ofReal_exp ]; push_cast; -- congr
       rw [ fourierIntegral_gaussian ( show 0<(R:ℂ).re from hR ) ]; unfold A; congr 2; ring
    rw [ ht ]; have hA:= ht 0; unfold main flag X at hA; simp only [pow_zero, zero_pow (by decide : (2:ℕ)≠0),zero_div,neg_zero, Real.exp_zero,mul_one,Complex.ofReal_zero, mul_zero, zero_mul,Complex.exp_zero,one_mul,Complex.ofReal_one] at hA
    rw [ integral_complex_ofReal, integral_gaussian ] at hA; rw [← hA]; push_cast; rfl
lemma pin2 : tit 2 R 0= (S / (2*R):ℝ) := by
    let f(x:ℝ):ℂ:=seat 1 R 0 x
    let e(x:ℝ):ℂ:= seat 0 R 0 x- (2*R:ℝ)* seat 2 R 0 x
    have ht(x:ℝ): HasDerivAt f (e x) x:= by
       unfold f e seat main flag; simp; convert! ( ofRealCLM.hasDerivAt (x:=x) |>.fun_mul ((( ( ofRealCLM.hasDerivAt (x:=x) ).pow 2).const_mul (R:ℂ)).neg.cexp) ) using 1; simp only [Pi.pow_apply,ofRealCLM_apply, ofReal_one,Pi.neg_apply]; ring
    obtain he:= integral_eq_zero_of_hasDerivAt_of_integrable ht ( show Integrable e from ( seat_int 0 hR 0 ).sub ( (seat_int 0 hR 2).const_mul _ )) ( seat_int 0 hR 1 )
    unfold e at he; rw [ integral_sub ( seat_int 0 hR 0 ) ( ( seat_int 0 hR 2 ).const_mul _ ), integral_const_mul ] at he
    change tit 0 R 0-_ * tit 2 R 0=_ at he; rw [cue 0 hR] at he; unfold X at he; norm_num at he; push_cast; rw [ eq_div_iff (mul_ne_zero (by norm_num) (by exact_mod_cast hR.ne')) ]; rw [mul_comm]; exact (sub_eq_zero.mp he).symm

/- prices.F. -/
def raw (m:Axis→ℕ)(R d:ℝ)(p:F):ℂ:= Tone.bill (axis d) p * ( ( Gaussian.ar m p* E (-R*Momentum.sq p):ℝ ):ℂ )
def trace (m:Axis→ℕ)(R d:ℝ):ℂ:= ∫ p:F, raw m R d p∂ covMeasure Axis
variable (m:Axis→ℕ)
omit hR in
lemma fare : raw m R d p=∏ i:Axis,seat (m i) R (if i=3 then d else 0) (p i):= by
    let k(i:Axis):= flag (if i=3 then d else 0) (p i)
    have he: (∏ i:Axis,k i)= flag d (p 3):= by
       rw [ Finset.prod_eq_single 3 ]; · simp [k]
       · intro i _ hi; simp [k,hi,flag]
       simp
    unfold raw seat main; simp_rw [ Finset.prod_mul_distrib, ← Complex.ofReal_prod, Gaussian.ar, Momentum.sq, Finset.mul_sum,Real.exp_sum ]; unfold k at he; rw [he, bill_act]; push_cast; ring

lemma raw_int : Integrable (raw m R d) μ:= by
    rw [ funext (fun p=> fare (R:=R) d p m), show μ=( ENNReal.ofReal capμ ) • volume from Gaussian.land ]; exact Integrable.smul_measure ( Integrable.fintype_prod ( «μ»:=fun _=>volume ) ( fun i=>seat_int ( if i=3 then d else 0 ) hR (m i) )) ENNReal.ofReal_ne_top
lemma raw_coin : trace m R d = ( (Gaussian.capμ:ℂ) * ∏ i:Axis,tit (m i) R (if i=3 then d else 0 )):= by
    unfold trace; simp_rw [ fare ]; rw [ show μ=( ENNReal.ofReal capμ ) • volume from Gaussian.land, integral_smul_measure, integral_fintype_prod_volume_eq_prod, ENNReal.toReal_ofReal (by unfold capμ; positivity) ]; rfl

-- smooth radial moments through phase. any d
def account (R d:ℝ)(m:Axis→ℕ)(n:ℕ)(p:F):ℂ:= Momentum.sq p^n • raw m R d p
def ticket (n:ℕ)(d R:ℝ)(p:F):ℂ:= Tone.bill (axis d) p * (↑( (AxisChoice.disk p)*(Momentum.sq p)^n*E (-R*p.sq) ):ℂ)
def sumG (n:ℕ)(d R:ℝ):ℂ:= ∫ p:F,ticket n d R p∂covMeasure Axis
local notation "α" => (fun _:Axis=>(0:ℕ))
local notation "σ" => Gaussian.shift
omit hR in
lemma route : account R d m (n+1) p= ∑ i:Axis,account R d (σ m i) n p:= by
    unfold account raw; simp_rw [ Gaussian.crop ];
    have hv:= show ∀ i:Axis,( (Z p)^n • ( τ p * ((↑(ar m p*(p i)^2*E (-R*p.sq)):ℂ)))) = p i^2 • ((Z p)^n • raw m R d p) from ?_
    · rw [pow_succ]; simp_rw [hv,← Finset.sum_smul ]; rw [mul_comm, mul_smul]; rfl
    intro i; unfold raw; simp_rw [ Complex.real_smul ]; push_cast; ring
lemma afford : Integrable (account R d m n) μ:= by induction n generalizing m with
    | zero=> rw [show account R d m 0=raw m R d from (funext (fun x=>by rw [account,pow_zero,one_smul])) ]; exact raw_int d hR m
    | succ n ih=> rw [ show account R d m (n+1)=fun p=> ∑ i,account R d (σ m i) n p from funext (fun _=> route ..) ]; exact integrable_finsetSum _ fun i _=> ih _
omit hR in
lemma pair (R:ℝ) : ticket n d R p= account R d (σ α 1) n p + account R d (σ α 2) n p:= by unfold ticket account raw; rw [crop,crop,γ_norm]; unfold AxisChoice.disk; simp only [Complex.real_smul]; push_cast; ring
lemma ticket_paid : Integrable (ticket n d R) μ:= by rw [ funext (fun p=> pair d p n R) ]; exact (afford d hR n _).add (afford d hR n _)
omit hR in
lemma ticketNorm (R:ℝ): ‖ticket n d R p‖=Ω p*p.sq^n*E (-R*p.sq):= by unfold ticket; have hp : 0≤Z p:= Finset.sum_nonneg (f:=fun i:Axis=> p i^2) (fun i _=>sq_nonneg _); rw [ norm_mul,bill_norm,one_mul, Complex.norm_real, Real.norm_of_nonneg ]; unfold AxisChoice.disk; positivity
lemma bound_DF (n:ℕ): HasDerivAt (sumG n d) (-sumG (n+1) d R) R:= by
    let P(a:ℝ)(p:F):= -ticket (n+1) d a p; let G(p):=‖ticket (n+1) d (R/2) p‖
    have hr: 0<R/2:=by linarith
    have hm(p:F)(a:ℝ): HasDerivAt (fun a=>ticket n d a p) (P a p) a:= by
       have hn: HasDerivAt (fun a:ℝ=>E (-a*p.sq)) (-p.sq* E (-a*p.sq)) a:= by convert! ((( hasDerivAt_id' a ).neg.mul_const p.sq).exp ) using 1; simp only [Pi.neg_apply]; ring
       convert! ( Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt a ( hn.const_mul ( Ω p*p.sq^n ) ) ).const_mul (τ p) using 1; unfold P ticket; simp only [ofRealCLM_apply]; rw [pow_succ]; push_cast; ring
    unfold sumG; rw [ ← integral_neg ]; refine ( hasDerivAt_integral_of_dominated_loc_of_deriv_le ( bound:=G ) (Ioi_mem_nhds (show R/2<R from (by linarith))) ((show ∀ᶠ x in (𝓝 R),0<x from Ioi_mem_nhds hR).mono (fun _ hR=> Integrable.aestronglyMeasurable ( ticket_paid d hR n ))) ( ticket_paid d hR n ) (Integrable.aestronglyMeasurable (f:=P R) ( ticket_paid d hR (n+1)|>.neg )) (Eventually.of_forall ?_) ( ticket_paid d hr (n+1)|>.norm ) (Eventually.of_forall ( fun p x _=> hm p x )) ).2
    intro p t ht; unfold P G; simp only [norm_neg]; rw [ ticketNorm, ticketNorm ]; have h0:0≤ Momentum.sq p:= Finset.sum_nonneg (f:= fun i:Axis=> p i^2) (fun i _=> sq_nonneg _); unfold AxisChoice.disk; have hx : R/2 < t:= ht; gcongr

def value (d R:ℝ):ℝ:= b₀* R⁻¹^3 * E (-X d/R)
lemma foundation : sumG 0 d R=(FourierGaussian.value d R:ℂ):= by
    unfold sumG; simp_rw [ FourierGaussian.pair d _ 0, account,pow_zero,one_smul ]; rw [ integral_add ( raw_int d hR _ ) (raw_int d hR _ ) ];
    change trace (σ α 1) R d+trace (σ α 2) R d=_
    rw [ raw_coin d hR, raw_coin d hR ]; -- collapse
    simp (disch:=norm_num) only [ show Finset.univ («α»:=Axis)={0,1,2,3} from rfl, Finset.prod_insert, Finset.prod_singleton, Gaussian.shift, Nat.zero_add ];
    simp (disch:=decide) only [Finset.prod_insert, Finset.prod_singleton, ↓reduceIte, if_neg (show (0:Axis)≠1 from by decide) ,if_neg (show (0:Axis)≠2 from by decide) ,if_neg (show (0:Axis)≠3 from by decide) ,if_neg (show (1:Axis)≠2 from by decide) ,if_neg (show (1:Axis)≠3 from by decide) ,if_neg (show (2:Axis)≠1 from by decide) ,if_neg (show (2:Axis)≠3 from by decide) ,if_neg (show (3:Axis)≠1 from by decide) ,if_neg (show (3:Axis)≠2 from by decide)]
    simp only [cue _ hR, show X 0=0 from (by norm_num [X]), pin2 hR,neg_zero,zero_div,Real.exp_zero,mul_one, ← Complex.ofReal_mul,← Complex.ofReal_add ]; apply congr_arg; have he: rock1 R^2=Real.pi/R:= Real.sq_sqrt (by positivity); unfold FourierGaussian.value b₀ capμ; ring_nf; rw [show S^4= (Real.pi/R)^2 from (by rw [← he]; ring) ]; ring

def one (d R:ℝ):ℝ:= b₀*R⁻¹^4 * ( 3-X d/R)* E (-X d/R)
lemma timeD (d:ℝ)(i:ℤ)(n:ℕ)(hn:n=0) : HasDerivAt ( FourierGaussian.value d ) ( -FourierGaussian.one d R ) R:= by
    unfold FourierGaussian.value FourierGaussian.one;
    let h:= hasDerivAt_id' R; have he': HasDerivAt (fun R:ℝ=>E (-X d/R)) ( (X d/R^2)*E (-X d/R) ) R:= by
       convert! ( ( (hasDerivAt_const R (-X d)).div h hR.ne' ).exp ) using 1; simp only [ Pi.pow_apply, Pi.inv_apply, Pi.div_apply ]; field_simp; ring
    convert! ((( ( h.inv hR.ne' ).pow 3 ).const_mul b₀ ).fun_mul he') using 1; simp only [ Pi.pow_apply, Pi.inv_apply, Pi.div_apply ]; field_simp; ring_nf; field_simp
lemma K_apply : sumG 1 d R= (FourierGaussian.one d R:ℂ):= by
    obtain he:= ( bound_DF d hR 0 ); let h:= ( ofRealCLM.hasFDerivAt.comp_hasDerivAt R (timeD hR d 0 0 rfl) ); have ht : (fun x=> ( ( FourierGaussian.value d x ):ℂ )) =ᶠ[𝓝 R] sumG 0 d:= ( show ∀ᶠ x in 𝓝 R,0<x from Ioi_mem_nhds hR ).mono fun x hx=> (foundation d hx).symm
    exact neg_injective ( by rw [ ← Complex.ofReal_neg ]; exact (he.congr_of_eventuallyEq ht).unique h )
omit hR
abbrev mass (t:ℝ):= E (2*t)
def dot (d t:ℝ)(k:F):ℂ:= Tone.bill (axis d) k * (( ↑( Shells.hot t (Z k)*(Z k)*Ω k ):ℂ ))
def bias (d t:ℝ):= ∫ k:F, dot d t k∂covMeasure Axis
def bonus (d t:ℝ)(k:F):ℂ:= dot d t k * (↑(PhasePair.rate t k):ℂ)
def wind (d t:ℝ):= ∫ k:F, bonus d t k∂covMeasure Axis
lemma mass_pos (t:ℝ):0<mass t:= Real.exp_pos _
variable (t:ℝ)
lemma ellipse : mass t=(E t)^2 := by unfold mass; rw [two_mul,Real.exp_add,sq]
lemma b_tick : dot d t p= (↑( mass t^2 ):ℂ)*ticket 1 d (mass t) p:= by
    unfold dot ticket Shells.hot; rw [ ellipse t ]; rw [ neg_mul ]; push_cast; ring
lemma dot_int : Integrable (dot d t) μ:= by rw [ funext (fun p=> b_tick d p t) ]; exact ( ticket_paid d ( mass_pos t ) 1 ).const_mul _
lemma bias_e : bias d t=( mass t:ℂ )^2 * sumG 1 d (mass t):= by
    unfold bias; simp_rw [ b_tick ]; rw [ integral_const_mul ]; push_cast; rfl
lemma strength_mass : ∀ x,HasDerivAt mass ( 2*mass x ) x:= by
    intro x; unfold mass; convert! (( ( hasDerivAt_id' x ).const_mul 2 ).exp ) using 1; ring
lemma derivativeD :
    HasDerivAt (bias d) (4*bias d t-( 2*(mass t:ℂ)^3)* sumG 2 d (mass t)) t := by
   simp_rw [funext ( bias_e d ) ]; unfold sumG -- avoid assumption
   have hv : HasDerivAt (fun t=> (mass t:ℂ)) ( 2*(mass t:ℂ)) t:= by
      convert! ( ofRealCLM.hasFDerivAt.comp_hasDerivAt t ( strength_mass t ) ) using 1; simp
   let U:= ( bound_DF d (mass_pos t) 1 ); convert! ( (hv.pow 2).fun_mul ( U.scomp t ( strength_mass t ) ) ) using 1; unfold sumG; simp only [ Complex.real_smul, Function.comp_apply, Pi.pow_apply ]; push_cast; ring
abbrev jump :ℝ:=Real.log 2 / 2
lemma at_jump : mass (t+jump)=2*mass t:= by unfold mass jump; rw [mul_add, Real.exp_add, mul_div_cancel₀, Real.exp_log (by norm_num), mul_comm ]; norm_num
local notation "M" => mass
local notation "J" => FourierGaussian.jump
lemma role :
    bonus d t p = dot d t p - dot d (t+J) p /4 - (( M t:ℂ )^3)*ticket 2 d ( M ( t+J ) ) p := by
    unfold bonus; rw [ PhasePair.definition, ← ellipse,b_tick,b_tick,at_jump t ]; unfold ticket; have ht: E (-(2* M t)* Z p)= ( E (-(M t)*Z p) )^2:= by rw [ show -(2*M t)*Z p= -(M t)*Z p+(-(M t)*Z p) from by ring, Real.exp_add,sq ]
    rw [ht]; simp_rw [neg_mul] at *; push_cast; ring
lemma wind_int : Integrable (bonus d t) μ:= by
    rw [ funext (fun p=> role d p t) ]; exact (( dot_int d t ).sub ((dot_int d (t+J)).div_const _)).sub ((ticket_paid d (mass_pos _) 2).const_mul _)
lemma prize_t : wind d t=bias d t-bias d (t+J)/2+deriv (bias d) (t+J)/16:= by
    rw [ ( derivativeD d ( t+J ) ).deriv ]; unfold wind; simp_rw [role]; rw [ integral_sub ( show Integrable (fun k=> dot d t k-dot d (t+J) k/4 ) μ from (( dot_int d t ).sub ((dot_int d (t+J)).div_const (4:ℂ)))) ((ticket_paid d (mass_pos _) 2).const_mul _), integral_sub (dot_int d t) ((dot_int d _ ).div_const _), integral_const_mul, integral_div ]; change bias _ _-bias _ _/4 - _ * sumG 2 _ _=_; rw [at_jump]; push_cast; ring
-- local primitives.Later.Tactics.
def scale (d t:ℝ):= X d / mass t
abbrev count0 (d:ℝ):ℝ:= b₀/(2*X d^2)
def stock (d t:ℝ):ℝ :=
      let x:=scale d t
      count0 d*( 1+x-x^2)*E (-x)
abbrev rise (d t:ℝ):ℂ:= ↑(stock d t)
def early (d t:ℝ):ℂ:= rise d t - rise d ( t+ FourierGaussian.jump ) /2 + bias d (t+ FourierGaussian.jump )/16
variable (hd:d≠0)
include hd
lemma df_pos : 0<X d := by unfold X; positivity
lemma report_t : bias d t= ↑( 2*count0 d* (scale d t)^2* ( 3-scale d t)* E (-scale d t):ℝ ):= by
   rw [bias_e,K_apply d (mass_pos t) ]; unfold scale; rw [ ← Complex.ofReal_pow, ← Complex.ofReal_mul ]; apply congr_arg; have he:=df_pos d hd; have ht:=mass_pos t; unfold count0 FourierGaussian.one; rw [neg_div]; field_simp
lemma stay : HasDerivAt (scale d) ( -2*scale d t ) t:= by convert! ( (hasDerivAt_const t (X d)).div (strength_mass t) (mass_pos t).ne' ) using 1; unfold scale; have ht:=mass_pos t; field_simp; ring
lemma warden : HasDerivAt (rise d) (bias d t) t:= by
    rw [report_t d t hd]; let s:=scale d; have hx(t:ℝ): HasDerivAt (scale d) ( -2*s t) t:=stay d t hd; apply Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t; 
    convert! ((( ( ( hx t ).const_add 1 |>.fun_sub ((hx t).pow 2) ).const_mul _ ).fun_mul (( hx t ).neg.exp))) using 1; simp only [Pi.neg_apply,Pi.pow_apply]; change _*E (-scale d t)=_; unfold s; ring
lemma vessel : HasDerivAt (early d) (wind d t) t:= by
    let L:=t+J; have hv(f:ℝ→ℂ)(v)(h:HasDerivAt f v L): HasDerivAt (fun t:ℝ=> f (t+J) ) v t := by simpa  +instances only [Function.comp_def,one_smul] using ( HasDerivAt.scomp (h:=fun t:ℝ=>t+J) t h ( (hasDerivAt_id' t).add_const J ) )
    rw [prize_t d t,( derivativeD d ( t+J ) ).deriv ]; exact ( ( warden d t hd ).sub ( (hv _ _ (warden d L hd)).div_const 2 ) ).add ( (hv _ _ (derivativeD d L)).div_const 16 )
lemma scale_infty : Tendsto (scale d) atBot atTop:= by
    have he:Tendsto (fun x:ℝ=>(M x)⁻¹) atBot atTop:= by
       unfold mass; simp_rw [ ← Real.exp_neg,← neg_mul ]; exact Real.tendsto_exp_atTop.comp (tendsto_const_mul_atTop_of_neg (by norm_num : (-(2:ℝ))<0) |>.mpr tendsto_id )
    unfold scale; simp_rw [div_eq_mul_inv]; exact (tendsto_const_mul_atTop_of_pos ( df_pos d hd )).mpr he
lemma time0 : Tendsto (scale d) atTop (𝓝 0):= by have hp:Tendsto mass atTop atTop:= Real.tendsto_exp_atTop.comp ((tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id); unfold scale; simp_rw [ div_eq_mul_inv ]; simpa only [ Function.comp_def,mul_zero] using ( ( tendsto_inv_atTop_zero.comp hp ).const_mul ( X d ) )
lemma dust (n:ℕ): Tendsto (fun x:ℝ=> scale d x^n * E (-scale d x)) atBot (𝓝 0):= (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp (scale_infty d hd) -- check Real
lemma reaches_cold : Tendsto (rise d) atBot (𝓝 0):= by
    refine (Complex.ofReal_zero ▸ Complex.continuous_ofReal.continuousAt.tendsto.comp (?_ : Tendsto (stock d) atBot (𝓝 0)))
    have ht:= ((( dust d hd 0 ).add (dust d hd 1) ).sub (dust d hd 2)).const_mul (count0 d)
    unfold stock; simp_rw [ mul_assoc, sub_mul, add_mul ]; simpa using ht
lemma reaches_end : Tendsto (rise d) atTop (𝓝 (count0 d:ℂ)):= by
    refine Complex.continuous_ofReal.continuousAt.tendsto.comp ?_
    let Φ(x:ℝ):=count0 d*(1+x-x^2)*E (-x)
    have hZ:Continuous Φ:= by unfold Φ; fun_prop
    convert ( hZ.continuousAt.tendsto.comp (time0 d hd)) using 1; all_goals (first| rfl|simp [Φ])
lemma velocity : Tendsto (bias d) atBot (𝓝 0) ∧ Tendsto (bias d) atTop (𝓝 0):= by
   -- use polynomial body
   rw [ funext ( fun t=> report_t d t hd ) ];
   let g(x:ℝ):=x^2*(3-x)*E (-x); let c:=2*count0 d; have he : (fun t:ℝ=> ↑(2* count0 d*scale d t^2*( 3-scale d t ) * E (-scale d t) :ℝ) : ℝ→ℂ)=fun t=> ↑( c*g (scale d t)):= by funext t; congr 1 <;> unfold g <;> ring
   rw [he]; have hh (l:Filter ℝ)(h:Tendsto (g∘scale d) l (𝓝 0)) : Tendsto (fun t=> (( ↑( c*g (scale d t)):ℂ ))) l (𝓝 0):= by simpa only [ Function.comp_def,mul_zero, ofReal_zero ] using ( Complex.continuous_ofReal.continuousAt.tendsto.comp ( h.const_mul c ) )
   apply And.intro <;> apply hh
   · unfold g; simp_rw [Function.comp_def]; rw [show (fun x:ℝ=> (scale d x)^2*(3-scale d x)*E (-scale d x))=(fun t=>3*(scale d t^2*E (-scale d t))-scale d t^3* E (-scale d t)) from funext fun t=>by ring ]; simpa using (( dust d hd 2 ).const_mul (3:ℝ)).sub (dust d hd 3)
   have hp: Continuous g:= by unfold g; fun_prop
   convert ( hp.continuousAt.tendsto.comp (time0 d hd)) using 1; simp [ g ]
lemma J0 : Tendsto (early d) atBot (𝓝 0):= by
   let P:=tendsto_atBot_add_const_right atBot J ( tendsto_id (x:=atBot) ); unfold early; simpa only [ Function.comp_def, id_eq,zero_div,sub_zero,add_zero ] using ( ( reaches_cold d hd ).sub ( ( (reaches_cold d hd).comp P ).div_const 2 ) ).add ( ( (velocity d hd|>.1).comp P ).div_const 16 )
lemma J1 : Tendsto (early d) atTop (𝓝 ( (count0 d:ℂ)/2 )):= by
    let c:= (count0 d:ℂ); let P:= tendsto_atTop_add_const_right atTop J ( tendsto_id (x:=atTop) )
    unfold early; obtain h:= (( reaches_end d hd ).sub ((( reaches_end d hd ).comp P ).div_const 2 ) ).add ((( velocity d hd|>.2 ).comp P ).div_const 16 ); rw [zero_div,add_zero,show c-c/2=c/2 from (by ring) ] at h; exact h
end
end YM.SignedWilsonExpansion.FourierGaussian
