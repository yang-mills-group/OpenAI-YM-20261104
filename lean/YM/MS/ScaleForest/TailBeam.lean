import YM.MS.ScaleForest.Aurora
/-!
# Second, REPEATED pole-graph line in the multiplier footprint

Both pinned computations contain the **high** factor of the retained IR
scale, i.e., `(1-Hρ)` where `Hρ=low`. Its square is required in the
dressed case. Keep that factor, which affects the multiplier even at
non-exceptional momentum. m=0 evaluation where appropriate. Don't here
claim you can use absolute Fubini (without external tests) in the uncut
multiplier; the *derivative in scale* of the contracted complement after
legitimate z specialization suffices. Phases and measure exactly as in MS.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Aurora
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle Snap XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic Triangle
open Next Next.Rank Next.Rank.Beamer Next.Rank.Radian Prayer
open MS.Drops
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {m : ℕ} (L K:Degree G)
local notation "ν"=> Drops.ν
local notation "U"=>xy (fax L) (fax K)
local notation "Λ"=> Next.Rank.Radian.wave

def Later(s:ℝ):=s+log (Real.sqrt 2)
lemma epoch_shift (s:ℝ): exp (Later s)^2=2* exp s^2:= by unfold Later; rw [exp_add, exp_log (by positivity),mul_pow,sq_sqrt (by norm_num),mul_comm]
lemma product_phase (p:SectorP m)(s:ℝ): (p.sq:ℂ)*evenPart p s ^2 = 2*evenPart p s - evenPart p (Later s) + (8:ℂ)⁻¹*shining p (Later s) := by
   unfold evenPart shining; simp_rw [ Swirl.Near.lown, City.brush ];
   rw [ show 2*exp (Later s)*(exp (Later s)^3 * exp (-(exp (Later s)^2 * p.sq))) =2*(exp (Later s)^2)^2* exp (-(exp (Later s)^2*p.sq)) from (by ring), epoch_shift, show -( 2*exp s^2*p.sq)= -(exp s^2*p.sq) + -(exp s^2*p.sq) from by ring, exp_add ]; push_cast;
   by_cases h:p.sq=0; · simp [h]
   have ht : (↑p.sq:ℂ)≠0:= by exact_mod_cast h;
   field_simp; ring

lemma high_bit (p:SectorP m)(s:ℝ): p.sq * evenPart p s=1-( low (exp s) p:ℂ):= by
   by_cases h:p.sq=0; · simp [h,Swirl.Near.lown]
   have he:(↑p.sq:ℂ)≠0:= by exact_mod_cast h
   unfold evenPart; push_cast; field_simp
lemma low_check (p:SectorP m)(r:ℝ): ‖1-( low r p:ℂ)‖ ≤ 1:= by
   rw [ ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real ]; rw [Swirl.Near.lown, Real.norm_eq_abs]; apply abs_le.mpr
   let u:= r^2*p.sq; have hv:0≤u:= mul_nonneg (sq_nonneg _) ((sq_nonneg ‖p‖).trans (sup_square p)); have he: (1+u)*exp (-u)≤1:= by rw [exp_neg, ← div_eq_mul_inv,div_le_one (by positivity: 0<exp u), add_comm]; exact Real.add_one_le_exp u
   change -(1:ℝ) ≤ 1 - (1+u)*exp (-u) ∧ _; change _ ∧ 1-(1+u)*exp (-u)≤1; constructor <;> linarith [mul_nonneg (show 0≤1+u by linarith) (show 0≤exp (-u) from (exp_pos _).le)]

-- This is the complementary soft part of the multiplier. Integrable even without tests. Raw pole numerator when no UV cutoff doesn't use this Fubini, but its limit eval can use this soft tail.
def tail₂ (p:QP)(s:ℝ): ℂ:= (p.sq:ℂ)⁻¹ - p.sq*(evenPart (m:=0) p s)^2
def pearler (p:QP)(s:ℝ) := 2*(p.sq * evenPart (m:=0) p s)*shining (m:=0) p s
lemma life_line (p:QP) (s:ℝ): HasDerivAt (tail₂ p) (-pearler p s) s:= by
   unfold tail₂; convert! ((((even_jet (m:=0) p s).pow 2).const_mul ( ↑p.sq:ℂ) ).const_sub _ ) using 1; norm_num [pearler]; ring
lemma costume (p:QP)(s:ℝ) :
   tail₂ p s = 2*dark_s p s - dark_s p (Later s)-(8:ℂ)⁻¹ * shining (m:=0) p (Later s):= by
   unfold tail₂; rw [product_phase (m:=0)]; have he(s:ℝ): dark_s p s=(p.sq:ℂ)⁻¹-evenPart (m:=0) p s:= by unfold dark_s evenPart; push_cast; ring
   simp_rw [he]; ring
lemma bread (p: E4)(s:ℝ): U (ν p)*tail₂ (ν p) s=2*wearΦ L K s p-wearΦ L K (Later s) p+(8:ℂ)⁻¹ *stage0 L K (Later s) p:= by
   rw [costume,annual]; unfold wearΦ; ring

variable (s:ℝ)(x:E4)
private abbrev worn (p:E4):ℂ:= Λ x p*(U (ν p)*tail₂ (ν p) s)
private abbrev wages (p:E4):ℂ:=Λ x p*(U (ν p)* (-pearler (ν p) s))
lemma tail_hold : Integrable (worn L K s x):= by
   have he(t:ℝ):=listener _ (hand L K t) x; convert (((he s).const_mul 2).sub (he (Later s))).add ((listener _ (stage_h L K (Later s)) x).const_mul (8:ℂ)⁻¹) using 1 <;> try rfl
   funext p; rw [worn,bread]; simp only [Pi.add_apply,Pi.sub_apply]; ring
lemma earn (p:E4): wages L K s x p= 2*(1-(Landau.low (exp s) (ν p):ℂ))*(Λ x p* stage0 L K s p):= by
   rw [annual]; unfold wages pearler; rw [ high_bit (m:=0) ]; ring
private lemma low_cont (s:ℝ) : Continuous fun k:QP=>(Landau.low (exp s) k: ℂ):= by
   simp_rw [ Swirl.Near.lown ]; unfold Momentum.sq; fun_prop
private lemma wrap_meas (s:ℝ) : Continuous fun k:E4=>(Landau.low (exp s) (ν k):ℂ) := (low_cont s).comp (Drops.ν.continuous)

lemma wages_hold : Integrable (wages L K s x):= by
    rw [ funext (earn L K s x) ]; suffices he : Continuous (fun t:E4=>2*(1-(Landau.low (exp s) (ν t):ℂ))) from
       (listener _ (stage_h L K s) x).bdd_mul he.aestronglyMeasurable (Eventually.of_forall (p:=fun t:E4=> ‖2*(1-(low (exp s) (ν t):ℂ))‖ ≤ 2) (by intro t; rw [norm_mul,Complex.norm_ofNat]; obtain h:=low_check (m:=0) (ν t) (exp s); linarith [h]))
    exact continuous_const.mul (continuous_const.sub (wrap_meas s))

lemma brackets (p:E4)(t:ℝ)(h:t∈Icc (s-1) (s+1)): ‖wages L K t x p‖≤2*(ntC (s+1) ‖p‖ *‖U (ν p)*leaseTax (s-1) p‖) := by
   rw [earn]; rw [norm_mul,norm_mul,norm_mul (Λ x p)]; simp only [price_wave,one_mul,Complex.norm_ofNat ]; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by norm_num : 0≤(2:ℝ)); exact (mul_le_of_le_one_left (norm_nonneg _) (low_check (m:=0) _ _)).trans (Drops.basin L K h p)

def paidTail := ∫ p:E4,worn L K s x p

def topFlow (x:E4)(s:ℝ):= gleam L K x - paidTail L K s x
lemma net_asset : paidTail L K s x = 2*γX L K x s - γX L K x (Later s) - (8:ℂ)⁻¹*sunny L K x (Later s):= by
    unfold paidTail; rw [sunny, γX, γX ]; simp_rw [worn,bread,Radian.wind,mul_add,mul_sub];
    have hh(t:ℝ):= listener _ (hand L K t) x; obtain hu:= listener _ (stage_h L K (Later s)) x;
    simp_rw [ mul_left_comm (Λ x _) (2:ℂ),mul_left_comm (Λ x _) (8⁻¹:ℂ) ]; rw [integral_add (((hh s).const_mul 2).sub' (hh (Later s))) (hu.const_mul (8:ℂ)⁻¹), integral_sub ((hh s).const_mul 2) (hh (Later s)) ]; simp_rw [ integral_const_mul ]; ring
lemma terminal_paid_start (hx:x≠0)(h:L.degree=0)(ht:K.degree=0): Tendsto (topFlow L K x) atBot (𝓝 0):= by
   have he(t:ℝ):topFlow L K x t=2*firstS L K x t-firstS L K x (Later t)+(8:ℂ)⁻¹*sunny L K x (Later t):= by rw [ topFlow,net_asset ]; unfold firstS; ring
   rw [funext he]; obtain hu:Tendsto Later atBot atBot:= tendsto_atBot_add_const_right atBot _ tendsto_id; obtain hs:= first_out L K x hx; simpa only [mul_zero,sub_zero,add_zero ,Function.comp_apply] using ((hs.const_mul (2:ℂ)).sub (hs.comp hu)).add (((sunny_bot L K h ht x hx).comp hu ).const_mul (8:ℂ)⁻¹)
lemma terminal_paid_top (h:L.degree=0) (ht:K.degree=0) : Tendsto (topFlow L K x) atTop (𝓝 (↑(gleam L K x):ℂ)):= by
   have he(t:ℝ):topFlow L K x t=2*firstS L K x t-firstS L K x (Later t)+(8:ℂ)⁻¹*sunny L K x (Later t):= by rw [topFlow,net_asset ]; unfold firstS; ring
   let c:ℂ:=gleam L K x; obtain hu:Tendsto Later atTop atTop:=tendsto_atTop_add_const_right atTop _ tendsto_id; obtain hh:=first_top L K x;
   rw [funext he]; obtain hz:= ((hh.const_mul (2:ℂ)).sub (hh.comp hu)).add (((sunny_end L K h ht x).comp hu).const_mul (8:ℂ)⁻¹); simpa only [mul_zero,add_zero,two_mul,add_sub_cancel_right ,Function.comp_apply] using hz

abbrev tapFlow (x:E4)(s:ℝ):= -(∫ p:E4, wages L K s x p)
lemma life_top : HasDerivAt (topFlow L K x) (tapFlow L K x s) s:= by
    have he:= hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound:=fun p:E4=>2*(ntC (s+1) ‖p‖ *‖U (ν p)*leaseTax (s-1) p‖))
       (Icc_mem_nhds (sub_one_lt s) (lt_add_one s)) (Eventually.of_forall fun t=> (tail_hold L K t x).1) (tail_hold L K s x)
       (wages_hold L K s x).1 (Eventually.of_forall fun t=> fun u hu=> brackets L K s x t u hu) ((winds0 L K (s-1) (s+1)).const_mul 2)
       (Eventually.of_forall fun p=> fun t _=> ((((life_line (ν p) t).const_mul (U (ν p))).const_mul (Λ x p))))
    exact he.2.const_sub _

lemma costFlow : tapFlow L K x s=∫ p:QP,Tone.bill (Theater.out x) p*(U p*pearler p s) ∂planeF:= by
    rw [tapFlow,← integral_neg,← ampFπ.integral_comp (Drops.ν.toHomeomorph.measurableEmbedding) (fun p=> Tone.bill (Theater.out x) p*(U p*pearler p s))]; apply integral_congr_ae; filter_upwards with p; rw [ν_bill,wages]; ring
lemma cumInt : Integrable (fun p:QP=>Tone.bill (Theater.out x) p*(U p*pearler p s)) planeF:= by
    rw [← ampFπ.integrable_comp_emb (Drops.ν.toHomeomorph.measurableEmbedding)]; convert (wages_hold L K s x).neg using 1; funext i; simp_rw [Pi.neg_apply,comp,ν_bill,wages,mul_neg,neg_neg]

end YM.MS.ScaleForest.Aurora
