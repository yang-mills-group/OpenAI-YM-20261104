import YM.MS.Image.Amber
/-!
# polynomial-log bounds for projected amplitudes

Prices after ε=0. S.basic.Interpolation also supplies Stamp over `t`. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Outlook
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}{K:Mob G}{F:Flats G}{n m:ℕ}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S:Scale I) {t y:I→ℝ}{f:E→ℂ}
lemma bound_r (h:∀ i,exp (t i)= S.length i)(b:ℤ)(hp:veg 0 (fun _:Unit=>f) 1): Bound S (fun i=> Alps.Bench.Forest.patch f b (t i)) (fun i=> S.length i^b):= by
   refine ⟨ fun i=> (Alps.Bench.Forest.plot ( hp.smooth ()) (b:ℂ)).part (t i), fun j=> ?_⟩; obtain ⟨C,hC,l,H⟩:= ride hp j; refine ⟨C,hC,l,fun i p hu=>?_⟩; let L:= S.length i; let g(x:E):= f (L • x); let v:= t i; have hc:ContDiff ℝ j f:= ((hp.smooth ()) : ContDiff ℝ ∞ f).of_le (by exact_mod_cast le_top); have hA:0< L:= S.pos i; have he:amount (b:ℂ) v= ( (L^b:ℝ):ℂ) := by rw [← Complex.ofReal_intCast,amount_mint]; unfold L v; rw [← h,← Real.rpow_intCast, mul_comm, Real.exp_mul]
   dsimp only; rw [show Alps.Bench.Forest.patch f (b:ℂ) (t i)= (L^b:ℝ) • fun p:E=> f (L • p) from funext (fun p=> (by unfold Alps.Bench.Forest.patch; rw [he,h]; rfl)),iteratedFDeriv_const_smul_apply (f:=fun p:E=> f (L • p)) (ContDiff.contDiffAt (hc.comp (f:=fun p:E=>L • p) (by fun_prop))),iteratedFDeriv_comp_const_smul L hc,norm_smul,norm_smul,norm_of_nonneg (zpow_nonneg hA.le _), norm_of_nonneg (pow_nonneg hA.le _) ]; change L^b*(L^j * _)≤C*S.full.cheap i p^l*( L^b * L^ j ); rw [← mul_assoc, mul_comm (_* L^j) ]; apply mul_le_mul_of_nonneg_right _ (mul_nonneg (zpow_nonneg hA.le _) (pow_nonneg hA.le _)); refine (H () ( L • p)).trans ?_; simp only [Pi.zero_apply,Pi.one_apply,abs_zero,add_zero,one_mul,mul_one,norm_smul,Real.norm_of_nonneg hA.le]; gcongr; exact le_mul_of_one_le_left ( by exact S.weight_pos i p |>.le) ( S.one_le i ) -- type shape weight def
lemma boundL (p:Poly)(h:∀ i,‖t i‖≤ S.basic i): Bound S (fun i (_:E)=>p.eval (t i)) 1:= by
   induction p using Polynomial.induction_on' with
   | monomial n a=>
       have he: Bound S (fun i (_:E)=>t i) 1:= Costs.scalar ⟨1,zero_lt_one,1,fun i p _=> by simpa only [pow_one,Pi.one_apply,one_mul,mul_one,Scale.full] using (h i).trans ( le_mul_of_one_le_right ( S.basic_pos i|>.le) ( S.one_le_weight i p))⟩
       simp only [Polynomial.eval_monomial]; convert! (Costs.L ( ContinuousLinearMap.mul ℝ ℝ a) ( he.pow n)) using 1; ext; simp
   | add p q hp hq=> simp only [Polynomial.eval_add]; exact hp.add hq
lemma bills (hp:Host F n)(w:Touch G m E) (hv:∀ i,‖y i+t i‖≤ S.basic i)(hx:∀ i, exp (t i)=S.length i): Bound S (fun i=>fieldVal (hereZ n F (t i) (y i) m) w) (fun i=> (S.length i ^ (mass w-n))):= by
   obtain ⟨R,H⟩:= tallP ( Moony.toast hp.bill); obtain ⟨N,hN⟩:= press_ready (F:=F) R (n:=R); let b:ℤ:=mass w-n
   simp_rw [vertical H hp.tall, show ∀ x c, fieldVal (plow x (t c) ( Press F R R (y c+t c)) m) w = _ from fun x c=> funext ( mix_slide hN (pressB H R) w x (t c) (y c))]; refine Costs.sum _ (fun i hi=>?_) ( fun i p hp=> zpow_nonneg (S.pos i).le _)
   rw [show -(n:ℂ)+mass w=(b:ℂ) by push_cast [b]; ring]; convert! ((boundL S (plate N i) (t:=fun i=>y i+t i) hv (E:=E))).smul (bound_r S hx b ( BigG ( pressB H R i ) _ w)) using 1; funext i p; change _=1 * _; simp [b]
open LogTime LogTime.IntervalFamily
lemma Billp (w:Wire (Branch G Axis) E FourP)(hp: Host F n): Bill (four n F) w n:= by
   refine bills (High.meet.primary) hp (m:=0) w (t:=fun i=> IntervalFamily.t i) (y:=fun i=>LogTime.IntervalFamily.index i) (fun i=> ?_) (fun i=>rfl); let t:=IntervalFamily.t i; let y:= IntervalFamily.index i; change ‖y+t‖≤(1+|y|)*(1+t); have ht:t≥0:= (meet.beg_nn _).trans i.ge; obtain hx:= norm_add_le y t; rw [norm_of_nonneg ht] at hx; apply hx.trans; rw [Real.norm_eq_abs]; nlinarith [abs_nonneg y]
lemma Risep (w:Wire (Branch G Axis) E FourP)(hp:Host F n): Bound meet.dawn (fun i x=> four n F (i,0) (sail w x)) fun _=>1:= by
   have h : ∀ i:ℝ,‖id i+(0:ℝ)‖≤ meet.dawn.basic i:= by intro i; change ‖i+(0:ℝ)‖≤(1+|i|)*(1+0); simp [Real.norm_eq_abs]
   convert bills meet.dawn hp (m:=0) w (t:=fun _=> (0:ℝ)) h (fun i=>rfl) using 1; rfl; ext; simp [High.meet] -- maybe defeq rfl not recognized
end YM.MS.Outlook
