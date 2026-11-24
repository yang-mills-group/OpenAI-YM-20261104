import YM.XSpace.Seated
/-!
# From momentum currency to e± for coupling diagnostic
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Set Filter MeasureTheory Trace Graph3 Maxwell Maxwell.Free Maxwell.Wick Photo Cirrus Normalize Tornado Chiral Structure1 AxesTangent Angle Season Lattice Relief Finale
open scoped Topology BigOperators Classical
variable {G:Gauge}{d:ℕ}(W:Initialize G)(g:G.Simple)(V:Store G){c:Shade.Cut}
abbrev f:= (Real.sqrt 2)⁻¹
abbrev toll (G:Gauge): Sec G 6 := ((f:ℂ)^3) • Tbk G
abbrev tin (G:Gauge): Sec G 6 := ((f:ℂ)^2) • Tuk G
abbrev tag (G: Gauge):= trip (toll G) (tin G) (tin G)
def lens (σ: Bool)(p:Name G): WickPol G:=symbol 0 (flavor (G:=G) 0 p.2 (∑ b:PlaqAxes,qNorm σ p.1 (six b) (endr b) • cell (six b) (endr b)))
lemma lei (σ:Bool)(p:Name G): lens σ p=(f:ℂ) • spark σ p:=by
  apply equalPol; intro X; rw [lens,spark,map_smul,symbol_test,symbol_test]
  unfold arm Fq qNorm; simp_rw [mul_smul, ← Finset.smul_sum, map_smul,LinearMap.smul_apply]; exact Complex.ofReal_mul ..
lemma charged (G:Gauge): (toll G).val=∑ i:Name G,∑ j:Name G,∑ k:Name G,fuel i j k • (lens true i*lens true j*lens true k):=by
  change _ • B G=_ ; unfold B; simp only [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>?_ ; rw [lei,lei,lei,smul_mul_smul,smul_mul_smul,pow_succ,pow_two,smul_comm]
lemma frontier (G:Gauge) : (tin G).val=(2:ℂ)⁻¹ • ∑ i:Name G,lens false i*lens false i:=by change _ • Chiral.U G=_; rw [U,smul_comm]; simp only [Finset.smul_sum,lei,smul_mul_smul,pow_two]
lemma stamp_fee (P:Structure1.Point G 6 3): P (tag G)=(↑(f^7:ℝ):ℂ)*P (token G):=by
  let F:= (↑f:ℂ); let v:= trip (F^3) (F^2) (F^2); rw [show tag G=fun i=> v i • token G i from funext fun i=>by fin_cases i <;> rfl]; rw [MultilinearMap.map_smul_univ,Fin.prod_univ_three]; change ((F^3* F^2)* F^2) • _=_; rw [Complex.ofReal_pow, ← pow_add,← pow_add];rfl
lemma t_odd : hinge 6 (toll G)= -toll G :=by unfold toll; rw [map_smul,bknots, smul_neg]
lemma u_even : hinge 6 (tin G)= tin G :=by unfold tin; rw [map_smul,uknots]
lemma t_real : reel 6 (toll G)= toll G:=by
  apply Subtype.ext; change realForm ((f:ℂ)^3 • B G)=_; rw [real_scale,star_pow,show star (↑f : ℂ)=_ from Complex.conj_ofReal f,b_real];rfl
lemma u_real : reel 6 (tin G)=tin G:=by apply Subtype.ext; change realForm ((f:ℂ)^2 • U G)=_; rw [real_scale,star_pow, show star (↑f:ℂ)=_ from Complex.conj_ofReal f]; rw [Chiral.u_real];rfl
lemma pos : 0<f:=by unfold f; positivity
lemma halfGram :2*f^2=1:=by unfold f; rw [inv_pow,Real.sq_sqrt (by norm_num)]; norm_num
-- state §tri prescription in normalized components; payment test elsewhere. single-line normalization explicit, not demanding off-support gauge-fixing invariance. U/B contractions follow. integrated minus through any cut. write formula with full e_i and so coefficient Pin.
abbrev m (i:P) (a:Axis)(x:E4):ℝ:= f* Season.line false i a x
abbrev clamp (i j:P)(x:E4):ℝ:= f^2 * surfT true false i j x
abbrev wave (c:Shade.Cut)(i j k:P)(u v b:E4):= f^5*∑ t:P,sweepT c i t j k u v b
abbrev aT (c:Shade.Cut)(i j k:P)(u v b:E4):= (∑ x:Axis,∑ y:Axis,qNorm true i x y*m j x (u-v)*m k y (u-b))-2*wave c i j k u v b
def numeric (G:Gauge)(c:Shade.Cut)(u v b:E4):=6*S_color G*∑ i:P,∑ j:P,∑ k:P,liftedSign i j k*(∑ m:P,∑ n:P,clamp j m (u-v)*clamp k n (u-b)*aT c i m n u v b)
lemma angel (c:Shade.Cut)(u v b:E4)(i j k:P): aT c i j k u v b = f^3 * atria c i j k u v b:=by
  unfold aT wave atria; rw [show ∀ x:ℝ,2 * (f^5*x)=f^3*x from fun x=> by rw [show f^5=f^2*f^3 from pow_add f 2 3]; rw [← mul_assoc, ← mul_assoc (2:ℝ), halfGram];simp]; rw [mul_sub]; apply congr_arg (·-_) ?_; unfold est m qNorm f; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=>?_ ; ring
lemma cheer (G:Gauge)(c:Shade.Cut)(u v b:E4): numeric G c u v b=f^7 * Angle.answer c G u v b:=by unfold numeric answer; rw [mul_left_comm (f^7)]; congr 1; unfold tens Angle.op spoken; simp_rw [angel,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun x _=>Finset.sum_congr rfl fun y _=>?_ ; unfold clamp; ring
variable {x: Points 3}
include g in
lemma on_stage (H:Granted V 6 c)(S:Manages c G 6)(h:x∈Good c 3): checked1 W V 6 x (tag G)=(↑(numeric G c (x 0) (x 1) (x 2)):ℂ):=by rw [stamp_fee,status₁ W g V H S h, cheer]; push_cast;rfl -- Q sphere
end YM.XSpace.Rose
