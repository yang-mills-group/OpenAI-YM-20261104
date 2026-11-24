import YM.MSbar.Atlas.Candle
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory Metric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f n':Side}{S:StepData c f}
open Precision Tree Pressure Push Push.AbsoluteSums ConnectedActivityE6 Push.Uniform
open Heath Bulk Finset
variable (P:Patch)(K:KernelChoices)(J:Voice G) (A B:Stage)(s:Palisade)
set_option quotPrecheck false
local notation "L"=> P.L
local notation "Ξ"=> tip G L
lemma chargesA (t:ℝ→ℕ)(h:Beam G P.L (fun x=>(t x:ℝ))):Beam G P.L (fun x=> (skirt (t x):ℝ)):=by
    simp only [skirt,Nat.cast_pow,Nat.cast_add,Nat.cast_one]; exact ((h.add h).add (Beam.coin _)).power _
lemma char (s:Patch) (G:Gauge):Beam G s.L (fun x=> (belt (radiusB (tip G s.L x)):ℝ)) :=by
    let k x:= radiusB (tip G s.L x); have h:= Beam.shore s.L G
    simp only [belt,Nat.cast_mul]; apply Beam.mul (chargesA s _ h); apply chargesA s; push_cast; exact (Beam.coin 2).mul h
def worker (B:Stage) (x t:ℝ) (p:ℕ):=
    let R:=radiusB x; let z:=B.supportExponent; let T:=temp x
    craft B.paths B.width t p R+(p*8:ℝ)*( lbt x*T^2*(2*Real.exp (B.width*8)*(81*meter B.width))+ability x*(2*Real.exp (z*10))*((2*(4*R+2)+1:ℝ)^4*meter z))
def Antlers (G:Gauge)(Lc : Side)(B:Stage)(s:ℝ):= worker B (tip G Lc s) (2*tip G Lc s) (skirt (radiusB (tip G Lc s)))
lemma starts (G:Gauge): Rate G P.L (-(8/10)) (Antlers G P.L B):=by
   let b:=tip G P.L; let q:=fun x=>radiusB (b x); have hs : Beam G P.L (fun x=> (q x:ℝ)):=Beam.shore P.L G
   have ht : Beam G P.L (fun x=> (skirt (q x):ℝ)):=chargesA P q hs
   let D x:=Heath.cape (skirt (q x)) B.width (q x)
   have hv : Pole G P.L D:=by
      have hp: Pole G P.L (fun x=> Real.exp (-B.width/2 * q x)):= (Pole.cape P.L G (a:=B.width/2) (half_pos B.width_pos)).lower (Eventually.of_forall fun x=>by rw [neg_div])
      exact (hp.mul ht.tick).mul ((((Beam.coin 2).mul hs).add (Beam.coin 1) |>.power 4).add (Beam.coin _) |>.tick)
   let Z x:=craft B.paths B.width (2*b x) (skirt (q x)) (q x)
   let e:= -(8/10:ℝ)
   have hF : Pole G P.L Z:=by
      let v (x:ℝ) := (2*b x)*(16*B.paths^2*Fintype.card PlaqAxes+B.paths*(crownAtom B.width 3+crownAtom B.width 4))
      apply (hv.mul (show Rate G P.L 1 v from ((Rate.hat (G:=G) («L»:=P.L)).mul_left _).mul_right _)).lower (Eventually.of_forall fun x=> ?_); exact le_of_eq (congr_arg abs (mul_comm (v x) _))
   have hT:Rate G P.L 0 (lbt ∘ b):=Rate.monitor.mul_left _
   have hc:Rate G P.L e (fun x=> lbt (b x)*temp (b x)^2*(2*Real.exp (B.width*8)*(81*meter B.width))):=((hT.mul (Rate.flame.pow 2)).mul_right _).weaken (by norm_num [e])
   let F x:=(2*(4*(q x:ℝ)+2)+1)^ (4:ℕ)*(meter B.supportExponent)
   have hh :Beam G P.L F:= ((((Beam.coin 2).mul (((Beam.coin 4).mul hs).add (Beam.coin 2))).add (Beam.coin 1) |>.power 4).mul (Beam.coin _))
   have hk:=(ht.mul (Beam.coin (8:ℝ))).tick.mul (hc.add ((((ability_rate G P.L).mul_right (2*Real.exp (B.supportExponent * 10))).mul hh.tick).weaken (by norm_num [e])))
   rw [zero_add] at hk; exact (hF e).add hk
lemma roam (G:Gauge): Rate G P.L (-19/10) (fun x=> hurry s (max (skies (tip G P.L x)) (arch (tip G P.L x))) (stockMove G s (tip G P.L x)) (2*winch (tip G P.L x))) :=by
    let k:=tip G P.L;let f x:=max (skies (k x)) (arch (k x));let d:=-(48/100:ℝ);let b:=-(6/5:ℝ);let a:=s.coords*countCost s.a;let c:=s.density; let u:= G
    have hv: Rate G P.L d f:=by
       have hx := (flog P (G:=G)).weaken (show -(1/2:ℝ) ≤ d by norm_num [d]); have hy:Rate G P.L d (arch∘k):=Rate.power
       intro e h; filter_upwards [hx _ h,hy _ h] with x hk hl; rcases le_total (skies (k x)) (arch (k x)) with hz|hz
       unfold f; rw [max_eq_right hz];exact hl
       unfold f; rw [max_eq_left hz]; exact hk
    let m:= stockMove G s ∘ k; have hm: Rate G P.L b m:= ((Rate.power (G:=G) («L»:=P.L)).mul_left (unit G s)).mul_left 2
    let Y x:=2*winch (k x); have he:Rate G P.L (b+-(2/5:ℝ)) Y:=(Rate.power.mul Rate.power).mul_left 2
    have hg:=((hv.mul_right (c*a)).mul_right a).mul hv
    have ht := (hm.mul ((hm.mul_right (c*a)).weaken (show b ≤ d+d by norm_num [b,d])|>.add hg)).weaken (show b+(d+d) ≤ (-19/10:ℝ) by norm_num [b,d]); exact ht.add ((he.mul ((hv.mul_right (c*a)).add (hg.weaken (by norm_num [d])))).weaken (by norm_num [b,d]))
-- buy walks.Need rpay equality start.
lemma walks (G:Gauge) : ∀ᶠ x:ℝ in atTop, ∀ {c:Side}(R:Rep G c), let b:=tip G P.L x;FaceValue B b R→∀ l:ℕ,l ≤ skirt (radiusB b)→
  outset R.p B.width B.paths (ability b) (lbt b) R.beta (radiusB b) l + R.beta*(hurry s (max (skies b) (arch b)) (stockMove G s b) (2*winch b) - increments b*distance b) ≤ rpay b:=by
    let f:=Antlers G P.L B; let z:=tip G P.L; let g x:= hurry s (max (skies (z x)) (arch (z x))) (stockMove G s (z x)) (2*winch (z x)); let h' x:= 2*z x*g x
    let w:=-(7/10:ℝ); have he := starts P B G; have hh:= roam P s G
    filter_upwards [(Work.E09.betaF_growth G P.L).eventually_gt_atTop 1,(Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G P.L)).eventually_ge_atTop 16, hh (-17/10) (by norm_num), he w (by norm_num [w])] with x hx hL hF hB c R b h i hi
    have hb:1<b:=hx; have hα:0<b:= by linarith
    let m:=b^w;let v:=b^(-17/10:ℝ)
    have ht':0≤v:=by unfold v; positivity
    have hm : b*v=m:=by unfold m v; rw [mul_comm b,←Real.rpow_add_one hα.ne']; congr 1; norm_num [w] --
    have hg:0≤ability b:=by unfold ability cue; positivity
    have hp':0< B.paths:=B.paths_pos; have hs':=meter_pos B.width_pos
    have hu : 0≤ lbt b := mul_nonneg zero_le_two (Real.exp_pos _).le
    have hs :0<R.beta:= (half_pos hα).trans_le h.beta
    have he : outset R.p B.width B.paths (ability b) (lbt b) R.beta (radiusB b) i ≤ Antlers G P.L B x:=by
       unfold outset Antlers worker
       have hW:= meter_pos B.price_pos; unfold craft Heath.cape life crownAtom; simp_rw [h.threshold,h.size,h.support]; have h0:=meter_pos (half_pos B.width_pos);let Y:= B.width; change _ ≤ 2*b*(16*B.paths^2* Fintype.card PlaqAxes+_)*Heath.cape _ _ _ + _
       unfold Heath.cape; dsimp only [b] at *; have hx:= h.upper;unfold tip at *; gcongr <;> first|positivity| exact_mod_cast hi
    let Y:=increments b*distance b; have hy :Y=v*Real.log b :=by unfold Y increments distance v; rw [← mul_assoc,← Real.rpow_add hα]; congr 2; norm_num
    have hz : Real.log b ≥ 16:= hL; have hK := mul_le_mul_of_nonneg_left (le_abs_self (g x) |>.trans hF) hs.le -- refine
    have ha :0≤Y:= hy ▸ mul_nonneg ht' (by linarith)
    have hm' := mul_le_mul_of_nonneg_right h.beta ha; unfold rpay; change _ + R.beta*(g x-Y)≤ - (b/8*Y)
    have hf:R.beta*g x ≤ R.beta*v := hK; have hs: v*b*Real.log b ≥ v*b*16:=mul_le_mul_of_nonneg_left hz (mul_nonneg ht' hα.le); have hc:b*Y=v*b*Real.log b:=by rw [hy];ring
    have Hs:R.beta*g x ≤ m+m:=hf.trans ((mul_le_mul_of_nonneg_right h.upper ht').trans_eq (by rw [← hm]; ring)); have he : outset R.p B.width B.paths _ _ _ _ _ ≤ m:=he.trans ((le_abs_self _).trans hB)
    have hm2:b*Y ≥ 16*m := by rw [hc,← hm]; linarith only [hs]
    have hm': b*Y ≤ 2*(R.beta*Y):=by linarith only [hm']
    have hm3:0≤ m:= hm ▸ mul_nonneg hα.le ht'; rw [mul_sub]; linarith only [he,hm2,hm3,Hs,hm']
end YM.MSbar.Heath.Stock
