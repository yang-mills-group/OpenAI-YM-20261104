import YM.MSbar.Sat.Willing
/-!
# Delaying to numerical thresholds. Native scales credits independent of volume. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge} -- repair
open Pressure Push.AbsoluteSums Push ConnectedActivityE6
-- Fram.Log powers.All use fine-score!
abbrev tip(G:Gauge)(L:Side)(x:ℝ) := betaF G x L
def Pole (G:Gauge) (L:Side) (f:ℝ→ℝ) :Prop:=∀ a,Rate G L a f
def Beam (G:Gauge)(L:Side)(f:ℝ→ℝ):Prop := ∃ c:ℝ, c>0∧∃ j:ℕ,∀ᶠ x in atTop, |f x| ≤ c*(Delay.bill G L x)^j
variable {L : Side}{a b :ℝ}{f g:ℝ→ℝ}
lemma Beam.coin (c:ℝ):Beam G L (fun _=>c) := ⟨1+|c|,add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg _),0,Eventually.of_forall fun x=>by simp⟩
lemma Beam.lower (h:Beam G L f)(hv:∀ᶠ x in atTop,|g x|≤|f x|):Beam G L g:=by obtain ⟨a,b,c,d⟩:=h; exact ⟨a,b,c,(hv.and d).mono fun x hx=> hx.1.trans hx.2⟩
lemma Beam.lit (G:Gauge)(L:Side): Beam G L (Delay.bill G L):=⟨1,zero_lt_one,1,Eventually.of_forall fun x=> by rw [abs_of_nonneg (zero_le_one.trans (Delay.bill_ge ..))]; simp⟩
lemma Beam.mul (h:Beam G L f)(hm:Beam G L g):Beam G L (fun x=>f x*g x):=by
   obtain ⟨c,hc,j,h⟩:=h; obtain ⟨a,ha,i,hg⟩:= hm; refine ⟨c*a,mul_pos hc ha,j+i, (h.and hg).mono fun x hx=>?_⟩
   dsimp only;rw [abs_mul,pow_add]; exact (mul_le_mul hx.1 hx.2 (abs_nonneg _) ((abs_nonneg _).trans hx.1)).trans_eq (by ring)
lemma Beam.add (h:Beam G L f)(hG:Beam G L g):Beam G L (fun x=>f x+g x):=by
   obtain ⟨c,hc,j,h⟩:=h; obtain ⟨a,ha,i,hg⟩:= hG; refine ⟨c+a,add_pos hc ha,max j i, (h.and hg).mono fun x hx=>?_⟩
   rw [add_mul]; exact (abs_add_le ..).trans (add_le_add (hx.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Delay.bill_ge ..) (le_max_left ..)) hc.le)) (hx.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Delay.bill_ge ..) (le_max_right ..)) ha.le)))
lemma Beam.power (h:Beam G L f)(n:ℕ):Beam G L (fun x=> f x^n):= by induction n with
    | zero=> simp_rw [pow_zero]; exact Beam.coin ..
    | succ n ih=> simp_rw [pow_succ]; exact ih.mul h
lemma Beam.tick (h:Beam G L f):Rate G L 0 f:=by
    obtain ⟨c,hc,j,d⟩:=h; intro a ha; have hp:= Rate.bill (G:=G) (L:=L)|>.pow j|>.mul_left c; rw [zero_mul] at hp
    filter_upwards [d,hp a ha] with x hx ht; exact hx.trans ((le_abs_self _).trans ht)
lemma Beam.shore (L:Side)(G:Gauge):Beam G L (fun x=> (radiusB (betaF G x L):ℝ)) := by
    refine (Beam.lit G L).lower (Eventually.of_forall fun x=>?_); simp only [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (radiusB (betaF G x L))),abs_of_nonneg (zero_le_one.trans (Delay.bill_ge G L x))]
    have h:((radiusB (tip G L x)):ℝ) < Real.log (tip G L x)^2+1 := Nat.ceil_lt_add_one (sq_nonneg _); unfold Delay.bill; linarith only [h,Nat.cast_nonneg (α:=ℝ) (radiusB x)]
lemma Beam.rare (G:Gauge)(L:Side): Beam G L (fun x => (radiusB x: ℝ)):=by refine (Beam.lit G L).lower (Eventually.of_forall fun x=>?_); rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (zero_le_one.trans (Delay.bill_ge G L x))]; unfold Delay.bill; linarith [sq_nonneg (Real.log (tip G L x))] -- dsimp
lemma Beam.logfine (G:Gauge)(L:Side): Beam G L (Real.log∘ tip G L):=by
   refine (Beam.lit G L).lower (Eventually.of_forall fun x=>?_); rw [Function.comp_apply, abs_of_nonneg (show 0≤ Delay.bill G L x from zero_le_one.trans (Delay.bill_ge ..))]; rw [abs_le]; unfold Delay.bill; have he := sq_nonneg (Real.log (tip G L x)+1); have hx:= sq_nonneg (Real.log (tip G L x)-1); have hm:=Nat.cast_nonneg (α:=ℝ) (radiusB x); constructor <;> nlinarith only [he,hx,hm]
lemma Beam.lesser (h:Beam G L f)(hv:0<a):∀ᶠ x in atTop, |f x|≤(Delay.fineMonitor G L x)^a:=by
    obtain ⟨c,hc,j,hb⟩:=h; exact (hb.and (Delay.monitor_pays G L j hc.le hv)).mono (fun x hx=>hx.1.trans hx.2)
lemma Beam.lax (h:Rate G L a f) (hv:a<0): Beam G L f:= (Beam.coin (G:=G) (L:=L) 1).lower (by simpa using h.below hv 1 zero_lt_one)
lemma Pole.mul(h:Pole G L f)(hv:Rate G L a g):Pole G L (fun x=> f x*g x):=fun i=>by simpa using! ((h (i-a)).mul hv)
lemma Pole.add (h:Pole G L f)(hv:Pole G L g):Pole G L (fun x=> f x+g x):=fun i=> (h i).add (hv i)
lemma Pole.lower (h:Pole G L f)(hv:∀ᶠ x in atTop,|g x|≤ |f x|):Pole G L g:=fun i=>(h i).compare hv
-- exponents, can buy simultaneously.Penalty β F.
lemma Pole.cape (L:Side)(G:Gauge)(hc:0<a):Pole G L (fun x=> Real.exp (-a * radiusB (betaF G x L))) := by
   let f:=tip G L; intro b c h; let k:=|c|
   have hp:= Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G L)
   filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop 1,hp.eventually_ge_atTop (k/a)] with x hx hk
   let y:=Real.log (f x); have hv : 0≤ y:= (Real.log_pos hx).le; have he : k≤ a*y:= ((div_le_iff₀ hc).mp hk).trans_eq (mul_comm ..)
   have hL: y^2 ≤ (radiusB (f x):ℝ):= Nat.le_ceil _
   rw [Real.rpow_def_of_pos (zero_lt_one.trans hx), abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone;  have hl:=mul_le_mul_of_nonneg_left hL hc.le; change -(a)*_≤ y*c; have ht:= mul_le_mul_of_nonneg_left (neg_abs_le c) hv; have hn:=mul_le_mul_of_nonneg_left he hv; linarith only [hl, ht, hn]
end YM.MSbar.Heath.Stock
