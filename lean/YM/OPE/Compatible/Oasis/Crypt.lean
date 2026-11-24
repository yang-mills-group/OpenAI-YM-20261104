import YM.OPE.Compatible.Oasis.Vole
/-! # Instant stage clocks rates. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.CardinalQ
open Function Filter Set Finset Lattice Laurent RG Wilson
open scoped Topology BigOperators Classical
open Drift Stroke Yolk Pill Spells
open Next.Scheduling Clock
variable {G:Gauge}{X E I:Type}{t s z V:ℝ}
variable {f:Filter I}{β q v w:I→ℝ} (h:Tendsto β f atTop)
include h
lemma bread : RateIs f (Counters β) (fun i=>gap (β i)) (-(1/2)):= by have hh:= canq h|>.rpow ((-1:ℝ)/2); rw[mul_one,neg_div] at hh; exact hh.congr ((h.eventually_ge_atTop 0).mono fun i hi=>by rw [← neg_div]; exact seedθ hi)
lemma edgeθ : RateIs f (Counters β) (fun i=>θj (β i)) (-(1/2)):=by have ht:= Bram h; rw[neg_div] at ht; exact ht.congr ((h.eventually_gt_atTop (0:ℝ)).mono (fun i hi=> peony hi.le))
lemma Φmask : Wax β f (fun i=>ℰb (β i)) (-(11/10)):=by
       have he := (bread h).rpow ((11:ℝ)/5); norm_num at he; apply (he.pays (carth h)).mono (by norm_num) -- check norm_num leaves index changed
lemma shiftT (hp:∀ᶠ i in f,q i-β i=t): ∀ᶠ i in f, θj (q i) ≤ 2*θj (β i):=by
       let A:ℝ:=4/3; have hx:1 < A:=by unfold A;norm_num
       filter_upwards [hp,h.eventually_gt_atTop 0,h.eventually (Clock.similar_gap_power 1 A hx),h.eventually (Clock.similar_watch_power 2 1 A hx), h.eventually_ge_atTop (t*t)] with i hi hh he hm hu
       have ht : Clock.near (β i) (q i):=by unfold Clock.near; rw [abs_sub_comm,hi]; nlinarith [Real.sqrt_nonneg (β i), Real.sq_sqrt hh.le,abs_nonneg t,sq_abs t]
       have hr:=he (q i) (β i) ht (Clock.same _); have hy:= hm (q i) (β i) ht (Clock.same _); rw [watch_two,watch_two] at hy; simp only [Real.rpow_one] at hr hy; have hz:A^2 ≤ 2:=by unfold A;norm_num
       unfold θj; apply le_trans (mul_le_mul hr hy (by positivity) (mul_nonneg (zero_le_one.trans hx.le) (Clock.gp hh).le)); refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hz (show 0≤gap (β i)* billV (β i) from mul_nonneg (Clock.gp hh).le (Real.exp_nonneg _)))
       unfold tick billV; ring
lemma ΥPay (hc:0<t): Wick β f (fun i=> Real.exp (-(t * coverJ (β i)))):=by
       intro a b hb; filter_upwards [(carth h).eventually_gt_atTop 0, ((carth h).const_mul_atTop hc).eventually_ge_atTop (-b)] with i hi hv
       rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_monotone
       have he:= Nat.le_ceil ((Counters β i)^2); change t*Counters β i ≥ -b at hv; change _ ≤ (coverJ (β i):ℝ) at he; linarith only[mul_le_mul_of_nonneg_left he hc.le,mul_le_mul_of_nonneg_right hv hi.le]
lemma ψsalary : Wick β f (fun i=> salary (β i)):=by
       intro s t ht; let x:=β; filter_upwards [βmoment h (s*2) (t*2) (by linarith only [ht])] with i hi; have he:=hi; rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at he; change ‖Real.sqrt (Ωb (β i))‖≤_; rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]; have hh:=Real.sq_sqrt (show 0≤Ωb (β i) from Real.exp_nonneg _); have hZ:Real.exp (t*2*Counters β i)=Real.exp (t*Counters β i)^2:=by rw [pow_two,← Real.exp_add]; congr 1; ring;
       rw[hZ] at he; nlinarith only [he, Real.exp_pos (t*Counters β i),Real.sqrt_nonneg (Ωb (β i)), hh]
lemma coverPs : Receipt β f (fun i=> (coverJ (β i):ℝ)):=by
       refine (((sans h).power 2 (carth h)).plus (Score.steady (1:ℝ) (carth h)) (carth h)).under (Eventually.of_forall ?_); intro i; rw[Real.norm_of_nonneg (Nat.cast_nonneg _)]; exact (Nat.ceil_lt_add_one (sq_nonneg (Real.log (β i)))).le
omit h in
lemma boothP (hp:∀ᶠ i in f,q i ∈ Icc (β i/2) (2*β i)): Pill.Shell β q f:=⟨1/2,2,(by norm_num),(by norm_num),hp.mono fun i hi=> ⟨by linarith only[hi.1],hi.2⟩⟩ -- h unused
end YM.OPE.CardinalQ
