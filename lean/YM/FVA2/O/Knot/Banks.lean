import YM.FVA2.O.Tune.Track
import YM.FVA2.O.Fusion.Whole
/-!
# Integrating directly in all real scales preserves viability (compact costs only)
For propagating solutions with arbitrary $t ≥ t₀$ data. No growth assumptions at the horizon.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Knot
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve
open scoped Topology ContDiff Interval
variable {E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [FiniteDimensional ℝ E][CompleteSpace F] {f:ℝ→ E→F}{s t r:ℝ}{j:ℕ}
private def month (a b:ℝ) : Measure ℝ := volume.restrict (Set.Ioc a b)
private instance (a b:ℝ): IsFiniteMeasure (month a b) := by unfold month; exact isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne -- find
omit [CompleteSpace F] in
lemma slim (hp:Gym f)(hc:∀ p,Continuous (fun t=> f t p)) (a b:ℝ): Majorant (month a b) f := by
    let M:=max ‖a‖ ‖b‖; refine ⟨ ( .of_forall fun i=>hp.sm i ),fun j p=> (hp.jet_c hc p j).aestronglyMeasurable,fun j p=>?_⟩; obtain ⟨K,hK,h⟩:= hp.day M 1 (by unfold M; positivity) zero_le_one p j; refine ⟨ closedBall p 1, closedBall_mem_nhds p zero_lt_one, fun _=> K,integrable_const .., (ae_restrict_mem measurableSet_Ioc).mono (fun i hi=>h _ ?_) ⟩; refine ⟨?_,?_⟩; · linarith [show -a≤‖a‖ from neg_le_abs a, le_max_left ‖a‖ ‖b‖, hi.1, show M=max ‖a‖ ‖b‖ from rfl]
    exact hi.2.trans (( le_abs_self b ).trans ( le_max_right ‖a‖ |b| )) -- parameter type coercion
abbrev cafe (f:ℝ→ E→F)(a b:ℝ)(x:E) := ∫ u in a..b, f u x
lemma bank_day (hp:Gym f)(hc:∀ p,Continuous (fun t=> f t p)) (a b:ℝ): ContDiff ℝ ∞ (Knot.cafe f a b):= by
    unfold Knot.cafe intervalIntegral; exact (slim hp hc a b).contDiff.sub (slim hp hc b a).contDiff
lemma cafe_j (hp:Gym f)(hc:∀ p,Continuous (fun t=> f t p)) (a b:ℝ)(x:E): iteratedFDeriv ℝ j ( Knot.cafe f a b ) x= Knot.cafe (fun t=> iteratedFDeriv ℝ j (f t)) a b x:= by
    unfold Knot.cafe intervalIntegral; let L(a b:ℝ):=fun x=>∫ u,f u x∂month a b; change iteratedFDeriv ℝ j ( L a b - L b a ) x=_; rw [iteratedFDeriv_sub_apply ( (slim hp hc a b).contDiff.contDiffAt.of_le (by exact_mod_cast le_top) ) (( slim hp hc b a ).contDiff.contDiffAt.of_le (by exact_mod_cast le_top)), (slim hp hc a b).identity, (slim hp hc b a).identity]; rfl
lemma Gym.cafe_p (hp:Tune.Gym f)(hc:∀ p,Continuous (fun t=> f t p))(a:ℝ) : Tune.Gym ( Knot.cafe f a ):= by
    constructor; intro r hr; refine ⟨ fun p=> bank_day hp hc _ _, fun j=>?_⟩; let M:= max ( ‖a‖ ) r + 1; have hM:0<M:= by unfold M; positivity
    have ha:‖a‖≤M:= le_trans (le_max_left ..) (le_add_of_nonneg_right zero_le_one); have hu:r≤ M:= le_trans (le_max_right ..) (le_add_of_nonneg_right zero_le_one); obtain ⟨C,hC,k,hK⟩:= hp.basic M hM.le|>.quoted j; refine ⟨ 2*C*M,by positivity,k,fun i p _=>?_ ⟩
    simp only [ Job.tx, Job.cw, one_pow, mul_one, Pi.one_apply ]; let t:=i.2.val; change ‖iteratedFDeriv ℝ j ( Knot.cafe f a t ) p‖≤_; rw [cafe_j hp hc]; let F(t:ℝ):= iteratedFDeriv ℝ j (f t) p; let K:= C*(1+‖p‖)^k; have h(k)(H:k∈Set.Icc (-M) M): ‖F k‖≤K:= by specialize hK (⟨ (),k,H⟩:camp M) p trivial; simpa only [ Pi.one_apply,one_pow,mul_one,cw,tx ] using hK; -- gear
    have hP: ‖t‖ ≤ M:= (htT i).trans hu; have hW := abs_le.mp ha; have ht := abs_le.mp hP; obtain he:= intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=t) (f:=F) (C:=K) (fun x hx=> h x ⟨le_trans (le_min hW.1 ht.1) hx.1.le,le_trans hx.2 (max_le hW.2 ht.2) ⟩); apply he.trans
    exact le_trans (mul_le_mul_of_nonneg_left (abs_le.mpr ( show - (2*M) ≤ t-a ∧ t-a ≤ 2*M from ⟨ (by linarith [ht.1,hW.2]),(by linarith [ht.2,hW.1])⟩)) ( show 0≤K from by unfold K; positivity)) (le_of_eq (by unfold K; ring))
end YM.FVA2.O.Knot
