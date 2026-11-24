import YM.OPE.Compatible.Kyoto.Orbs
import YM.Next.SCHEDULE.Vicinity
/-! # Instant stage clocks. Minimal conform tests before Ω reality. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.CardinalQ
open Function Filter Set Finset Lattice Laurent RG Wilson
open scoped Topology BigOperators Classical
open Drift Stroke Yolk Pill Spells
open Next.Scheduling Clock
variable {G:Gauge}{X E I:Type}{t s z V:ℝ}
abbrev billV (x:ℝ):=Real.exp ((Real.log (Real.log x))^2)
abbrev θj (x:ℝ):= Clock.gap x * billV x
abbrev coverJ (x:ℝ) := Nat.ceil (Real.log x^ (2:ℕ))
abbrev Ωb (x:ℝ):= Real.exp (-((billV x) ^ ((1 : ℝ)/5)))
abbrev ℰb (x:ℝ):= Clock.gap x ^ (11/5:ℝ)
abbrev capL (u x:ℝ):= 2* billV x^u
abbrev salary (x:ℝ) := Real.sqrt (Ωb x)
lemma βδ (hp:0 < t):t= (gap t)⁻¹^ (2:ℕ):= by unfold gap; rw [inv_inv,Real.sq_sqrt hp.le]
lemma seedθ (hp:0 ≤ t): t^((-1:ℝ)/2) = Clock.gap t := by rw [neg_div,Real.rpow_neg hp,← Real.sqrt_eq_rpow]; rfl
lemma peony {x:I→ℝ}{i:I}(hp:0 ≤ x i): GripU x i=θj (x i) := by change (x i)^((-1:ℝ)/2)*_= _; rw [seedθ hp]; rfl
lemma τcoin {c:RG.Calendar G}{k:ℕ}{x:ℝ}(h:c.hatBeta k=x) : c.threshold k=θj x ∧ c.coverSize k=coverJ x∧ c.forcedAllowance k=Ωb x ∧ c.allowance k=ℰb x ∧ c.loopCap k=capL (c.theta (c.J k)) x:= by subst x; exact ⟨rfl,rfl,rfl,rfl,rfl⟩ -- equality check
variable {f:Filter I}{β q:I→ℝ} (h:Tendsto β f atTop)
include h
lemma βmoment : Wick β f (fun i=> Ωb (β i)):=by
       intro a; let K:= Counters β; let p:= -a; -- RateLE f K
       let v(i):= gap (β i)^((2:ℝ)*a); have hv:RateIs f K v (-(a:ℝ)):=by
            have he:RateIs f K (gap∘β) (-1/2):= (show RateIs f K (Sparks β) (-1/2) from (by simpa only [mul_one] using (canq h).rpow (-1/2))).congr ( (h.eventually_ge_atTop (0:ℝ)).mono fun i hi=> seedθ hi); simpa only [Function.comp_def,show 2*a*((-1:ℝ)/2)= -a from by ring] using! (he.rpow (2*a))
       let Y(i):= Ωb (β i); have hx: Tendsto (fun i=>v i*Y i) f (𝓝 0) :=by
             have hp := Clock.burnt (2*a) 1 2 (1/5) zero_lt_one (by norm_num) (by norm_num); apply (hp.comp h).congr'; filter_upwards with i; dsimp only [Function.comp_apply,v,Y]; rw [watch_two (β i),neg_one_mul]; rfl -- charges
       let z:=fun i=>v i*Y i; have ht: RateLE f K z 0:= RateLE.absBound 2 (carth h) (hx.norm.eventually (ge_mem_nhds (by simp))); apply RateLE.congr (show RateLE f K (fun i=> z i*(v i)⁻¹) a from (by simpa only [neg_neg, zero_add] using! ht.mul (hv.inv.pays (carth h)))); filter_upwards [hv.1] with i hi; unfold z; field_simp; rfl
lemma CoinS (a:ℝ): RateIs f (Counters β) (fun i=> capL a (β i)) 0:=by
       have hu: RateIs f (Counters β) (fun i=>billV (β i)) 0:=by
             have he := Bram h; let F(i):= GripU β i / gap (β i); have hV: RateIs f (Counters β) (Clock.gap ∘ β) (-1/2):= (show RateIs f (Counters β) (Sparks β) (-1/2) from (by simpa only[mul_one] using (canq h).rpow (-1/2))).congr ((h.eventually_ge_atTop (0:ℝ)).mono fun i hi=> seedθ hi)
             have hx: RateIs f (Counters β) F 0:=by simpa only[sub_self] using! he.div hV
             refine hx.congr ?_; filter_upwards [h.eventually_gt_atTop 0] with i hi; unfold F; rw [peony hi.le]; exact mul_div_cancel_left₀ _ (Clock.gp hi).ne'
       exact (by simpa only [mul_zero,zero_add] using! (RateIs.const (carth h) (by norm_num:(0:ℝ)< 2)).mul (hu.rpow a))
end YM.OPE.CardinalQ
