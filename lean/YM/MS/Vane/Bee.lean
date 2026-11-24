import YM.MS.Vane.Rocket
/-!
# Middle.Sep.Anchor gain and progress helper. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I E W:Type}{G:Gauge}{P:Geo I}{x E':ℝ} {b:Bool}{F H:Glade G I}{X: I→QP}{Y:Recount G}{n k l h:ℕ}[DecidableEq W]{s:Finset W}
 {K L:Planet G I}
local notation "℧"=> Gulf P
lemma caress (t:Stem P): ( Gulf P ).stream t=Set.Icc 0 ( tstart t ):= by
    ext; change ((_∈ Set.Icc _ _ ∧ _∈ Set.Iic _)↔_); simp only [ Set.mem_Icc,Set.mem_Iic ]; obtain H:= authority t|>.2; dsimp only [ Belt.tstart ] at *; grind
namespace Fits
variable (Z:Belt I) (v:I→ℝ) {r:ℝ}
def lower (P:Belt I)(x:I→ℝ): Prop:= ∀ p:P.time, P.stream p= Set.Icc (x p.1) p.2.val
lemma lens (Z:Belt I)(F:Glade G I) (h:Fits b F H)(hv:lower Z v): Dash b Z F H (fun p=> F p.1 (v p.1)):= by
    intro p u he; obtain hs:= h.pace p.1 u he; obtain ht:= h.stroll p.1 u he;
    have hp:v p.1 ≤ p.2.val:= by obtain hx : p.2.val∈ Z.stream p:= ⟨p.2.property,Set.mem_Iic.mpr le_rfl⟩; exact ( hv p ▸ hx : p.2.val∈ Set.Icc (v p.1) p.2.val ).1
    rw [Mu,hv p, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun i _=> hs i ) ( ht.intervalIntegrable .. )]; ring
lemma positiveR (h:Fits b F H): Dash b ℧ F H ( Early P F ):= lens (v:=fun _=>0) ℧ F h caress -- lower arg explicit
lemma subFit {U V: Glade G I}(h:Fits b F H)(hv:Fits b U V): Fits b (F-U) ( H-V ) := ⟨ fun i v hx=> ( h.stroll i v hx ).sub ( hv.stroll i v hx ), fun i u hh t=> ( h.pace i u hh t ).sub (hv.pace i u hh t) ⟩
end Fits
abbrev charge (R:W→ℕ)(s:Finset W):= ∑ i∈ s,R i
lemma toll_charge (R:W→ℕ){i:Finset W}(hi:i⊆ s): charge R i+charge R (s \ i)= charge R s:= by unfold charge; rw [add_comm]; exact Finset.sum_sdiff hi
-- generic 
lemma shines (K:Belt I){A:K.time→ℝ}(h:CourseK K.price 1 (plug L))(hx: Here true true K H ( rateS K 4 ))(hy:Here false true K F A)(hv:nn A): Here false false K ( expJ L H F ) A:= by
   apply Lease.sticks ( trunks h hx hy (fun _=>zero_le_one) (rateC _ _) hv ); intro s; unfold positive rateS; simp only [ Pi.one_apply, Pi.mul_apply, one_mul ]; rw [← mul_assoc, zpow_neg, show K.price.length s ^ (4:ℤ)= K.price.length s ^ (4:ℕ) from rfl,mul_inv_cancel₀ (pow_ne_zero _ ( K.price.pos s|>.ne' )),one_mul ]; -- hp cancel
lemma lighting (hs:Sheet (℧).price 1 (plug L))(hx:CoverSep P X)(hp:Here false true ℧ F (rateS ℧ n))(he:Here false true ℧ H ( rateS ℧ k )) : Bud P (n+k) 0 (regionC (fun _=>planeF) X L F H):= by
    intro j; obtain ⟨⟨C,hC,hT⟩,⟨a,ha,hA⟩⟩:= hx; refine Lease.sticks ( PulseQ (v:=fun i=>P.roots i.1) (A:=X ∘ Sigma.fst) hs hp he (fun _=>zero_le_one) ( rateC _ _ ) (rateC _ _ ) (fun _=>exp_pos _) (fun i=> hA i.1) (fun i=> le_trans ( le_of_eq ( near i ) ) ( exp_monotone ( authority i|>.2 ))) ⟨ C,hC,0,fun i=> by simpa only [Function.comp_apply,pow_zero,mul_one] using hT i.1⟩ ha j ) ?_; intro i; rw [dotzero, dotzero, roll, Pi.one_apply,one_mul, ← stock,zero_add, add_zero, Nat.zero_add]; -- dotzero hidden eta etc.
end YM.MS.Vane
