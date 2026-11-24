import YM.MS.Rake.OPulse
/-!
# Low, mid, far univ clocks. Parameters may be path-indexed for opaque compact costs. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
-- subtraction scale η in native units, separation height θ.B. permit extra fixed costs via v.Basic.Later elegantly.
structure Geo (I:Type) where
    θ: I→ℝ
    η: I→ℝ
    room (i:I): 0≤ θ i
namespace Geo
variable (P:Geo I)
def sepLog (P:Geo I) := P.θ
def η0 (P:Geo I):= P.η
abbrev roots (P:Geo I)(i:I) := exp (P.θ i)
abbrev habitat (P:Geo I)(i:I) := 1+|P.η i|
def market (J:I→ Set ℝ)(p:Moments I ℝ): Scale (FrameT J):={
    length x:= exp (p x.1 x.2)
    pos x:=exp_pos _
    basic x:= habitat P x.1 * (1+|x.2.val|)
    one_le x:=one_le_mul_of_one_le_of_one_le (by simp [habitat]) (by simp) }
def solar (J:I→Set ℝ)(h:∀ i,MeasurableSet (J i))(p:Moments I ℝ): Belt I where
   slot:= J
   meas:= h
   price:= P.market J p
abbrev east (P:Geo I)(b:Bool) := solar P (fun _=> Set.Iic 0) (fun _=> measurableSet_Iic) (fun _ t=>if b then 0 else t) -- lattice true clamp negative
abbrev Gulf (P:Geo I):= solar P (fun i=>Set.Icc 0 (P.θ i)) (fun _=>measurableSet_Icc) (fun _=>id)
abbrev West (P:Geo I):= solar P (fun i=> Set.Ici (P.θ i)) (fun _=> measurableSet_Ici) (fun _=>id)
def birthTar (P: Geo I){K:Belt I} (k:ℕ)(p:K.time) := exp (tstart p)* (exp ( - P.θ p.1 ))^k
abbrev rateS (K:Belt I)(v:ℤ)(p:K.time):= K.price.length p ^ (-v:ℤ)
-- math walk.
lemma planWalk (J:I→Set ℝ)(h:∀ i,MeasurableSet (J i))(p:Moments I ℝ)(H:∀ i,Monotone (p i)): Walk ( solar P J h p ):= by
   constructor; · intro u v he hh; change exp ( p v.1 (tstart v) ) ≤ exp (p u.1 u.2); rw [← he]; exact exp_monotone ( H u.1 ( sub_nonneg.mp hh ) );
   intro u v he hi; change habitat P v.1 * (1+ |tstart v| ) ≤ habitat P u.1 * (1+|tstart u|) * (1+( tstart u- tstart v)); rw [← he,mul_assoc]; have hh: tstart u≥tstart v:= sub_nonneg.mp hi
   apply mul_le_mul_of_nonneg_left _ ( zero_le_one.trans ( show (1:ℝ)≤habitat P u.1 from by simp [habitat])); have hz : |tstart v|≤ |tstart u|+( tstart u-tstart v):= by nth_rw 1 [show tstart v=tstart u-(tstart u-tstart v) by abel]; apply le_trans ( abs_sub _ _ ); rw [abs_of_nonneg (sub_nonneg.mpr hh)]
   nlinarith [ abs_nonneg (tstart u)]
lemma ΒEast (b:Bool): Walk (east P b):= planWalk _ _ _ _ (fun i=>by intro x y hx; dsimp only; split; rfl; exact hx)
lemma εGulf : Walk (Gulf P):= planWalk _ _ _ _ fun _=> monotone_id
lemma εWest : Walk (West P):= planWalk _ _ _ _ (fun _=> monotone_id)
lemma born (G: Gauge)(b:Bool) : Birth G (east P b) (birthTar P):= by
   have he(k:ℕ){J:Belt I}:nn (birthTar (K:=J) P k):=by intro p; unfold birthTar; positivity
   refine ⟨fun k=>he _,ΒEast P b, (fun i=>rfl),fun i=>?_⟩; apply breakWalk (ΒEast ..) _ zero_lt_one; refine ⟨he _,1,zero_lt_one,?_⟩; intro p q hp hv; unfold birthTar; rw [show P.θ q.fst=P.θ p.fst from congr_arg P.θ hp.symm]; apply le_of_eq; rw [one_mul,← mul_assoc,← Real.exp_add,show ( -1*δf p q+tstart p )=tstart q from (by unfold tstart δf; ring)] -- order? RHS tstart p yes
end Geo
-- constructors.Recount.Budget
variable (P:Geo I) (G I)
end YM.MS.Rake
