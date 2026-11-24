import YM.AllOrder.Wheel.Estate
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Wheel
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Catch Catch.Clock Floe StateE Pace Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{L n f : Side}{ι:Type*}{T:Clock ι} {K:KernelChoices}{P:Patch}{σ C b a D η κ:ℝ}{k l p j M:ℕ}
-- general (any heights finite). For Phys bill carries ωalt stamp.Lift consumer.
open ConnectedActivityE6.Coat
variable (N:ℕ)
abbrev wag (Γ:Coin)(k:ℕ)(β:ℝ):= delay Γ k (gStep β) -- full powers starts Ω2
abbrev now (Γ:Coin)(k:ℕ)(β:ℝ):= β*(1+ wag Γ k β)
variable (γ:ι→ℝ)
structure Epoch (T:Clock ι)(b:ι→ℝ):Prop where
  one : ∀ᶠ i in T.rail,0 < b i
  price : T.Meter b 1
  stepI : T.Meter (fun i=> gStep (b i)) (-(1/2))
  starts : T.Meter (fun i=> (gStep (b i))⁻¹) (1/2)
namespace Epoch
variable {b:ι→ℝ}
lemma orbit (h:Epoch T b) {Y:Type*}(u:Y→ι)(P:Clock Y)(hp:T.Fare (U:=P) u): Epoch P (b ∘ u):= ⟨hp.tends.eventually h.one,h.price.pays _ hp, h.stepI.pays _ hp,h.starts.pays _ hp⟩
lemma hours(h:Epoch T b)(x:Age): T.Meter (fun i=> ratioW (gStep (b i)) x.e x.r) (graded x.e+x.r/2) := by unfold ratioW; simp only [←inv_pow]; exact ((h.stepI.pow x.e).mul (h.starts.pow x.r)).weak (by unfold graded; linarith)
end Epoch
variable {b:ι→ℝ}(h:Epoch T b)
structure Hall (T:Clock ι)(k:ℕ)(b:ι→ℝ)(Q:ι→ Coin) :Prop where
 tune : Epoch T b
 fee :∀ i≤k,T.Meter (fun j=> Q j i) 0
 mild : ∀ᶠ i in T.rail,Q i 0=0∧Q i 1=0
namespace Hall
-- Holds up prediction projected δ & median.SHIFT prop. Use exact δ at actual AFTER rounding.Reader. For real comparison full Lease needs projector fee budget only after L.Le.
variable {Q:ι→ Coin}(hQ:Hall T k b Q)
local notation "b'"=> (fun i=> gStep (b i))
local notation "f"=> (fun i=> wag (Q i) k (b i))
local notation "A"=> (fun i=> now (Q i) k (b i))
local notation "H"=>T.Meter
include hQ
lemma logic : TaylorCap T k (b') f Q :=by
 refine ⟨hQ.fee,fun j hj=>?_⟩; unfold wag delay; let u:=range (k+1); let t:=range (j+1); let V v i:= b' i^v*Q i v; rw [show (fun i:ι=>_)= fun i=> ∑ k∈u\t, V k i from ?_]; -- placeholders
 · apply Clock.Meter.sum; intro i hi; rcases (Finset.mem_sdiff.mp hi) with ⟨ht,hx⟩; unfold u at ht; unfold t at hx; simp only [mem_range,not_lt] at ht hx; exact ((hQ.tune.stepI.pow i).mul (hQ.fee i (by omega))).weak (by unfold graded; have ht:=Nat.cast_le (α:=ℝ)|>.mpr hx; linarith)
 funext i; exact Eq.symm (eq_sub_of_add_eq (sum_sdiff («f»:=fun j=>V j i) (s₁:=t) (s₂:=u) (range_mono (by omega)))) -- `sum_sdiff` nat? syntax
lemma approaches : Tendsto f T.rail (𝓝 0):= (logic hQ).tends (tendsto_const_nhds.congr' (hQ.mild.mono fun _ hi=> hi.1.symm))
lemma born : ∀ᶠ i in T.rail,0 < 1 +f i ∧0<A i:= ( ((approaches hQ).eventually (lt_mem_nhds (by norm_num : -(1:ℝ)<0))).and hQ.tune.one).mono fun i hi=> by
 let v:= wag (Q i) k (b i); have ht : -1< v:= hi.1; have hv:0<1+v:=(by linarith); exact ⟨hv,mul_pos hi.2 hv⟩
lemma cellar (v:Age): TaylorCap T k b' (fun i=>(1+f i)^ elapsed v) (fun i=> Pace.ladder (elapsed v) (Q i)):= by
 let F (x:ℝ):=(1+x)^(elapsed v); let hL:ContDiffAt ℝ ω F 0:= Pace.nice _; let hp := TaylorCap.process F hL (logic hQ) (tendsto_const_nhds.congr' (hQ.mild.mono fun _ hi=> hi.1.symm)) hQ.tune.stepI (hQ.tune.one.mono fun _ hi=> Fare.gS _ hi|>.1); refine hp.fit (EventuallyEq.refl ..) (fun j hj=> hQ.mild.mono fun i hi=>?_); let hh:= Act.swell (Q i) hj
 exact (hh.transit (hi.1.symm ▸ hL)).trans_at (coin_word (elapsed v) hh hi.1) le_rfl
omit hQ in
lemma bubble {x:ℝ}(h:0<x) (v:ℝ)(hi:0<1+v): gStep (x*(1+v))= rhythm (gStep x) v:= by
 rw [gStep, Real.sqrt_mul h.le,_root_.mul_inv_rev]; unfold gStep rhythm; rw [Real.rpow_neg hi.le,← Real.sqrt_eq_rpow]; exact mul_comm ..
lemma tissue (v:Age): ∀ᶠ i in T.rail, ratioW (gStep (A i)) v.e v.r= (1+f i)^(elapsed v)* ratioW (b' i) v.e v.r:= by
 filter_upwards [hQ.tune.one,born hQ] with i hi h; unfold now; rw [bubble hi _ h.1]; apply Pace.rhythmic _ _ _ (gS _ hi|>.1) h.1
-- tailPre T cost δprojection.Serv.Need near threshold quiet.Occ.
lemma price_d (hj:l ≤ k) : H (fun i=> wag (Q i) k (b i)-delay (Q i) l (b' i)) (graded (l+1)):= (logic hQ).stamps l hj
-- Full magnitude & Δ if k=2+N
lemma fee_d (hK:2≤k): H (fun i=> now (Q i) k (b i) - b i - Q i 2) (-(1/2:ℝ)):= by
 let Q' i:= delay (Q i) 2 (b' i); refine (((hQ.tune.price).mul (price_d hQ hK)).weak (by norm_num [graded])).eq_mem ?_; filter_upwards [hQ.tune.one,hQ.mild] with i hi hx; have ht:Q' i=(b' i)^2*Q i 2:= (by unfold Q' delay; rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]; simp [hx.1,hx.2]); change b i * (f i - Q' i)= _; rw [ht]; change _= b i* (1+ f i)-_ - _; have h:= Fare.gS _ hi|>.2; linear_combination -(Q i 2) * h
end Hall
end YM.AllOrder.Wheel
