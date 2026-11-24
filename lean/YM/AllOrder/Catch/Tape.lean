import YM.AllOrder.Catch.Clouds
import YM.AllOrder.Laplace.Tilt
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Finset Topology Metric MeasureTheory
open PhysicalNext Repeat Lantern ConnectedActivityE6 Blaze Brush PositionX.Jet Laplace Laplace.SigmaP Tensor
open PertExtension.Series Radial
open scoped Topology Classical BigOperators ContDiff
variable {X Y ι:Type*}{V U W:X → Type}
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (U i)][∀ i,NormedSpace ℝ (U i)]
variable {T:Clock X} (p a b c:X→ℝ) {k j n:ℕ}{s B b₀:ℝ} (f:X→Word ℝ)
local notation "H"=> T.Meter
-- `progression` through a ray at time v. calibration B. all levels travel.From `k` onward charges x^-.5 orders.
def graded (u:ℕ):ℝ:=-(1/2:ℝ)*u
structure TaylorCap (T:Clock X)(k:ℕ)(b:X→ℝ)(u:X→ℝ)(a:X→ Word ℝ):Prop where
   steps (j:ℕ) (hj:j≤k): T.Meter (fun i=> a i j) 0
   stamps (j:ℕ) (hj:j≤k): T.Meter (fun i=> u i - delay (a i) j (b i)) (graded (j+1))
namespace TaylorCap
variable {p a b c f} {g:X→Word ℝ}
lemma const (T:Clock X)(hp:T.Meter a 0): TaylorCap T k b a (fun i=> just (a i)):= by
 refine ⟨fun j _=>?_, fun j _=>?_⟩; · cases j; exact hp; exact Clock.Meter.nil _ _
 exact (Clock.Meter.nil _ _).eq_mem (Eventually.of_forall (fun i=>(by simp [delay,just])))
lemma pair (h:TaylorCap T k b a f)(he:TaylorCap T k b c g): TaylorCap T k b (a+c) (f+g):= by
 constructor; · exact fun j hj=> (h.steps j hj).add (he.steps j hj)
 intro j hj; exact ((h.stamps j hj).add (he.stamps j hj)).eq_mem (Eventually.of_forall fun i=>by simp only [delay,Pi.add_apply,smul_add,sum_add_distrib]; abel)
lemma negate (h:TaylorCap T k b a f): TaylorCap T k b (-a) (-f):= ⟨fun j hj=> (h.steps j hj).neg, fun j hj=> (h.stamps j hj).neg.eq_mem (Eventually.of_forall fun i=>by simp [delay]; abel)⟩
lemma less (h:TaylorCap T k b a f)(he:TaylorCap T k b c g): TaylorCap T k b (a-c) (f-g):= by simpa only [sub_eq_add_neg] using h.pair he.negate
lemma lead (h:TaylorCap T k b a f): H (fun i=> a i-f i 0) (-(1/2)):=(by simpa [delay,graded] using h.stamps 0 (Nat.zero_le _))
lemma small (h:TaylorCap T k b a f): H a 0:= ((h.lead.weak (by norm_num : -(1/2:ℝ)≤0)).add (h.steps 0 (Nat.zero_le _))).eq_mem (Eventually.of_forall fun i=> sub_add_cancel ..)
lemma fit (h:TaylorCap T k b a f) (hc:a=ᶠ[T.rail] c)(he:∀ j≤k,∀ᶠ i in T.rail,f i j=g i j) : TaylorCap T k b c g := by
 refine ⟨fun j hj=>(h.steps j hj).eq_mem (he _ hj), fun j hj=> (h.stamps j hj).eq_mem ((hc.and ?_).mono fun i hi=> congr_arg₂ (·- ·) hi.1 hi.2)⟩
 change ∀ᶠ i in T.rail, delay (f i) j (b i)=delay (g i) j (b i); have hx:= eventually_all.mpr (show ∀ i:Fin (k+1),∀ᶠ x in T.rail,f x i.val=g x i.val from fun i=> he i.val (by have h:=i.isLt; omega)); exact hx.mono fun i hi=> Finset.sum_congr rfl (fun a ha=> congr_arg (_ • ·) (hi ⟨a,(by have h:= mem_range.mp ha; omega)⟩) ) -- fix
lemma repriced {U:Clock Y}(h:TaylorCap T k b a f)(u:Y→X)(he:T.Fare (U:=U) u): TaylorCap U k (b∘u) (a∘u) (f∘u):= ⟨fun j hj=> (h.steps j hj).pays u he,fun j hj=> (h.stamps j hj).pays u he⟩
lemma zoom (h:TaylorCap T k b a f)(he:j≤k):TaylorCap T j b a f:= ⟨fun r hr=> h.steps _ (hr.trans he), fun r hr=>h.stamps _ (hr.trans he)⟩
end TaylorCap
-- normJ for ℝ.Public. No η yet
lemma journal (f:ℝ→ℝ)(k:ℕ)(i:ℝ) : |someJ f k|≤ normJ k f 0 := by unfold someJ; rw [smul_eq_mul, abs_mul, abs_of_nonneg (by positivity),← Real.norm_eq_abs,← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; apply mul_le_of_le_one_left (norm_nonneg _); rw [inv_le_one₀ (by positivity)]; exact_mod_cast (Nat.factorial_pos k)
lemma cover_j {f:X→ ℝ→ℝ} (h:Cover T k s (fun _=>1) f (fun i=>0))(he:j≤k): H (fun i=> someJ (f i) j) s := fun e he'=> by filter_upwards [h e he'] with i hi; exact (journal _ _ 0).trans ((Brush.offer.1 hi).2 _ he)
lemma owns (f:ℝ→ℝ)(n:ℕ)(t:ℝ): delay (someJ f) n t= Work.G05.blockTaylor n f t:= by -- wrong namespace?
 unfold delay; rw [Work.G05.blockTaylor, Finset.sum_apply]; apply Finset.sum_congr rfl; intro j hj; change _= diagonal (Tensor.coeff f j 0) t; rw [show t=t • (1:ℝ) from (by simp), Tensor.homogeneous]; simp only [someJ, iteratedDeriv_eq_iteratedFDeriv, smul_eq_mul, mul_one]; rfl
-- book x=b.Office.Brush on all |x|≤b at exponent a (maybe negative permits).
variable {b} {f':X→ℝ→ℝ}{v:ℝ}
local notation "χ"=> (fun i=>Metric.closedBall (0:ℝ) (b i))
local notation "T₀"=> T.book (fun i=>Metric.closedBall (0:ℝ) (b i))
variable (h:T.Meter b v)(he:v < 0)(ht:∀ᶠ i in T.rail, 0<b i)
lemma ask (hf: Cover (V:=fun i=>ℝ) (U:=fun i=>ℝ) (T₀) k s (fun i=>1) (fun i=>f' i.1) (fun i=>i.2.1))(e:ℝ)(hS:s<e) : ∀ᶠ i in T.rail,∀ p:ℝ, p∈ Metric.closedBall 0 (b i)→ Brush k (T.cost i^e) 1 (f' i) p:= T.booked _ _|>.1 (hf e hS)
include ht
lemma tips (hf:Cover (V:=fun i=>ℝ) (U:=fun i=>ℝ) (T₀) k s (fun i=>1) (fun i=>f' i.1) (fun i=>i.2.1)): Cover T k s (fun i=>1) f' (fun i=>0):= fun e hE=> ((ask hf e hE).and ht).mono fun i hi=> hi.1 0 (mem_closedBall_self hi.2.le)
include h he ht
lemma prices_tape (hf:Cover (V:=fun i=>ℝ) (U:=fun i=>ℝ) (T₀) k s (fun i=>1) (fun i=>f' i.1) (fun i=>i.2.1))(hj:j<k): T.Meter (fun i=>f' i (b i)-delay (someJ (f' i)) j (b i)) (s+v*(j+1:ℕ)):= by
 intro e he'; obtain ⟨w,hw,hb⟩:= exists_between he'; let s':= w-v*(j+1:ℕ); have hh:s<s':=(by unfold s'; linarith); filter_upwards [ht,h.low he zero_lt_one,ask hf s' hh,((Clock.Meter.pale T s').mul (h.pow (j+1))) e (by unfold s'; linarith)] with i hi hx hp hm;
 have hz:∀ (j:ℝ),‖j‖ ≤ b i→ Brush k (T.cost i^s') 1 (f' i) j:= fun j hj=> hp j (mem_closedBall_zero_iff.mpr hj); have hW:= Local.Taylor.forecast hi (by linarith only [hx,le_abs_self (b i)]) (Nat.succ_le_of_lt hj) hz (x:=b i) (Real.norm_of_nonneg hi.le|>.le); rw [owns]; exact hW.bound.trans ((le_abs_self _).trans hm)
end YM.AllOrder.Catch
