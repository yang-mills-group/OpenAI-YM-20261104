import YM.AllOrder.Floe.Cascade
import YM.AllOrder.Floe.Lucent
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
namespace Pace
/-! Unit two normalization law. Before re-stepping q. Note forward rather than inverse series chosen: evaluate fitted output g' coefficients := f(g) kernels to pay at the input coupling g.] -/
abbrev Coin := ℕ→ℝ -- array Ω, corrections to g^-2; index e, begins at 2
abbrev Earn (q:Coin)(α:ℝ):= q 0=0 ∧ q 1=0 ∧ q 2=α
variable {q d:Coin}{L:ℝ→ℝ}
def ladder (t:ℝ)(q:Coin):Tape:= PositionX.Jet.ren q (someJ (fun x:ℝ=> (1+x)^t))
-- prefactor power with step ratio; legal when g=b at input. q includes all orders.N finite jets computed coefficient wise.
def elapsed (i:Age):ℝ:= (i.r-i.e:ℝ) /2
def rhythm (p:ℝ)(t:ℝ):ℝ:= p*(1+t)^(-(1/2:ℝ))
def cap (i:Age)(p u:ℝ):= (1+u)^ (elapsed i)*Plateau.ratioW p i.e i.r
lemma nice (v:ℝ): ContDiffAt ℝ ω (fun x:ℝ=> (1+x)^v) 0:= ContDiffAt.rpow_const_of_ne (contDiffAt_const.add contDiffAt_id) (by change 1+(0:ℝ) ≠0; simp)
lemma coin_word (t:ℝ)(h:Act k L q)(hp:q 0=0):Act k (fun x=> (1+L x)^t) (ladder t q):= h.dial (eo_Act k (nice t)) hp -- n is Side! use k.
lemma start (t:ℝ)(h:q 0=0): ladder t q 0=1:= (ren_light h _).trans (by simp)
lemma next (t:ℝ)(h:q 0=0)(hp:q 1=0): ladder t q 1=0:= (PositionX.Jet.tip h _).trans (by rw [hp,zero_smul])
lemma synch (h:∀ i≤k,q i=d i) (t:ℝ): fitto (ladder t q) (ladder t d) k:= price_p (fun _ _=>rfl) h
lemma rhythmic (i:Age)(p u:ℝ)(hp:0<p)(hu:0<1+u): Plateau.ratioW (rhythm p u) i.e i.r=cap i p u:= by
 let r:=i.r; let e:=i.e; let x:= (1+u); have hx:0<x:= hu; change (p*x^(-(1/2:ℝ)))^e * ((p*x^(-(1/2:ℝ)))^r)⁻¹= x^((r-e:ℝ)/2) * (p^e*(p^r)⁻¹);
 have h0 (k:ℕ) : (p*x^(-(1/2:ℝ)))^k=p^k * x^((-(1/2:ℝ))*k):= by rw [mul_pow,Real.rpow_mul_natCast hx.le]
 rw [h0,h0,_root_.mul_inv_rev,← Real.rpow_neg hx.le]; -- converse multiplication
 have hv : ∀ a b:ℝ,x^a*x^b=x^(a+b):= fun a b=> (Real.rpow_add hx ..).symm
 have ht : x^ ((r-e:ℝ)/2)= x^ (-(1/2:ℝ)*e)*x^ (-(-(1/2:ℝ)*r)):= by rw [hv,show -(1/2:ℝ)*e+-(-(1/2:ℝ)*r)=_ from (show _=(r-e:ℝ)/2 from (by ring))]
 rw [ht]; ring
-- polynomial earnings on ladder via ordinary Faà di Bruno, fixed `k*l` power. no period.Credit
variable {ι:Type}{q:ι → Coin}{α:Type*} {U:Finset α}{f g:ι→ℝ}{L:ι→ℝ}
abbrev Cost (Γ:ι→ℝ)(k:ℕ)(C:ι→ℝ):Prop:= CreditF Γ k fun i=> |C i|
namespace Cost
variable {u:ι→ℝ}
lemma fixed (v:ℝ):Cost L k (fun _=>v):=(freeC _ (abs_nonneg _)).up (Nat.zero_le _)
lemma plus (h:Cost L k f)(hh:Cost L k g): Cost L k (fun i=> f i+g i):= (h.add hh).down (fun _=>abs_add_le ..) (fun _=> abs_nonneg _)
lemma neg (h:Cost L k f): Cost L k (fun i=> -f i):= by unfold Cost; simp_rw [abs_neg]; exact h
lemma minus (h:Cost L k f)(hh:Cost L k g):Cost L k (fun i=> f i-g i):= by simp_rw [sub_eq_add_neg]; exact plus h (neg hh)
lemma mul (h:Cost L k f)(hh:Cost L j g): Cost L (k+j) (fun i=> f i*g i):= by unfold Cost; simp only [abs_mul]; exact CreditF.mul h hh
lemma sum {f:α→ι→ℝ}(h:∀ i∈U,Cost L k (f i)): Cost L k (fun x=>∑ i∈U,f i x):=(CreditF.sum _ h).down (fun i=> Finset.abs_sum_le_sum_abs ..) fun _=> abs_nonneg _
lemma prod {f:α→ι→ℝ}(h:∀ i∈U,Cost L k (f i)): Cost L (k*U.card) (fun x=>∏ i∈U,f i x):=by
 induction U using Finset.induction_on with
 | empty=> simpa using Cost.fixed (L:=L) (k:=0) 1
 | insert i S ht ih=> simp only [card_insert_of_notMem ht, prod_insert ht, Nat.mul_add,Nat.mul_one]; rw [Nat.add_comm]; exact Cost.mul (h i (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma up (h:Cost L k f)(he:k≤j): Cost L j f:=CreditF.up h he
lemma transfer (h:∀ p≤j,Cost L k (fun i=>q i p)) (t:ℝ): Cost L (k*j) (fun i=> ladder t (q i) j):= by
 unfold ladder PositionX.Jet.ren PositionX.Jet.order; simp_rw [smul_eq_mul]; let A:=someJ (fun x:ℝ=> (1+x)^t);
 apply Cost.up (j:=k*j) (Cost.mul (Cost.fixed (k:=0) ((j.factorial:ℝ))⁻¹) ?h)
 case h=>
    refine (show Cost L (k*j) (fun i=> (∑ p:OrderedFinpartition j,(∏ n, ((p.partSize n).factorial:ℝ) * (q i) (p.partSize n)) * ((p.length.factorial:ℝ) * A p.length))) from ?_)
    apply Cost.sum; intro p _; refine (Cost.mul (k:=k*p.length) (Cost.up (Cost.prod (k:=k) (fun i _=> (Cost.up (j:=k) (Cost.mul (k:=0) (Cost.fixed _) (h _ (p.partSize_le i))) (by omega)))) (by rw [card_univ,Fintype.card_fin])) (Cost.fixed (k:=0) _)).up (by simpa using Nat.mul_le_mul_left k p.length_le)
 omega
end Cost
end Pace
end YM.AllOrder.Floe
