import YM.AllOrder.Floe.Campus
import YM.AllOrder.Till.Coherence
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Till
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function Matrix
open Extra.Iteration Push.AbsoluteSums Plateau
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {k w:ℕ} {n : Side}
local notation "T" => RG.Atom G k
open AnalyticBridge VerifiedReset Next.Scheduling
open Floe StateE
variable {p:BudgetPoint}{u:Site n} {X:Support n}{C B:ℝ}
open Floe StateE Pace Step.PlanV
variable (A:Layout G) (u:Age→ℝ) (X:Finset Age) (w:ℕ)
-- total render.Envelope assigned at β'. Offer kernel via Label. Sym.H.Sum.Real.Local Kit cost. Conserve actual orientation.X.
namespace Tilt
def sundry(u:Age→ℝ)(X:Finset Age)(n:Side)(o:Site n):=∑ i∈X,u i • print (A i) w n o
abbrev rates (t:ℝ) (i:Age):= ratioW t i.e i.r
abbrev patch (G:Gauge)(w:ℕ)(n:Side)(o:Site n)(X:Finset Age)(A:Layout G)(t:ℝ):= sundry A w (rates t) X n o
local notation "S"=> sundry A w u X
lemma regional : gardenfold w (S):= by intro n m i j U V h; unfold sundry; simp only [Finset.sum_apply,Pi.smul_apply]; exact sum_congr rfl (fun k hk=> congr_arg (u k • ·) (print_out (A k) w n m i j U V h)) -- type.. syntax
lemma signed (n:Side) : PhysicalNext.Repeat.Trio.Mirrors (S n):= by intro x s b U; unfold sundry; simp only [Finset.sum_apply,Pi.smul_apply]; exact Finset.sum_congr rfl (fun i hi=> congr_arg (u i • ·) (signs (A i) w n ..))
-- Price cap at Γf and ν, ticket. complete supports.Omega.
abbrev price (A:BudgetPoint)(G:Gauge)(k:ℕ)(w:ℕ)(x g:ℝ)(X:Finset Age):ℝ:=∑ i∈X,|rates g i| *bill G A w i.r (authority k i x)
abbrev priceAt (G:Gauge)(k:ℕ)(P d r:ℕ)(w t x g:ℝ)(X:Finset Age):ℝ:=∑ i∈X,|rates g i| * (Push.Local.turnCost P d*(authority k i x*(Wages.startup G i.r d P*t^i.r*(1+w)^Wages.grade i.r d P))) -- r redundant.next real lflag.
lemma sameprice (V:BudgetPoint) (G:Gauge)(k:ℕ)(w:ℕ)(x η:ℝ) : price V G k w x η X = priceAt G k V.order V.power 0 w V.threshold x η X:=rfl
section ask
variable (P : Step.Fees) (hp:∀ i,0<P i) {C: Age→ℝ}{x:ℝ}
    (ht:∀ i ∈ X, Quoted (A i) (P i) (authority k i x)) (hB : ∀ i∈X, 4*i.r ≤ w)
local notation "Fη"=> fun n o=> Fairness p o (court o w)
include ht
lemma paint (g:G.Simple)(η:ℝ)(n:Side)(h:4≤n.val)(i:Site n)(p:BudgetPoint) (hp:∀ i,0<P i) (hv:∀ i∈X,4*i.r≤w): Fairness p i (court i w) (Tilt.patch G w n i X A η) (price p G k w x η X) := Fairness.enroll X (fun v hv'=>(fair (A v) p i w (ht v hv') (hp v) (hv v hv') (by unfold Age.r; omega) h g).scale (rates η v)) -- include ht
end ask
variable (h:∀ i∈X,4*i.r≤w)
include h
lemma emit (n:Side)(U:Config G n) : ∑ x,S n x U=∑ i∈X,u i*Extra.Iteration.action (legible (A i) w) U:= by unfold sundry; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; rw [sum_comm]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [← mul_sum,reads (A i) U w (h i hi)] -- arguments
lemma sunset (v:ℝ)(hv:0<v)(β:ℝ)(hQ:v^2*β=1)(U:Config G n): β*∑ i∈X, v^i.stamp*Extra.Iteration.action (legible (A i) w) U=∑ x,Tilt.patch G w n x X A v U := by
 rw [emit A (rates v) X w h]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; unfold rates ratioW; have hz:= i.recovery
 have he : v^2*v^i.e=v^i.stamp*v^i.r:= by rw [← pow_add,← pow_add,← hz,Nat.add_comm 2]
 field_simp; let V:=Extra.Iteration.action (legible (A i) w) U; change _*_*V*_ = V*_; linear_combination - β * V * he + V*v^i.e * hQ
end Tilt
end YM.AllOrder.Till
