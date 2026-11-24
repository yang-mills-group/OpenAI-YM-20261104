import YM.Qlocal.Feud.Baker
/-!
 # Budget on Θ model letters, both projection & rain.Model.Ar.
 All fields / pose.Real direction.Ph.Any period.Audition all.Field.
 Uses Militia at both sides.Shape.View support rooted costs retained.
 Also future reconstruction. Keep true unwrapped path deflator.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Feud
open Function Filter Lattice Laurent RG Wilson Stationary Metric
open Marker Multi Finset
open Push Uniform
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze ConnectedActivityE6 AnalyticBridge Quipu Quipu.Sonnet
variable {V:Type}[DecidableEq V] {ι E:Type} {G:Gauge}{k n j r i z m w:ℕ} {c:Side} {d t a b v u C φ g:ℝ}{R:Census V}
namespace Cider
open Album Vase
variable (s:Senses R) (A:Tale R G) (p:A.Decision) (h: A.Allows (a+b) C) (he:∀ (i:Fin (A.depth+1)) (r:Fin ((i:ℕ)+A.boom s+1)) (j:ℕ), p s i r j→ w ≤ (A.array s i r j).momentum) -- coercion i:Nat inferred?
  (ha:0<a)(hb:0≤b)
-- avoid binder r: implicit i wrong.Make explicip.
set_option quotPrecheck false
variable (o:V→Site c)(W:Config G c)
local notation "X"=> o (Sonnet.root s)
local notation "I"=> Fin (A.depth+1)
local notation "J" i=> Fin (Fin.val i+Lagger.dues A.power s.val+1)
local notation "D"=> nod b w
local notation "Ya"=> A.markℓ p o s
local notation "P[" i "," r "]"=>Tale.playing A p o s i r
-- Price shape.Basis.N.Effect, weights chosen BEFORE Θ arrays. includes Rank0.
noncomputable def allowance (G:Gauge)(j method height boom:ℕ)(a d:ℝ) : ℝ:= ∑ i: Fin (height+1),∑ r:Fin (i.val+boom+1), (1+ (2^j:ℝ)*(2^j:ℝ)^(i.val+boom-r.val)*capita G r method j d a+ ticketC G method r.val)
lemma solvable (G:Gauge)(j t n r:ℕ)(ha:0<a)(hd:0≤d): 0 ≤ allowance G j t n r a d:= by
 unfold allowance; refine sum_nonneg fun i _ => sum_nonneg fun r _=> ?_; have he:= ticketC_pos G t r.val; have hp:= capita_ge G r.val t j hd ha; positivity
local notation "u0"=> allowance G j A.method A.depth (A.boom s) a d
local notation "mulL"=> ℝ -- alias unused
include h he ha hb
-- c>0 nonnegative from h.Summable.The V.Tensor Health.
lemma safe : 0 ≤ C:= (h.pay s 0 0).2.2 |> le_trans (tsum_nonneg (h.pay s 0 0).1) -- explicit.Tactic
-- P scope ALL.Even absolute probe group.
lemma income (hd:0≤d)(hh:‖t‖≤1) : ‖Ya t W‖ ≤ u0*(D*C):= by
 have hv(i:I)(r:J i): ‖A.playing p o s i r W‖ ≤ ticketC G A.method r.val * D * C:= by
    apply faithful _ (A.array s i r) (h.pay ..) (fun j hj=> he i r j hj.1) ha hb (X) W A.method
 let M:= D*C; have hM:0≤M:=mul_nonneg (Real.exp_nonneg _) (safe s A p h he ha hb)
 unfold Tale.markℓ allowance; rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>?_)); rw [Finset.sum_mul]; apply (norm_sum_le ..).trans (Finset.sum_le_sum (fun r _=>?_)); rw [norm_mul,norm_pow]; have hh':=hv i r
 apply (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hh)).trans; apply hh'.trans
 rw [mul_assoc (ticketC ..)]; change ticketC G A.method r.val * M≤ _*M; apply mul_le_mul_of_nonneg_right _ hM; refine le_add_of_nonneg_left (?_); have he':= capita_ge G r.val A.method j hd ha; positivity
-- rank positive.N.H
variable [NormedAddCommGroup E][NormedSpace ℝ E] {x:E} (T:E→ Config G c) (hT:Weather T x)
variable (v0:E→ℝ)(hz:Mode T x j d)(hm: Allows j v0 x 1)
omit h he ha hb in
lemma tower (t:ℕ)(hm:Allows j v0 x 1): Allows j (v0^t) x ((2^j:ℝ)^t):= by
 induction t with
 | zero=> rw [pow_zero,pow_zero]; exact allows_const x (v:=(1:ℝ)) norm_one.le
 | succ i ih=> rw [pow_succ,pow_succ']; refine (Allows.bilinear (ContinuousLinearMap.mul ℝ ℝ) ih hm (ContinuousLinearMap.opNorm_mul_le ..)).mono ?_; rw [mul_one,mul_one] -- defeq Pi.mul
include hT hz hm
lemma life : Allows j (fun x=>Ya (v0 x) (T x)) x (u0*(D*C)) := by
 let d₀:= A.method; let Z i r:= A.array s i r; let v(i:I)(r:J i):= A.playing p o s i r; let M:=D*C; have hM:0≤M:=mul_nonneg (Real.exp_nonneg _) (safe s A p h he ha hb)
 have hv (i:I)(r:J i): Allows j (v i r ∘ T) x (capita G r d₀ j d a *D*C):= upper _ (Z i r) (h.pay ..) (fun j hj=> he i r j hj.1) ha hb (X) hz hT _
 unfold allowance Tale.markℓ; rw [Finset.sum_mul]; apply allows_sum; intro i _; rw [Finset.sum_mul]; apply allows_sum; intro r _; let f:=(v0 ^ A.stampE s i r); let n:= ((2^j:ℝ)^A.stampE s i r); apply (Allows.bilinear (f:=f) (ContinuousLinearMap.mul ℝ ℝ) (tower v0 _ hm) (hv i r) (ContinuousLinearMap.opNorm_mul_le ..)).mono; let L:=capita G r d₀ j d a
 change 2^j*(1:ℝ)*n*(L*D*C)≤ (1 + (2^j:ℝ)*n*L+ ticketC G d₀ r.val)*M; rw [mul_one,mul_assoc L, ←mul_assoc]; apply mul_le_mul_of_nonneg_right _ hM; linarith only [ticketC_pos G d₀ r.val]
-- use `rent` to buy Beauty estimates.Domain architecture.Motion.Price.FormalSupport.
end Cider
end YM.Qlocal.Feud
