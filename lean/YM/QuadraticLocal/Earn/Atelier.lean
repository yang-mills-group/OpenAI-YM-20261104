import YM.QuadraticLocal.Earn.Crowd
/-!
 ## Window lenses: seeing all orientations now
 Hor costs across engagement h_ij. For paying analytic Handoff credit
 and old curriculum residuals. Need a rendering survey first; compare
 root location THETA P of each sanctioned club. Never bind poly products
 across arbitrary unions.Our costs are joint hit sanctions per intended
 polynomial load. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Earn.Club RemainderComparison
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e σ r b :ℝ} {k u i' j h : ℕ}
variable (X:ι→ Row P R G α) (q:Ratio c n) (w:V→ℝ) (hw:∀ i,0<w i)
namespace Accumulate
local notation "C"=> (Club X)
set_option quotPrecheck false
local notation "L"=> q.count.val
local notation "Δ"=> (1/2:ℝ)
def spade (ε:ℝ)(L':Side)(r:ℕ):ℝ:= ((81*(L'.val:ℝ)^4+1)^r * Real.exp 1 * ((ε/2)⁻¹^(4*r) * (4*r).factorial * Real.exp (ε/2)))
def sink (ε:ℝ)(L':Side)(r:ℕ):ℝ:= spade ε L' r* (1-Real.exp (-(ε/2)))⁻¹
local notation "Lx"=> ((q.count.val:ℝ)^4)
local notation "φ"=> rootPrice X w σ
local notation "Θ"=> fun x=> Club.roof X x q
local notation "ψ"=> fun x=> Club.reach X x q
local notation "A"=> fun i=> Breeze.areaBudget i k Lx
-- poly inequality
local notation "ℓ"=> ((g/2)⁻¹^(4*k) * (4*k).factorial * Real.exp (g/2))
variable (hg:0<g) (k)
include hg
lemma shovel (Lb:Side)(k:ℕ) : 0 < spade g Lb k:=by unfold spade; positivity -- notation L captures
lemma sinking (L':Side)(k:ℕ): 0<sink g L' k:= by have he:= shovel hg L' k; have hh: 0<1-Real.exp (-(g/2)):= sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)); exact mul_pos he (inv_pos.mpr hh)
lemma paid_poly (i:ℕ): (Real.exp (-g*i)* A i) ≤ spade g q.count k * (Real.exp (-(g/2)))^i :=by
    let a:=Real.exp (-(g/2)); let b:=A i; let s:ℝ:=1+(i:ℝ); let t:= Lx; let v:=81*t+1; have ht:0≤t:=by unfold t; positivity
    have hi:1≤ s:=le_add_of_nonneg_right (Nat.cast_nonneg _);
    have hp: ((ballCost i):ℝ) ≤ (81:ℝ) * s^4:= by
      unfold s ballCost; push_cast; calc
       _ ≤ (3*(1+(i:ℝ)))^4:= pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) i]) _
       _ = _:= by ring
    have hϵ:=Real.exp_pos (-g*i); have hv:0<v:= by unfold v; positivity
    have he: A i ≤ (s^(4*k)*v^k)*Real.exp 1:= by
       unfold Breeze.areaBudget; rw [pow_mul s,← mul_pow]; refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (?_: ((ballCost i):ℝ)*t+1 ≤ s^4*v) _) (Real.exp_nonneg _)
       unfold v; nlinarith only [one_le_pow₀ (n:=4) hi, mul_le_mul_of_nonneg_right hp ht]
    apply le_trans (mul_le_mul_of_nonneg_left he hϵ.le)
    calc
       Real.exp (-g*i) * (s^(4*k)*v^k*Real.exp 1) ≤ Real.exp (-g*i) * ((ℓ) * Real.exp ((g/2)*i) * v^k* Real.exp 1):= by
         gcongr; exact polynomial_cost (half_pos hg) (Nat.cast_nonneg i) _
       _ = (ℓ)* v^k * Real.exp 1*(Real.exp ((g/2)*i)*Real.exp (-g*i)):=by ring
       _ = _:= by rw [← Real.exp_add,← Real.exp_nat_mul]; rw [show g/2*(i:ℝ) + -g*(i:ℝ)= ↑i* -(g/2) from (by ring)]; unfold spade v t; ring
omit hg
variable (hp:Offers X w σ b)
variable (hb:b≤1) (hk:∀ t: Club X,t.val.card ≤ k)
include hw hp hb hk
lemma total (v:Site c) (hg:0<g): SumBudget (fun F:C=> if Θ F=v then Real.exp (-g*(ψ F:ℝ)) * rootPrice X w σ F else 0) (b*sink g q.count k):=by
 let y:= sink g q.count k; let a:= Real.exp (-(g/2)); let U:=spade g q.count k; have hx:0≤b:= budget_nonneg (hp 0)
 rw [show b*sink g q.count k=(b*U)*(1-a)⁻¹ from (mul_assoc ..).symm]; let k' := b*y; let f (F:C):= if (Θ F)=v then (Real.exp (-g* (ψ F:ℝ)))* rootPrice X w σ F else 0
 refine budget_degrees ψ ?_ (mul_nonneg hx (shovel hg ..).le) (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith : -(g/2)<0)) ?_
 · intro i; split; exact mul_nonneg (Real.exp_nonneg _) (active X w hw ..).le; exact le_rfl
 intro d S hS; let x:=Real.exp (-g*(d:ℝ)); let p(F:C):= if closer X q F v d then rootPrice X w σ F else 0;
 change ∑ C₁ ∈ S, _ ≤ _
 have he:= sum_congr (s₁:= S) (f:=f) rfl (g:=fun F=>x*p F) (fun F (hi:F∈S)=> by
    unfold f p; split_ifs with h hq hq
    next=> dsimp only; rw [hS F hi]
    next=> exact (hq ⟨(hS F hi).le,h⟩).elim
    next=> exact (h (hq.2)).elim
    next=> exact (mul_zero _).symm) -- parser
 refine he.trans_le ((budget_sum (budget_scale (Real.exp_pos (-g*(d:ℝ))).le (inside k X q w hw hp hb hk d v)) S).trans ?_)
 change x*(b* A d) ≤ (b*U)*a^d; rw[mul_left_comm,mul_assoc]; exact mul_le_mul_of_nonneg_left (paid_poly k q hg d) hx
-- maybe inside has k first?
end Accumulate
end YM.QuadraticLocal.Earn
