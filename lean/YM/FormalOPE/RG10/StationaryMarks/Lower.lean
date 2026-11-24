import YM.FormalOPE.RG10.StationaryMarks.Asympt
import YM.PertExtension.PTBills
/-!
 # radial vanishing prior to stationary truncation
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Inherit Push.Loops Chart Lattice RG
open Series.Tested
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{I:Type}[Fintype I]
local notation "μ"=>physical G I
local notation "ν"=>tangent G I
local notation "E"=>Direction G I
variable {P:ChartRatio G}{A O:Spending G I} (L:LocalRatio P)

-- reusable orders. suppress poly shifts only after computing the full product.
abbrev Waits (l:ℕ)(O:Spending G I):= RadialOrder l (O ∘ expLinks G I)
lemma waits_no (hf:Curtain O): Waits 0 O:= fun u=> (directions hf.germ u).bounded
lemma waits_high (C:Component A) : Waits 2 A:= by
 intro u; let f:= A ∘ expLinks G I
 have hi:= directions C.centered.smooth u 1
 have he: peval (fun j=> jet f j u) 1=0:= by ext1 i; simp [peval, Zone.eval, Finset.sum_range_succ, C.centered.base1 u,f,C.center]
 rwa [he,sub_zero] at hi
lemma waits_mul {f g:Spending G I}{i j:ℕ}(hf:Waits i f)(hg:Waits j g): Waits (i+j) (f*g):= fun u=> bill_mul (hf u) (hg u)
lemma waits_cargo {n l:ℕ} (c : Fin n→Spending G I) (h:∀ i:Fin n,Waits l (c i)): Waits (l*n) (∏ i,c i):= by
 intro u; let k (i:Fin n)(t:ℝ):= (c i ∘ expLinks G I) (t • u); have hu:= bill_product (Finset.univ) (fun _:Fin n=> l) k (fun i _=>h i u)
 rw [show ∑ _:Fin n,l=l*n by simp [mul_comm]] at hu
 convert hu using 1 <;> try rfl
 funext t; simp [k,Finset.prod_apply]
include L in
lemma tired {l j:ℕ}(hf:Curtain O)(hw:Waits l O)(hk:j<l)(u:E): jet (offer P O) j u=0:= by
 have hJ:= (Ratio.jacobian_smooth L (U:=I)).of_le le_top (m:=∞)
 have he:= bill_mul ((directions hJ u).bounded) (hw u); rw [zero_add] at he
 exact (directions (hJ.mul hf.germ) u).vanish he hk
include L in
lemma lower (A:Spending G I){l j:ℕ}(hf:Curtain O)(hw:Waits l O)(hk:j<l): summing P A O j=0:= by
 have he (u:E): normTerm (offer P O) (A∘ expLinks G I) j u=0:= by
  have hu: integrandSeries (A ∘ expLinks G I) (offer P O) j u=0:= by
    unfold integrandSeries Zone.mul; refine Finset.sum_eq_zero fun p hp=>?_
    change jet (offer P O) _ u * _=0; rw [tired L hf hw (lt_of_le_of_lt _ hk),zero_mul]; exact p.fst.le_add_right _ |>.trans_eq (Finset.mem_antidiagonal.mp hp)
  unfold normTerm; rw [hu,zero_mul]
 unfold summing Radial.moment; simp_rw [he]; exact integral_zero _ _
end YM.FormalOPE.RG10.StationaryMarks
