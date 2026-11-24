import YM.Comparison.RG02.Sky.Flux
/-!
# Summable cover rooted contraction and its period shadow; winding paid

 Through every stipulated finite-degree connected diagram. Read vacuum diagrams per cell, before
 doing sums over root locations. Use the normalized connected coefficient with log convention (if reading on full
 moment after the log, use Marker exponential & `Order.value` etc). `Wires` primitive hypotheses
 for the cover comparison (formal supplier), not claiming all period Step inputs come from covers
 with these prices. In applying a termwise tensor input estimate to a `Wires`, supply pricing at
 TRUE cover distances. Output torus anchoring estimates can use `taxi` from Ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Sky
open Function Filter Lattice RG Push.AbsoluteSums
open Flux (push push_if Abs)
open scoped Classical Topology BigOperators

namespace Net
variable {F : Type*} {D : F→ Type*} {P : Type*} [Fintype F] {o : P} {K : Net P D}
  (Y : K.Guide o) {R : Type*} [AddCommGroup R]

abbrev Wires (D : F→ Type*) (X : Type*) := ∀ i:F,(D i→ X) → ℂ
abbrev Clocks {X : Type*} (W : Wires D X) := ∀ i, Abs (W i)

def area (W : Wires D R) (x : Options P R o) := Flux.product W (K.meter x.val)
lemma draw (W : Wires D R) {E : Type*} (c : E→ Plan D R)(f : E→ℂ) (h : push c f=Flux.product W) : area (K:=K) (o:=o) W=push (Y.arrive ∘ c) (fun d=> if Coherent Y (c d) then f d else 0):= by
   funext x; rw [area,← h,push_if,push_if]; apply tsum_congr; intro i
   have he : Coherent Y (c i) ∧ Y.arrive (c i)=x ↔ c i=K.meter x.val:= by
      refine ⟨fun ⟨hb,hx⟩=> hb.symm.trans (congrArg (fun X:Options P R o=> K.meter X.val) hx), fun hi=>?_⟩
      rw [hi]; exact ⟨coherence Y x,Y.landed x⟩
   by_cases hv : c i= K.meter x.val
   · obtain ⟨hx,ht⟩:= he.mpr hv; rw [comp_apply,if_pos ht,if_pos hx,if_pos hv]
   rw [if_neg hv,comp_apply]; split_ifs <;> tauto

variable (c:Side) (W:Wires D Cover) (H:Clocks W)
def atlas (d:Plan D Cover): ℂ := if Coherent Y d then Flux.product W d else 0
def modify (d:Plan D Cover): ℂ := if Coherent Y (page c d) then Flux.product W d else 0

include H
lemma atlas_abs : Abs (atlas Y W) := by
   unfold Abs atlas; simp_rw [apply_ite (‖·‖),norm_zero]; exact Flux.support _ _ (Flux.abs_product W H)
lemma modify_abs : Abs (modify Y c W) := by
   unfold Abs modify; simp_rw [apply_ite (‖·‖),norm_zero]; exact Flux.support _ _ (Flux.abs_product W H)
omit H
def tile {X : Type*} : (X → Cover) → X → Site c := fun k=> wrap c ∘ k
def urban : Wires D (Site c) := fun i=> push (tile c) (W i)
def climb := area (K:=K) (o:=o) W
def hill := area (K:=K) (o:=o) (urban c W)
lemma visible : climb (K:=K) (o:=o) W=push Y.arrive (atlas Y W):= by
   apply draw Y W id (Flux.product W); funext x; rw [push_if, tsum_eq_single x]
   · exact if_pos rfl
   intro j hj; exact if_neg hj
include H
lemma border : hill (K:=K) (o:=o) c W=push (toTorus c ∘ Y.arrive) (modify Y c W):= by
   rw [show toTorus c (o:=o) ∘ Y.arrive= Y.arrive ∘ page c from ?_]; swap
   · exact funext fun v=>(Guide.transport ..).symm
   exact draw Y _ (page c) (Flux.product W) (Flux.many W (fun _=>tile c) H)
include Y in
lemma climb_abs : Abs (climb (K:=K) (o:=o) W) := by
   rw [visible Y]; exact (Flux.push_sum _ _ (atlas_abs Y W H).of_norm).norm
include Y in
lemma hill_abs : Abs (hill (K:=K) (o:=o) c W) := by
   rw [border Y c W H]; exact (Flux.push_sum _ _ (modify_abs Y c W H).of_norm).norm
omit H
def gainsPageCoherence (d : Plan D Cover): Prop:= Coherent Y (page c d) ∧ ¬ Coherent Y d
def excess (d : Plan D Cover): ℂ:= if gainsPageCoherence Y c d then Flux.product W d else 0
lemma extra (d): modify Y c W d - atlas Y W d=excess Y c W d:= by
   unfold excess modify atlas; by_cases h:Coherent Y d
   · simp only [h,Y.stay _ d h,↓reduceIte,sub_self,gainsPageCoherence,true_and,not_true]
   rw [if_neg h,sub_zero]; unfold gainsPageCoherence; split_ifs <;> tauto
include H
lemma excess_abs : Abs (excess Y c W) := by
   unfold Abs excess; simp_rw [apply_ite (‖·‖),norm_zero]; exact Flux.support _ _ (Flux.abs_product W H)

-- any reader AFTER anchor. includes holding several displacements etc.
omit H
variable {B G : Type*} (p : Options P Cover o →B) (u : Options P (Site c) o →G) (v : B→ G)
include H
lemma comparison (h : u ∘ toTorus c=v ∘ p) : push u (hill (K:=K) (o:=o) c W) - push v (push p (climb (K:=K) (o:=o) W)) = push ((v ∘ p) ∘ Y.arrive) (excess Y c W):= by
   rw [← Flux.push_comp p v _ (climb_abs Y W H).of_norm, border Y c W H, visible Y,
     ← Flux.push_comp Y.arrive _ _ (atlas_abs Y W H).of_norm, ← Flux.push_comp _ u _ (modify_abs Y c W H).of_norm, ← show (u ∘ toTorus c) ∘ Y.arrive = u ∘ (toTorus c ∘ Y.arrive) from rfl,h,← Flux.push_sub _ _ _ (modify_abs Y c W H).of_norm (atlas_abs Y W H).of_norm,funext (extra Y c W)]
omit H
namespace Ports
/-! Every retained exp and polynomial-log cost included in positions at given period. -/
variable [∀ i,Fintype (D i)] {a:F→ℝ}{σ : ℝ} {W}
def Offering (a:F→ℝ) (σ:ℝ) (W:Wires D Cover) := ∀ i, SumBudget (fun d=>Real.exp (σ*mileage d)*‖W i d‖) (a i)
omit [Fintype F] in
lemma Offering.clocks (h:Offering a σ W)(he:0≤σ): Clocks W:= by
   intro i; refine (budget_mono (f:=fun d=>Real.exp (σ*mileage d)*‖W i d‖) (h i) (fun d=> norm_nonneg _) ?_).2.1
   intro d; exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg he (mileage_cost d)))
lemma Offering.whole (h:Offering a σ W): SumBudget (fun d:Plan D Cover=> Real.exp (σ*toll d)*‖Flux.product W d‖) (∏ i,a i):= by
   convert Flux.product_budget _ a h using 1
   ext1 d
   unfold Flux.product toll; rw [Finset.mul_sum, Real.exp_sum,norm_prod,← Finset.prod_mul_distrib]

variable {δ : B→ℝ} {m: ℝ} (w:G→ℝ) [Fintype P]
-- For any retained exponential etc. use with p,u that measure jet displacements etc;
-- often only hold torus locations `tile y` and convert the cover part by tile-push.
omit [Fintype P] in
lemma standard (hw:Offering a σ W)(hs:0≤σ)(he:∀ i,0≤δ i) (h:∀ d,δ (p (Y.arrive d))≤Real.exp (σ*toll d)): SumBudget (fun j=>δ j*‖push p (climb (K:=K) W) j‖) (∏ i,a i):= by
   rw [visible Y,← Flux.push_comp Y.arrive p (atlas Y W) (atlas_abs Y W (hw.clocks hs)).of_norm]; apply Flux.push_budget _ _ he _ (atlas_abs Y W (hw.clocks hs)); refine budget_mono hw.whole (fun i=> mul_nonneg (he _) (norm_nonneg _)) ?_; intro d; unfold atlas; split <;> rename_i H
   · exact mul_le_mul_of_nonneg_right (h d) (norm_nonneg _)
   have hp(d:Plan D Cover) : 0 ≤ Real.exp (σ*toll d)*‖Flux.product W d‖:= hw.whole.1 d
   rw [norm_zero,mul_zero]; exact hp d

lemma world (hw:Offering a σ W)(hs : 0≤σ)(he:u ∘ toTorus c=v ∘ p)(ha:∀ i,0≤w i) (hm: 0 ≤ m)(h: ∀ d, w (v (p (Y.arrive d))) ≤ Real.exp ((σ-m*(Y.rate+1))*toll d)) : SumBudget (fun j=> w j * ‖push u (hill (K:=K) c W) j-push v (push p (climb (K:=K) W)) j‖) (Real.exp (-m*c.val) * ∏ i,a i):= by
   have hh:= hw.clocks hs
   have ht: (∏ i,a i) ≥ 0:= budget_nonneg hw.whole
   simp_rw [← Pi.sub_apply, comparison Y c W hh p u v he]
   apply Flux.push_budget _ w ha _ (excess_abs Y c W hh)
   apply budget_mono (budget_scale (Real.exp_pos _).le hw.whole) (fun i=>mul_nonneg (ha _) (norm_nonneg _)); intro d
   unfold excess; rw [← mul_assoc,← Real.exp_add]; split
   next H=>
      have hy:= Guide.odd Y c d H.1 H.2
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply (h d).trans; apply Real.exp_monotone; nlinarith [mul_nonneg (sub_nonneg.mpr hy) hm]
   next=> rw [norm_zero,mul_zero]; positivity
end Ports
end Net
end YM.Comparison.RG02.Sky
