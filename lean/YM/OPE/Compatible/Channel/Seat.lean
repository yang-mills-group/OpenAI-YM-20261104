import YM.OPE.Compatible.Channel.Turn
/-!
# `coupon` linear block, measure on Page stencils.
Foundation for covariance and contractions positive order. Functionals on full tori. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r n:ℕ} {I J T:Type*}[Fintype T][Fintype I] {L c f:Side} {A:Cross L T I}{η U:ℝ}
namespace Script
open Page
-- all arrays 
abbrev linePay (A:Cross L T I) (v: Cover × T)(u:Cover × I):= A (wrap L v.1,v.2) u.2 (u.1-cellar L v.1)
def call (A:Cross L T I) (x:Cover)(p:Page T r)(q:Page I r):= ∏ i,linePay A ((slide x p) i) (q i)
def countermove (A:Cross L T I)(x:Cover)(p:Script T r): Script I r:= fun q=>∑' i,p i * call A x i q
variable (h:A.strip η U)(he:0<η)
include h he
-- sooting each shifted line. use Brier.general
omit [Fintype T] [Fintype I] in
lemma one_price (a:Cover×T)(b:I)(m:ℕ): Sack (fun y:Cover=> poise m (y-cellar L a.1)) (fun y=> linePay A a (y,b)) (widthCost η m * U):=by
    have hx := width_income he (h (wrap L a.1,a.2) b) m; let f := A (wrap L a.1,a.2) b
    have hs : Sack (liftCost m) f (widthCost η m*U) := by unfold Sack; simp_rw [mul_comm (liftCost m _ :ℝ)]; exact hx
    let v:= Equiv.subRight (cellar L a.1); rw [show poise m (I:=Axis)=liftCost m from funext fun a=>by unfold poise liftCost notch; push_cast;rfl]
    exact hs.adroit v
omit h he
-- assemble slabs into Soot
omit [Fintype T] in
lemma layered (v:Script I r) {d:ℕ}{x:ℝ} (h:∀ i:Ink I r, Sack (poise d) (fun a=> v (syn a i)) x): soot d v ((Fintype.card (Ink I r):ℝ)*x):=by
    let V i a:= v (syn a i); let F : Ink I r × Bin r ≃ Page I r := Equiv.trans (Equiv.prodComm ..) (blurb ..)
    have he':0 ≤ fun j:Ink I r=> x:= fun i=>(h i).coins
    have hs : Sack (fun i:Ink I r × Bin r=> (figure d) (F i)) (v ∘ F) ((Fintype.card (Ink I r):ℝ)*x):=by
       apply Sack.barrel (p:=V) (u:=poise d) (fun i=> h i) (a:=fun _=> x) ?_ -- expected nondef
       exact ⟨he',(hasSum_fintype _).summable,(by rw [tsum_fintype];simp)⟩
    simpa [comp_def] using! (hs.adroit F.symm)
include h he
omit [Fintype T] in
lemma charges (i:Page T r)(x:Cover)(m:ℕ): soot m (call A x i) ((Fintype.card (Ink I r):ℝ) * (poise m (parcelY (fun _ : Fin r=>0) L (xy (slide x i))) * (widthCost η m*U)^r)):=by
   let t:=slide x i; let k:= parcelY (fun _ : Fin r=>0) L (xy t)
   apply layered; intro j
   let V(a:Fin r)(v:Cover):= linePay A (t a) (v,j a); let p a (v:Cover):= poise m (v-cellar L (t a).1)
   have hv:Sack (fun i=>poise m (i-k)) (weave V) ((widthCost η m*U)^r):=by
      refine (trellis (f:=V) (u:=p) (fun a=> one_price h he _ (j a) m) (fun a i=> poise_one m (i-cellar L (t a).1))).minor (fun i=>zero_le_one.trans (poise_one m (i-k))) (fun i=>?_ ) (le_of_eq (by simp))
      apply (couple_powers (i-k) m).trans_eq; unfold weave; refine prod_congr rfl fun a _=>?_
      have he: stepOut k a=cellar L (t a).1:=by unfold k parcelY; change cellar L ((0:Cover)+stepOut t.xy a)=_;rw [zero_add];rfl
      rw [show stepOut (i-k) a= stepOut i a-stepOut k a from rfl,he]
   -- same scaling
   let F a:= poise m (a-k)*‖weave V a‖; have ht : 0 ≤ poise m k:= zero_le_one.trans (poise_one m k)
   apply Work.F08.budget_minor (g:= fun a=> poise m k* F a) ⟨fun i=> mul_nonneg ht (hv.1 i),hv.2.1.mul_left _, (by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hv.2.2 ht)⟩ (fun i=> mul_nonneg (zero_le_one.trans (poise_one m i)) (norm_nonneg _)); intro b
   change poise m b* ‖weave V b‖≤ _; unfold F; rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); conv_lhs => rw [show b=k+(b-k) by abel]
   exact poise_cumul ..
--
end Script
end YM.OPE.Flume
