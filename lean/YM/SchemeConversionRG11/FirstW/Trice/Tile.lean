import YM.SchemeConversionRG11.FirstW.Trice.Gate
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS
open scoped ContDiff BigOperators Topology Classical
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{s t u:StepPath T} {A B C:Sight T G} {P Q:Hall T ℝ} {x y z:E4}{R:ℝ}
lemma ledger_here (P:Hall T ℝ) (A B C:Sight T G) (i j a b:Axis): MinusUnit T (P*ack T A B C i j a b)= MinusUnit T (rating (stalkH T A j) (torso P (claw T B C a b)) i):= by
 funext k; unfold MinusUnit; rw [← shift_inner]; apply congrArg _; apply Finset.sum_congr rfl; intro v _; simp only [ack, Pi.mul_apply,torso,real_inner_smul_right]
lemma nominal (o:StepPath T) (P: Hall T ℝ): MinusUnit T P=MinusUnit T (slipU T o P):= funext fun k=>by unfold MinusUnit; apply congrArg _; exact Eq.symm (Equiv.sum_comp (Equiv.addRight (o k)) _)
lemma MinusUnit.sub_h (P Q: Hall T ℝ): MinusUnit T (P-Q)=MinusUnit T P-MinusUnit T Q:= funext fun k=>by simp only [MinusUnit,Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]
def CoreH (u v:E4→G.Color) (k:Axis) (w:E4):= -(inner ℝ (u w) (grad k v w))
lemma slide_core (u v:E4→G.Color) (k:Axis) (x w:E4): CoreH u v k (w+x)=CoreH (fun y=>u (y+x)) (fun y=> v (y+x)) k w := by unfold CoreH grad Analysis.D; rw [fderiv_comp_add_right (f:=v) x]
lemma pitch_trans (p: Badge G) (b: Bool) (x y w:E4) (i:Axis): toast p b (x-y) i w=toast p b x i (w+y):= by unfold toast; rw [show w-(x-y)=w+y-x by abel]
variable {A₀ B₀ C₀: Badge G}{u₁ u₂ u₃:Bool}
local notation "L1" => Laurel A₀ u₁ T s
local notation "L2" => Laurel B₀ u₂ T t
local notation "L3" => Laurel C₀ u₃ T u
local notation "A1" => toast A₀ u₁ x
local notation "A2" => toast B₀ u₂ y
local notation "A3" => toast C₀ u₃ z
lemma flux_hit (W:Wash) (hr:W.rOut<R) (hs:sails T s x) (ht:sails T t y) (hu:sails T u z) (hx:R<‖y-x‖) (he:R<‖z-x‖) (hc:MarkGrid T c) (i j a b:Axis):
   let X:=CoreH (A1 j) (stance (blot W x) (pitch A2 A3 a b)) i
   Integrable X ∧ Tendsto (MinusUnit T (Mask T s W*ack T L1 L2 L3 i j a b)) atTop (𝓝 (∫ v,X v)):= by
 intro X
 obtain ⟨HP,H⟩:= local_rate (A₀:=A₀) (B₀:=B₀) (C₀:=C₀) (b₁:=u₁) (b₂:=u₂) (b₃:=u₃) W hr hx he (sails_sub ht hs) (sails_sub hu hs) hc i j a b -- H
 let V:= CoreH (toast A₀ u₁ 0 j) (stance (blot W 0) (pitch (toast B₀ u₂ (y-x)) (toast C₀ u₃ (z-x)) a b)) i
 change Integrable V at HP
 have hv (w): V w=X (w+x):= by
    unfold X; rw [slide_core]; unfold V CoreH; rw [show toast A₀ u₁ 0 j w= _ from show toast A₀ u₁ 0 j w=A1 j (w+x) from sub_self x ▸ pitch_trans A₀ u₁ x x w j]; apply congrArg (fun u:E4→G.Color=> -(inner ℝ _ (grad i u w))); funext p; simp only [stance,pitch,pitch_trans,blot]; rw [sub_zero,add_sub_cancel_right]
 have hb: Integrable X:= (HP.comp_sub_right x).congr (Eventually.of_forall fun w=> by simp only [hv,sub_add_cancel])
 have heq: slipU T s (Mask T s W*ack T L1 L2 L3 i j a b)= Mask T 0 W*ack T (Laurel A₀ u₁ T 0) (Laurel B₀ u₂ T (t-s)) (Laurel C₀ u₃ T (u-s)) i j a b := by
   rw [show slipU T s (Mask T s W * ack T L1 L2 L3 i j a b)= resiteR T (Mask T s W) s* slipU T s (ack T L1 L2 L3 i j a b) from rfl]; simp only [lift_ack,statue,resite_mask,sub_self]
 refine ⟨hb,?_⟩; rw [nominal s,heq,ledger_here, show (∫ v,X v)=∫ v,V v from ?_]; exact H
 simp_rw [hv, integral_add_right_eq_self X]
lemma ack_all (W:Wash) (hr:W.rOut<R) (hs:sails T s x) (ht:sails T t y) (hu:sails T u z) (hx:R<‖y-x‖) (he:R<‖z-x‖) (hp:R<‖z-y‖) (hc:MarkGrid T c) (i j a b:Axis):
 Tendsto (MinusUnit T (ack T L1 L2 L3 i j a b)) atTop (𝓝 ((∫ v,(1-blot W x v)*vst A1 A2 A3 i j a b v)+(∫ v,CoreH (A1 j) (stance (blot W x) (pitch A2 A3 a b)) i v))) := by
 have h:= (flux_hit (A₀:=A₀) (B₀:=B₀) (C₀:=C₀) (u₁:=u₁) (u₂:=u₂) (u₃:=u₃) W hr hs ht hu hx he hc i j a b).2; have H:= exterior_budget (b₁:=u₁) (b₂:=u₂) (b₃:=u₃) (A₀:=A₀) (B₀:=B₀) (C₀:=C₀) i j a b W W hs ht hu (hr.trans (norm_sub_rev x y ▸ hx)) (hr.trans hp) (hr.trans (norm_sub_rev x z ▸ he)) hc
 let A:=ack T L1 L2 L3 i j a b; apply (H.2.add h).congr; intro l; rw [sub_mul, one_mul,MinusUnit.sub_h,Pi.sub_apply,sub_add_cancel]
end YM.RG11.FirstW
