import YM.AllOrder.Laplace.Pass
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels
import YM.Work.F05.Actions
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical
open Lattice Wilson RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext Repeat Lapis Lantern Fare Next.Fluctuations Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat
open Work.F05 AnalyticBridge.GaussianFieldAlignment Locations
open scoped BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}
variable (F J: Forest S.ratio)(s:Signed)(x:Site c)
local notation "K"=>Precision.Key F G
local notation "Y0"=>Poll.Body (Precision.Key F G)
def jointTour : F.Slice G≃ₜ (Locations.forest s x F).Slice G where
   toFun:=Turn.glide s x F
   invFun y i:=
     let a:=(free s x F).symm i; if s.flip a.val.2 then (y a)⁻¹ else y a
   left_inv y:= by funext i; unfold Turn.glide; simp; split_ifs <;> simp
   right_inv y:= by funext i; unfold Turn.glide; simp; split_ifs <;> simp
   continuous_toFun:= by apply continuous_pi; intro a; unfold Turn.glide; split <;> fun_prop
   continuous_invFun:= by apply continuous_pi; intro a; dsimp only; split <;> fun_prop
lemma at_one :(jointTour F s x) (1:F.Slice G)=1:=by funext i; unfold jointTour; change (if _ then (1:G.El)⁻¹ else (1:G.El))=1; simp
lemma saving : MeasurePreserving (jointTour (G:=G) F s x) (F.order G) ((Locations.forest s x F).order G):= Turn.forest_toll _ _ _ _
variable (A : Site c → G.El)
-- coarse residual gauge on free variables. Uses arbitrary forest kept.
set_option maxHeartbeats 200000 in
def fitted: F.Slice G≃ₜ F.Slice G where
   toFun y i:= A (S.ratio.parent i.val.1)*y i*(A (S.ratio.parent (i.val.1+step i.val.2)))⁻¹
   invFun y i:= (A (S.ratio.parent i.val.1))⁻¹*y i*(A (S.ratio.parent (i.val.1+step i.val.2)))
   left_inv y:=by funext i; group
   right_inv y:=by funext i; group
   continuous_toFun:= by apply continuous_pi; intro i; exact (continuous_const.mul (continuous_apply i)).mul continuous_const
   continuous_invFun:= by apply continuous_pi; intro i; exact (continuous_const.mul (continuous_apply i)).mul continuous_const
lemma fitted_pays : MeasurePreserving (fitted F A) (F.order G) (F.order G):= measurePreserving_pi _ _ fun i:F.Free=> G.preserve_two_sided (A _) (A _)⁻¹
lemma worn (v : F.Slice G) : F.drape (fitted F A v)= Lattice.gauge (A ∘ S.ratio.parent) (F.drape v):= by
   funext i; by_cases h:i ∈ F.trunks
   · unfold Lattice.gauge; rw [show F.drape v i=1 from F.on_tree _ ⟨i,h⟩,show F.drape (fitted F A v) i=1 from F.on_tree (fitted F A v) (⟨i,h⟩:↥F.trunks), Function.comp_apply, Function.comp_apply, F.trunk_internal h]; simp
   unfold Lattice.gauge; rw [show F.drape v i=v _ from F.off_tree _ (⟨i,h⟩:F.Free), show F.drape (fitted F A v) i= _ from F.off_tree (fitted F A v) (⟨i,h⟩:F.Free)]; rfl
lemma fitted_inv : (fitted F A).symm=fitted F A⁻¹:=by ext1 x; funext i; change _= (A _)⁻¹*x i*((A _)⁻¹)⁻¹; simp; rfl
lemma fitted_op (u:G.El): fitted F (fun _=>u) (1:F.Slice G)=1 := by funext i; change u*1*u⁻¹=1; simp
lemma fitted_live : Continuous (fun x: (Site c→G.El) × F.Slice G=> fitted F x.1 x.2) := by unfold fitted; apply continuous_pi; intro i; change Continuous (fun x: (Site c → G.El) × F.Slice G => x.1 (S.ratio.parent i.val.1)* x.2 i*(x.1 (S.ratio.parent (i.val.1+step i.val.2)))⁻¹); fun_prop
lemma rerouted_one: Profiles.reroute F J G (1:F.Slice G)=1:= by rw [← show exposure F (G:=G) (0:Bid.Dir G c) 0=(1:F.Slice G) from exposure_zero F]; apply reroute_exposure_zero
end YM.AllOrder.Laplace
