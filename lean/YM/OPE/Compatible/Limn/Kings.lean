import YM.OPE.Compatible.Limn.App
import YM.OPE.Compatible.Spades.Area
/-! # Graft coupling massive laws via projection -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side}{X Y:Type}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
open PhysicalNext.Repeat.Aroma Jargon
variable {t r R B b ε:ℝ}{m:ℕ}
variable {S:StepData c f}{F:Forest S.ratio} {I:Seats F}
open Finset Module
section
variable [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ X][FiniteDimensional ℝ Y]
def LieP (T: X→L[ℝ] Y)(Z:Law Y)(H:Law X):Prop:= ∀ x y,H.P x y= Z.P (T x) (T y)
noncomputable def dimT (T:X→L[ℝ] Y)(Z:Law Y)(H:Law X): Y→L[ℝ] X:= LinearMap.toContinuousLinearMap ((H.inverse ∘ₗ T.toLinearMap.dualMap) ∘ₗ Z.P)
variable (T:X→L[ℝ] Y)(Z:Law Y)(H:Law X)(h:LieP T Z H)
lemma hid (x:Y)(y:X): Z.P x (T y)=H.P (dimT T Z H x) y:=by change _=H.P (H.inverse ((Z.P x).comp _)) y; rw[Law.applies];rfl
include h
lemma dryW (x:X): dimT T Z H (T x)=x:=by
       change H.inverse (Z.P (T x) ∘ₗ T.toLinearMap)=x; rw [show (Z.P (T x) ∘ₗ T.toLinearMap)=_ from (show _=H.P x from LinearMap.ext (fun y=>(h x y).symm)),Law.solves]
lemma Along (x:Y)(y:X): Z.P (x-T (dimT T Z H x)) (T y)=0:=by rw [Z.P.map_sub,LinearMap.sub_apply,←h,hid T Z H,sub_self] -- hid both?
lemma CostV {y:X}(x:Y): Z.P (x+T y) (x+T y)=Z.P (x-T (dimT T Z H x)) (x-T (dimT T Z H x))+ H.P (y+dimT T Z H x) (y+dimT T Z H x):=by
       let u:=x-T (dimT T Z H x); let v:=T (y+dimT T Z H x); have he:u+v=x+T y:=by unfold u v; rw [map_add]; abel
       have hH : Z.P u v=0:= Along T Z H h _ _; change Z.P _ _= Z.P u u+_; rw[←he, Z.P.map_add,LinearMap.add_apply, (Z.P u).map_add,(Z.P v).map_add,hH,Z.turns v u,hH,zero_add,add_zero]; rw [h] -- force binder
omit h in
lemma reverseT (p:Module.Dual ℝ X) : Z.inverse (p ∘ₗ (dimT T Z H).toLinearMap)=T (H.inverse p):= by
       have hz(y:Y): Z.P (T (H.inverse p)) y = p (dimT T Z H y):=by rw [Z.turns,hid T Z H,H.turns,H.applies];
       rw [← show Z.P (T (H.inverse p))= _ from (show _=p.comp (dimT T Z H).toLinearMap from LinearMap.ext hz),Law.solves]
lemma tacks (p q:Module.Dual ℝ X) : Z.wick (p ∘ₗ (dimT T Z H).toLinearMap) (q ∘ₗ (dimT T Z H).toLinearMap) = H.wick p q:=by unfold Law.wick; rw [reverseT T Z H]; change q (dimT _ _ _ (T (H.inverse p)))= _; rw[dryW T Z H h] -- insert h
lemma echoW [MeasurableSpace X][BorelSpace X][MeasurableSpace Y][BorelSpace Y](μ:Measure X)(ν:Measure Y)[μ.IsAddHaarMeasure][ν.IsAddHaarMeasure] (p:X→ℝ):Z.average ν (p ∘ dimT T Z H) = H.average μ p:= Jargon.margin Z H (dimT T Z H).toLinearMap ν μ LinearMap.id (tacks T Z H h) p
end
variable (I)(Z:Law (AxisChart G F))
noncomputable def bit := Libra.giraffe (((stake I (G:=G)).toLinearMap.dualMap ∘ₗ Z.P) ∘ₗ (stake I).toLinearMap) (fun _ _=> Z.turns ..) (fun p h=> keptZ Z (stake I p) (ne_zero_of_norm_ne_zero (show ‖stake I p‖≠0 from (firmly I p).symm ▸ (norm_ne_zero_iff.mpr h)))) -- names
lemma inflect: LieP (stake I) Z (bit I Z):= fun _ _=>rfl
end YM.OPE.Limn
