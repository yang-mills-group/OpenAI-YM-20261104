import YM.OPE.Compatible.Blaze.Glass
/-! # Interchange on all phase seats -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix Tree
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Stationary
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Prairies Woody Virgin Work.F08 Flume.Page Drift
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open YM.AnalyticNext.QuarticMatch.Joint
variable {n c f:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} (a:Axis)
local notation "T!"=> Shade G
local notation "A!"=> stave m j T!
lemma plusP (p q:Script T! r): shapeR a r (p+q)=shapeR a r p+shapeR a r q:=by ext1 x; unfold shapeR; rw [Pi.add_apply,Pi.add_apply,mul_add]
lemma spay (p: Script T! r)(t:ℝ):shapeR a r (t • p)=t • shapeR a r p:=by ext1 x; unfold shapeR;rw [Pi.smul_apply, Pi.smul_apply]; exact mul_left_comm ..
noncomputable def aft (a:Axis) (G:Gauge)(m j:ℕ) :  (Silt.Float.stave m j (Shade G))→L[ℝ]  (Silt.Float.stave m j (Shade G)):=by
     let M(v: (Silt.Float.stave m j (Shade G))):= (j+1:ℝ)^m *‖v‖; let S:= seed m j (Shade G); let f(x: (Silt.Float.stave m j (Shade G))):=Silt.Float.plant m (shapeR a j (S x)) (M x) (lifePrice a (m:=m) (S x) _ (humor x))
     have hv(x: (Silt.Float.stave m j (Shade G))): S (f x)= shapeR a j (S x):= botany ..
     let P: (Silt.Float.stave m j (Shade G))→ₗ[ℝ]  (Silt.Float.stave m j (Shade G)):={ toFun:=f,map_add':=fun x y=> seed_inj m _ _ (by show S _=S _;rw [map_add,hv,hv,hv,map_add,plusP]), map_smul':=fun x y=> seed_inj m _ _ (by show S _=S _;simp_rw [map_smul, hv,map_smul, spay];rfl)}
     exact P.mkContinuous ((j+1:ℝ)^m) (fun x=> kept_stalk (lifePrice a (S x) _ (humor x)))
lemma aft_v (x:A!) : seed m j _ (aft a G m j x)= shapeR a j (seed m j _ x):=botany _ _ _ (lifePrice a (seed m j (Shade G) x) ‖x‖ (humor x)) -- infer
noncomputable def crew (a:Axis) (G:Gauge)(k m:ℕ):Seat k m (Shade G)→L[ℝ] Seat k m (Shade G):= ContinuousLinearMap.pi (fun i=> aft a G m i.val ∘L ContinuousLinearMap.proj i)
lemma railZ (q:Seat k m T!)(j:ℕ): lilies m k _ (crew a G k m q) j=shapeR a j (lilies m k _ q j):=by
     rw [soup,soup,moduleAt]; split; next h=> exact aft_v a _
     next h=> rw [_root_.zero_apply,_root_.zero_apply,map_zero];ext1 x;simp [shapeR]
variable {τ:Phase→ℕ}
local notation "W"=> Tower T! d τ
noncomputable def Mirror (a:Axis) (G:Gauge)(d:ℕ)(τ: Phase→ℕ): Tower (Shade G) d τ →L[ℝ] Tower (Shade G) d τ:= ContinuousLinearMap.pi fun i=> crew a G (d+i.val) (τ i) ∘L ContinuousLinearMap.proj i
lemma sunward (v: W)(j:Phase)(k:ℕ):spread G d τ (Mirror a G d τ v) j k=shapeR a _ (spread G d τ v j k):=railZ ..
lemma sun2 (v: W): Mirror a G d τ (Mirror a G d τ v)=v:=bloomP G d τ (funext fun i=>funext fun j=>by rw [sunward,sunward,discoS])
lemma sunherd (v:Tower (Shade G) d τ)(hv: Rainbow (spread G d τ v)): Rainbow (spread G d τ (Mirror a G d τ v)):=fun i j=>by rw [sunward]; exact sortedS _ _ (hv i j)
lemma toner (v: W)(x: Site n)(y: Bid.Dir G n): inkM (spread G d τ (Mirror a G d τ v)) d x y=inkM (spread G d τ v) d (dart a x) (streak a G n y):=by
    have hp (j:Phase): (inkM (spread G d τ (Mirror a G d τ v)) d x y).seq j.val= (inkM (spread G d τ v) d (dart a x) (streak a G n y)).seq j.val:=by rw [vein_i,vein_i]; unfold Flair; simp_rw [sunward]; exact Finset.sum_congr rfl fun i _=>rightS a _ x (fun _=>y)
    exact JetS.eta _ _ (hp 0) (hp 1) (hp 2)
end YM.OPE.Quit
