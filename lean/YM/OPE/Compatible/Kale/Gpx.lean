import YM.OPE.Compatible.Kale.Rust
/-! # Finite leaders over the measured quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
local notation "Z"=> solar G d τ
variable (H:Even c.val) (X:Plot H){A:Alps K T i v}
local notation "V"=> Libra.Keys G (Limb H)
local notation "E'"=> Libra.Keys G (Stand.Free X)
def cutφ (p: Tower (Shade G) d τ)(x:Site c):ScriptJ V:= Vtap p x ∘ cloak H
-- Pay
variable (Vj:Bor H A b)
def isolate (p q: Tower (Shade G) d τ) (x y: Site c):= X.charted (cutφ H p x *cutφ H q y) -- Lean cannot infer?
lemma CloudH (p: Z)(x:Site c): (Pond H).Marbles (cutφ H p.val x):=Flux H (p.property.2 c x)
lemma isolateB (p q:Z)(x y: Site c) : (isolate H X p.val q.val x y).B:= X.composeWard (prodMar (Pond H) (CloudH H p x) (CloudH H q y))
def RGram (p q: Z) (x y: Site c) (L: ChartRatio G):Token:= (Vj.L X).pay L (isolate H X p.val q.val x y)
lemma parade (p q:Z)(x y: Site c)(Y:Plot H)(ht:LocalRatio R):RGram H X Vj p q x y R= RGram H Y Vj p q x y R:=Vj.bodes X Y (prodMar _ (CloudH H p x) (CloudH H q y)) ht
-- Bor any proofs same 
lemma cargo (x: E')(s:ℕ)(hs:0<s): jet (Vj.L X).f s x= jet (swornV A.clip A.live (n:=c)) s (rayS H X G x)/4:=riseR H X Vj hs x
local notation "o¤"=> penon (Vj.L X)
lemma real_power (u v:E')(W':Bor H A v') : (penon (Vj.L X)).P u v = (penon (W'.L X)).P u v:=by
   let L':=penon (W'.L X); have he(x:E'): (o¤).P x x=L'.P x x:=by
      apply mul_right_cancel₀ (M₀:=ℝ) (show (2:ℝ)⁻¹≠ 0 by norm_num); exact ((penon_shape _ _).symm.trans ((cargo H X Vj _ 2 (by decide)).trans (((cargo H X W' _ 2 (by decide))).symm.trans (penon_shape ..))))
   have hh:= he (u+v); simp_rw [map_add,LinearMap.add_apply,he] at hh; rw [show (o¤).P v u=(o¤).P u v from (o¤).turns ..,L'.turns v u] at hh; linarith
lemma real_law (W': Bor H A v'): penon (Vj.L X)=penon (W'.L X):=by
      have hh (A B:Law E')(h:A.P=B.P): A=B:=by cases A; cases B; simp_all
      exact hh _ _ (LinearMap.ext (fun i=> LinearMap.ext (fun j=> real_power H X Vj i j W')))
include Vj
lemma jewel (W':Bor H A b) (p q:Z) (x y:Site c)(hp:G.Simple)(h:LocalRatio R) : RGram H X Vj p q x y R= RGram H X W' p q x y R:=by
      let X':=penon (Vj.L X); have hx(u:E'):jet (W'.L X).f 2 u= X'.P u u/2:=by unfold X';rw [real_law H X Vj W'];exact penon_shape ..
      unfold RGram; rw [Lid.cutOut (Vj.L X) h X' _ (penon_shape _), Lid.cutOut (W'.L X) h X' _ hx]; rw [funext (show ∀ i:E',(Vj.L X).hat R i=(W'.L X).hat R i from fun i=>(SwiftD H X Vj h hp i).trans (SwiftD H X W' h hp i).symm)]
end YM.OPE.Quit
