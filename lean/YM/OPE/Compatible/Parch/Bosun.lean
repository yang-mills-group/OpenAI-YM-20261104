import YM.OPE.Compatible.Parch.Bond
/-!
# Project.O1 Coal receipt
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score Tree Woody Next.Free FreeResolvent
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver Tensor
open Drift Char Silt Silt.Float Module Variance Merchant Merchant.SiteL Stand
variable {i j d k m r l:ℕ}{n:Side}{K:Sponsor G}{T:Seasons K}{v:ℝ}
section
variable {D V W X:Type}[Fintype D][Fintype W]
variable (L:Libra.Keys G D→ₗ[ℝ] Dual' (Libra.Keys G D))(F:Libra.Keys G W→L[ℝ] Libra.Keys G D)(P:Law (Libra.Keys G W))
local notation "I!"=>Libra.Keys G D
local notation "J!"=>Libra.Keys G W
open FoldU
namespace OrientX
variable {R:Cascade.Score D V}
lemma crux (p:I!→ℝ)(x:I!)(r:ℕ)(y:J!): P.P (ν (F:=F) (L:=L) (P:=P) p x r) y=pop (Tensor.coeff p (r+1) 0) x (mate F L P x) (F y):=by unfold ν; rw [P.applies]; rfl
noncomputable abbrev νrt (p:I!→ℝ)(r:ℕ): I!→ J!:= fun x=>ν (F:=F) (L:=L) (P:=P) p x r
lemma boundω {p:I!→ℝ} {C t κ:ℝ}(hp:∀ x: Fin (r+1)→I!, (∀ i,‖x i‖≤1)→ ‖(Tensor.coeff p (r+1) 0) x‖≤ C) (hV:0 ≤ C)(ht:1 ≤ t)(hx: LimitR t (fun u=>mate F L P u))(hA:LimitR t (fun x=>F x)) (hk:0<κ)(he:∀ x:J!,κ*‖x‖^2 ≤ P.P x x) : LimitR (↑(r+1)*(t^(r+1)*C)/κ) (νrt L F P p r):=by
       have hT:=zero_lt_one.trans_le ht; intro x hx'; refine pinL hk he _ _ (by positivity) ?_ ; intro y hh; exact popper hp hT x (mate F L P x) (F y) (hx'.trans ht) (hx _ hx') (hA _ hh)
lemma dutyω (p:I!→ℝ)(r:ℕ):ContDiff ℝ ω (νrt L F P p r):=by
       apply smoothI (P:=P); intro i; simp_rw [νrt, crux L F P p _ r i]; exact pol_s (Tensor.coeff p (r+1) 0) (mate F L P) (F i)
lemma dotGauge (p:I!→ℝ)(x:I!)(r:ℕ)(t:ℝ): ν (F:=F) (L:=L) (P:=P) p (t • x) r=t^r • ν (F:=F) (L:=L) (P:=P) p x r :=by
       unfold ν ωDot; rw [map_smul,FoldU.popC]; rw [← map_smul]; rfl
lemma fuelω (p:I!→ℝ)(r:ℕ): νrt L F P p r=rank (νrt L F P p r) r:= by
       exact (Tall.pint (dutyω L F P ..) (fun x t=>dotGauge L F P _ x r t)|>.symm)
variable {P L F} (h:OrientX R L F P)
include h
lemma bargeω(p:I!→ℝ)(he:LevelA R p)(hx:ContDiffAt ℝ ω p 0) (r:ℕ):
          Tall (νrt L F P p r) r ∧ (∀ x v,νrt L F P p r (x+gillS R v)=νrt L F P p r x) ∧∀ g:G.El,∀ i:I!,νrt L F P p r (glint _ g i)=glint W g (νrt L F P p r i):=
               ⟨Tall.tag le_rfl (fuelω _ _ _ p r),fun i j=> h.frameS p he hx j i,fun g i=> h.FrameAd p he hx i g⟩ -- missing assumptions
-- E is read from local source through X.BL.H porac
end OrientX
end
end YM.OPE.Claw
