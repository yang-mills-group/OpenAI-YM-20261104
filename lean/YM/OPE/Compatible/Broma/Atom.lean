import YM.OPE.Compatible.Broma.Wage
/-!
# Dual Tau op bound. include coarse Reg repeated Crest
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v:ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
variable (B:Medal P G K.K P.J) (H:LocalRatio R) (hp:Crest G P K.K m) (hs:G.Simple)
local notation "X!" => TileC T P p R b
local notation "u!" => (upperX:X!→ℝ)
local notation "q!" => (downK:X!→ℝ)
local notation "UX" => (Qmark B (UA (H:=T) (P:=P) (p:=p) (V:=R) (C:=b)))
local notation "YX" => (Qmark B (VA (H:=T) (P:=P) (p:=p) (V:=R) (C:=b)))
variable {hs' : Crest G P K.K m}
lemma brimLg (P Q:M→Seat k m I→L[ℝ] Seat i j J) (T W:M→ℝ) (ht:1 ≤ T) (hw:0 ≤ W) (h:∀ l:ℕ,
    Auger j (fun u:M × Metric.closedBall (0: Seat k m I) 1=> lilies j i _ (P u.1 u.2.val) l)
        (fun u:M × Metric.closedBall (0: Seat k m I) 1=> lilies j i _ (Q u.1 u.2.val) l) (W∘Prod.fst) (T∘Prod.fst)): Brim P Q T W:=by
          let K:=M× Metric.closedBall (0:Seat k m I) 1; let f(u:K):= P u.1 u.2.val; let g(u:K):= Q u.1 u.2.val; have ht':1 ≤ T ∘(fun i:K=>i.1):=fun i=> ht _; have hw':0 ≤ W∘(fun i:K=>i.1):=fun i=>hw _
          have he:= brimL (M:=K) (p:=f) (q:=g) (T:=T∘Prod.fst) (m:=j) (I:=J) h ht' hw'; exact ⟨grantV P he.A ht zero_le_one, grantV Q he.B ht zero_le_one, grantV (P-Q) he.D ht hw⟩
include hs hp H
lemma civic (x y:Phase) (s:ℝ) (d:ℕ) (k:ℕ) (h:k ≤ m) (g:45≤k) (hz:∀ i:X!, Era (UX i) (UA i)) (hb:∀ i:X!,Era (YX i) (VA i)): Brim
     (fun i:X! => sectorOp P K.K (UA i) (UX i) R s g d x y hs (hz i) H)
     (fun i:X! => sectorOp P K.K (VA i) (YX i) R s g d x y hs (hb i) H) u! q!:=by
        apply brimLg (m:=k) _ _ _ _ (max_cap _ _ _ _ _) (fun i=>by show 0 ≤ (1/2:ℝ)^i.2; positivity); intro l
        simp_rw [publicity]; let Y:=Seat (d+x.val) k (Shade G); let X:= X! × Metric.closedBall (0:Y) 1; let u (i:X):=i.2.val; let v(j:X):= pointer G d x k (u j); refine dockW B H hp hs s k h (fun i:X=>i.1) v (fun x j=>?_) y d l
        refine ⟨1,zero_le_one,0,fun t=>?_⟩; have hv: ‖u t‖≤1 := Metric.mem_closedBall.mp t.2.property |>.trans' (dist_zero_right .. |>.symm.le); exact ((pointerFee (d:=d) _ _ x).2 j).tips (by simpa using hv)
