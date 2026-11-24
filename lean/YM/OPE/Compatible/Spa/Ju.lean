import YM.OPE.Compatible.Spa.Coin
/-!
# Lifting a fixed reading into a family of flags

Given `Bals` and the flag family `U`, `Gadget` lifts any fixed phase coordinate
at degree `e` to one element of each corresponding flag. Every lift has the
prescribed `ReadK` value, and the underlying family satisfies `Wealth ... Y 1`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
section
private lemma lift_constant_mint (U : Ω Z M Y) (e : Fin (l+1)) (z : Mint Z e.val) :
    ∃ f : (i : M) → U.flag e.val i, Wealth (fun i => (f i).val) Y 1 ∧
      ∀ i, U.read e.val e.isLt i (f i) = z := by
  obtain ⟨p, hp, hr⟩ := U.zark Z.r Z.t Z.bill e.val e.isLt (zero_le_one : (0 : M → ℝ) ≤ 1)
    (fun _ => z) (wealthC z.val) 0 (Nat.zero_le _) (fun _ => trims.be _)
  exact ⟨p, hp, fun i => (hr i).2⟩

private lemma read_section {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (C : Bals Hp Z a A' κ) (U : Ω Z M Y) (e : J!) (x : Jewel (A' e.val)) (i : M)
    (p : U.flag e.val i) (h : U.read e.val e.isLt i p = Plato Z e.val (A' e.val) e.isLt x) :
    ReadK Z κ U e i p = x :=
  (congrArg (κ e) h).trans ((C.tricks e).len x)

set_option maxHeartbeats 200000 in
lemma Gadget {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}(C:Bals Hp Z a A' κ)(U: Ω Z M Y)(e:J!)(x:Jewel (A' e.val)):∃ f:(i:M)→U.flag e.val i,Wealth (fun i=>(f i).val) Y 1∧∀ i, ReadK Z κ U e i (f i)=x:=by
  obtain ⟨p, hp, hr⟩ := lift_constant_mint Z U e (Plato Z e.val (A' e.val) e.isLt x)
  exact ⟨p, hp, fun i => read_section Hp Z a C U e x i (p i) (hr i)⟩
end
end YM.OPE.Stroke
