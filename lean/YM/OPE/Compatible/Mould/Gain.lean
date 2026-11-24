import YM.OPE.Compatible.Mould.Boot
/-! # ζ covariance area.MSR -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {u ν:M→ℝ}{hp:4 ≤ i}{V:(j:M)→Alps K T i (u j)}
namespace Topic
local notation "μ"=> lapPrice (Patch.L P)
local notation "J!"=> Mint Z e
abbrev BoxesΦ (t:ℕ)(he:t<l+1): Mint Z t ≃ₗ[ℝ] (Phase→ Bead G l t) := phaseMap H hs B Z.station D₀ (Z.bill t he)
abbrev UΦ (he:e<l+1) (p:Mint Z e)(i:Phase): Bead G l e := BoxesΦ Z e he p i
lemma vintage (A: Ω Z M ν)(he:e<l+1)(j:M) (p:A.flag e j)(x:Phase)(hv:trims x.val p.val): UΦ Z he (A.read e he j p) x= (Drift.Turns D₀ x).Tap e (p.val x):=(A.quake e he j p x hv).2.2
variable (V':Ω Z M ν)
lemma riseΦ (he:e<l+1) (p:Mint Z e)(i j:Phase)(hv:i.val+1=j.val): UΦ Z he (WaneZ Z e he p) j=UΦ Z he p i:= spup H hs X B Z.station D₀ _ i j hv p
lemma rise0 (he:e<l+1)(p:Mint Z e):UΦ Z he (WaneZ Z e he p) 0=0:= raw0 H hs X B Z.station D₀ _ p
lemma bridgeV (j:ℕ)(hz:j≤3)(he:e<l+1)(p:Mint Z e): trims j p.val↔ ∀ i:Phase,i.val<j→ UΦ Z he p i=0:= (Eave.Vita (T:=Drift.Turns D₀) (Z.bill e he) j hz).symm -- name
variable (V:Even n.val)(x y:Site n)
abbrev WingP (u v:Mint Z e)(i:ℕ):Token:=⟨UnitBorn Hp Z a V x y 0 i u v,UnitBorn Hp Z a V x y 1 i u v,UnitBorn Hp Z a V x y 2 i u v⟩
lemma scoreP (u v:J!)(i:ℕ):WingP Hp Z a V x y u v i= annualP H hs X Z.station D₀ (spose a G d τ) (ContinuousLinearMap.id ℝ (solar G d τ)) V x y Hp u v i:=by
      exact JetS.eta _ _ (flareP Hp Z a u v V x y 0 i).symm (flareP Hp Z a u v V x y 1 i).symm (flareP Hp Z a u v V x y 2 i).symm
variable (ht:Pins K P x y)(hx:Attest G P d k e l m τ n)
include ht hx
lemma Polygon0 (i:ℕ)(he:e<l+1)(p q:J!): WingP Hp Z a V x y (WaneZ Z e he p) q i=Ū*WingP Hp Z a V x y p q i ∧ WingP Hp Z a V x y p (WaneZ Z e he q) i= Ū * WingP Hp Z a V x y p q i:=by
     simp_rw [scoreP]; exact skated H hs X B Z.station D₀ (Z.bill e he) (spose a G d τ) (ContinuousLinearMap.id ℝ _) V x y (GuardZ H hs X B D₀ a) (GuardI H hs X B D₀) hx Hp ht p q i
end Topic
end YM.OPE.Stroke
