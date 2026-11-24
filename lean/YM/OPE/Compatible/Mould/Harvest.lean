import YM.OPE.Compatible.Mould.Regal
/-!
# marker reconstruction faithful on the graded rank ideals. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic Variance
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J}{w:ℝ}{D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m){Z:Topic H hs X B D₀}{a:Axis}
open Flume.Script Maxwell Balsam Nestle Pert.Full
variable {p₁:Clip}{u ν:M→ℝ}{hp:4≤ i}{V:(j:M)→Alps K T i (u j)}{hq:1 ≤ u}{U: Z.Ω M u}(T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(L:Lance X)
local notation "S!"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
local notation "F!"=>Tracts G d τ
local notation "D!" x=>Topic.Dross Hp Z a x
include L T' hq
lemma arsenal (hx:∀ i,(V i).clip=p₁)(hp':l*l≤τ 0)(hz:0≤ν)(he:e<l+1): HostE e ν U S! ∧ SonE e he ν U S! (Topic.Dross Hp Z a e) :=by
      induction e using Nat.strong_induction_on with | h e ih=>
        have hv:= neal (hq:=hq) Hp T' L he hz (fun i hi=>(ih _ hi (hi.trans he)).2) hx ((Nat.mul_le_mul_right l (show e ≤ l by omega)).trans hp'); exact ⟨hv,summons (hq:=hq) Hp T' L _ hv hz⟩
-- general dependency. any asset sap
variable (Z a)
lemma harvestZ (hv:l*l≤τ 0)(hz:∀ j,(V j).clip=p₁)(he:e<l+1)(hν: 0 ≤ ν)(x:M→ Mint Z e)(hx:∀ i,x i∈ Dross Hp Z a e)(ht:Wealth (fun i=>(x i).val) u ν)(i:Phase)(hT:∀ j,trims i.val (x j).val):∃ p:∀ j,U.flag e j,Wealth (fun j=>(p j).val) u ν ∧∀ j,(p j).val∈ S! j ∧ U.read e he j (p j)=x j ∧ trims i.val (p j).val:=by
     obtain ⟨p,hV,hF⟩:= (arsenal (V:=V) (hq:=hq) Hp T' L hz hv hν he).2 x ht hx _ i.isLt.le hT (e+1) (fun _ y hy=> by omega); exact ⟨p,hV,fun j=>⟨(hF j).1,(hF j).2.1,(hF j).2.2.1⟩⟩
end YM.OPE.Stroke
