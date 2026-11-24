import YM.OPE.Compatible.Mould.Swell
/-!
# Radar general χ.Match through realization. -/
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
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J}{w:ℝ}{D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m){Z:Topic H hs X B D₀}{a:Axis}
open Flume.Script Maxwell Balsam Nestle Pert.Full
variable {p₁:Clip}{u ν:M→ℝ}{hp:4≤ i}{V:(j:M)→Alps K T i (u j)}{hq:1 ≤ u}{U: Z.Ω M u}(T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
local notation "S!"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
local notation "F!"=>Tracts G d τ
section
-- SAP Ψ
abbrev Head_ (k:ℕ)(e:ℕ)(v:M→ℝ) (U:Z.Ω M u)(R:M→Submodule ℝ (Tracts G d τ)):Prop:=∀ p:M→ Bead G l e,Wealth p u v → (∀ i,p i∈ Ghost G l e∧ LimitQ (p i) k)→∃ y:(j:M)→ (U.flag e j), Wealth (fun i=>(y i).val) u v∧ ∀ i,(y i).val∈R i∧ Crop k ((y i).val)∧ tag D₀ e (y i).val=p i
abbrev HostE (e:ℕ)(v:M→ℝ) (U:Z.Ω M u)(R:M→Submodule ℝ (Tracts G d τ)):Prop:=∀ k:ℕ,Head_ k e v U R
abbrev SonE (e:ℕ)(he:e<l+1)(v:M→ℝ) (U:Z.Ω M u)(R:M→Submodule ℝ (Tracts G d τ))(Δ:Submodule ℝ (Z.Mint e)):Prop:=∀ p:M→ Z.Mint e, Wealth (fun i=>(p i).val) u v→ (∀ i,p i ∈ Δ)→∀ k:ℕ,k≤3→ (∀ j,trims k (p j).val)→∀ r:ℕ,(∀ i,LimitQ (UΦ Z he (p i) 0) r)→∃ y:∀ j,U.flag e j,Wealth (fun j=>(y j).val) u v∧∀ i,(y i).val∈ R i∧ U.read e he i (y i)=p i∧ trims k (y i).val∧ Crop r (y i).val
lemma discU (he:e<l+1)(j:M)(p:U.flag e j): UΦ Z he (U.read e he j p) 0= tag D₀ e p.val:= vintage Z U he j p 0 (trims.be _)
include T'
lemma NemTag (L:Lance X)(he:e<l+1)(x:M)(v:U.flag e x)(h:(v.val)∈ Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀) x): tag D₀ e v.val∈ Ghost G l e :=by
      rw [← discU he]; exact Nem Hp Z a he T'.dimD T'.cap T'.vol (U.read _ he _ v) 0 (stockMe Hp T' x v h) (trims.be _) L
end
end YM.OPE.Stroke
