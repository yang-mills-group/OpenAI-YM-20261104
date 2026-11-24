import YM.OPE.Compatible.Docks.Syrup
import YM.OPE.Compatible.Docks.Mil
import YM.OPE.Compatible.Tune.Theta
import YM.OPE.Compatible.Tune.Race
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Paired real and imaginary coefficient readings

`Bright` collects the real and imaginary responses into a real-linear map on
coefficients. `WaveD` identifies its phase-zero reading with the paired `GateQ`
reading of `ζWide`. Under `Lineage`, `scent` gives `Bright` a `Wax` bound at
exponent zero. `SpinOrbit` uses all three phases for the quadratic reading.
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
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l (d+6) w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
section
open GlowPack
variable (W:GlowPack Hp Z a (k:=k)) (U:Z.Ω M Y)(hq:1 ≤ Y)(hp:4 ≤ i)(V:(i':M)→Alps K T i (Y i'))
local notation "W!"=>Dux G l W.W
local notation "E!"=>Eagle Hp Z a W
variable {W Hp Z a U V} {hq hp}
variable (D:Cart Hp Z a W U hq hp V) (j':M)
open GlowPack
open Silt.Phere
open Pill Yolk Spells Silt.Phere
local notation "U!"=> τ
local notation "M*!"=> solar G (d+6) τ
variable {A:Labels.Frame G l}{A0:Source.Hol G}{T':Source.SectionData A}
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
section
local notation "Jθ"=>A.Index
variable (O:I→ A.Index → Asp T' A0 d)(B':Spells.Pad G)(μx:I→M)
noncomputable abbrev DentP (z:I)(i':A.Index)(q:ℂ→L[ℝ]ℝ):M*!:= crestL G D₀.aware 0 (MotionH (K:=K) O B' (fun i:I=> (V (μx i)).gear) hp (τ:=τ) z i' q)
noncomputable abbrev Cloz (i:I)(j:A.Index):= (DentP (D₀:=D₀) O B' μx (V:=V) (hp:=hp) i j Complex.reCLM, DentP (D₀:=D₀) (V:=V) O B' μx (hp:=hp) i j Complex.imCLM)
noncomputable def Bright (i:I): A.Coeff→L[ℝ] (M*!× M*!):= Arco (Cloz (D₀:=D₀) (V:=V) O B' μx (hp:=hp) i)
lemma WaveD (z:I): (doublet (Eψ D (μx z) 0)).comp (Bright O B' μx z (D₀:=D₀) (V:=V) (hp:=hp))=(doublet (GateQ D (μx z))).comp (ζWide O B' (fun i:I=> (V (μx i)).gear) hp D₀ z):=by
      let x :=μx z; let L := (GateQ D x); let Q:= Eψ D x 0
      let P(t:A.Index) := (Cloz (D₀:=D₀) O B' μx (V:=V) (hp:=hp) z t)
      let y(q):= folψ O B' (fun i=> (V (μx i)).gear) hp D₀ z q; let K(i:A.Index):= (y i Complex.reCLM,y i Complex.imCLM)
      have he(i:A.Index)(q): Eψ D x 0 (DentP (D₀:=D₀) O B' μx (V:=V) (hp:=hp) z i q)=L (y i q):= FundsP D x _
      have hh(i): doublet Q (P i)=doublet L (K i):=Prod.ext (he i Complex.reCLM) (he i Complex.imCLM); exact AlignmentP P K Q L hh

variable {η ℓ β:I→ℝ}{f:Filter I}{R':I→BudgetPoint}
variable (hL:Lineage (f:=f) (β:=β) η K.K (fun i:I=> (V (μx i)).gear) hp ℓ R' O (τ 0))
local notation "Bₗ"=> (Bright O B' μx (D₀:=D₀) (V:=V) (hp:=hp))
-- The quadratic operator combines the three phase readings.
noncomputable abbrev Opκ (p:ℝ):= Eψ D j' 0 + p • Eψ D j' 1+(p^2) • Eψ D j' 2
noncomputable def SpinOrbit (p:ℝ) (i:I): A.Coeff→L[ℝ] (OrthoC W× OrthoC W):= doublet (Opκ D (μx i) p) ∘L (Bₗ i)
include hL
lemma scent : Wax β f Bₗ 0:=by
        let Aη:=(fun i:I=> (V (μx i)).gear); have hT:=carth hL.born; have hp':Wax β f (Bₗ) 0:=portF _ (fun i=>TwinC (hLeaf i Complex.reCLM) (hLeaf i Complex.imCLM)) hL.born; exact hp'
where
    hLeaf (j:A.Index)(q:ℂ→L[ℝ]ℝ): Wax β f (fun i=> DentP (D₀:=D₀) O B' μx (V:=V) (hp:=hp) i j q) 0:=by
        have he:=waitG hL.born (Salary.strikesFee (Junk:=I) B' K.K _ (hL.wages j) q (fun i:I=> (V (μx i)).gear) hp (m:=τ 0)); let L:=crestL G D₀.aware 0; apply RateLE.of_norm_le (F:=fun i=> DentP O B' μx i j q (D₀:=D₀) (V:=V) (hp:=hp)) (((RateLE.const ‖L‖ (carth hL.born)|>.mul he.norm)).mono (by norm_num)); exact Eventually.of_forall fun i=> L.le_opNorm _
end
end
end YM.OPE.Stroke
