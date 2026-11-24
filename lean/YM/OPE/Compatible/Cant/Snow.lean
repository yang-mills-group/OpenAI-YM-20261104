import YM.OPE.Compatible.Spa.Laur
import YM.OPE.Compatible.Cant.Pole
import YM.OPE.Compatible.Cant.Foam
/-!
# Transport conditions at a single index

`YM.OPE.Stroke.Ace` records commutation with `Gift`, preservation of the phase flags, scaling of their graded coordinates, and a bound on the difference between shifted source and target pairings.
`sprintGate` obtains these conditions for each individual map in a `Topic.Sprint`.
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
local notation "JΛ"=> Fin (l+1) -- use
open Pipes
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
variable {uα:I→ℝ}{A:(v:I)→Alps K T j (uα v)}
local notation "μ"=>lapPrice (Patch.L P)
section
variable (U: Alps K T i v)(A:Alps K T j v')
-- These conditions describe one of the maps in a Sprint.
structure Ace (D:Stern K P τ l d w)(H:LocalRatio R)(hs:G.Simple)(a:Axis)(U: Alps K T i v)(A:Alps K T j v')(hq:0≤ v)(he:0≤ v')(hp:4 ≤ i)(hj:4≤ j)(m:ℕ)(Y:Tracts G d τ→L[ℝ] Tracts G d τ) :Prop where
     comm (x:F!) : Y (Gift G D.aware x)= Gift G D.aware (Y x)
     flag (n:ℕ)(ht:n ≤ l+1)(x:F!)(u:Phase)(he:trims u.val x): Y x u ∈ (Drift.Turns D u).flag n↔ x u∈ (Drift.Turns D u).flag n
     tapes (n:ℕ)(ht:n<l+1)(x:F!)(u:Phase)(hp:trims u.val x)(hx:x u∈ (Drift.Turns D u).flag n): (Drift.Turns D u).Tap n (Y x u)= (μ n)^m • (Drift.Turns D u).Tap n (x u)
     travel(n:Side)(V:Even n.val)(x y:Site n)(hq':barrier P≤n.val)(hz:Pins K P x y)(z:Phase)(p q:F!) : Thick ((μ l)*(μ l)) (fun i=> Topic.PhaseP (H:=H) (D₀:=D) (hs:=hs) U hp hq a x y V z (i+m) p q - PhaseP (D₀:=D) (H:=H) A hj he a x y V z i (Y p) (Y q) (hs:=hs))
end
lemma sprintGate {b':M→ℝ}{hp': 0≤Y}{hb:0≤ b'}{hv:4 ≤ j}{A:(k:M)→Alps K T j (b' k)} {F:M→Tracts G d τ→L[ℝ] Tracts G d τ}(h: Topic.Sprint H hs D₀ Y b' a V A hp hv hp' hb r F)(i:M): Ace D₀ H hs a (V i) (A i) (hp' i) (hb i) hp hv r (F i):=by
     exact ⟨h.mood i,fun u hu x n he'=>h.march.flag _ _ i hu x he',fun u hu x n hz hx=> h.march.tapC _ _ i hu x hz hx,fun n V' x y he ht s p q=> h.budget n V' x y he ht s i p q⟩
variable (V'':Even n.val)(x y:Site n)(hv':Pins K P x y)
local notation "LZ"=>Z.Mint
set_option maxHeartbeats 200000 in
lemma shootZ (t:Phase)(p q:LZ e)(i j:ℕ):Por Hp Z e t V'' x y a (i+j) p q=Por Hp Z e t V'' x y a i (Soul (P:=P) (e:=e) Z.station j p) (Soul (P:=P) (e:=e) Z.station j q):=by
       exact congrArg₂ (fun u v=> Scar Hp Z t V'' x y a (e:=e) u v) (forkP Z.station (μ e) 3 i j p) (forkP Z.station (μ e) 3 i j q)
lemma EpSky (z:Phase)(p q:Mint Z e)(m:ℕ): Sky (μ e*(μ e)) 6 (fun i=> Por Hp Z e z V'' x y a (i+m) p q):=by
        simp_rw[shootZ]; exact sunV H hs X Z.station D₀ (spose a G d τ) (ContinuousLinearMap.id ℝ (solar G d τ)) V'' x y Hp ..
end YM.OPE.Stroke
