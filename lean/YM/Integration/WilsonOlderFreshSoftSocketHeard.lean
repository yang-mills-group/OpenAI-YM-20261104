import YM.Integration.WilsonOlderFreshSoftSocketMeasured
import YM.Integration.WilsonIndependentCollarWeightedCruise

/-! The one signed K-figure is heard on its originally placed c-root, then on the same earlier stop v, without resampling the root or redoing the normalized quiet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketHeard
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet seats ticket)
open WilsonOlderFreshSoftSocketFaces (raw fill)
open WilsonReceivedFixedDigitHistory WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(d:I→ℕ){D:I→ℕ}

def hearing {E E':Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup E'][NormedSpace ℝ E']
    (f:E→L[ℝ]E'):Era G E→ₗ[ℝ]Era G E' where
  toFun:=tuftV f
  map_add' a b:=by
    apply Prod.ext
    · funext n e r z;exact f.map_add _ _
    · funext e r z;exact f.map_add _ _
  map_smul' l a:=by
    apply Prod.ext
    · funext n e r z;exact f.map_smul l _
    · funext e r z;exact f.map_smul l _

local notation "L_" => R.family.path.levels
local notation "O_" => R.metals.O
variable (κ:(i:I)→Knob (D i))(pt:I→Chamber)
def during (N K c:ℕ)(cells:Digits L_ I)(root:I → Cover)(S:Finset I)(f:Pen D S→L[ℝ]ℝ)
    (Y:Outerm G D):Era G ℝ:=tuftV f (levelsO (itinerary L_ O_ d N cells (K-c) c Y root) S)

theorem original (simple:G.Simple)(ratio:LocalRatio O_)(L:ℂ→L[ℝ]ℝ)(N per K c v:ℕ)
    (cells:Digits L_ I)(S:Finset I)(w:(i:I)→R.family.label (d i))
    (vc:v≤c)(ck:c≤K)(live:K≤N)(y:I → Cover)(f:Pen D S→L[ℝ]ℝ):
    ∑b:Columns R (fun i:S=>d i),L (packet R d S w N per K b) •
      cruises L_ O_ N (mass d S) c v (during R d N K c cells y S f
        (WilsonOlderFreshSoftFigures.stencil R D d (seats R d S b) κ pt))=
    ∑q:(i:S)→Choice R d i,L (ticket R d S w N per K q) •
      cruises L_ O_ N (mass d S) c v (during R d N K c cells y S f (raw R d κ pt (fill R d S q))):=by
  classical
  let P (b:Columns R (fun i:S=>d i)):=WilsonOlderFreshSoftFigures.stencil R D d (seats R d S b) κ pt
  let Z (q:(i:S)→Choice R d i):=raw R d κ pt (fill R d S q)
  let F:=during R d N K c cells y S f
  let op:Era G ℝ→Era G ℝ:=cruises L_ O_ N (mass d S) c v
  have live':c+(K-c)≤N:=by omega
  have fund (W:Outerm G D)(law:Wellness d W):Auth (mass d S) (F W):=
    (placedO _ ((sound L_ O_ d N cells simple ratio W law (K-c) c live').level' y) S).tuft f
  have hp (b:Columns R (fun i:S=>d i)):Auth (mass d S) (F (P b)):=fund _ <|
    (OriginalCoverReanchoring.deposited (WilsonOlderFreshSoftFigures.seed R D d (seats R d S b) κ pt)
      (fun _ _=>Nat.le_add_left _ _)).1
  have hz (q:(i:S)→Choice R d i):Auth (mass d S) (F (Z q)):=fund _ <|
    (OriginalCoverReanchoring.deposited (WilsonOlderFreshSoftSocketPole.raw R d κ pt (fill R d S q))
      (fun _ _=>Nat.le_add_left _ _)).1
  have entry:=congrArg (hearing (G:=G) f)
    (WilsonOlderFreshSoftSocketMeasured.original R d κ pt simple ratio L N per K cells S w c ck live y)
  simp only [map_sum,map_smul] at entry
  have funds:∑b:Columns R (fun i:S=>d i),L (packet R d S w N per K b) • F (P b)=
      ∑q:(i:S)→Choice R d i,L (ticket R d S w N per K q) • F (Z q):=entry
  have h:=congrArg op funds
  change cruises L_ O_ N (mass d S) c v _=cruises L_ O_ N (mass d S) c v _ at h
  rw [WilsonIndependentCollarWeightedCruise.original L_ O_ simple ratio vc (ck.trans live) univ
    (fun b=>L (packet R d S w N per K b)) (fun b=>F (P b)) (fun b _=>hp b),
    WilsonIndependentCollarWeightedCruise.original L_ O_ simple ratio vc (ck.trans live) univ
      (fun q=>L (ticket R d S w N per K q)) (fun q=>F (Z q)) (fun q _=>hz q)] at h
  exact h

end YM.Integration.WilsonOlderFreshSoftSocketHeard
end
