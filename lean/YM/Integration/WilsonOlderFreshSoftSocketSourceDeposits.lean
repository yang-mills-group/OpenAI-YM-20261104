import YM.Integration.WilsonOlderFreshSoftSocketTotal
import YM.Integration.WilsonOlderFreshSoftRoseScalarLedger
import YM.Integration.WilsonOlderFreshSoftFigureReading

/-! Each occupied subface of a finite roster keeps its own previous marked
scalar and each signed contribution from nonconstant ranks. The remaining
ordinary response is the continued nonconstant part at the chosen older stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketSourceDeposits
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet seats ticket)
open WilsonOlderFreshSoftSocketFaces (raw fill)
open WilsonOlderFreshSoftSocketRestored (degree stopped coin)
open WilsonOlderFreshSoftSocketKinetic (kinetic)
open WilsonOlderFreshHybridClock (flat)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReportingAbsoluteInletForecastBooks (value)
open WilsonOriginalStarSceneWords (pole)
open WilsonReceivedFixedDigitHistory WilsonCoeffUV.Winding ActualRunPhysicalPages Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(d:I→ℕ){D:I→ℕ}
local notation "L_" => R.family.path.levels
local notation "O_" => R.metals.O


open WilsonOlderFreshSoftSocketHeard (during)
open WilsonOlderFreshSoftSocketTotal (figure normalized cost listen)
open WilsonOlderFreshSoftFigures (stencil)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonOlderFreshSoftRoseScalarLedger (front feed)
open WilsonOlderFreshTerminalProgramme (series)

variable (κ:(i:I)→Knob (D i))(pt:I→Chamber)(N per K c w v:ℕ)(routes:WilsonReceivedFixedDigitHistory.Digits R.family.path.levels I)
  (S:Finset I)(x:(i:I)→R.family.label (d i))(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)
local notation "k₀" => mass d S

def paidScalar (L:Levels G)(O:ChartRatio G)(N k c w v:ℕ)(P:Era G ℝ)(p:ℕ)(θ:ℝ):ℝ:=
  series p θ fun e=>coeff e (clock L O N w v (clock L O N c w (ScalarTrim P.2)+
    ∑i∈Ico w c,clock L O N i w (feed L O N k c i P)))

theorem projected (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N k c w v:ℕ)(vw:v≤w)(wc:w≤c)(cn:c≤N)(P:Era G ℝ)(legal:Auth k P)(p:ℕ)(θ:ℝ):
    flat (cruises L O N k w v (scalarOnly (front L O N k c w P))) p θ=paidScalar L O N k c w v P p θ:=by
  unfold paidScalar
  rw [←WilsonOlderFreshSoftRoseScalarLedger.original L O simple ratio N k c w wc cn P legal]
  unfold flat
  rw [WilsonOlderFreshSoftCoverScalar.received L O simple ratio N k w v (wc.trans cn) vw]
  simp only [uband,shine_lit]

theorem split (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N k c w v:ℕ)(vw:v≤w)(wc:w≤c)(cn:c≤N)(P:Era G ℝ)(legal:Auth k P)(p:ℕ)(θ:ℝ):
    flat (front L O N k c v P) p θ-paidScalar L O N k c w v P p θ=
      flat (cruises L O N k w v (axeR (front L O N k c w P))) p θ:=by
  let H:=front L O N k c w P
  have live:Auth k H:=cruising L simple ratio wc cn legal
  have keep:Auth k (scalarOnly H):=live.sub live.axe
  have signed:H-scalarOnly H=axeR H:=by dsimp [scalarOnly]; abel
  have move:=cruisePlus L vw simple ratio (wc.trans cn) live keep
  rw [signed] at move
  rw [←projected L O simple ratio N k c w v vw wc cn P legal p θ]
  change (listen p θ) (cruises L O N k c v P)-(listen p θ) (cruises L O N k w v (scalarOnly H))=
    (listen p θ) (cruises L O N k w v (axeR H))
  rw [←map_sub,move,cruisesMore L O P vw wc]
  rfl

def terminal (coeffs:(i:I)→Knob (D i))(phase:I→Chamber)(N per K c w v:ℕ)
    (routes:WilsonReceivedFixedDigitHistory.Digits R.family.path.levels I)(S:Finset I)
    (x:(i:I)→R.family.label (d i))(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)(p:ℕ)(θ:ℝ):ℂ:=
  ∑b:Columns R (fun i:S=>d i),packet R d S x N per K b*
    (paidScalar R.family.path.levels R.metals.O N (mass d S) c w v
      (WilsonOlderFreshSoftSocketHeard.during R d N K c routes y S f
        (stencil R D d (seats R d S b) coeffs phase)) p θ:ℂ)

def remainder (coeffs:(i:I)→Knob (D i))(phase:I→Chamber)(N per K c w v:ℕ)
    (routes:WilsonReceivedFixedDigitHistory.Digits R.family.path.levels I)(S:Finset I)
    (x:(i:I)→R.family.label (d i))(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)(p:ℕ)(θ:ℝ):ℂ:=
  ∑b:Columns R (fun i:S=>d i),packet R d S x N per K b*
    (flat (cruises R.family.path.levels R.metals.O N (mass d S) w v
      (axeR (WilsonOlderFreshSoftRoseScalarLedger.front R.family.path.levels R.metals.O N (mass d S) c w
        (WilsonOlderFreshSoftSocketHeard.during R d N K c routes y S f
          (stencil R D d (seats R d S b) coeffs phase))))) p θ:ℂ)

theorem original (simple:G.Simple)(ratio:LocalRatio O_)(vw:v≤w)(wc:w≤c)(ck:c≤K)(kn:K≤N)(p:ℕ)(θ:ℝ):
    figure R d κ pt N per K c v routes S x y f p θ -
      terminal R d κ pt N per K c w v routes S x y f p θ=
    remainder R d κ pt N per K c w v routes S x y f p θ:=by
  unfold figure terminal remainder
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro b _
  rw [←mul_sub,←Complex.ofReal_sub]
  congr 2
  let W:=stencil R D d (seats R d S b) κ pt
  have lawful:Wellness d W:=
    ((WilsonOlderFreshSoftFigures.original R D d 0 (w:=1) zero_lt_one).choose_spec.2 (seats R d S b) κ pt).1
  have high:=sound L_ O_ d N routes simple ratio W lawful (K-c) c (by omega)
  exact split L_ O_ simple ratio N k₀ c w v vw wc (ck.trans kn) (during R d N K c routes y S f (stencil R D d (seats R d S b) κ pt)) ((placedO _ (high.level' y) S).tuft f) p θ

theorem normalizedCost (simple:G.Simple)(ratio:LocalRatio O_)(vw:v≤w)(wc:w≤c)(ck:c≤K)(kn:K≤N)(p:ℕ)
    (kept:∀q:Selection R d S,degree R d S (fill R d S q)≤p){θ:ℝ}(θ₀:0≤θ)(θ₁:θ≤1):
    ‖normalized R d κ pt N per K c v routes S x y f p θ-
      terminal R d κ pt N per K c w v routes S x y f p θ‖≤
      (∑q:Selection R d S,‖weight R d N per K x S q‖*cost R d κ pt N per K c v routes S y f p θ q)+
      ‖remainder R d κ pt N per K c w v routes S x y f p θ‖:=by
  have price:=WilsonOlderFreshSoftSocketTotal.original R d κ pt N per K c v routes S x y f
    simple ratio (vw.trans wc) ck kn p kept θ₀ θ₁
  have signed:=original R d κ pt N per K c w v routes S x y f simple ratio vw wc ck kn p θ
  calc
    _ ≤ ‖normalized R d κ pt N per K c v routes S x y f p θ-figure R d κ pt N per K c v routes S x y f p θ‖+
      ‖figure R d κ pt N per K c v routes S x y f p θ-terminal R d κ pt N per K c w v routes S x y f p θ‖:=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ :=by rw [norm_sub_rev (normalized ..),signed];exact add_le_add price le_rfl

end YM.Integration.WilsonOlderFreshSoftSocketSourceDeposits
end
