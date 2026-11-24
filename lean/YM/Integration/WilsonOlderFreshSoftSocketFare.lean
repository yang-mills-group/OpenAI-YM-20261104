import YM.Integration.WilsonOlderFreshSoftSocketCensus
import YM.Integration.WilsonOlderFreshSoftSocketTest
import YM.Integration.WilsonOlderFreshSoftSocketRose

/-! The original measured source and its signed normalized scalar on the same funded collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketFare
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftOrdinary (material)
open WilsonOlderFreshSoftSocketRestored (stopped coin)
open WilsonIndependentCollarOrdinaryWeak (price)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonCoeffUV.Winding
variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I](R:Run G)(D d:I→ℕ)(p:ℕ)

open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketRestored (degree)
open WilsonOlderFreshSoftSocketKinetic (kinetic)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketTotal (figure normalized cost)
open WilsonReportingAbsoluteInletForecastBooks (value)
open ActualRunPhysicalPages Pert.Asymptotics
local notation "g_" => regulatorRun R.family

def bracket (N per K v h p:ℕ):ℝ:=
  let μ:=kinetic R.family.path.levels R.metals.O N K v
  let θ:=g_ N per v
  (g_ N per K^h)⁻¹*(θ^(p+1)*((h:ℝ)+2)*(WilsonReportingAbsoluteInletForecastBooks.mass p μ)^h+
    |(θ*value p μ θ)^h-g_ N per K^h|)

theorem original (S:Finset I)(occupied:S.Nonempty)(V:Realm G (p+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)
    (dorm:Dormitory V (mass d S) 0 Credit.leanC)(N per K c v:ℕ)
    (first:V.anchor≤v)(vc:v≤c)(ck:c≤K)(live:K≤N)(nK:g_ N per K≤1)(nv:g_ N per v≤1)
    (A B:ℝ)(front:PadRank V c K A)(march:PadRank V v c B)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(w:(i:I)→R.family.label (d i))
    (cells:Digits V.draws I)(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)
    (target H:ℕ)(kept:∀q:Selection R d S,degree R d S (fill R d S q)≤H)(crop:H≤p)
    (prepaid:∀h≤H,bracket R N per K v h p≤g_ N per v^target):
    let tape:=cast (congrArg (fun l=>Digits l I) draw) cells
    let θ:=g_ N per v
    ‖figure R d κ pt N per K c v tape S w y f p θ-normalized R d κ pt N per K c v tape S w y f p θ‖≤
      ((∑b:Columns R (fun i:S=>d i),‖packet R d S w N per K b‖)*WilsonOlderFreshSoftSocketCensus.fee R d S)*
        (θ^target*(‖f‖*gross R D d p S A B)):=by
  classical
  let tape:=cast (congrArg (fun l=>Digits l I) draw) cells
  let θ:=g_ N per v
  have θ0:0≤θ:=(ActualRunKernelPackets.regulator_pos R N per v (vc.trans (ck.trans live))).le
  have pm (Z:PowerSeries ℝ):0≤WilsonReportingAbsoluteInletForecastBooks.mass p Z:=
    sum_nonneg fun _ _=>abs_nonneg _
  have marked (q:(i:I)→Choice R d i):=
    WilsonOlderFreshSoftSocketTest.original R D d p S occupied V draw paid dorm N K c v first vc ck live
      A B front march κ pt q cells y f
  have cash:0≤ ‖f‖*gross R D d p S A B:=(pm _).trans (marked fun _=>Sum.inl ())
  have item (q:Selection R d S):
      cost R d κ pt N per K c v tape S y f p θ q≤θ^target*(‖f‖*gross R D d p S A B):=by
    exact mul_le_mul (prepaid _ (kept q)) (marked (fill R d S q)) (pm _) (pow_nonneg θ0 _)
  have simple:=V.hG
  have ratio:LocalRatio R.metals.O:=paid ▸ V.green
  apply (WilsonOlderFreshSoftSocketTotal.original R d κ pt N per K c v tape S w y f
    simple ratio vc ck live p (fun q=>(kept q).trans crop) θ0 nv).trans
  calc (∑q:Selection R d S,‖weight R d N per K w S q‖*cost R d κ pt N per K c v tape S y f p θ q)≤
      ∑q:Selection R d S,‖weight R d N per K w S q‖*(θ^target*(‖f‖*gross R D d p S A B)):=
        sum_le_sum fun q _=>mul_le_mul_of_nonneg_left (item q) (norm_nonneg _)
       _≤_:=by
         rw [←Finset.sum_mul]
         exact mul_le_mul_of_nonneg_right (WilsonOlderFreshSoftSocketCensus.original R d N per K live nK S w)
           (mul_nonneg (pow_nonneg θ0 _) cash)

end YM.Integration.WilsonOlderFreshSoftSocketFare
end
